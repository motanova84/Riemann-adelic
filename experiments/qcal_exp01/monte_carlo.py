"""Reproducible operating characteristics under specified synthetic models."""

from dataclasses import dataclass
from typing import Any, Iterable, Optional

import numpy as np

from .statistics import binomial_interval, gaussian_log_bayes_factor


@dataclass(frozen=True)
class MonteCarloResult:
    """Power and false-positive estimates with exact binomial intervals.

    duration_s=M/fs is conditional on M *independent* Gaussian observations.
    Oversampled filtered phase observations usually are not independent;
    high-SNR Gaussian phase noise and a calibrated exact reference are assumed.
    These results are simulations, not laboratory measurements.
    """

    sample_count: int
    duration_s: float
    trials: int
    threshold_log_bf: float
    h1_detections: int
    h0_false_positives: int
    h1_power: float
    h0_false_positive_rate: float
    h1_power_interval: tuple[float, float]
    h0_false_positive_interval: tuple[float, float]


def simulate_power(
    sample_sizes: Iterable[int], *, sigma: float, trials: int = 1000,
    reference_std: float = 0.1, fs: float = 1_000_000.0,
    threshold_log_bf: float = float(np.log(100.0)), seed: int = 0,
    slope_h1: float = 13.4034, slope_h0: float = 13.3000,
    intercept_prior_mean: float = 0.0, intercept_prior_sd: float = 1.0,
    quadratic_h0: Optional[float] = None, confidence: float = 0.95,
) -> list[MonteCarloResult]:
    """Simulate H1 detection power and H0 false-positive rate with default_rng.

    Each independent replication draws exact x_i ~ N(0, reference_std²), a
    shared-model intercept from its declared prior (or fixed if sd=0), and
    independent ε_i ~ N(0, sigma²). H1 and H0 reuse random draws for variance
    reduction, but each hypothesis's replications remain independent.
    Detection means log BF >= threshold_log_bf, which is not a frequentist
    significance level; the H0 rate is measured, not assumed.

    Args:
        sample_sizes: Positive integer numbers M of independent samples.
        sigma: Known positive response noise, not a fitted residual deviation.
        trials: Positive number of Monte Carlo replications per M.
        reference_std: Positive standard deviation of the calibrated reference.
        fs: Assumed independent observation rate in Hz, for duration M/fs.
        threshold_log_bf: Prespecified natural-log evidence threshold.
        seed: Nonnegative integer seed for reproducibility.
        slope_h1: Fully specified linear H1 slope.
        slope_h0: Fully specified linear H0 slope.
        intercept_prior_mean: Common proper intercept prior mean.
        intercept_prior_sd: Common prior deviation; zero means point intercept.
        quadratic_h0: Optional fixed H0 quadratic coefficient.
        confidence: Coverage for exact binomial intervals.

    Returns:
        One record per requested M, preserving input order.

    Raises:
        ValueError: Invalid acquisition, prior, model or replication parameters.
    """
    sizes = list(sample_sizes)
    if any(isinstance(n, bool) or not isinstance(n, (int, np.integer)) or n <= 0
           for n in sizes):
        raise ValueError("sample_sizes must contain positive integers")
    if isinstance(trials, bool) or not isinstance(trials, (int, np.integer)) or trials <= 0:
        raise ValueError("trials must be a positive integer")
    if isinstance(seed, bool) or not isinstance(seed, (int, np.integer)) or seed < 0:
        raise ValueError("seed must be a nonnegative integer")
    if (not all(np.isfinite(v) for v in (reference_std, fs, threshold_log_bf)) or
            reference_std <= 0 or fs <= 0):
        raise ValueError("reference_std and fs must be positive; threshold finite")
    # Validate even when no sample sizes were requested.
    gaussian_log_bayes_factor([], [], sigma, slope_h1=slope_h1, slope_h0=slope_h0,
                              intercept_prior_mean=intercept_prior_mean,
                              intercept_prior_sd=intercept_prior_sd,
                              quadratic_h0=quadratic_h0)
    binomial_interval(0, int(trials), confidence)
    rng = np.random.default_rng(seed)
    q0 = 0.0 if quadratic_h0 is None else quadratic_h0
    results = []
    for n in sizes:
        h1_count = h0_count = 0
        for _ in range(trials):
            x = rng.normal(0.0, reference_std, n)
            noise = rng.normal(0.0, sigma, n)
            intercept = rng.normal(intercept_prior_mean, intercept_prior_sd)
            common = intercept + noise
            options = dict(slope_h1=slope_h1, slope_h0=slope_h0,
                           intercept_prior_mean=intercept_prior_mean,
                           intercept_prior_sd=intercept_prior_sd, quadratic_h0=quadratic_h0)
            log1 = gaussian_log_bayes_factor(x, common + slope_h1 * x, sigma, **options)
            log0 = gaussian_log_bayes_factor(
                x, common + slope_h0 * x + q0 * x**2, sigma, **options
            )
            h1_count += int(log1 >= threshold_log_bf)
            h0_count += int(log0 >= threshold_log_bf)
        results.append(MonteCarloResult(
            int(n), float(n / fs), int(trials), float(threshold_log_bf),
            h1_count, h0_count, h1_count / trials, h0_count / trials,
            binomial_interval(h1_count, int(trials), confidence),
            binomial_interval(h0_count, int(trials), confidence),
        ))
    return results


def plot_operating_characteristics(
    results: Iterable[MonteCarloResult], ax: Optional[Any] = None,
) -> Any:
    """Optionally plot synthetic power and H0 error with binomial intervals.

    Matplotlib is imported only when plotting; the returned Axes can be saved
    by the caller. Acquisition time is explicitly conditional on independence.
    """
    import matplotlib.pyplot as plt

    records = list(results)
    if not records:
        raise ValueError("at least one Monte Carlo result is required")
    if ax is None:
        _, ax = plt.subplots()
    times = np.array([record.duration_s for record in records])
    for name, field, interval in (
        (r"$H_1$ detection power", "h1_power", "h1_power_interval"),
        (r"$H_0$ false-positive rate", "h0_false_positive_rate", "h0_false_positive_interval"),
    ):
        values = np.array([getattr(record, field) for record in records])
        bounds = np.array([getattr(record, interval) for record in records])
        ax.errorbar(times, values, yerr=np.maximum(0.0, np.vstack(
            (values - bounds[:, 0], bounds[:, 1] - values))), marker="o", label=name)
    ax.set_xlabel(r"Conditional acquisition time $T=M/f_s$ (s; independent samples)")
    ax.set_ylabel(r"Probability of $\log \mathrm{BF}_{10}\geq$ threshold")
    ax.set_ylim(0, 1)
    ax.legend()
    return ax

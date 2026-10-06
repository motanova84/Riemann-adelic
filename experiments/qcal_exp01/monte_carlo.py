"""Reproducible operating characteristics under specified synthetic models."""

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
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
    detection_rule: str = "log BF10 > threshold"


def simulate_power(
    sample_sizes: Iterable[int], *, sigma: float, trials: int = 1000,
    reference_std: float = 0.1, fs: float = 1_000_000.0,
    threshold_log_bf: float = 5.0, seed: int = 0,
    slope_h1: float = 13.4034, slope_h0: float = 13.3000,
    intercept_prior_mean: float = 0.0, intercept_prior_sd: float = 1.0,
    quadratic_h0: Optional[float] = None, confidence: float = 0.95,
) -> list[MonteCarloResult]:
    """Simulate H1 detection power and H0 false-positive rate with default_rng.

    Each independent replication draws exact x_i ~ N(0, reference_std²), a
    shared-model intercept from its declared prior (or fixed if sd=0), and
    independent ε_i ~ N(0, sigma²). H1 and H0 reuse random draws for variance
    reduction, but each hypothesis's replications remain independent.
    Detection means log BF > threshold_log_bf (strict), which is not a frequentist
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
            h1_count += int(log1 > threshold_log_bf)
            h0_count += int(log0 > threshold_log_bf)
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
    ax.set_ylabel(r"Probability of $\log \mathrm{BF}_{10}>$ threshold")
    ax.set_ylim(0, 1)
    ax.legend()
    return ax


def coupling_standard_error_from_snr(
    snr_linear: Any, *, sample_count: int, reference_std: float,
    dual_channel: bool = True,
) -> np.ndarray:
    """Return analytic σ_kappa for a high-SNR independent Gaussian phase model.

    Power SNR = A²/E|n_I+i n_Q|² with independent equal-variance quadrature
    noise. One channel has phase variance ≈1/(2 SNR); the difference of two
    independent equally noisy channels has variance ≈1/SNR. Assume an exact
    centered reference orthogonal to any fitted intercept/drift, with
    Σ x_i²=M*reference_std². Then σ_kappa=σ_phase/sqrt(Σ x_i²).

    This is an idealized analytic benchmark, not a calibration of filtered,
    low-SNR, correlated, or measured experimental data.

    Args:
        snr_linear: Positive finite scalar or array of linear power SNR.
        sample_count: Positive integer number of independent observations M.
        reference_std: Positive RMS of centered calibrated x0.
        dual_channel: Whether two equally noisy independent phase channels differ.

    Returns:
        Array of conditional standard errors in rad/reference units.
    """
    snr = np.asarray(snr_linear, dtype=float)
    if (not np.all(np.isfinite(snr)) or np.any(snr <= 0)
            or not np.isfinite(reference_std) or reference_std <= 0):
        raise ValueError("SNR and reference_std must be finite and positive")
    if (isinstance(sample_count, bool)
            or not isinstance(sample_count, (int, np.integer)) or sample_count <= 0):
        raise ValueError("sample_count must be a positive integer")
    phase_variance = (1.0 if dual_channel else 0.5) / snr
    return np.sqrt(phase_variance / (sample_count * reference_std**2))


def plot_sigma_kappa_vs_snr(
    snr_db: Optional[Any] = None, *, sample_count: int = 1000,
    reference_std: float = 0.1, slope_h1: float = 13.4034,
    slope_h0: float = 13.3000, dual_channel: bool = True,
    ax: Optional[Any] = None,
) -> Any:
    """Plot conditional analytic σ_kappa versus power SNR in dB.

    Δκ/3 is a three-standard-deviation separation from a fixed alternative.
    Δκ/6 instead gives nonoverlapping ±3σ intervals about both point slopes
    (equivalently a midpoint classification margin of three σ). Neither is
    a Bayes-factor threshold or a claim of physical confirmation.
    """
    import matplotlib.pyplot as plt

    db = np.linspace(10.0, 60.0, 101) if snr_db is None else np.asarray(snr_db, dtype=float)
    if db.ndim != 1 or not db.size or not np.all(np.isfinite(db)):
        raise ValueError("snr_db must be a finite nonempty vector")
    if not np.isfinite(slope_h1) or not np.isfinite(slope_h0) or slope_h1 == slope_h0:
        raise ValueError("point slopes must be finite and distinct")
    errors = coupling_standard_error_from_snr(
        10 ** (db / 10), sample_count=sample_count,
        reference_std=reference_std, dual_channel=dual_channel,
    )
    if ax is None:
        _, ax = plt.subplots()
    delta = abs(slope_h1 - slope_h0)
    ax.semilogy(db, errors, label=r"Conditional analytic $\sigma_\kappa$")
    ax.axhline(delta / 3, linestyle="--", label=r"Fixed-alternative $3\sigma$: $\Delta\kappa/3$")
    ax.axhline(delta / 6, linestyle=":", label=r"Nonoverlapping $\pm3\sigma$/classification: $\Delta\kappa/6$")
    ax.set_xlabel("Power SNR (dB)")
    ax.set_ylabel(r"$\sigma_\kappa$ (rad / declared displacement unit)")
    ax.set_title(f"Synthetic high-SNR independent model; M={sample_count}")
    ax.legend()
    return ax


def _project_output_path(value: str) -> Path:
    """Resolve an explicitly selected output path, including temporary folders."""
    return Path(value).expanduser().resolve()


def main(argv: Optional[list[str]] = None) -> int:
    """Run reproducible synthetic MC and optionally save JSON and PNG plots.

    Example:
        python -m experiments.qcal_exp01.monte_carlo --sample-sizes 100 1000
        --trials 100 --sigma .1 --seed 0 --output results/example.json

    JSON records configuration, point hypotheses, covariance/prior assumptions,
    seed/generator, strict detection rule, and intervals. Output paths are
    explicitly selected by the caller.
    """
    parser = argparse.ArgumentParser(description="Conditional synthetic point-model evidence simulation")
    parser.add_argument("--sample-sizes", nargs="+", type=int, default=[100, 1000, 10000])
    parser.add_argument("--sigma", type=float, default=0.1,
                        help="Independently specified response Gaussian SD in rad")
    parser.add_argument("--trials", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--fs", type=float, default=1_000_000.0)
    parser.add_argument("--reference-std", type=float, default=0.1)
    parser.add_argument("--threshold-log-bf", type=float, default=5.0)
    parser.add_argument("--slope-h1", type=float, default=13.4034)
    parser.add_argument("--slope-h0", type=float, default=13.3000)
    parser.add_argument("--quadratic-h0", type=float, default=None)
    parser.add_argument("--intercept-prior-mean", type=float, default=0.0)
    parser.add_argument("--intercept-prior-sd", type=float, default=1.0)
    parser.add_argument("--confidence", type=float, default=0.95)
    parser.add_argument("--output", type=_project_output_path)
    parser.add_argument("--plot", type=_project_output_path)
    parser.add_argument("--snr-plot", type=_project_output_path)
    args = parser.parse_args(argv)
    if args.snr_plot and args.slope_h1 == args.slope_h0:
        parser.error("--snr-plot requires distinct point slopes")
    config = {name: getattr(args, name) for name in (
        "sigma", "trials", "reference_std", "fs", "threshold_log_bf", "seed",
        "slope_h1", "slope_h0", "intercept_prior_mean", "intercept_prior_sd",
        "quadratic_h0", "confidence",
    )}
    try:
        results = simulate_power(args.sample_sizes, **config)
    except ValueError as error:
        parser.error(str(error))
    document = {
        "schema_version": 1,
        "source": "synthetic Monte Carlo; no physical acquisition or DMA",
        "interpretation": "Conditional model discrimination only; no physics validation or RH proof",
        "configuration": {"sample_sizes": args.sample_sizes, **config},
        "random_generator": {"api": "numpy.random.default_rng", "bit_generator": "PCG64",
                             "numpy_version": np.__version__, "seed": args.seed},
        "hypotheses": {
            "H1": {"mean": "b + slope_h1*x", "point_slope": args.slope_h1},
            "H0": {"mean": "b + slope_h0*x + quadratic_h0*x^2",
                   "point_slope": args.slope_h0, "fixed_quadratic": args.quadratic_h0},
        },
        "assumptions": {
            "noise": "Independent N(0,sigma^2) response errors; sigma specified, never residual-fitted",
            "reference": "Exact independently calibrated x_i ~ N(0,reference_std^2)",
            "units": "Response rad; reference in declared displacement units",
            "intercept": "Common proper Gaussian prior integrated analytically; sd=0 is a point intercept",
            "marginal_covariance": "sigma^2*I_M + intercept_prior_sd^2*1_M*1_M^T",
            "simulation_intercept": "Each replication draws b from the same declared prior",
            "duration": "T=M/fs only conditional on independent observations, not oversampled FIR outputs",
            "phase_caveat": "Independent Gaussian phase errors require a high-SNR approximation and covariance calibration",
            "decision": "Strict log BF10 > threshold_log_bf; natural logarithm",
            "intervals": "Exact equal-tailed Clopper-Pearson binomial intervals",
            "replications": "H1 and H0 share random numbers; trials independent within each hypothesis",
        },
        "analytic_snr_benchmark": {
            "model": "High-SNR independent equally noisy dual IF phase channels",
            "power_snr_definition": "A^2 / E|n_I+i*n_Q|^2",
            "differential_phase_variance": "1/SNR",
            "reference_norm": "sum(x_i^2)=M*reference_std^2, centered and orthogonal to nuisance trends",
            "sigma_kappa": "1/sqrt(SNR*M*reference_std^2)",
            "sample_count": args.sample_sizes[-1],
            "snr_db_range": [10, 60],
            "single_fixed_alternative_3sigma_limit": abs(args.slope_h1 - args.slope_h0) / 3,
            "nonoverlapping_3sigma_classification_limit": abs(args.slope_h1 - args.slope_h0) / 6,
            "caveat": "Analytic approximation, not a measured or FIR-corrected uncertainty",
        },
        "results": [asdict(result) for result in results],
    }
    text = json.dumps(document, indent=2, allow_nan=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    if args.plot or args.snr_plot:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        if args.plot:
            ax = plot_operating_characteristics(results)
            ax.set_title("Synthetic conditional Monte Carlo (independent Gaussian samples)")
            args.plot.parent.mkdir(parents=True, exist_ok=True)
            ax.figure.savefig(args.plot, dpi=150, bbox_inches="tight")
            plt.close(ax.figure)
        if args.snr_plot:
            ax = plot_sigma_kappa_vs_snr(
                sample_count=args.sample_sizes[-1], reference_std=args.reference_std,
                slope_h1=args.slope_h1, slope_h0=args.slope_h0,
            )
            args.snr_plot.parent.mkdir(parents=True, exist_ok=True)
            ax.figure.savefig(args.snr_plot, dpi=150, bbox_inches="tight")
            plt.close(ax.figure)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

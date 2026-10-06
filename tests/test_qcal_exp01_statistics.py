"""Exact-evidence and reproducible simulation tests under declared assumptions."""

import numpy as np
import pytest
from scipy.stats import multivariate_normal

from experiments.qcal_exp01.monte_carlo import plot_operating_characteristics, simulate_power
from experiments.qcal_exp01.statistics import (
    binomial_interval,
    gaussian_log_bayes_factor,
)


@pytest.mark.parametrize("prior_sd", [0.0, 0.8, 10.0])
@pytest.mark.parametrize("quadratic", [None, 0.4])
def test_evidence_equals_direct_proper_gaussian_integral(
    prior_sd: float, quadratic: float,
) -> None:
    """Analytic integration agrees with the full covariance Gaussian density."""
    rng = np.random.default_rng(42)
    x = rng.normal(0, 0.2, 20)
    y = 0.6 + 13.4034 * x + rng.normal(0, 0.05, x.size)
    sigma = 0.05
    covariance = sigma**2 * np.eye(x.size) + prior_sd**2 * np.ones((x.size, x.size))
    mean1 = 0.4 + 13.4034 * x
    mean0 = 0.4 + 13.3 * x + (0 if quadratic is None else quadratic) * x**2
    direct = (multivariate_normal.logpdf(y, mean=mean1, cov=covariance)
              - multivariate_normal.logpdf(y, mean=mean0, cov=covariance))
    actual = gaussian_log_bayes_factor(
        x, y, sigma, intercept_prior_mean=0.4,
        intercept_prior_sd=prior_sd, quadratic_h0=quadratic,
    )
    assert actual == pytest.approx(direct, rel=1e-8, abs=1e-8)


def test_bayes_factor_direction_empty_and_equal_models() -> None:
    """Point slope evidence has the declared sign and no hidden residual noise fit."""
    x = np.linspace(-1, 1, 100)
    assert gaussian_log_bayes_factor(x, 13.4034 * x, 0.01) > 100
    assert gaussian_log_bayes_factor(x, 13.3 * x, 0.01) < -100
    assert gaussian_log_bayes_factor([], [], 0.1) == 0
    assert gaussian_log_bayes_factor(x, x, 0.1, slope_h0=13.4034) == 0
    with pytest.raises(TypeError):
        gaussian_log_bayes_factor(x, x)  # Noise must be explicitly supplied.
    for sigma in (0, -1, np.nan):
        with pytest.raises(ValueError):
            gaussian_log_bayes_factor(x, x, sigma)
    with pytest.raises(ValueError):
        gaussian_log_bayes_factor(x, x, 0.1, intercept_prior_sd=np.inf)
    with pytest.raises(ValueError):
        gaussian_log_bayes_factor(x, x, 0.1, intercept_prior_sd=-1)
    with pytest.raises(ValueError):
        gaussian_log_bayes_factor([1, 2], [1], 0.1)
    with pytest.raises(ValueError):
        gaussian_log_bayes_factor([np.nan], [0], 0.1)


def test_optional_fixed_quadratic_h0() -> None:
    """A quadratic H0 is a prespecified alternative, not an implicit fitted model."""
    x = np.linspace(-1, 1, 200)
    y0 = 13.3 * x + 0.4 * x**2
    assert gaussian_log_bayes_factor(x, y0, 0.01, quadratic_h0=0.4) < -100


def test_binomial_intervals_include_boundaries() -> None:
    """Zero observed false positives are not reported as a known zero rate."""
    zero = binomial_interval(0, 100)
    all_events = binomial_interval(100, 100)
    assert zero[0] == 0 and 0 < zero[1] < 0.1
    assert all_events[1] == 1 and 0.9 < all_events[0] < 1
    assert zero[1] == pytest.approx(1 - 0.025 ** (1 / 100))
    for args in [(-1, 100), (101, 100), (0, 0), (0.5, 100)]:
        with pytest.raises(ValueError):
            binomial_interval(*args)


def test_monte_carlo_reproducibility_power_and_h0_error() -> None:
    """Both hypotheses are simulated; acquisition time is conditional on independence."""
    kwargs = dict(sigma=0.03, trials=400, reference_std=0.1, seed=52)
    results = simulate_power([10, 200], **kwargs)
    assert results == simulate_power([10, 200], **kwargs)
    short, long = results
    assert long.h1_power > short.h1_power
    assert long.h1_power > 0.85
    assert long.h0_false_positive_rate < 0.03
    assert long.duration_s == 200 / 1_000_000
    assert long.h1_power_interval[0] <= long.h1_power <= long.h1_power_interval[1]
    assert long.h0_false_positive_interval[0] <= long.h0_false_positive_rate
    assert long.h0_false_positive_interval[1] > 0
    assert long.h1_detections == round(long.h1_power * long.trials)
    assert long.h0_false_positives == round(long.h0_false_positive_rate * long.trials)


def test_monte_carlo_optional_quadratic_and_fixed_intercept() -> None:
    """The generator uses the very same fully specified alternative as evidence."""
    result = simulate_power(
        [100], sigma=0.01, trials=100, reference_std=0.3, seed=4,
        quadratic_h0=0.4, intercept_prior_mean=0.5, intercept_prior_sd=0,
    )[0]
    assert result.h1_power > 0.95
    assert result.h0_false_positive_rate < 0.05


def test_optional_plot_uses_conditional_time_and_both_hypotheses() -> None:
    """Optional plotting exposes statistical assumptions rather than a physics claim."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    records = simulate_power([10, 20], sigma=0.1, trials=10, seed=3)
    ax = plot_operating_characteristics(records)
    assert "independent samples" in ax.get_xlabel()
    assert len(ax.get_legend().get_texts()) == 2
    ax.figure.canvas.draw()  # Also validates math labels against mathtext.
    plt.close(ax.figure)


@pytest.mark.parametrize("kwargs", [
    {"sigma": -1}, {"sigma": 0.1, "trials": 0},
    {"sigma": 0.1, "fs": 0}, {"sigma": 0.1, "reference_std": 0},
    {"sigma": 0.1, "confidence": 1}, {"sigma": 0.1, "seed": -1},
    {"sigma": 0.1, "intercept_prior_sd": np.inf},
])
def test_monte_carlo_input_validation(kwargs: dict) -> None:
    """Invalid simulations fail before generating apparently meaningful probabilities."""
    with pytest.raises(ValueError):
        simulate_power([10], **kwargs)
    with pytest.raises(ValueError):
        simulate_power([1.5], sigma=0.1)

"""Conditional Gaussian point-model evidence, not global physics confirmation."""

from typing import Optional

import numpy as np
from numpy.typing import ArrayLike
from scipy.stats import beta

from .dsp import _vector


def gaussian_log_bayes_factor(
    x: ArrayLike, y: ArrayLike, sigma: float, *,
    slope_h1: float = 13.4034, slope_h0: float = 13.3000,
    intercept_prior_mean: float = 0.0, intercept_prior_sd: float = 1.0,
    quadratic_h0: Optional[float] = None,
) -> float:
    """Return log p(y|H1,x)/p(y|H0,x) for two fully specified slopes.

    H1: y_i = b + slope_h1*x_i + ε_i.
    H0: y_i = b + slope_h0*x_i + quadratic_h0*x_i² + ε_i.
    The optional quadratic coefficient is fixed *before* looking at the data,
    not fitted. In both hypotheses ε_i are independent N(0, sigma²) errors
    and x is an exact calibrated reference, independent of the errors.
    sigma must be independently known: plugging in a residual estimate is
    not this Bayes factor. These assumptions do not automatically hold for
    low-SNR phase extraction or correlated FIR outputs. If drift or another
    deterministic component is removed, it must be known independently.
    Estimating such a component from these same observations changes the
    likelihood and cannot be silently substituted into this point-model BF.

    A common proper prior b ~ N(intercept_prior_mean, intercept_prior_sd²)
    is integrated analytically. sd=0 denotes a fully specified point intercept.
    With r=y-slope*x-quadratic*x²-prior_mean, the quadratic form is
    ||r-mean(r)||²/sigma² + n*mean(r)²/(sigma²+n*prior_sd²).
    The two common covariance determinants cancel exactly. An empty data set
    returns zero evidence. No improper flat intercept prior is supported.

    Args:
        x: Finite, real, one-dimensional calibrated reference observations.
        y: Matching finite real responses (for example, phase residuals).
        sigma: Independently known positive Gaussian standard deviation.
        slope_h1: Fully specified H1 coupling in response/reference units.
        slope_h0: Fully specified H0 coupling in the same units.
        intercept_prior_mean: Prespecified common prior mean or point intercept.
        intercept_prior_sd: Finite nonnegative prior deviation; zero is fixed.
        quadratic_h0: Optional prespecified H0 quadratic coefficient.

    Returns:
        Natural-log Bayes factor. Positive values support H1 within these models.

    Raises:
        ValueError: Nonfinite input, shape mismatch or invalid noise/prior.
    """
    x0, response = _vector(x, "x"), _vector(y, "y")
    if x0.shape != response.shape:
        raise ValueError("x and y must have the same shape")
    q0 = 0.0 if quadratic_h0 is None else quadratic_h0
    if not all(np.isfinite(v) for v in
               (sigma, slope_h1, slope_h0, intercept_prior_mean, intercept_prior_sd, q0)):
        raise ValueError("noise, model and prior parameters must be finite")
    if sigma <= 0 or intercept_prior_sd < 0:
        raise ValueError("sigma must be positive and prior_sd nonnegative")
    if not x0.size:
        return 0.0
    r1 = response - intercept_prior_mean - slope_h1 * x0
    r0 = response - intercept_prior_mean - slope_h0 * x0 - q0 * x0**2
    m0, m1 = float(np.mean(r0)), float(np.mean(r1))
    c0, c1 = r0 - m0, r1 - m1
    # Difference-of-squares form avoids subtracting two large residual sums.
    difference = np.dot(c0 - c1, c0 + c1) / sigma**2
    difference += x0.size * (m0 - m1) * (m0 + m1) / (
        sigma**2 + x0.size * intercept_prior_sd**2
    )
    return float(0.5 * difference)


def binomial_interval(
    successes: int, trials: int, confidence: float = 0.95,
) -> tuple[float, float]:
    """Return an exact equal-tailed Clopper–Pearson binomial interval.

    Args:
        successes: Integer event count between zero and trials.
        trials: Positive number of independent Bernoulli replications.
        confidence: Coverage probability strictly between zero and one.

    Returns:
        Conservative lower and upper probability bounds, including endpoints.
    """
    if (isinstance(successes, bool) or isinstance(trials, bool) or
            not isinstance(successes, (int, np.integer)) or
            not isinstance(trials, (int, np.integer)) or
            trials <= 0 or not 0 <= successes <= trials):
        raise ValueError("require integer 0 <= successes <= positive trials")
    if not np.isfinite(confidence) or not 0 < confidence < 1:
        raise ValueError("confidence must be between zero and one")
    alpha = (1 - confidence) / 2
    lower = 0.0 if successes == 0 else float(beta.ppf(alpha, successes, trials - successes + 1))
    upper = 1.0 if successes == trials else float(beta.ppf(1 - alpha, successes + 1, trials - successes))
    return lower, upper

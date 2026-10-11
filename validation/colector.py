"""Numerical consistency checks for supplied conditional collector data.

No data are acquired here. Passing tolerances is neither experimental
confirmation nor an RH proof. Use decimal strings to avoid binary-float
input rounding. The synthetic witness 2.5782 is not a universal constant.
"""

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Sequence, Union

import mpmath as mp

RealInput = Union[str, int, float, mp.mpf]
AXIS_NAMES = ("geometrico", "fisico", "biologico")


@dataclass(frozen=True)
class Eje:
    """Supplied axis; name is canonical, phase and invariant are finite reals."""

    nombre: str
    fase: RealInput
    invariante: RealInput


@dataclass(frozen=True)
class Acoplamiento:
    """Independent before/after measurements of epsilon and frequency f0."""

    epsilon_antes: RealInput
    f0_antes: RealInput
    epsilon_despues: RealInput
    f0_despues: RealInput


@dataclass(frozen=True)
class Residual:
    """Transparent comparison using |left-right| <= atol + rtol*scale."""

    left: mp.mpf
    right: mp.mpf
    discrepancy: mp.mpf
    tolerance: mp.mpf
    passed: bool


@dataclass(frozen=True)
class Report:
    """Strict bounds, positivity and rounded residuals, not empirical evidence."""

    kappa: mp.mpf
    dps: int
    positive: bool
    in_interval: bool
    biological_positive: bool
    checks: dict[str, Residual]
    passed: bool
    precision_note: str = (
        "Interval membership uses the supplied value exactly; kappa is rounded. "
        "Residuals use rounded calculations at dps, not certified error bounds. "
        "Zero tolerance means equality of rounded calculations, not exact reals; "
        "cancellation can hide discrepancies. Lost float/mpf digits cannot be "
        "recovered. Passing is not empirical confirmation or an RH proof."
    )


def _finite(value: RealInput, label: str) -> mp.mpf:
    """Convert a finite real input or raise ValueError with its field label."""
    if isinstance(value, bool):
        raise ValueError(f"{label} must be a finite real")
    try:
        result = mp.mpf(value)
    except (ValueError, TypeError, OverflowError) as exc:
        raise ValueError(f"{label} must be a finite real") from exc
    if not mp.isfinite(result):
        raise ValueError(f"{label} must be a finite real")
    return result


def _compare(left: mp.mpf, right: mp.mpf, atol: mp.mpf, rtol: mp.mpf) -> Residual:
    """Return a symmetric mixed absolute/relative residual at local precision."""
    discrepancy = abs(left - right)
    tolerance = atol + rtol * max(abs(left), abs(right))
    return Residual(left, right, discrepancy, tolerance, bool(discrepancy <= tolerance))


def _strict_interval(value: RealInput) -> bool:
    """Compare supplied finite values exactly, independently of working dps."""
    if isinstance(value, mp.mpf):
        # An mpf stores an exact dyadic value; it cannot recover its input digits.
        sign, mantissa, exponent, _ = value._mpf_
        exact = Fraction((-1 if sign else 1) * mantissa) * Fraction(2)**exponent
    else:
        exact = Fraction(value)
    return Fraction(2578, 1000) < exact < Fraction(2579, 1000)


def validate(
    kappa: RealInput,
    axes: Sequence[Eje],
    aeffmax_observed: RealInput,
    coupling: Acoplamiento,
    *,
    atol: RealInput,
    rtol: RealInput,
    dps: int = 50,
) -> Report:
    """Check membership and the three conditional laws against supplied data.

    Args:
        kappa: Abstract collector parameter, strictly between 2.578 and 2.579.
        axes: Exactly one of each AXIS_NAMES, with finite phase and invariant.
        aeffmax_observed: Independently supplied biological observation.
        coupling: Supplied before/after epsilon and f0 values.
        atol: Explicit finite nonnegative absolute tolerance.
        rtol: Explicit finite nonnegative relative tolerance.
        dps: Local decimal precision, an integer >= 30 (default 50).

    Returns:
        Report with each pairwise axis discrepancy, membership residuals,
        observed biological residual versus κ²/(2π), coupling product residual,
        strict bounds, independent biological positivity and aggregate pass.
        Interval bounds compare the supplied value exactly, without tolerance.
        The reported kappa and residual values are rounded to working precision.

    Raises:
        ValueError: For nonfinite inputs, invalid names or tolerances/precision.

    Notes:
        This checks consistency with assumptions, not their physical truth.
        mpmath precision is restored on success and failure. It does not
        recover digits already lost in float or low-precision mpf inputs.
        Residuals are rounded, not certified enclosures; zero tolerance means
        equality of rounded calculations, not equality of exact real values.
        Increasing dps may reveal discrepancies hidden by cancellation.
    """
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise ValueError("dps must be an integer >= 30")
    if len(axes) != 3 or {axis.nombre for axis in axes} != set(AXIS_NAMES):
        raise ValueError(f"axes must contain exactly one of each {AXIS_NAMES}")
    with mp.workdps(dps):
        absolute = _finite(atol, "atol")
        relative = _finite(rtol, "rtol")
        if absolute < 0 or relative < 0:
            raise ValueError("atol and rtol must be nonnegative")
        parameter = _finite(kappa, "kappa")
        values = {}
        for axis in axes:
            _finite(axis.fase, f"{axis.nombre}.fase")
            values[axis.nombre] = _finite(axis.invariante, f"{axis.nombre}.invariante")
        observed = _finite(aeffmax_observed, "aeffmax_observed")
        before = _finite(coupling.epsilon_antes, "epsilon_antes") * _finite(coupling.f0_antes, "f0_antes")
        after = _finite(coupling.epsilon_despues, "epsilon_despues") * _finite(coupling.f0_despues, "f0_despues")
        checks = {
            f"membership:{name}": _compare(values[name], parameter, absolute, relative)
            for name in AXIS_NAMES
        }
        for first, second in combinations(AXIS_NAMES, 2):
            checks[f"structure:{first}:{second}"] = _compare(
                values[first], values[second], absolute, relative
            )
        checks["biological"] = _compare(observed, parameter**2 / (2 * mp.pi), absolute, relative)
        checks["product"] = _compare(before, after, absolute, relative)
        positive = bool(parameter > 0)
        in_interval = _strict_interval(kappa)
        biological_positive = bool(observed > 0)
        passed = (
            positive and in_interval and biological_positive
            and all(check.passed for check in checks.values())
        )
        return Report(
            parameter, dps, positive, in_interval, biological_positive, checks, passed
        )

"""Numerical consistency checks for supplied conditional collector data.

No data are acquired here. Passing tolerances is neither experimental
confirmation nor an RH proof. Use decimal strings to avoid binary-float
input rounding. The synthetic witness 2.5782 is not a universal constant.
"""

from dataclasses import dataclass
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
    """Strict bounds, all residuals and aggregate consistency at given dps."""

    kappa: mp.mpf
    dps: int
    positive: bool
    in_interval: bool
    checks: dict[str, Residual]
    passed: bool


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
        strict bounds and aggregate pass. Interval bounds have no tolerance.

    Raises:
        ValueError: For nonfinite inputs, invalid names or tolerances/precision.

    Notes:
        This checks consistency with assumptions, not their physical truth.
        mpmath precision is restored on success and failure. It does not
        recover digits already lost in float or low-precision mpf inputs.
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
        in_interval = bool(mp.mpf("2.578") < parameter < mp.mpf("2.579"))
        passed = positive and in_interval and all(check.passed for check in checks.values())
        return Report(parameter, dps, positive, in_interval, checks, passed)

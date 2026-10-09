"""Synthetic consistency tests, not biological or experimental evidence."""

from dataclasses import replace
from pathlib import Path
import re

import mpmath as mp
import pytest

from validation.colector import AXIS_NAMES, Acoplamiento, Eje, validate

ROOT = Path(__file__).resolve().parents[1]
# Independently supplied, precomputed synthetic observation rounded to 49 d.p.
OBSERVED = "1.0579212477474702068742643813019940129981341163664"


def synthetic_data() -> dict:
    """Return synthetic observations with nontrivial product-preserving coupling."""
    return {
        "kappa": "2.5782",
        "axes": [Eje(name, str(index), "2.5782") for index, name in enumerate(AXIS_NAMES)],
        "aeffmax_observed": OBSERVED,
        "coupling": Acoplamiento("0.01", "141.7001", "0.02", "70.85005"),
        "atol": "1e-45",
        "rtol": "1e-45",
    }


def test_synthetic_witness_and_all_residuals() -> None:
    """Check every pair, structural membership, biology and independent coupling."""
    report = validate(**synthetic_data())
    assert report.passed and report.positive and report.in_interval
    assert len(report.checks) == 8
    assert len([key for key in report.checks if key.startswith("structure:")]) == 3
    for residual in report.checks.values():
        assert residual.passed
        assert residual.discrepancy <= residual.tolerance
    assert report.checks["product"].left == report.checks["product"].right


@pytest.mark.parametrize("kappa", ["2.578", "2.579", "2.5779", "2.5791", "0", "-2.5782"])
def test_strict_bounds_cannot_be_relaxed_by_tolerance(kappa: str) -> None:
    """Even a huge explicit tolerance cannot relax the open parameter interval."""
    data = synthetic_data()
    data.update(kappa=kappa, atol="100", rtol="100")
    report = validate(**data)
    assert not report.passed and not report.in_interval


@pytest.mark.parametrize("kappa", ["2.5781", "2.5788"])
def test_parameter_is_not_forced_to_witness(kappa: str) -> None:
    """Other collectors in the open interval satisfy the conditional model."""
    data = synthetic_data()
    with mp.workdps(60):
        observed = mp.nstr(mp.mpf(kappa)**2 / (2 * mp.pi), 55)
    data.update(
        kappa=kappa,
        axes=[Eje(name, 0, kappa) for name in AXIS_NAMES],
        aeffmax_observed=observed,
    )
    assert validate(**data).passed


def test_all_pairwise_discrepancies_are_checked() -> None:
    """Axes from freely constructed records need not have identical invariants."""
    data = synthetic_data()
    data["axes"] = [Eje(name, 0, str(index)) for index, name in enumerate(AXIS_NAMES)]
    report = validate(**data)
    assert not report.passed
    pairs = {key: value for key, value in report.checks.items() if key.startswith("structure:")}
    assert [value.discrepancy for value in pairs.values()] == [1, 2, 1]
    assert all(not value.passed for value in pairs.values())


def test_common_wrong_invariant_fails_membership() -> None:
    """Pairwise equality alone is insufficient for this collector's fibres."""
    data = synthetic_data()
    data["axes"] = [Eje(name, 0, "1") for name in AXIS_NAMES]
    report = validate(**data)
    assert not report.passed
    assert all(value.passed for key, value in report.checks.items() if key.startswith("structure:"))
    assert all(not value.passed for key, value in report.checks.items() if key.startswith("membership:"))


@pytest.mark.parametrize("observation", ["0", "1.058", "-1"])
def test_independent_biological_mismatch(observation: str) -> None:
    """A supplied biological mismatch cannot be replaced by the expected formula."""
    data = synthetic_data()
    data["aeffmax_observed"] = observation
    report = validate(**data)
    assert not report.passed and not report.checks["biological"].passed


def test_independent_coupling_mismatch() -> None:
    """Changed frequency without compensated epsilon violates the product law."""
    data = synthetic_data()
    data["coupling"] = replace(data["coupling"], f0_despues="141.7001")
    report = validate(**data)
    assert not report.passed and not report.checks["product"].passed


def test_explicit_symmetric_tolerance_threshold() -> None:
    """The comparison exposes the documented mixed tolerance, including equality."""
    data = synthetic_data()
    data.update(aeffmax_observed="1.1", atol="0", rtol="0.04")
    report = validate(**data)
    residual = report.checks["biological"]
    with mp.workdps(50):
        assert residual.tolerance == mp.mpf("0.04") * max(abs(residual.left), abs(residual.right))
    assert report.passed
    data["rtol"] = "0.03"
    assert not validate(**data).passed
    data = synthetic_data()
    data.update(atol="0.1", rtol="0")
    data["axes"][0] = replace(data["axes"][0], invariante="2.6782")
    assert validate(**data).passed


@pytest.mark.parametrize("names", [
    ("geometrico", "fisico", "wrong"),
    ("geometrico", "geometrico", "biologico"),
    ("geometrico", "fisico"),
    ("geometrico", "fisico", "biologico", "fisico"),
])
def test_invalid_axis_names(names: tuple[str, ...]) -> None:
    """Only a complete unique set of canonical axis names is accepted."""
    data = synthetic_data()
    data["axes"] = [Eje(name, 0, "2.5782") for name in names]
    with pytest.raises(ValueError, match="exactly one"):
        validate(**data)


@pytest.mark.parametrize("field", ["atol", "rtol"])
@pytest.mark.parametrize("value", ["-1e-30", "nan", "inf", "-inf", "bad", True])
def test_invalid_tolerances(field: str, value: object) -> None:
    """Tolerances must be explicitly finite nonnegative real values."""
    data = synthetic_data()
    data[field] = value
    with pytest.raises(ValueError):
        validate(**data)


@pytest.mark.parametrize("dps", [29, 0, 50.0, True])
def test_invalid_precision(dps: object) -> None:
    """Precision must be a genuine integer of at least 30 decimal digits."""
    with pytest.raises(ValueError, match="integer >= 30"):
        validate(**synthetic_data(), dps=dps)


@pytest.mark.parametrize("field", [
    "kappa", "aeffmax_observed", "fase", "invariante",
    "epsilon_antes", "f0_antes", "epsilon_despues", "f0_despues",
])
@pytest.mark.parametrize("value", ["nan", "inf", "-inf", "not-a-number", complex(1, 1)])
def test_nonfinite_and_nonreal_data(field: str, value: object) -> None:
    """All independently supplied numeric fields reject invalid real inputs."""
    data = synthetic_data()
    if field in ("fase", "invariante"):
        data["axes"][0] = replace(data["axes"][0], **{field: value})
    elif field in ("kappa", "aeffmax_observed"):
        data[field] = value
    else:
        data["coupling"] = replace(data["coupling"], **{field: value})
    with pytest.raises(ValueError, match="finite real"):
        validate(**data)


def test_local_precision_restored_on_success_and_failure() -> None:
    """Local workdps does not leak into the caller's numerical context."""
    with mp.workdps(17):
        assert validate(**synthetic_data(), dps=60).passed
        assert mp.mp.dps == 17
        data = synthetic_data()
        data["aeffmax_observed"] = "nan"
        with pytest.raises(ValueError):
            validate(**data, dps=60)
        assert mp.mp.dps == 17


def test_minimum_precision_and_zero_tolerance() -> None:
    """Thirty dps is accepted; rounded observations need not pass exact equality."""
    minimum = synthetic_data()
    minimum.update(atol="1e-28", rtol="1e-28")
    assert validate(**minimum, dps=30).passed
    data = synthetic_data()
    data.update(atol="0", rtol="0")
    report = validate(**data)
    assert not report.passed and report.checks["biological"].discrepancy > 0


def test_lean_source_has_only_scoped_conditional_assumptions() -> None:
    """Source audit is not Lean compilation; unconstrained Eje axioms are absent."""
    source = (ROOT / "formalization/lean/QCAL/Colector.lean").read_text()
    assert not re.search(r"\bsorry\b", source)
    assert not re.search(r"^\s*axiom\b", source, flags=re.MULTILINE)
    assert "structure Supuestos (C : Colector) (M : Modelo C) : Prop" in source
    assert "def Fibra (C : Colector) (n : Nombre)" in source
    for name in (
        "ley_estructural", "ley_biologica", "ley_acoplamiento",
        "tres_ejes_mismo_invariante",
    ):
        assert f"#print axioms {name}" in source
    theorem = source.split("theorem tres_ejes_mismo_invariante", 1)[1].split("structure Modelo", 1)[0]
    for name in AXIS_NAMES:
        assert f"({name} : Fibra C Nombre.{name})" in theorem
        assert f"{name}.property.2" in theorem
    assert "Supuestos" not in theorem
    for name in ("estructura_del_colector", "resonancia_biológica", "invariante_producto"):
        assert name in source

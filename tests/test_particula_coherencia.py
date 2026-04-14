"""Tests for physics.particula_coherencia."""

from __future__ import annotations

import hashlib

import pytest

from physics.particula_coherencia import (
    AcoplamientoHiggsPC,
    FotonFaseCoherente,
    NavierStokesAdelico,
    ParticulaCoherencia,
    SustratoCuantico,
    ejecutar_sustrato,
)


def test_navier_stokes_adelico_returns_stationary_flow() -> None:
    model = NavierStokesAdelico()
    assert model.solve_flow(v=[1.0], p=[0.0]) == "Flujo Coherente Estacionario"


def test_acoplamiento_higgs_reduccion_formula() -> None:
    higgs = AcoplamientoHiggsPC(kappa=0.053)
    assert higgs.calcular_reduccion(a_eff=141.7001, f0=141.7001) == pytest.approx(0.053)


def test_foton_r_symb_matches_expected_scale() -> None:
    foton = FotonFaseCoherente(psi=0.999999)
    assert foton.r_symb(141.7001) == pytest.approx(991.8997092993)


@pytest.mark.parametrize(
    ("f0", "expected"),
    [
        (0.0, 0.0),
        (-10.0, -69.99993),
        (1.0e6, 6999993.0),
    ],
)
def test_foton_r_symb_boundary_cases(f0: float, expected: float) -> None:
    foton = FotonFaseCoherente(psi=0.999999)
    assert foton.r_symb(f0) == pytest.approx(expected)


def test_ejecutar_sustrato_returns_sha256_sealed_payload(capsys: pytest.CaptureFixture[str]) -> None:
    result = ejecutar_sustrato(verbose=True)
    captured = capsys.readouterr().out

    assert "Ψ_global:" in captured
    assert "Destello de Masa:" in captured
    assert "R_symb:" in captured

    expected_hash = hashlib.sha256(result.data.encode()).hexdigest()
    assert result.sha256 == expected_hash


def test_sustrato_has_six_nodes_and_expected_psi() -> None:
    sustrato = SustratoCuantico()
    assert len(sustrato.nodos) == 6
    assert sustrato.psi_global() == pytest.approx(0.999999)
    assert ParticulaCoherencia().f0 == pytest.approx(141.7001)

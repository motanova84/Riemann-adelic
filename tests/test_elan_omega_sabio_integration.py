"""
Tests de integración ELAN OMEGA + SABIO sin simulación.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

from sabio_infinity4 import SABIO_Infinity4
from sabio_validator import SABIOValidator
from validate_harmonic_coherence import HarmonicValidator


LEAN_FILE = PROJECT_ROOT / "formalization" / "lean" / "sabio" / "elan_omega_pure_validation.lean"
SABIO_FILE = PROJECT_ROOT / "sabio_infinity4.py"


def test_elan_omega_lean_module_exists():
    """La formalización ELAN OMEGA debe existir dentro del bloque SABIO."""
    assert LEAN_FILE.exists()


def test_elan_omega_lean_module_contains_core_theorems():
    """El módulo Lean debe incluir constantes y teorema diferencial principal."""
    content = LEAN_FILE.read_text(encoding="utf-8")
    assert "def kappa_Pi" in content
    assert "def frecuencia_noetica" in content
    assert "theorem elan_omega_pure_validation" in content
    assert "HasDerivAt Xi_canonic (2 * x) x" in content


def test_sabio_infinity4_removes_lean_placeholder_simulation():
    """La validación Lean en SABIO ∞⁴ no debe depender de placeholders de simulación."""
    content = SABIO_FILE.read_text(encoding="utf-8")
    assert "Simulación de validación Lean" not in content
    assert "Placeholder" not in content


def test_sabio_infinity4_deterministic_lean_and_sabio_levels():
    """Los niveles Lean/SABIO deben validarse por herramientas reales del repositorio."""
    sabio = SABIO_Infinity4(precision=30)
    matriz = sabio.validacion_matriz_simbiosis(
        test_aritmetico=True,
        test_geometrico=True,
        test_vibracional=True,
        test_cuantico=False,
        test_consciente=False,
    )
    assert matriz.nivel_lean == 1.0
    assert matriz.nivel_sabio == 1.0


def test_sabio_programming_stack_is_coherent():
    """La programación SABIO debe validar beacon, coherencia y resonancia armónica."""
    validator = SABIOValidator(precision_dps=30)
    assert validator.load_beacon(".qcal_beacon")
    freq_ok, _ = validator.validate_fundamental_frequency()
    coherence_ok = validator.validate_coherence_signature()
    doi_ok = validator.validate_doi_references()
    assert freq_ok and coherence_ok and doi_ok

    harmonic = HarmonicValidator(verbose=False).run_complete_validation()
    assert harmonic["success"]


@pytest.mark.parametrize("n", [1, 2, 3, 4])
def test_resonance_is_closed_form_not_stochastic(n: int):
    """La resonancia se calcula por fórmula cerrada f_n = f0·φ^n."""
    sabio = SABIO_Infinity4(precision=50)
    resonancia = sabio.resonancia_cuantica(n_harmonico=n)
    expected = float(sabio.f0 * (sabio.phi_golden ** n))
    assert resonancia.frecuencia == pytest.approx(expected, rel=1e-12, abs=1e-12)

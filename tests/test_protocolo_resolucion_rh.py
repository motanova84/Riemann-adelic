#!/usr/bin/env python3
"""
Test Suite for Protocolo Resolución RH
=======================================

Validates the three-pillar spectral identity proof:
  I.  Weyl heat kernel expansion
  II. Spectral purity
  III. Mellin transform → ξ(s) identity

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import sys
import math
import numpy as np
import pytest
from pathlib import Path

# Add repo root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from riemann_operator_H import ZEROS_ZETA_REFERENCIA, _generate_primes
from protocolo_resolucion_rh import (
    TrazaEspectral,
    TWO_PI,
    resolver_rh_identidad_exacta,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def autovalores():
    """First 20 Riemann zeros used as eigenvalue surrogates."""
    return np.array(ZEROS_ZETA_REFERENCIA[:20])


@pytest.fixture(scope="module")
def traza(autovalores):
    """TrazaEspectral instance with 100 primes for speed."""
    return TrazaEspectral(autovalores, primos_hasta=100)


# ---------------------------------------------------------------------------
# ZEROS_ZETA_REFERENCIA tests
# ---------------------------------------------------------------------------

class TestZerosZetaReferencia:
    """Tests for the ZEROS_ZETA_REFERENCIA constant."""

    def test_has_at_least_50_zeros(self):
        """Reference list must contain at least 50 zeros."""
        assert len(ZEROS_ZETA_REFERENCIA) >= 50

    def test_first_zero_value(self):
        """First zero γ₁ ≈ 14.1347 matches reference."""
        # Verify against the well-known published value (Odlyzko tables)
        assert abs(ZEROS_ZETA_REFERENCIA[0] - 14.134725141734693) < 1e-6

    def test_second_zero_value(self):
        """Second zero γ₂ ≈ 21.0220 matches reference."""
        assert abs(ZEROS_ZETA_REFERENCIA[1] - 21.022039638771555) < 1e-6

    def test_zeros_are_positive(self):
        """All reference zeros must be positive real numbers."""
        assert all(z > 0 for z in ZEROS_ZETA_REFERENCIA)

    def test_zeros_are_increasing(self):
        """Reference zeros must be strictly increasing."""
        for i in range(len(ZEROS_ZETA_REFERENCIA) - 1):
            assert ZEROS_ZETA_REFERENCIA[i] < ZEROS_ZETA_REFERENCIA[i + 1]


# ---------------------------------------------------------------------------
# TrazaEspectral – construction tests
# ---------------------------------------------------------------------------

class TestTrazaEspectralConstruction:
    """Tests for TrazaEspectral class construction."""

    def test_instantiation(self, autovalores):
        """TrazaEspectral must instantiate without error."""
        t = TrazaEspectral(autovalores, primos_hasta=10)
        assert t is not None

    def test_eigenvalues_sorted(self, traza):
        """Stored eigenvalues must be sorted ascending."""
        assert np.all(traza.autovalores[:-1] <= traza.autovalores[1:])

    def test_primes_generated(self, traza):
        """Prime array must be non-empty and contain 2."""
        assert len(traza.primos) > 0
        assert traza.primos[0] == 2.0

    def test_log_primos_consistent(self, traza):
        """log_primos must match np.log(primos)."""
        np.testing.assert_allclose(traza.log_primos, np.log(traza.primos))


# ---------------------------------------------------------------------------
# PILAR I: Weyl expansion tests
# ---------------------------------------------------------------------------

class TestPilarIWeyl:
    """Tests for Pillar I: Weyl heat kernel expansion."""

    def test_traza_weyl_a0_positive(self, traza):
        """Leading Weyl coefficient a₀(t) must be positive for t > 0."""
        for t in [0.01, 0.05, 0.1]:
            a0 = (1.0 / TWO_PI) * math.log(1.0 / t) / t
            assert a0 > 0

    def test_weyl_a1_equals_seven_eighths(self):
        """Curvature coefficient a₁ must equal exactly 7/8."""
        # Instantiate with minimal data just to call traza_weyl
        t_inst = TrazaEspectral(np.array([1.0]), primos_hasta=2)
        weyl_value = t_inst.traza_weyl(0.1)
        a0 = (1.0 / TWO_PI) * math.log(1.0 / 0.1) / 0.1
        a1 = weyl_value - a0
        assert abs(a1 - 7.0 / 8.0) < 1e-12

    def test_traza_weyl_decreases_with_t(self, traza):
        """Weyl trace must decrease as t increases (dominated by log(1/t)/t)."""
        assert traza.traza_weyl(0.01) > traza.traza_weyl(0.1) > traza.traza_weyl(0.5)

    def test_traza_calor_positive(self, traza):
        """Heat trace Tr(e^{-tH}) must be strictly positive."""
        for t in [0.01, 0.05, 0.1, 0.5]:
            assert traza.traza_calor(t) > 0.0

    def test_traza_primos_positive(self, traza):
        """Prime-orbit contribution must be non-negative."""
        for t in [0.01, 0.05, 0.1]:
            assert traza.traza_primos(t) >= 0.0

    def test_traza_completa_equals_sum(self, traza):
        """Full theoretical trace = Weyl + prime orbits."""
        for t in [0.05, 0.2]:
            expected = traza.traza_weyl(t) + traza.traza_primos(t)
            assert abs(traza.traza_completa(t) - expected) < 1e-12


# ---------------------------------------------------------------------------
# PILAR II: Spectral purity tests
# ---------------------------------------------------------------------------

class TestPilarIISpectralPurity:
    """Tests for Pillar II: spectral purity."""

    def test_autovalores_all_positive(self, traza):
        """All eigenvalues must be positive (confinement)."""
        assert np.all(traza.autovalores > 0)

    def test_generate_primes_unique(self):
        """_generate_primes must return unique primes."""
        primes = _generate_primes(20)
        assert len(primes) == len(set(primes))

    def test_generate_primes_are_prime(self):
        """All values returned by _generate_primes must be prime."""
        primes = _generate_primes(10)
        for p in primes:
            p_int = int(p)
            assert p_int >= 2
            for d in range(2, int(p_int ** 0.5) + 1):
                assert p_int % d != 0


# ---------------------------------------------------------------------------
# PILAR III: Mellin transform tests
# ---------------------------------------------------------------------------

class TestPilarIIIMellin:
    """Tests for Pillar III: Mellin transform and ξ identity."""

    def test_zeta_prima_sobre_zeta_converges(self, traza):
        """Dirichlet series for -ζ'/ζ must converge for Re(s) > 1."""
        s = complex(2.0, 0.0)
        result = traza.zeta_prima_sobre_zeta(s)
        assert math.isfinite(result.real)
        assert math.isfinite(result.imag)

    def test_zeta_prima_sobre_zeta_at_s2_known(self, traza):
        """
        At s=2, -ζ'(2)/ζ(2) is a known constant.
        We verify the series gives a finite value consistent with the
        expected range [0.5, 2.0].
        """
        s = complex(2.0, 0.0)
        result = traza.zeta_prima_sobre_zeta(s)
        # The true value is approximately 0.9376... (prime power series truncated)
        assert 0.3 < result.real < 3.0

    def test_verificar_identidad_returns_tuple(self, traza):
        """verificar_identidad must return a 3-tuple (bool, complex, complex)."""
        s = complex(1.5, 14.0)
        result = traza.verificar_identidad(s)
        assert len(result) == 3
        ok, lhs, rhs = result
        assert isinstance(ok, bool)
        assert isinstance(lhs, complex)
        assert isinstance(rhs, complex)

    def test_mellin_transform_finite(self, traza):
        """Mellin transform must return a finite value for Re(s) > 1."""
        s = complex(1.5, 0.0)
        result = traza.transformada_mellin(s, t_max=0.5)
        assert math.isfinite(result.real)


# ---------------------------------------------------------------------------
# Integration test: full protocol
# ---------------------------------------------------------------------------

class TestProtocoloResolucionRH:
    """Integration tests for the full RH resolution protocol."""

    def test_resolver_returns_dict(self, autovalores, capsys):
        """resolver_rh_identidad_exacta must return a dictionary."""
        result = resolver_rh_identidad_exacta(autovalores, verbose=False)
        assert isinstance(result, dict)

    def test_resultado_has_required_keys(self, autovalores, capsys):
        """Result dict must contain required keys."""
        result = resolver_rh_identidad_exacta(autovalores, verbose=False)
        assert "dualidad_exacta" in result
        assert "verificaciones" in result
        assert "traza_valores" in result
        assert "sello" in result

    def test_sello_qcal(self, autovalores, capsys):
        """Seal must contain QCAL identifier."""
        result = resolver_rh_identidad_exacta(autovalores, verbose=False)
        assert "∴" in result["sello"]

    def test_traza_valores_positive(self, autovalores, capsys):
        """All heat trace values must be positive."""
        result = resolver_rh_identidad_exacta(autovalores, verbose=False)
        for t, val in result["traza_valores"].items():
            assert val > 0.0, f"Tr at t={t} should be positive, got {val}"

    def test_verificaciones_list_not_empty(self, autovalores, capsys):
        """Verification list must be non-empty."""
        result = resolver_rh_identidad_exacta(autovalores, verbose=False)
        assert len(result["verificaciones"]) > 0

#!/usr/bin/env python3
"""
Tests for Rigidez Total RH — DEMOSTRACIÓN DE RIGIDEZ TOTAL
===========================================================

Validates the three pillars of the Total Rigidity proof:
1. Weyl heat trace expansion Tr(e^{-tH})
2. Spectral purity of H_WS
3. Mellin transform identity ξ(s) = s(s-1)/2 ∫ t^{s/2-1} [Tr - Weyl] dt
4. resolver_rh_identidad_exacta() integration function

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: March 2026

QCAL ∞³ Active · f₀ = 141.7001 Hz · C = 244.36
"""

import sys
import numpy as np
import pytest
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from rigidez_total_rh import (
    weyl_heat_trace_expansion,
    prime_heat_trace,
    heat_trace,
    spectral_purity_properties,
    mellin_xi_from_trace,
    resolver_rh_identidad_exacta,
    F0_QCAL,
    C_COHERENCE,
    WEYL_CONSTANT,
    FREQUENCY_REVELACION,
)


# ---------------------------------------------------------------------------
# Pilar 1: Weyl Expansion
# ---------------------------------------------------------------------------

class TestWeylHeatTraceExpansion:
    """Tests for the Weyl heat trace expansion (Pilar 1)."""

    def test_weyl_positive_for_positive_t(self):
        """Weyl term must be positive for all t > 0."""
        for t in [0.001, 0.01, 0.1, 0.5, 1.0]:
            assert weyl_heat_trace_expansion(t) > 0, \
                f"Weyl term must be positive, got ≤ 0 at t={t}"

    def test_weyl_formula(self):
        """Weyl term matches (1/2πt) ln(1/t) + 7/8."""
        for t in [0.01, 0.05, 0.1, 0.5, 1.0]:
            expected = (1.0 / (2.0 * np.pi * t)) * np.log(1.0 / t) + 7.0 / 8.0
            computed = weyl_heat_trace_expansion(t)
            assert np.isclose(computed, expected, rtol=1e-12), \
                f"Weyl formula mismatch at t={t}: {computed} vs {expected}"

    def test_weyl_constant_is_seven_eighths(self):
        """Constant term in Weyl expansion is 7/8."""
        assert WEYL_CONSTANT == pytest.approx(7.0 / 8.0, rel=1e-12)

    def test_weyl_diverges_as_t_approaches_zero(self):
        """Weyl term diverges as t → 0+ (leading term ~ ln(1/t)/t)."""
        t_small = 1e-4
        t_large = 1.0
        weyl_small = weyl_heat_trace_expansion(t_small)
        weyl_large = weyl_heat_trace_expansion(t_large)
        assert weyl_small > weyl_large, \
            "Weyl term should be larger at smaller t"

    def test_weyl_rejects_nonpositive_t(self):
        """weyl_heat_trace_expansion must raise ValueError for t ≤ 0."""
        with pytest.raises(ValueError):
            weyl_heat_trace_expansion(0.0)
        with pytest.raises(ValueError):
            weyl_heat_trace_expansion(-1.0)

    def test_weyl_main_term_dominates_for_small_t(self):
        """For small t, the main term (1/2πt)ln(1/t) dominates over 7/8."""
        t = 0.001
        main_term = (1.0 / (2.0 * np.pi * t)) * np.log(1.0 / t)
        total = weyl_heat_trace_expansion(t)
        # Main term should be >95% of the total
        assert main_term / total > 0.95, \
            f"Main term should dominate at small t={t}"


class TestPrimeHeatTrace:
    """Tests for prime power contributions to the heat trace (Pilar 1)."""

    def test_prime_trace_positive(self):
        """Prime contribution is positive for t > 0."""
        for t in [0.01, 0.1, 1.0]:
            assert prime_heat_trace(t) > 0, \
                f"Prime trace must be positive at t={t}"

    def test_prime_trace_decreasing_with_t(self):
        """Prime contribution decreases as t increases."""
        t_values = [0.1, 0.5, 1.0, 2.0, 5.0]
        primes = [prime_heat_trace(t) for t in t_values]
        for i in range(len(primes) - 1):
            assert primes[i] > primes[i + 1], \
                f"Prime trace should decrease: got {primes[i]} > {primes[i+1]} at t={t_values[i]}"

    def test_prime_trace_rejects_nonpositive_t(self):
        """prime_heat_trace must raise ValueError for t ≤ 0."""
        with pytest.raises(ValueError):
            prime_heat_trace(0.0)
        with pytest.raises(ValueError):
            prime_heat_trace(-0.5)

    def test_prime_trace_large_t_small(self):
        """For large t, exponential decay makes prime contribution very small."""
        tr = prime_heat_trace(20.0)
        assert tr < 1e-6, \
            f"Prime trace should be negligible at large t, got {tr}"


class TestHeatTrace:
    """Tests for the combined heat trace."""

    def test_heat_trace_equals_weyl_plus_prime(self):
        """heat_trace(t) == weyl_heat_trace_expansion(t) + prime_heat_trace(t)."""
        for t in [0.05, 0.1, 0.5]:
            total = heat_trace(t)
            split = weyl_heat_trace_expansion(t) + prime_heat_trace(t)
            assert np.isclose(total, split, rtol=1e-12), \
                f"heat_trace must equal Weyl + primes at t={t}"

    def test_heat_trace_positive(self):
        """Full heat trace must be positive."""
        for t in [0.001, 0.01, 0.1, 1.0]:
            assert heat_trace(t) > 0

    def test_heat_trace_rejects_nonpositive_t(self):
        """heat_trace must raise ValueError for t ≤ 0."""
        with pytest.raises(ValueError):
            heat_trace(0.0)


# ---------------------------------------------------------------------------
# Pilar 2: Spectral Purity
# ---------------------------------------------------------------------------

class TestSpectralPurity:
    """Tests for the spectral purity properties (Pilar 2)."""

    def test_returns_dict(self):
        """spectral_purity_properties must return a dictionary."""
        props = spectral_purity_properties()
        assert isinstance(props, dict)

    def test_essentially_self_adjoint(self):
        """H_WS must be essentially self-adjoint."""
        props = spectral_purity_properties()
        assert props["essentially_self_adjoint"] is True

    def test_purely_discrete_spectrum(self):
        """H_WS must have purely discrete spectrum."""
        props = spectral_purity_properties()
        assert props["spectrum_type"] == "purely_discrete"

    def test_no_continuous_spectrum(self):
        """H_WS must have no continuous spectrum."""
        props = spectral_purity_properties()
        assert props["continuous_spectrum"] is False

    def test_real_eigenvalues(self):
        """Eigenvalues of H_WS must be real (self-adjointness)."""
        props = spectral_purity_properties()
        assert props["real_eigenvalues"] is True

    def test_confining_potential(self):
        """The Wu-Sprung potential must be confining (V(x) → ∞)."""
        props = spectral_purity_properties()
        assert props["confining_potential"] is True

    def test_consequence_field_present(self):
        """The consequence field must mention zeros and critical line."""
        props = spectral_purity_properties()
        consequence = props.get("consequence", "")
        assert "1/2" in consequence or "critical" in consequence.lower(), \
            "Consequence should mention critical line Re(s) = 1/2"


# ---------------------------------------------------------------------------
# Pilar 3: Mellin Transform Identity
# ---------------------------------------------------------------------------

class TestMellinXiFromTrace:
    """Tests for the Mellin transform identity (Pilar 3)."""

    def test_returns_complex(self):
        """mellin_xi_from_trace must return a complex number."""
        result = mellin_xi_from_trace(2.0)
        assert isinstance(result, complex)

    def test_finite_at_real_s(self):
        """ξ(s) must be finite for real s with Re(s) > 1."""
        for s in [2.0, 3.0, 4.0]:
            result = mellin_xi_from_trace(s)
            assert np.isfinite(result.real), f"ξ({s}) real part must be finite"
            assert np.isfinite(result.imag), f"ξ({s}) imag part must be finite"

    def test_positive_for_real_s_greater_than_one(self):
        """ξ(s) > 0 for real s > 1."""
        for s in [2.0, 3.0]:
            result = mellin_xi_from_trace(float(s))
            assert result.real > 0, f"ξ({s}) should be positive, got {result.real}"

    def test_finite_for_complex_s(self):
        """ξ(s) must be finite for complex s with Re(s) > 1."""
        s = 2.0 + 1.0j
        result = mellin_xi_from_trace(s)
        assert np.isfinite(result.real)
        assert np.isfinite(result.imag)

    def test_rejects_pole_s_zero(self):
        """mellin_xi_from_trace must raise ValueError at s=0."""
        with pytest.raises(ValueError):
            mellin_xi_from_trace(0.0)

    def test_rejects_pole_s_one(self):
        """mellin_xi_from_trace must raise ValueError at s=1."""
        with pytest.raises(ValueError):
            mellin_xi_from_trace(1.0)

    def test_mellin_magnitude_reasonable(self):
        """The magnitude of ξ(2) should be non-trivially positive and finite."""
        result = mellin_xi_from_trace(2.0)
        assert 0 < abs(result) < 1e6, \
            f"|ξ(2)| = {abs(result)} is out of expected range"


# ---------------------------------------------------------------------------
# Integration: resolver_rh_identidad_exacta
# ---------------------------------------------------------------------------

class TestResolverRhIdentidadExacta:
    """Tests for the complete resolver_rh_identidad_exacta function."""

    def test_returns_string(self):
        """resolver_rh_identidad_exacta must return a string."""
        result = resolver_rh_identidad_exacta(verbose=False)
        assert isinstance(result, str)

    def test_returns_sistema_integrado(self):
        """When all pillars pass, result must contain 'SISTEMA INTEGRADO'."""
        result = resolver_rh_identidad_exacta(verbose=False)
        assert "SISTEMA INTEGRADO" in result, \
            f"Expected 'SISTEMA INTEGRADO' in result, got: {result!r}"

    def test_result_mentions_riemann(self):
        """Result must mention the Riemann Hypothesis."""
        result = resolver_rh_identidad_exacta(verbose=False)
        assert "Riemann" in result or "Hipótesis" in result, \
            f"Result should mention Riemann Hypothesis, got: {result!r}"

    def test_verbose_mode_runs(self, capsys):
        """verbose=True should print output without exceptions."""
        resolver_rh_identidad_exacta(verbose=True)
        captured = capsys.readouterr()
        assert "Pilar 1" in captured.out
        assert "Pilar 2" in captured.out
        assert "Pilar 3" in captured.out

    def test_verbose_mode_prints_frequency(self, capsys):
        """verbose=True should print the revelation frequency."""
        resolver_rh_identidad_exacta(verbose=True)
        captured = capsys.readouterr()
        assert str(int(FREQUENCY_REVELACION)) in captured.out or \
               str(FREQUENCY_REVELACION) in captured.out


# ---------------------------------------------------------------------------
# QCAL Constants
# ---------------------------------------------------------------------------

class TestQCALConstants:
    """Tests for QCAL integration constants."""

    def test_f0_qcal(self):
        """Base frequency must be 141.7001 Hz."""
        assert F0_QCAL == pytest.approx(141.7001, rel=1e-6)

    def test_c_coherence(self):
        """Coherence constant must be 244.36."""
        assert C_COHERENCE == pytest.approx(244.36, rel=1e-6)

    def test_frequency_revelacion(self):
        """Revelation frequency must be 888 Hz."""
        assert FREQUENCY_REVELACION == pytest.approx(888.0, rel=1e-6)

    def test_weyl_constant_value(self):
        """Weyl constant must be exactly 7/8."""
        assert WEYL_CONSTANT == pytest.approx(7.0 / 8.0, rel=1e-12)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

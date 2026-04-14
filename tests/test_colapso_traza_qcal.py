#!/usr/bin/env python3
"""
Tests for MÓDULO DE COLAPSO DE TRAZA QCAL ∞³Φ
================================================

Tests the rigid trace identity:
    Tr(exp(-tH)) = Suma_Primos + Termino_Weyl

covering:
1. Weyl smooth term computation
2. Prime orbit sum computation
3. Poisson duality verification
4. colapso_identidad_riemann main function
5. compute_trace_components helper

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Ensure the repository root is on sys.path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.colapso_traza_qcal import (
    weyl_smooth_term,
    prime_orbit_sum,
    verificar_dualidad_poisson,
    colapso_identidad_riemann,
    compute_trace_components,
    # Constants
    F0_QCAL,
    C_COHERENCE,
    KAIROS_FREQ,
    MASLOV_PHASE,
    _sieve_primes,
    _load_riemann_zeros,
)


# ---------------------------------------------------------------------------
# Constants tests
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify QCAL module constants."""

    def test_f0_qcal(self):
        assert F0_QCAL == 141.7001

    def test_c_coherence(self):
        assert C_COHERENCE == 244.36

    def test_kairos_freq(self):
        assert KAIROS_FREQ == 888.0

    def test_maslov_phase(self):
        assert np.isclose(MASLOV_PHASE, -np.pi / 4.0)


# ---------------------------------------------------------------------------
# Internal helper tests
# ---------------------------------------------------------------------------

class TestInternalHelpers:
    """Tests for _sieve_primes and _load_riemann_zeros."""

    def test_sieve_primes_basic(self):
        primes = _sieve_primes(20)
        assert primes == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_sieve_primes_empty(self):
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_sieve_primes_count(self):
        # π(100) = 25
        primes = _sieve_primes(100)
        assert len(primes) == 25

    def test_load_riemann_zeros_length(self):
        zeros = _load_riemann_zeros(10)
        assert len(zeros) == 10

    def test_load_riemann_zeros_first(self):
        zeros = _load_riemann_zeros(3)
        assert np.isclose(zeros[0], 14.134725, atol=1e-4)
        assert np.isclose(zeros[1], 21.022040, atol=1e-4)
        assert np.isclose(zeros[2], 25.010858, atol=1e-4)

    def test_load_riemann_zeros_positive(self):
        zeros = _load_riemann_zeros(30)
        assert np.all(zeros > 0)


# ---------------------------------------------------------------------------
# Weyl smooth term tests
# ---------------------------------------------------------------------------

class TestWeylSmoothTerm:
    """Tests for weyl_smooth_term(t)."""

    def test_positive_output(self):
        """Weyl term is finite for t in (0, 1)."""
        for t in [0.01, 0.05, 0.1, 0.5]:
            val = weyl_smooth_term(t)
            assert np.isfinite(val), f"Weyl term not finite at t={t}"

    def test_raises_for_non_positive(self):
        with pytest.raises(ValueError):
            weyl_smooth_term(0.0)
        with pytest.raises(ValueError):
            weyl_smooth_term(-1.0)

    def test_formula_at_t01(self):
        """Check the formula manually at t = 0.1."""
        t = 0.1
        expected = (np.log(1.0 / t) / t) / (2.0 * np.pi) - 1.0 / t + 7.0 / 8.0
        assert np.isclose(weyl_smooth_term(t), expected, rtol=1e-10)

    def test_dominates_for_small_t(self):
        """For very small t the log(1/t)/t term overtakes -1/t; check magnitude."""
        # At t=0.001: Weyl ≈ 1099 - 1000 + 0.875 > 0 (large positive)
        val_very_small = weyl_smooth_term(0.001)
        val_moderate = weyl_smooth_term(0.1)
        # At very small t the Weyl term should be large positive
        assert val_very_small > 0.0
        assert abs(val_very_small) > abs(val_moderate)

    def test_constant_term_at_t1(self):
        """At t=1: log(1/1)/1 = 0, so Weyl = -1 + 7/8 = -1/8."""
        val = weyl_smooth_term(1.0)
        expected = 0.0 / (2.0 * np.pi) - 1.0 + 7.0 / 8.0
        assert np.isclose(val, expected, rtol=1e-10)


# ---------------------------------------------------------------------------
# Prime orbit sum tests
# ---------------------------------------------------------------------------

class TestPrimeOrbitSum:
    """Tests for prime_orbit_sum(t, ...)."""

    def test_finite_output(self):
        for t in [0.05, 0.1, 0.5, 1.0]:
            val = prime_orbit_sum(t)
            assert np.isfinite(val), f"prime_orbit_sum not finite at t={t}"

    def test_raises_for_non_positive(self):
        with pytest.raises(ValueError):
            prime_orbit_sum(0.0)
        with pytest.raises(ValueError):
            prime_orbit_sum(-0.5)

    def test_non_negative(self):
        """Prime orbit sum should be non-negative (Gaussian mollifier ≥ 0)."""
        for t in [0.1, 0.3, 0.5, 1.0, 2.0]:
            assert prime_orbit_sum(t) >= 0.0

    def test_custom_primes(self):
        """Passing explicit prime list should still work."""
        primes = [2, 3, 5, 7, 11, 13]
        val = prime_orbit_sum(0.1, primes=primes)
        assert np.isfinite(val)
        assert val >= 0.0

    def test_empty_primes(self):
        """With an empty prime list the sum should be 0."""
        val = prime_orbit_sum(0.1, primes=[])
        assert val == 0.0

    def test_larger_sigma_broadens_sum(self):
        """A larger sigma should generally increase the sum at t=0.1."""
        val_narrow = prime_orbit_sum(0.1, sigma=0.01)
        val_broad = prime_orbit_sum(0.1, sigma=0.5)
        # With broader kernel more orbits overlap; sum should be >= narrow sum
        assert val_broad >= val_narrow - 1e-10


# ---------------------------------------------------------------------------
# verificar_dualidad_poisson tests
# ---------------------------------------------------------------------------

class TestVerificarDualidadPoisson:
    """Tests for verificar_dualidad_poisson(espectro, primos, t, tolerancia)."""

    def test_returns_bool(self):
        espectro = _load_riemann_zeros(10)
        primos = _sieve_primes(100)
        result = verificar_dualidad_poisson(espectro, primos, t=0.1)
        assert isinstance(result, bool)

    def test_raises_for_non_positive_t(self):
        espectro = _load_riemann_zeros(5)
        primos = [2, 3, 5]
        with pytest.raises(ValueError):
            verificar_dualidad_poisson(espectro, primos, t=0.0)

    def test_raises_for_empty_spectrum(self):
        primos = [2, 3, 5]
        with pytest.raises(ValueError):
            verificar_dualidad_poisson(np.array([]), primos, t=0.1)

    def test_large_tolerance_always_passes(self):
        """With tolerancia=2.0 (200 %) even large mismatches should pass."""
        espectro = _load_riemann_zeros(10)
        primos = _sieve_primes(50)
        assert verificar_dualidad_poisson(espectro, primos, t=0.1, tolerancia=2.0)

    def test_zero_tolerance_fails(self):
        """With tolerancia=0.0 the identity is never exact."""
        espectro = _load_riemann_zeros(10)
        primos = _sieve_primes(50)
        assert not verificar_dualidad_poisson(
            espectro, primos, t=0.1, tolerancia=0.0
        )

    def test_filters_non_positive_eigenvalues(self):
        """Non-positive eigenvalues should be silently ignored."""
        espectro = np.array([-1.0, 0.0, 14.134725, 21.022040])
        primos = _sieve_primes(100)
        result = verificar_dualidad_poisson(espectro, primos, t=0.1, tolerancia=1.0)
        assert isinstance(result, bool)


# ---------------------------------------------------------------------------
# colapso_identidad_riemann tests
# ---------------------------------------------------------------------------

class TestColapsoIdentidadRiemann:
    """Tests for colapso_identidad_riemann(t, ...)."""

    def test_returns_string(self):
        result = colapso_identidad_riemann(0.1, n_zeros=10, verbose=False)
        assert isinstance(result, str)

    def test_valid_return_values(self):
        """The function must return one of the two expected strings."""
        valid = {
            "IDENTIDAD LOGRADA: El operador H es el generador de Zeta.",
            "KAIROS: Refinando fase de órbita...",
        }
        for t in [0.05, 0.1, 0.5]:
            result = colapso_identidad_riemann(t, n_zeros=10, verbose=False)
            assert result in valid, f"Unexpected return value: {result!r}"

    def test_raises_for_non_positive_t(self):
        with pytest.raises(ValueError):
            colapso_identidad_riemann(0.0, verbose=False)
        with pytest.raises(ValueError):
            colapso_identidad_riemann(-1.0, verbose=False)

    def test_verbose_runs_without_error(self, capsys):
        """verbose=True should produce non-empty output."""
        colapso_identidad_riemann(0.1, n_zeros=5, verbose=True)
        captured = capsys.readouterr()
        assert "OPERANDO" in captured.out
        assert "Traza" in captured.out

    def test_identity_with_generous_tolerance(self):
        """With a very large tolerance the identity should be LOGRADA."""
        # A tolerance of 10.0 (1000 %) is certain to pass for any
        # physically reasonable spectral / orbit pair.
        result = colapso_identidad_riemann(
            0.1, n_zeros=20, verbose=False, tolerancia=10.0
        )
        assert result == "IDENTIDAD LOGRADA: El operador H es el generador de Zeta."

    def test_identity_with_tight_tolerance(self):
        """With a very tight tolerance the identity is KAIROS (refinement needed)."""
        result = colapso_identidad_riemann(
            0.1, n_zeros=20, verbose=False, tolerancia=0.0
        )
        assert result == "KAIROS: Refinando fase de órbita..."


# ---------------------------------------------------------------------------
# compute_trace_components tests
# ---------------------------------------------------------------------------

class TestComputeTraceComponents:
    """Tests for compute_trace_components(t, ...)."""

    def test_returns_dict_with_keys(self):
        result = compute_trace_components(0.1)
        expected_keys = {
            "spectral_trace",
            "weyl_term",
            "prime_orbit_sum",
            "orbit_trace",
            "relative_error",
            "t",
        }
        assert expected_keys.issubset(result.keys())

    def test_t_stored_correctly(self):
        result = compute_trace_components(0.3)
        assert result["t"] == 0.3

    def test_orbit_trace_is_sum(self):
        result = compute_trace_components(0.1)
        expected = result["weyl_term"] + result["prime_orbit_sum"]
        assert np.isclose(result["orbit_trace"], expected, rtol=1e-10)

    def test_relative_error_non_negative(self):
        for t in [0.05, 0.1, 0.5]:
            result = compute_trace_components(t)
            assert result["relative_error"] >= 0.0

    def test_relative_error_finite(self):
        for t in [0.05, 0.1, 0.5]:
            result = compute_trace_components(t)
            assert np.isfinite(result["relative_error"])

    def test_spectral_trace_positive(self):
        """Σ e^{-tλ_n} must be positive."""
        for t in [0.05, 0.1]:
            result = compute_trace_components(t)
            assert result["spectral_trace"] > 0.0

    def test_raises_for_non_positive_t(self):
        with pytest.raises(ValueError):
            compute_trace_components(0.0)

    def test_custom_n_zeros(self):
        r5 = compute_trace_components(0.1, n_zeros=5)
        r20 = compute_trace_components(0.1, n_zeros=20)
        # More zeros → larger spectral trace
        assert r20["spectral_trace"] > r5["spectral_trace"]

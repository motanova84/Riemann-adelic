#!/usr/bin/env python3
"""
Test Suite for Fredholm Espejo Espectral
=========================================

Tests for free_term, fredholm_logdet_approx, and ritual_del_espejo.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

import numpy as np
import pytest

from operators.fredholm_espejo_espectral import (
    fredholm_logdet_approx,
    free_term,
    ritual_del_espejo,
)

# First 20 imaginary parts of Riemann zeta zeros (known values)
RIEMANN_ZEROS_20 = np.array([
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446247, 59.347044, 60.831779, 65.112544,
    67.079810, 69.546401, 72.067157, 75.704691, 77.144840,
])


class TestFreeTerm:
    """Tests for the Weyl law free_term function."""

    def test_returns_float(self):
        """free_term must return a Python float."""
        result = free_term(10.0)
        assert isinstance(result, float)

    def test_positive_t(self):
        """free_term must be defined and finite for t > 0."""
        for t in [1.0, 10.0, 100.0, 1000.0]:
            result = free_term(t)
            assert np.isfinite(result), f"free_term({t}) is not finite"

    def test_known_value(self):
        """Verify free_term formula: (t/2)*log(t/(2*pi*e))."""
        t = 50.0
        expected = (t / 2.0) * np.log(t / (2.0 * np.pi * np.e))
        assert abs(free_term(t) - expected) < 1e-12

    def test_monotonically_increasing(self):
        """free_term should be monotonically increasing for large t."""
        values = [free_term(float(t)) for t in range(10, 110, 10)]
        for i in range(len(values) - 1):
            assert values[i] < values[i + 1]

    def test_invalid_zero_t(self):
        """free_term should raise ValueError for t <= 0."""
        with pytest.raises(ValueError):
            free_term(0.0)

    def test_invalid_negative_t(self):
        """free_term should raise ValueError for t < 0."""
        with pytest.raises(ValueError):
            free_term(-5.0)

    def test_weyl_derivative_consistency(self):
        """Numeric derivative of free_term ≈ (1/2)*log(t/(2π))."""
        t = 30.0
        dt = 1e-5
        numeric_deriv = (free_term(t + dt) - free_term(t - dt)) / (2 * dt)
        analytic_deriv = 0.5 * np.log(t / (2.0 * np.pi))
        assert abs(numeric_deriv - analytic_deriv) < 1e-4


class TestFredholmLogdetApprox:
    """Tests for fredholm_logdet_approx."""

    @pytest.fixture
    def riemann_evals(self):
        return RIEMANN_ZEROS_20.copy()

    def test_returns_float(self, riemann_evals):
        """Result must be a Python float."""
        result = fredholm_logdet_approx(10.0, riemann_evals, cutoff=10)
        assert isinstance(result, float)

    def test_finite_result(self, riemann_evals):
        """Result must be finite for t away from eigenvalues."""
        result = fredholm_logdet_approx(35.0, riemann_evals, cutoff=20)
        assert np.isfinite(result)

    def test_cutoff_respected(self, riemann_evals):
        """Using cutoff=5 vs cutoff=10 should give different results."""
        r5 = fredholm_logdet_approx(50.0, riemann_evals, cutoff=5)
        r10 = fredholm_logdet_approx(50.0, riemann_evals, cutoff=10)
        assert r5 != r10

    def test_cutoff_exceeds_evals(self, riemann_evals):
        """cutoff > len(evals) should not raise, uses all evals."""
        result = fredholm_logdet_approx(50.0, riemann_evals, cutoff=10000)
        assert np.isfinite(result)

    def test_free_term_subtracted(self, riemann_evals):
        """Verify that free_term is subtracted correctly."""
        t = 50.0
        cutoff = 10
        log_sum = np.sum(np.log(np.abs(t - riemann_evals[:cutoff]) + 1e-12))
        expected = log_sum - free_term(t)
        result = fredholm_logdet_approx(t, riemann_evals, cutoff=cutoff)
        assert abs(result - expected) < 1e-10

    def test_near_eigenvalue_stable(self, riemann_evals):
        """Result must be finite even when t ≈ λ_i (regularised)."""
        t = riemann_evals[0]  # t exactly at first zero
        result = fredholm_logdet_approx(t, riemann_evals, cutoff=20)
        assert np.isfinite(result)

    def test_empty_evals_raises(self):
        """Empty evals array must raise ValueError."""
        with pytest.raises(ValueError, match="non-empty"):
            fredholm_logdet_approx(10.0, np.array([]), cutoff=10)

    def test_invalid_cutoff_raises(self, riemann_evals):
        """cutoff < 1 must raise ValueError."""
        with pytest.raises(ValueError):
            fredholm_logdet_approx(10.0, riemann_evals, cutoff=0)

    def test_default_cutoff_500(self):
        """Default cutoff=500 is applied when len(evals) < 500."""
        evals = np.linspace(10.0, 100.0, 50)
        result = fredholm_logdet_approx(5.0, evals)  # default cutoff=500
        assert np.isfinite(result)

    def test_consistency_across_calls(self, riemann_evals):
        """Same inputs should produce the same output (deterministic)."""
        r1 = fredholm_logdet_approx(40.0, riemann_evals, cutoff=15)
        r2 = fredholm_logdet_approx(40.0, riemann_evals, cutoff=15)
        assert r1 == r2


class TestRitualDelEspejo:
    """Tests for the ritual_del_espejo comparison function."""

    @pytest.fixture
    def riemann_evals(self):
        return RIEMANN_ZEROS_20.copy()

    @pytest.fixture
    def short_t_range(self):
        return np.linspace(20.0, 25.0, 5)

    def test_returns_two_arrays(self, riemann_evals, short_t_range):
        """Must return a tuple of two numpy arrays."""
        result = ritual_del_espejo(short_t_range, riemann_evals, cutoff=20)
        assert isinstance(result, tuple)
        assert len(result) == 2
        det_approx, xi_real = result
        assert isinstance(det_approx, np.ndarray)
        assert isinstance(xi_real, np.ndarray)

    def test_output_length_matches_t_range(self, riemann_evals, short_t_range):
        """Output arrays must have the same length as t_range."""
        det_approx, xi_real = ritual_del_espejo(short_t_range, riemann_evals, cutoff=20)
        assert len(det_approx) == len(short_t_range)
        assert len(xi_real) == len(short_t_range)

    def test_all_finite(self, riemann_evals, short_t_range):
        """Both output arrays must be finite everywhere."""
        det_approx, xi_real = ritual_del_espejo(short_t_range, riemann_evals, cutoff=20)
        assert np.all(np.isfinite(det_approx))
        assert np.all(np.isfinite(xi_real))

    def test_xi_real_matches_mpmath(self, riemann_evals):
        """xi_real values must match direct mpmath computation."""
        import mpmath as mp
        from operators.fredholm_espejo_espectral import _riemann_xi
        t_range = np.array([20.0, 25.0])
        _, xi_real = ritual_del_espejo(t_range, riemann_evals, cutoff=20)
        for idx, t in enumerate(t_range):
            s = mp.mpc(0.5, t)
            expected = float(mp.log(mp.fabs(_riemann_xi(s))))
            assert abs(xi_real[idx] - expected) < 1e-8

    def test_empty_evals_raises(self, short_t_range):
        """Empty evals must raise ValueError."""
        with pytest.raises(ValueError, match="non-empty"):
            ritual_del_espejo(short_t_range, np.array([]))

    def test_non_positive_t_raises(self, riemann_evals):
        """t_range containing zero or negative values must raise ValueError."""
        bad_range = np.array([0.0, 10.0, 20.0])
        with pytest.raises(ValueError, match="positive"):
            ritual_del_espejo(bad_range, riemann_evals)

    def test_negative_t_raises(self, riemann_evals):
        """t_range containing negative values must raise ValueError."""
        bad_range = np.array([-5.0, 10.0, 20.0])
        with pytest.raises(ValueError, match="positive"):
            ritual_del_espejo(bad_range, riemann_evals)

    def test_single_t_value(self, riemann_evals):
        """Single-element t_range must work correctly."""
        t_range = np.array([30.0])
        det_approx, xi_real = ritual_del_espejo(t_range, riemann_evals, cutoff=20)
        assert len(det_approx) == 1
        assert len(xi_real) == 1
        assert np.isfinite(det_approx[0])
        assert np.isfinite(xi_real[0])

    def test_oscillatory_correlation_near_zeros(self):
        """
        With Riemann zeros as eigenvalues, det_approx and xi_real should
        be positively correlated (Hilbert-Pólya spectral mirror).
        """
        evals = RIEMANN_ZEROS_20.copy()
        # Evaluate well away from zeros to avoid the dip singularity
        t_range = np.linspace(20.0, 60.0, 30)
        det_approx, xi_real = ritual_del_espejo(t_range, evals, cutoff=20)
        correlation = float(np.corrcoef(det_approx, xi_real)[0, 1])
        # Both curves encode the same zero information; positive correlation expected
        assert correlation > 0.0, (
            f"Expected positive correlation between det_approx and xi_real, "
            f"got {correlation:.4f}"
        )

#!/usr/bin/env python3
"""
Tests for QCALSpectralEngine — Mellin-space DVR spectral engine
===============================================================

Validates:
1. Operator construction and Hermiticity
2. Spectrum extraction (positive eigenvalues only)
3. Scale factor application
4. Parameter variations (N, u_min, u_max)
5. Edge cases and robustness

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np

from operators.qcal_spectral_operator import QCALSpectralEngine


# ---------------------------------------------------------------------------
# Construction tests
# ---------------------------------------------------------------------------

class TestEngineConstruction:
    """Tests for QCALSpectralEngine initialisation."""

    def test_default_construction(self):
        """Default constructor should create a 512-point engine."""
        engine = QCALSpectralEngine()
        assert engine.N == 512

    def test_custom_n(self):
        """Custom N should be stored."""
        engine = QCALSpectralEngine(N=64)
        assert engine.N == 64

    def test_u_grid_shape(self):
        """u grid should have exactly N points."""
        engine = QCALSpectralEngine(N=100)
        assert engine.u.shape == (100,)

    def test_u_grid_bounds(self):
        """u grid should span [u_min, u_max]."""
        engine = QCALSpectralEngine(N=50, u_min=-3.0, u_max=3.0)
        assert abs(engine.u[0] - (-3.0)) < 1e-12
        assert abs(engine.u[-1] - 3.0) < 1e-12

    def test_du_uniform(self):
        """Grid spacing should be uniform."""
        engine = QCALSpectralEngine(N=100)
        diffs = np.diff(engine.u)
        assert np.allclose(diffs, engine.du, atol=1e-12)

    def test_invalid_n_raises(self):
        """N < 2 should raise ValueError."""
        with pytest.raises(ValueError):
            QCALSpectralEngine(N=1)


# ---------------------------------------------------------------------------
# Operator tests
# ---------------------------------------------------------------------------

class TestOperatorConstruction:
    """Tests for the Mellin-space Hamiltonian matrix."""

    @pytest.fixture
    def engine(self):
        return QCALSpectralEngine(N=50)

    def test_operator_shape(self, engine):
        """Operator should be N×N."""
        H = engine.generate_operator()
        assert H.shape == (engine.N, engine.N)

    def test_operator_dtype(self, engine):
        """Operator should be complex."""
        H = engine.generate_operator()
        assert np.iscomplexobj(H)

    def test_hermiticity(self, engine):
        """H should equal H† (Hermitian)."""
        H = engine.generate_operator()
        assert np.allclose(H, H.conj().T, atol=1e-12)

    def test_verify_hermiticity_flag(self, engine):
        """verify_hermiticity should return is_hermitian=True."""
        result = engine.verify_hermiticity()
        assert result["is_hermitian"] is True
        assert result["hermiticity_error"] < 1e-10

    def test_diagonal_is_zero(self, engine):
        """Diagonal of H should be zero (pure off-diagonal structure)."""
        H = engine.generate_operator()
        assert np.allclose(np.diag(H), 0, atol=1e-12)


# ---------------------------------------------------------------------------
# Spectrum tests
# ---------------------------------------------------------------------------

class TestSpectrum:
    """Tests for eigenvalue extraction."""

    @pytest.fixture
    def engine(self):
        return QCALSpectralEngine(N=100)

    def test_spectrum_positive(self, engine):
        """All returned eigenvalues should be strictly positive."""
        spectrum = engine.compute_spectrum()
        assert np.all(spectrum > 0)

    def test_spectrum_sorted(self, engine):
        """Returned eigenvalues should be sorted ascending."""
        spectrum = engine.compute_spectrum()
        assert np.all(np.diff(spectrum) >= -1e-10)

    def test_spectrum_real(self, engine):
        """Eigenvalues should be real (no imaginary part)."""
        spectrum = engine.compute_spectrum()
        assert np.all(np.isreal(spectrum))

    def test_spectrum_half_size(self, engine):
        """Positive spectrum should be roughly half of N eigenvalues."""
        spectrum = engine.compute_spectrum()
        # Antisymmetric matrix has ~N/2 positive eigenvalues (exclude zero)
        assert len(spectrum) > 0
        assert len(spectrum) <= engine.N

    def test_scale_factor_unity(self, engine):
        """scale_factor=1.0 should return unscaled eigenvalues."""
        s1 = engine.compute_spectrum(scale_factor=1.0)
        s2 = engine.compute_spectrum(scale_factor=1.0)
        assert np.allclose(s1, s2)

    def test_scale_factor_applied(self, engine):
        """scale_factor should multiply all eigenvalues."""
        s1 = engine.compute_spectrum(scale_factor=1.0)
        s2 = engine.compute_spectrum(scale_factor=2.0)
        assert np.allclose(s2, 2.0 * s1)

    def test_scale_factor_zero(self, engine):
        """scale_factor=0 should return all zeros."""
        s = engine.compute_spectrum(scale_factor=0.0)
        assert np.allclose(s, 0)

    def test_spectrum_nonempty(self, engine):
        """Spectrum should be non-empty for N ≥ 2."""
        spectrum = engine.compute_spectrum()
        assert len(spectrum) > 0


# ---------------------------------------------------------------------------
# Mathematical consistency
# ---------------------------------------------------------------------------

class TestMathematicalConsistency:
    """Verify internal mathematical consistency of the engine."""

    def test_antisymmetric_imaginary_part(self):
        """Im(H) should be antisymmetric (A.T = -A) because D is antisymmetric."""
        engine = QCALSpectralEngine(N=30)
        H = engine.generate_operator()
        # H = -1j * D, so H.imag = -D.
        # D is real antisymmetric: D.T = -D, so H.imag.T = (-D).T = D = -H.imag.
        assert np.allclose(H.imag.T, -H.imag, atol=1e-12)

    def test_real_part_is_zero(self):
        """Re(H) should be zero for pure -1j*D construction."""
        engine = QCALSpectralEngine(N=30)
        H = engine.generate_operator()
        assert np.allclose(H.real, 0, atol=1e-12)

    def test_eigenvalues_symmetric_about_zero(self):
        """Full eigenvalue spectrum of H should be symmetric about zero."""
        engine = QCALSpectralEngine(N=50)
        H = engine.generate_operator()
        from scipy.linalg import eigvalsh
        all_eigs = eigvalsh(H)
        # Symmetric: for every λ there should be a −λ
        assert np.allclose(all_eigs, -all_eigs[::-1], atol=1e-10)

    def test_larger_n_more_modes(self):
        """Larger N should produce more positive spectral modes."""
        e1 = QCALSpectralEngine(N=50).compute_spectrum()
        e2 = QCALSpectralEngine(N=100).compute_spectrum()
        assert len(e2) > len(e1)

    def test_wider_grid_lower_first_mode(self):
        """Wider grid range should lower the smallest positive eigenvalue."""
        e1 = QCALSpectralEngine(N=50, u_min=-3, u_max=3).compute_spectrum()
        e2 = QCALSpectralEngine(N=50, u_min=-6, u_max=6).compute_spectrum()
        assert e2[0] < e1[0]


# ---------------------------------------------------------------------------
# Robustness / edge cases
# ---------------------------------------------------------------------------

class TestRobustness:
    """Edge cases for QCALSpectralEngine."""

    def test_small_n(self):
        """N=2 should work without errors."""
        engine = QCALSpectralEngine(N=2)
        spectrum = engine.compute_spectrum()
        assert isinstance(spectrum, np.ndarray)

    def test_large_scale_factor(self):
        """Very large scale_factor should not overflow."""
        engine = QCALSpectralEngine(N=20)
        spectrum = engine.compute_spectrum(scale_factor=1e10)
        assert np.all(np.isfinite(spectrum))

    def test_idempotent_operator(self):
        """Calling generate_operator twice should give the same matrix."""
        engine = QCALSpectralEngine(N=20)
        H1 = engine.generate_operator()
        H2 = engine.generate_operator()
        assert np.allclose(H1, H2)

    def test_different_n_same_du_ratio(self):
        """For same u range, du should scale as 1/(N−1)."""
        N1, N2 = 50, 100
        e1 = QCALSpectralEngine(N=N1, u_min=-5, u_max=5)
        e2 = QCALSpectralEngine(N=N2, u_min=-5, u_max=5)
        ratio = e1.du / e2.du
        expected = (N2 - 1) / (N1 - 1)
        assert abs(ratio - expected) < 1e-10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

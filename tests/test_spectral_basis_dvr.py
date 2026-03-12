#!/usr/bin/env python3
"""
Tests for Spectral Basis DVR Operator
=====================================

Tests for the cosine/parity DVR spectral basis implementation including:
  - DVR basis construction
  - Adaptive arithmetic potential with Gaussian convolution
  - Eigenvalue computation and Hermiticity
  - Riemann zero correlation
  - Spectral determinant vs ξ comparison

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.spectral_basis_dvr import (
    SpectralBasisDVR,
    prime_sieve,
    validar_evidencia_brutal,
    DVRBasisResult,
    AdaptivePotentialResult,
    EigenvalueResult,
    ZeroCorrelationResult,
    SpectralDeterminantResult,
    SpectralDVRCertificate,
    F0_QCAL,
    C_COHERENCE,
)


# ============================================================
# Utility tests
# ============================================================

class TestPrimeSieve:
    """Test prime sieve utility."""

    def test_small_primes(self):
        primes = prime_sieve(20)
        assert primes == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_no_primes_below_2(self):
        assert prime_sieve(1) == []
        assert prime_sieve(0) == []

    def test_single_prime(self):
        assert prime_sieve(2) == [2]

    def test_count_up_to_100(self):
        primes = prime_sieve(100)
        assert len(primes) == 25  # 25 primes up to 100


# ============================================================
# Operator construction tests
# ============================================================

class TestSpectralBasisDVRInit:
    """Test operator initialization and parameter validation."""

    def test_default_init(self):
        op = SpectralBasisDVR(N=50, L=8.0)
        assert op.N == 50
        assert op.L == 8.0
        assert op.epsilon_0 == pytest.approx(0.04, abs=1e-10)
        assert len(op.u_grid) == op.n_grid

    def test_invalid_N(self):
        with pytest.raises(ValueError, match="N must be at least 10"):
            SpectralBasisDVR(N=5)

    def test_invalid_L(self):
        with pytest.raises(ValueError, match="L must be positive"):
            SpectralBasisDVR(N=20, L=-1.0)

    def test_invalid_epsilon(self):
        with pytest.raises(ValueError, match="epsilon_0 must be positive"):
            SpectralBasisDVR(N=20, L=8.0, epsilon_0=-0.01)

    def test_invalid_n_primes(self):
        with pytest.raises(ValueError, match="n_primes must be at least 1"):
            SpectralBasisDVR(N=20, L=8.0, n_primes=0)

    def test_invalid_max_k(self):
        with pytest.raises(ValueError, match="max_k must be at least 1"):
            SpectralBasisDVR(N=20, L=8.0, max_k=0)

    def test_grid_bounds(self):
        op = SpectralBasisDVR(N=20, L=8.0, n_grid=100)
        assert op.u_grid[0] == pytest.approx(-8.0, abs=1e-10)
        assert op.u_grid[-1] == pytest.approx(8.0, abs=1e-10)

    def test_grid_symmetry(self):
        op = SpectralBasisDVR(N=20, L=8.0, n_grid=200)
        grid = op.u_grid
        # Grid should be symmetric around 0
        np.testing.assert_allclose(grid + grid[::-1], 0.0, atol=1e-12)


# ============================================================
# Basis tests
# ============================================================

class TestDVRBasis:
    """Test cosine basis construction."""

    @pytest.fixture
    def small_op(self):
        return SpectralBasisDVR(N=20, L=6.0, n_grid=200)

    def test_build_basis_type(self, small_op):
        result = small_op.build_basis()
        assert isinstance(result, DVRBasisResult)

    def test_basis_shape(self, small_op):
        result = small_op.build_basis()
        assert result.basis_matrix.shape == (small_op.n_grid, small_op.N)

    def test_basis_n_basis(self, small_op):
        result = small_op.build_basis()
        assert result.n_basis == small_op.N
        assert result.L == small_op.L

    def test_n0_mode_constant(self, small_op):
        """The n=0 cosine mode should be constant."""
        result = small_op.build_basis()
        phi0 = result.basis_matrix[:, 0]
        # All values equal
        assert np.std(phi0) < 1e-10

    def test_n0_normalization(self, small_op):
        """n=0 mode should be normalized: ∫φ₀² du ≈ 1."""
        result = small_op.build_basis()
        phi0 = result.basis_matrix[:, 0]
        norm_sq = np.sum(phi0 ** 2) * small_op.du
        assert norm_sq == pytest.approx(1.0, abs=0.02)

    def test_n1_normalization(self, small_op):
        """n=1 mode should be normalized: ∫φ₁² du ≈ 1."""
        result = small_op.build_basis()
        phi1 = result.basis_matrix[:, 1]
        norm_sq = np.sum(phi1 ** 2) * small_op.du
        assert norm_sq == pytest.approx(1.0, abs=0.02)

    def test_even_parity(self, small_op):
        """All cosine basis functions should be even: φ(u) = φ(-u)."""
        result = small_op.build_basis()
        for n in range(small_op.N):
            phi_n = result.basis_matrix[:, n]
            # Check φ(u) ≈ φ(-u) (reversed grid)
            np.testing.assert_allclose(phi_n, phi_n[::-1], atol=1e-10)

    def test_psi_range(self, small_op):
        result = small_op.build_basis()
        assert 0.0 <= result.psi <= 1.0


# ============================================================
# Potential tests
# ============================================================

class TestAdaptivePotential:
    """Test adaptive Gaussian-convolved arithmetic potential."""

    @pytest.fixture
    def small_op(self):
        return SpectralBasisDVR(N=20, L=8.0, epsilon_0=0.1,
                                n_primes=10, max_k=3, n_grid=500)

    def test_build_potential_type(self, small_op):
        result = small_op.build_potential()
        assert isinstance(result, AdaptivePotentialResult)

    def test_potential_shape(self, small_op):
        result = small_op.build_potential()
        assert result.V.shape == (small_op.n_grid,)

    def test_potential_non_negative(self, small_op):
        """Gaussian-convolved potential should be non-negative."""
        result = small_op.build_potential()
        assert np.all(result.V >= 0)

    def test_potential_finite(self, small_op):
        result = small_op.build_potential()
        assert np.all(np.isfinite(result.V))

    def test_potential_even_symmetry(self, small_op):
        """Potential should be symmetric V(u) = V(-u)."""
        result = small_op.build_potential()
        V = result.V
        np.testing.assert_allclose(V, V[::-1], atol=1e-8)

    def test_potential_peaks_near_log2(self, small_op):
        """Potential should have a peak near u = log(2) ≈ 0.693."""
        result = small_op.build_potential()
        u = small_op.u_grid
        log2 = np.log(2)
        # Find peak in range [log2 - 0.5, log2 + 0.5]
        mask = (u > log2 - 0.5) & (u < log2 + 0.5)
        V_region = result.V[mask]
        V_outside = result.V[~mask & (u > 0)]
        # Peak should be higher than average outside
        if len(V_region) > 0 and len(V_outside) > 0:
            assert np.max(V_region) > np.mean(V_outside)

    def test_adaptive_epsilon(self, small_op):
        """Epsilon should decrease with k."""
        eps1 = small_op.adaptive_epsilon(1)
        eps2 = small_op.adaptive_epsilon(2)
        eps4 = small_op.adaptive_epsilon(4)
        assert eps1 > eps2 > eps4

    def test_psi_range(self, small_op):
        result = small_op.build_potential()
        assert 0.0 <= result.psi <= 1.0

    def test_n_prime_powers_positive(self, small_op):
        result = small_op.build_potential()
        assert result.n_prime_powers > 0


# ============================================================
# Operator matrix tests
# ============================================================

class TestOperatorMatrix:
    """Test H_ε matrix construction."""

    @pytest.fixture
    def small_op(self):
        return SpectralBasisDVR(N=30, L=8.0, n_primes=5, max_k=2, n_grid=300)

    def test_build_operator_shape(self, small_op):
        H, _, _ = small_op.build_operator_matrix()
        assert H.shape == (small_op.N, small_op.N)

    def test_operator_symmetric(self, small_op):
        """H_ε should be real symmetric (Hermitian)."""
        H, _, _ = small_op.build_operator_matrix()
        diff = np.max(np.abs(H - H.T))
        assert diff < 1e-12, f"Hermiticity error {diff} too large"

    def test_operator_real(self, small_op):
        """H_ε matrix should be real-valued."""
        H, _, _ = small_op.build_operator_matrix()
        assert H.dtype.kind == 'f'  # floating point real

    def test_kinetic_diagonal(self, small_op):
        """Without potential, T is diagonal with entries (nπ/L)²."""
        # Build basis and zero potential
        basis = small_op.build_basis()
        # Create zero potential
        from operators.spectral_basis_dvr import AdaptivePotentialResult
        zero_pot = AdaptivePotentialResult(
            V=np.zeros(small_op.n_grid),
            epsilon_values=[],
            n_prime_powers=0,
            psi=0.0,
        )
        H, _, _ = small_op.build_operator_matrix(basis, zero_pot)

        # Check diagonal entries match (nπ/L)²
        for n in range(small_op.N):
            expected = (n * np.pi / small_op.L) ** 2
            assert H[n, n] == pytest.approx(expected, rel=1e-10)

        # Check off-diagonal is zero
        off_diag = H - np.diag(np.diag(H))
        assert np.max(np.abs(off_diag)) < 1e-12


# ============================================================
# Eigenvalue tests
# ============================================================

class TestEigenvalues:
    """Test eigenvalue computation."""

    @pytest.fixture
    def small_op(self):
        return SpectralBasisDVR(N=40, L=8.0, n_primes=10, max_k=2, n_grid=400)

    def test_eigenvalue_type(self, small_op):
        result = small_op.compute_eigenvalues(n_eigenvalues=20)
        assert isinstance(result, EigenvalueResult)

    def test_eigenvalue_count(self, small_op):
        result = small_op.compute_eigenvalues(n_eigenvalues=20)
        assert result.n_computed == 20

    def test_eigenvalues_real(self, small_op):
        """All eigenvalues must be real (operator is symmetric)."""
        result = small_op.compute_eigenvalues(n_eigenvalues=20)
        assert np.all(np.isfinite(result.eigenvalues))
        assert np.all(np.isreal(result.eigenvalues))

    def test_eigenvalues_sorted(self, small_op):
        """Eigenvalues should be sorted ascending."""
        result = small_op.compute_eigenvalues(n_eigenvalues=20)
        eigs = result.eigenvalues
        assert np.all(eigs[:-1] <= eigs[1:])

    def test_hermiticity_error_small(self, small_op):
        """H should be symmetric to machine precision."""
        result = small_op.compute_eigenvalues(n_eigenvalues=10)
        assert result.hermiticity_error < 1e-12

    def test_psi_range(self, small_op):
        result = small_op.compute_eigenvalues(n_eigenvalues=10)
        assert 0.0 <= result.psi <= 1.0

    def test_n_eigenvalues_capped_at_N(self, small_op):
        """Cannot request more eigenvalues than basis size."""
        result = small_op.compute_eigenvalues(n_eigenvalues=1000)
        assert result.n_computed <= small_op.N

    def test_positive_eigenvalues_exist(self, small_op):
        """At least some positive eigenvalues should exist."""
        result = small_op.compute_eigenvalues(n_eigenvalues=30)
        assert np.any(result.eigenvalues > 0)


# ============================================================
# Zero correlation tests
# ============================================================

class TestZeroCorrelation:
    """Test Riemann zero correlation."""

    @pytest.fixture
    def medium_op(self):
        return SpectralBasisDVR(N=60, L=10.0, n_primes=15, max_k=3, n_grid=600)

    def test_correlation_type(self, medium_op):
        eigs = medium_op.compute_eigenvalues(n_eigenvalues=30).eigenvalues
        result = medium_op.correlate_with_zeros(eigs, n_zeros=10)
        assert isinstance(result, ZeroCorrelationResult)

    def test_pearson_r_range(self, medium_op):
        """Pearson r should be in [-1, 1]."""
        eigs = medium_op.compute_eigenvalues(n_eigenvalues=30).eigenvalues
        result = medium_op.correlate_with_zeros(eigs, n_zeros=10)
        assert -1.0 <= result.pearson_r <= 1.0

    def test_mae_positive(self, medium_op):
        eigs = medium_op.compute_eigenvalues(n_eigenvalues=30).eigenvalues
        result = medium_op.correlate_with_zeros(eigs, n_zeros=10)
        assert result.mean_abs_error >= 0.0

    def test_n_compared(self, medium_op):
        eigs = medium_op.compute_eigenvalues(n_eigenvalues=30).eigenvalues
        result = medium_op.correlate_with_zeros(eigs, n_zeros=10)
        assert result.n_compared >= 1

    def test_psi_range(self, medium_op):
        eigs = medium_op.compute_eigenvalues(n_eigenvalues=30).eigenvalues
        result = medium_op.correlate_with_zeros(eigs, n_zeros=10)
        assert 0.0 <= result.psi <= 1.0

    def test_fetch_zeros_positive(self, medium_op):
        """Fetched zeros should all be positive (imaginary parts > 0)."""
        zeros = medium_op.fetch_riemann_zeros(5)
        assert all(z > 0 for z in zeros)
        assert len(zeros) >= 1

    def test_first_zero_approx(self, medium_op):
        """First Riemann zero should be near 14.1347."""
        zeros = medium_op.fetch_riemann_zeros(1)
        assert zeros[0] == pytest.approx(14.1347, abs=0.01)


# ============================================================
# Spectral determinant tests
# ============================================================

class TestSpectralDeterminant:
    """Test spectral determinant computation."""

    @pytest.fixture
    def small_op(self):
        return SpectralBasisDVR(N=30, L=8.0, n_primes=5, max_k=2, n_grid=300)

    def test_log_det_type(self, small_op):
        eigs = np.array([14.0, 21.0, 25.0])
        t_vals = np.array([10.0, 20.0, 30.0])
        log_det = small_op.compute_log_det(t_vals, eigs)
        assert log_det.shape == t_vals.shape
        assert np.all(np.isfinite(log_det))

    def test_spectral_determinant_type(self, small_op):
        eigs = small_op.compute_eigenvalues(n_eigenvalues=20).eigenvalues
        result = small_op.compute_spectral_determinant(
            eigs, t_min=5.0, t_max=30.0, n_t=20
        )
        assert isinstance(result, SpectralDeterminantResult)

    def test_correlation_range(self, small_op):
        eigs = small_op.compute_eigenvalues(n_eigenvalues=20).eigenvalues
        result = small_op.compute_spectral_determinant(
            eigs, t_min=5.0, t_max=30.0, n_t=20
        )
        assert -1.0 <= result.correlation <= 1.0

    def test_synchrony_range(self, small_op):
        eigs = small_op.compute_eigenvalues(n_eigenvalues=20).eigenvalues
        result = small_op.compute_spectral_determinant(
            eigs, t_min=5.0, t_max=30.0, n_t=20
        )
        assert 0.0 <= result.synchrony_score <= 1.0

    def test_psi_range(self, small_op):
        eigs = small_op.compute_eigenvalues(n_eigenvalues=20).eigenvalues
        result = small_op.compute_spectral_determinant(
            eigs, t_min=5.0, t_max=30.0, n_t=20
        )
        assert 0.0 <= result.psi <= 1.0

    def test_t_values_correct(self, small_op):
        eigs = small_op.compute_eigenvalues(n_eigenvalues=20).eigenvalues
        result = small_op.compute_spectral_determinant(
            eigs, t_min=5.0, t_max=30.0, n_t=20
        )
        assert len(result.t_values) == 20
        assert result.t_values[0] == pytest.approx(5.0, abs=1e-10)
        assert result.t_values[-1] == pytest.approx(30.0, abs=1e-10)

    def test_log_xi_finite(self, small_op):
        """log|ξ| should be finite for t in valid range."""
        t_vals = np.array([10.0, 20.0, 30.0, 40.0])
        log_xi = small_op.compute_log_xi(t_vals)
        assert log_xi.shape == t_vals.shape
        assert np.all(np.isfinite(log_xi))


# ============================================================
# Full validation pipeline test
# ============================================================

class TestValidationPipeline:
    """Test full validation pipeline."""

    @pytest.fixture
    def tiny_op(self):
        """Very small operator for quick pipeline test."""
        return SpectralBasisDVR(N=20, L=6.0, n_primes=5, max_k=2, n_grid=200)

    def test_validate_returns_certificate(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=20)
        assert isinstance(cert, SpectralDVRCertificate)

    def test_certificate_psi_range(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=20)
        assert 0.0 <= cert.psi <= 1.0

    def test_certificate_has_hash(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=20)
        assert cert.certificate_hash.startswith("0xQCAL_DVR_")

    def test_certificate_eigenvalue_count(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=20)
        assert cert.n_eigenvalues <= tiny_op.N

    def test_certificate_zeros_compared(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=20)
        assert cert.n_zeros_compared >= 1

    def test_certificate_timing(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=10)
        assert cert.computation_time_ms > 0

    def test_certificate_pearson_range(self, tiny_op):
        cert = tiny_op.validate(n_eigenvalues=10, n_zeros=5, n_t=10)
        assert -1.0 <= cert.pearson_correlation <= 1.0


# ============================================================
# Convenience function test
# ============================================================

class TestValidarEvidenciaBrutal:
    """Test the top-level convenience function."""

    def test_returns_certificate(self):
        cert = validar_evidencia_brutal(
            N_basis=20,
            L=6.0,
            epsilon_0=0.1,
            n_eigenvalues=10,
            n_zeros=5,
        )
        assert isinstance(cert, SpectralDVRCertificate)

    def test_certificate_valid_fields(self):
        cert = validar_evidencia_brutal(
            N_basis=20,
            L=6.0,
            epsilon_0=0.1,
            n_eigenvalues=10,
            n_zeros=5,
        )
        assert cert.n_basis == 20
        assert cert.L == pytest.approx(6.0, abs=1e-10)
        assert cert.epsilon_0 == pytest.approx(0.1, abs=1e-10)


# ============================================================
# Constants tests
# ============================================================

class TestConstants:
    """Test QCAL constants are correct."""

    def test_f0_qcal(self):
        assert F0_QCAL == pytest.approx(141.7001, abs=1e-4)

    def test_c_coherence(self):
        assert C_COHERENCE == pytest.approx(244.36, abs=1e-2)

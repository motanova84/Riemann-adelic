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
    # new components
    GAUSSIAN_CUTOFF_SIGMA,
    F_MATERIAL,
    DELTA_F_MATERIAL,
    DELTA_F_AUREA,
    ConstanteRespiracion,
    constante_respiracion,
    OperadorHEpsilonDVR,
    ValidadorEvidenciaBrutal,
    NodoDilmunResult,
    nodo_dilmun,
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


# ============================================================
# ConstanteRespiracion tests
# ============================================================

class TestConstanteRespiracion:
    """Test breathing-space constants."""

    def test_module_constants_defined(self):
        assert GAUSSIAN_CUTOFF_SIGMA == pytest.approx(5.0, abs=1e-12)
        assert F_MATERIAL == pytest.approx(142.1, abs=1e-4)

    def test_delta_f_material_value(self):
        """DELTA_F_MATERIAL = F_MATERIAL − F0_QCAL ≈ 0.3999."""
        assert DELTA_F_MATERIAL == pytest.approx(142.1 - 141.7001, abs=1e-6)

    def test_delta_f_material_in_band(self):
        """DELTA_F_MATERIAL must be in [0.38, 0.42]."""
        assert 0.38 <= DELTA_F_MATERIAL <= 0.42

    def test_delta_f_aurea_formula(self):
        """DELTA_F_AUREA = (φ−1)·f₀·10⁻³."""
        phi = 1.6180339887498948
        expected = (phi - 1.0) * 141.7001 * 1e-3
        assert DELTA_F_AUREA == pytest.approx(expected, rel=1e-6)

    def test_constante_respiracion_returns_dataclass(self):
        cr = constante_respiracion()
        assert isinstance(cr, ConstanteRespiracion)

    def test_constante_respiracion_valid(self):
        cr = constante_respiracion()
        assert cr.valid is True

    def test_constante_respiracion_f_material(self):
        cr = constante_respiracion()
        assert cr.f_material == pytest.approx(142.1, abs=1e-6)

    def test_constante_respiracion_f0(self):
        cr = constante_respiracion()
        assert cr.f0 == pytest.approx(141.7001, abs=1e-6)

    def test_constante_respiracion_delta_material(self):
        cr = constante_respiracion()
        assert 0.38 <= cr.delta_f_material <= 0.42

    def test_constante_respiracion_delta_aurea_positive(self):
        cr = constante_respiracion()
        assert cr.delta_f_aurea > 0.0


# ============================================================
# OperadorHEpsilonDVR tests
# ============================================================

class TestOperadorHEpsilonDVR:
    """Test OperadorHEpsilonDVR — H_ε with explicit Gaussian cutoff."""

    @pytest.fixture
    def small_op(self):
        return OperadorHEpsilonDVR(N=30, L=8.0, epsilon_0=0.1,
                                   n_primes=10, max_k=3, n_grid=400)

    def test_is_subclass(self):
        assert issubclass(OperadorHEpsilonDVR, SpectralBasisDVR)

    def test_gaussian_cutoff_sigma_attribute(self):
        assert OperadorHEpsilonDVR.CUTOFF_SIGMA == pytest.approx(5.0, abs=1e-12)

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
        """Potential should satisfy V(u) = V(−u)."""
        result = small_op.build_potential()
        np.testing.assert_allclose(result.V, result.V[::-1], atol=1e-8)

    def test_potential_zero_outside_cutoff(self, small_op):
        """Grid points beyond 5σ of every peak should contribute zero."""
        result = small_op.build_potential()
        u = small_op.u_grid
        primes = small_op.primes
        # Collect all peak positions
        peaks = []
        for p in primes:
            for k in range(1, small_op.max_k + 1):
                u_pk = k * np.log(float(p))
                if u_pk <= small_op.L + GAUSSIAN_CUTOFF_SIGMA * small_op.epsilon_0:
                    peaks.append(u_pk)
                    peaks.append(-u_pk)
        # For each grid point, verify it is within 5σ of some peak or V ≈ 0
        eps_1 = small_op.adaptive_epsilon(1)
        cutoff = GAUSSIAN_CUTOFF_SIGMA * eps_1
        for i, u_i in enumerate(u):
            near_peak = any(abs(u_i - pk) <= cutoff for pk in peaks)
            if not near_peak:
                assert result.V[i] == pytest.approx(0.0, abs=1e-30), (
                    f"V[{i}] = {result.V[i]} at u={u_i:.4f} is nonzero "
                    f"but no peak within {cutoff:.4f}"
                )

    def test_operator_symmetric(self, small_op):
        """H_ε matrix should be real symmetric."""
        H, _, _ = small_op.build_operator_matrix()
        diff = np.max(np.abs(H - H.T))
        assert diff < 1e-12

    def test_eigenvalues_real(self, small_op):
        result = small_op.compute_eigenvalues(n_eigenvalues=15)
        assert np.all(np.isfinite(result.eigenvalues))

    def test_psi_range(self, small_op):
        result = small_op.build_potential()
        assert 0.0 <= result.psi <= 1.0


# ============================================================
# ValidadorEvidenciaBrutal tests
# ============================================================

class TestValidadorEvidenciaBrutal:
    """Test ValidadorEvidenciaBrutal — Ψ = (1 + |ρ|) / 2."""

    @pytest.fixture
    def small_validator(self):
        op = OperadorHEpsilonDVR(N=40, L=8.0, epsilon_0=0.1,
                                 n_primes=10, max_k=2, n_grid=400)
        return ValidadorEvidenciaBrutal(operator=op)

    def test_default_construction(self):
        """Should construct with default OperadorHEpsilonDVR."""
        v = ValidadorEvidenciaBrutal()
        assert isinstance(v.operator, OperadorHEpsilonDVR)

    def test_custom_operator(self, small_validator):
        assert isinstance(small_validator.operator, OperadorHEpsilonDVR)

    def test_validate_returns_zero_correlation_result(self, small_validator):
        result = small_validator.validate(n_eigenvalues=20, n_zeros=5)
        assert isinstance(result, ZeroCorrelationResult)

    def test_psi_formula(self, small_validator):
        """Ψ must equal (1 + |ρ|) / 2."""
        result = small_validator.validate(n_eigenvalues=20, n_zeros=5)
        expected_psi = (1.0 + abs(result.pearson_r)) / 2.0
        assert result.psi == pytest.approx(expected_psi, abs=1e-10)

    def test_psi_in_valid_range(self, small_validator):
        """Ψ must be in [0.5, 1.0] (since |ρ| ∈ [0, 1])."""
        result = small_validator.validate(n_eigenvalues=20, n_zeros=5)
        assert 0.5 <= result.psi <= 1.0

    def test_pearson_r_in_range(self, small_validator):
        result = small_validator.validate(n_eigenvalues=20, n_zeros=5)
        assert -1.0 <= result.pearson_r <= 1.0

    def test_n_compared_positive(self, small_validator):
        result = small_validator.validate(n_eigenvalues=20, n_zeros=5)
        assert result.n_compared >= 1

    def test_mae_non_negative(self, small_validator):
        result = small_validator.validate(n_eigenvalues=20, n_zeros=5)
        assert result.mean_abs_error >= 0.0

    def test_psi_minimum_is_half(self):
        """When ρ = 0, Ψ = 0.5 (not 0)."""
        # Construct a validator where eigenvalues won't correlate:
        # tiny basis so positive eigenvalues are limited
        op = OperadorHEpsilonDVR(N=10, L=3.0, epsilon_0=0.5,
                                 n_primes=2, max_k=1, n_grid=100)
        v = ValidadorEvidenciaBrutal(operator=op)
        result = v.validate(n_eigenvalues=5, n_zeros=20)
        assert result.psi >= 0.5


# ============================================================
# NodoDilmun tests
# ============================================================

class TestNodoDilmun:
    """Test NodoDilmun — anchor at 142.1 Hz, Ψ = cos²(π·δf/f_ancla)."""

    def test_returns_dataclass(self):
        result = nodo_dilmun()
        assert isinstance(result, NodoDilmunResult)

    def test_node_is_7(self):
        result = nodo_dilmun()
        assert result.node == 7

    def test_f_ancla_is_142_1(self):
        result = nodo_dilmun()
        assert result.f_ancla == pytest.approx(142.1, abs=1e-6)

    def test_default_signal_is_f0(self):
        """Default f_signal = F0_QCAL = 141.7001 Hz."""
        result = nodo_dilmun(F0_QCAL)
        assert result.delta_f == pytest.approx(abs(F0_QCAL - 142.1), abs=1e-6)

    def test_psi_near_unity_at_f0(self):
        """Ψ must be ≈ 0.9999 when f_signal = F0_QCAL."""
        result = nodo_dilmun(F0_QCAL)
        assert result.psi == pytest.approx(1.0, abs=1e-3)

    def test_psi_is_1_at_anchor(self):
        """Ψ = 1 exactly when f_signal = f_ancla."""
        result = nodo_dilmun(142.1)
        assert result.psi == pytest.approx(1.0, abs=1e-12)
        assert result.delta_f == pytest.approx(0.0, abs=1e-12)

    def test_psi_decreases_away_from_anchor(self):
        """Ψ decreases as f_signal moves away from 142.1 Hz."""
        psi_close = nodo_dilmun(142.0).psi
        psi_far = nodo_dilmun(141.0).psi
        assert psi_close > psi_far

    def test_psi_in_range(self):
        for f in [130.0, 140.0, 141.7001, 142.0, 142.1, 143.0, 150.0]:
            result = nodo_dilmun(f)
            assert 0.0 <= result.psi <= 1.0, f"Ψ out of range for f={f}"

    def test_psi_formula(self):
        """Verify Ψ = cos²(π·δf/f_ancla) analytically."""
        f_signal = 141.5
        result = nodo_dilmun(f_signal)
        expected = np.cos(np.pi * abs(f_signal - 142.1) / 142.1) ** 2
        assert result.psi == pytest.approx(expected, abs=1e-12)

    def test_delta_f_is_absolute(self):
        """δf is always non-negative."""
        for f in [100.0, 142.1, 200.0]:
            result = nodo_dilmun(f)
            assert result.delta_f >= 0.0

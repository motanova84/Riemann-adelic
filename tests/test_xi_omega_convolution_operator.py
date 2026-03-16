#!/usr/bin/env python3
"""
Tests for XI-OMEGA Convolution Operator
========================================

Comprehensive test suite for the XI-OMEGA module implementing:
- Jacobi theta function kernel Φ(u)
- Periodic prime potential V_p(u)
- Self-adjoint positive convolution operator T
- Hamiltonian H = -log T
- Spectral density

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.xi_omega_convolution_operator import (
    XiOmegaConvolutionOperator,
    JacobiThetaResult,
    PrimePotentialResult,
    ConvolutionKernelResult,
    OperatorTResult,
    HamiltonianResult,
    SpectralDensityResult,
    XiOmegaCertificate,
    F0_QCAL,
    C_COHERENCE,
    _sieve_primes,
)


# =============================================================================
# Fixtures
# =============================================================================


@pytest.fixture
def op_small():
    """Small operator for quick tests (N=32)."""
    return XiOmegaConvolutionOperator(
        n_grid=32, L=2.0 * np.pi, tau=0.5,
        n_theta_terms=20, max_primes=5, n_harmonics=2, epsilon_reg=0.2,
    )


@pytest.fixture
def op_medium():
    """Medium operator for structural tests (N=64)."""
    return XiOmegaConvolutionOperator(
        n_grid=64, L=2.0 * np.pi, tau=0.5,
        n_theta_terms=30, max_primes=10, n_harmonics=3, epsilon_reg=0.15,
    )


# =============================================================================
# Tests: Initialization
# =============================================================================


class TestInitialization:
    """Test operator initialization and parameter validation."""

    def test_default_initialization(self):
        """Test that default parameters initialize correctly."""
        op = XiOmegaConvolutionOperator()
        assert op.n_grid == 128
        assert op.L == pytest.approx(2.0 * np.pi, rel=1e-10)
        assert op.tau == pytest.approx(0.5, rel=1e-10)

    def test_grid_length(self, op_small):
        """Test that grid has correct number of points."""
        assert len(op_small.u_grid) == op_small.n_grid

    def test_grid_range(self, op_small):
        """Test that grid spans [0, L)."""
        assert op_small.u_grid[0] == pytest.approx(0.0, abs=1e-12)
        assert op_small.u_grid[-1] < op_small.L
        assert op_small.u_grid[-1] == pytest.approx(
            op_small.L - op_small.L / op_small.n_grid, rel=1e-10
        )

    def test_grid_spacing(self, op_small):
        """Test uniform grid spacing."""
        diffs = np.diff(op_small.u_grid)
        assert np.all(np.abs(diffs - op_small.du) < 1e-12)

    def test_invalid_n_grid(self):
        """Test that n_grid < 4 raises ValueError."""
        with pytest.raises(ValueError, match="n_grid"):
            XiOmegaConvolutionOperator(n_grid=2)

    def test_invalid_L(self):
        """Test that L ≤ 0 raises ValueError."""
        with pytest.raises(ValueError, match="L must be positive"):
            XiOmegaConvolutionOperator(L=-1.0)

    def test_invalid_tau(self):
        """Test that tau ≤ 0 raises ValueError."""
        with pytest.raises(ValueError, match="tau must be positive"):
            XiOmegaConvolutionOperator(tau=0.0)

    def test_invalid_epsilon_reg(self):
        """Test that epsilon_reg ≤ 0 raises ValueError."""
        with pytest.raises(ValueError, match="epsilon_reg must be positive"):
            XiOmegaConvolutionOperator(epsilon_reg=0.0)


# =============================================================================
# Tests: Sieve of Eratosthenes
# =============================================================================


class TestSievePrimes:
    """Test prime sieve helper."""

    def test_small_primes(self):
        """Test known small primes."""
        assert _sieve_primes(10) == [2, 3, 5, 7]
        assert _sieve_primes(20) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_no_primes_below_2(self):
        """Test empty list for n_max < 2."""
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_prime_count(self):
        """Test prime counting: π(100) = 25."""
        assert len(_sieve_primes(100)) == 25


# =============================================================================
# Tests: Jacobi Theta Function
# =============================================================================


class TestJacobiTheta:
    """Test Jacobi theta function computation."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        result = op_small.compute_jacobi_theta()
        assert isinstance(result, JacobiThetaResult)

    def test_grid_length(self, op_small):
        """Test that theta values have correct length."""
        result = op_small.compute_jacobi_theta()
        assert len(result.theta_values) == op_small.n_grid
        assert len(result.u_grid) == op_small.n_grid

    def test_theta_positive(self, op_small):
        """Test that Θ₃(u|iτ) > 0 for τ > 0 (it is a probability density)."""
        result = op_small.compute_jacobi_theta()
        assert np.all(result.theta_values > 0), (
            f"Theta has non-positive values; min={np.min(result.theta_values):.6f}"
        )

    def test_theta_at_origin(self, op_small):
        """Test Θ₃(0|iτ) = 1 + 2Σ exp(-πn²τ) > 1."""
        result = op_small.compute_jacobi_theta()
        # u=0 is the first grid point
        assert result.theta_values[0] > 1.0

    def test_theta_symmetry(self, op_small):
        """Test Θ₃(u|iτ) = Θ₃(-u|iτ) = Θ₃(L-u|iτ) (periodic even function)."""
        result = op_small.compute_jacobi_theta()
        theta = result.theta_values
        N = op_small.n_grid
        # θ(u_k) should equal θ(u_{N-k}) for periodic even function
        # u_0=0, u_k = k*L/N, u_{N-k} = (N-k)*L/N = L - k*L/N ≡ -k*L/N mod L
        for k in range(1, N // 2):
            assert theta[k] == pytest.approx(theta[N - k], rel=1e-6), (
                f"Theta not even at k={k}: θ[k]={theta[k]:.6f}, θ[N-k]={theta[N-k]:.6f}"
            )

    def test_tau_dependence(self, op_small):
        """Test that larger tau gives more concentrated kernel (smaller spread)."""
        result_small_tau = op_small.compute_jacobi_theta(tau=0.1)
        result_large_tau = op_small.compute_jacobi_theta(tau=2.0)
        # For larger tau, e^{-πn²τ} decays faster → more uniform (closer to 1)
        # For smaller tau, the peak at u=0 is higher
        assert result_small_tau.theta_values[0] >= result_large_tau.theta_values[0]

    def test_convergence_error_small(self, op_small):
        """Test that convergence error is small for reasonable tau."""
        result = op_small.compute_jacobi_theta(tau=0.5)
        assert result.convergence_error < 1e-10

    def test_tau_stored(self, op_small):
        """Test that the tau value is stored correctly."""
        custom_tau = 0.3
        result = op_small.compute_jacobi_theta(tau=custom_tau)
        assert result.tau == pytest.approx(custom_tau, rel=1e-10)


# =============================================================================
# Tests: Prime Potential
# =============================================================================


class TestPrimePotential:
    """Test periodic prime potential computation."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        result = op_small.compute_prime_potential()
        assert isinstance(result, PrimePotentialResult)

    def test_grid_length(self, op_small):
        """Test potential has correct length."""
        result = op_small.compute_prime_potential()
        assert len(result.potential_values) == op_small.n_grid

    def test_potential_non_negative(self, op_small):
        """Test that potential is non-negative (sum of Gaussians with + coefficients)."""
        result = op_small.compute_prime_potential(amplitude=1.0)
        assert np.all(result.potential_values >= 0.0)

    def test_primes_used_count(self, op_small):
        """Test that correct number of primes are used."""
        result = op_small.compute_prime_potential()
        assert len(result.primes_used) == op_small.max_primes

    def test_first_prime_is_2(self, op_small):
        """Test that the first prime is 2."""
        result = op_small.compute_prime_potential()
        assert result.primes_used[0] == 2

    def test_all_primes_correct(self, op_small):
        """Test that primes used are actually prime."""
        result = op_small.compute_prime_potential()
        for p in result.primes_used:
            assert _sieve_primes(p)[-1] == p, f"{p} is not prime"

    def test_amplitude_scaling(self, op_small):
        """Test that amplitude scales the potential linearly."""
        result1 = op_small.compute_prime_potential(amplitude=1.0)
        result2 = op_small.compute_prime_potential(amplitude=2.0)
        np.testing.assert_allclose(
            result2.potential_values, 2.0 * result1.potential_values, rtol=1e-10
        )


# =============================================================================
# Tests: Convolution Kernel Φ(u)
# =============================================================================


class TestConvolutionKernel:
    """Test convolution kernel Φ(u) construction."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        result = op_small.compute_kernel()
        assert isinstance(result, ConvolutionKernelResult)

    def test_kernel_length(self, op_small):
        """Test kernel has correct length."""
        result = op_small.compute_kernel()
        assert len(result.kernel_values) == op_small.n_grid

    def test_kernel_positive(self, op_small):
        """Test that Φ(u) > 0 for all u (theta dominates)."""
        result = op_small.compute_kernel()
        assert np.all(result.kernel_values > 0), (
            f"Kernel has non-positive values; min={np.min(result.kernel_values):.6f}"
        )

    def test_kernel_real_even(self, op_small):
        """Test that kernel is real and even (required for self-adjointness)."""
        result = op_small.compute_kernel()
        assert result.is_real_even, (
            "Kernel should be real and even after symmetrization"
        )

    def test_positivity_shift(self, op_small):
        """Test that adding a positivity_shift shifts Φ̂(0) upward by the shift value."""
        result_no_shift = op_small.compute_kernel(positivity_shift=0.0)
        result_with_shift = op_small.compute_kernel(positivity_shift=10.0)
        # Adding c to all kernel values increases rfft[0]/N by c (since rfft[0]=sum → +c*N, then /N → +c)
        delta = result_with_shift.fourier_coeffs[0] - result_no_shift.fourier_coeffs[0]
        assert delta == pytest.approx(10.0, rel=1e-6)

    def test_fourier_coeffs_length(self, op_small):
        """Test Fourier coefficient array has correct length (rfft size)."""
        result = op_small.compute_kernel()
        expected_len = op_small.n_grid // 2 + 1
        assert len(result.fourier_coeffs) == expected_len

    def test_zeroth_fourier_coeff_largest(self, op_small):
        """Test Φ̂(0) > Φ̂(n) for n > 0 (kernel concentrated at origin)."""
        result = op_small.compute_kernel()
        fc = result.fourier_coeffs
        assert fc[0] == pytest.approx(np.max(fc), rel=1e-6)


# =============================================================================
# Tests: Operator T
# =============================================================================


class TestOperatorT:
    """Test convolution operator T construction."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        result = op_small.compute_operator_T()
        assert isinstance(result, OperatorTResult)

    def test_T_matrix_shape(self, op_small):
        """Test T matrix has correct shape N×N."""
        result = op_small.compute_operator_T()
        N = op_small.n_grid
        assert result.T_matrix.shape == (N, N)

    def test_T_self_adjoint(self, op_small):
        """Test that T is self-adjoint (‖T - Tᵀ‖/‖T‖ < 1e-10)."""
        result = op_small.compute_operator_T()
        assert result.is_self_adjoint, (
            f"T not self-adjoint; error={result.self_adjointness_error:.2e}"
        )

    def test_T_positive(self, op_small):
        """Test that T is positive semidefinite (all eigenvalues ≥ 0)."""
        result = op_small.compute_operator_T()
        assert result.is_positive, (
            f"T not positive; min eigenvalue={result.positivity_defect:.6e}"
        )

    def test_T_eigenvalues_sorted(self, op_small):
        """Test that eigenvalues are returned in sorted order."""
        result = op_small.compute_operator_T()
        eigs = result.eigenvalues_T
        assert np.all(np.diff(eigs) >= -1e-12), "Eigenvalues not sorted"

    def test_T_eigenvalues_count(self, op_small):
        """Test eigenvalue count equals N."""
        result = op_small.compute_operator_T()
        assert len(result.eigenvalues_T) == op_small.n_grid

    def test_T_circulant_structure(self, op_small):
        """Test that T[i,j] depends only on (i-j) mod N (circulant)."""
        result = op_small.compute_operator_T()
        T = result.T_matrix
        N = op_small.n_grid
        # First row determines circulant: T[i,j] = T[0, (j-i) mod N]
        for i in range(1, min(5, N)):
            for j in range(min(5, N)):
                expected = T[0, (j - i) % N]
                assert T[i, j] == pytest.approx(expected, rel=1e-6), (
                    f"Circulant structure violated at [{i},{j}]"
                )

    def test_T_trace_positive(self, op_small):
        """Test that Tr(T) > 0."""
        result = op_small.compute_operator_T()
        assert np.trace(result.T_matrix) > 0


# =============================================================================
# Tests: Hamiltonian H = -log T
# =============================================================================


class TestHamiltonian:
    """Test Hamiltonian H = -log T construction."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        result = op_small.compute_hamiltonian()
        assert isinstance(result, HamiltonianResult)

    def test_H_matrix_shape(self, op_small):
        """Test H matrix has correct shape N×N."""
        result = op_small.compute_hamiltonian()
        assert result.H_matrix.shape == (op_small.n_grid, op_small.n_grid)

    def test_H_self_adjoint(self, op_small):
        """Test that H is self-adjoint."""
        result = op_small.compute_hamiltonian()
        assert result.is_self_adjoint, "H should be self-adjoint"

    def test_H_real_spectrum(self, op_small):
        """Test that H has real eigenvalues."""
        result = op_small.compute_hamiltonian()
        assert result.is_real_spectrum, "H should have real spectrum"

    def test_H_eigenvalues_count(self, op_small):
        """Test eigenvalue count equals N."""
        result = op_small.compute_hamiltonian()
        assert len(result.eigenvalues_H) == op_small.n_grid

    def test_H_eigenvalues_sorted(self, op_small):
        """Test eigenvalues returned in sorted order."""
        result = op_small.compute_hamiltonian()
        eigs = result.eigenvalues_H
        assert np.all(np.diff(eigs) >= -1e-10), "Eigenvalues not sorted"

    def test_H_spectral_relation_to_T(self, op_small):
        """Test H = -log T: eigenvalues satisfy h_n = -log(λ_n(T))."""
        T_result = op_small.compute_operator_T(enforce_positivity=True)
        H_result = op_small.compute_hamiltonian()

        # Eigenvalues of T (positive, sorted ascending)
        eigs_T = np.sort(T_result.eigenvalues_T[T_result.eigenvalues_T > 1e-15])
        # Corresponding H eigenvalues should be -log(eigs_T)
        expected_H_eigs = np.sort(-np.log(eigs_T))

        # Compare a few eigenvalues
        n_compare = min(len(expected_H_eigs), len(H_result.eigenvalues_H), 5)
        np.testing.assert_allclose(
            np.sort(H_result.eigenvalues_H)[:n_compare],
            np.sort(expected_H_eigs)[:n_compare],
            rtol=1e-4,
            err_msg="H eigenvalues should equal -log(T eigenvalues)",
        )

    def test_psi_in_range(self, op_small):
        """Test that QCAL Ψ coherence is in [0, 1]."""
        result = op_small.compute_hamiltonian()
        assert 0.0 <= result.psi <= 1.0

    def test_riemann_zeros_returned(self, op_small):
        """Test that Riemann zeros are included in result."""
        result = op_small.compute_hamiltonian(n_riemann_zeros=10)
        assert len(result.riemann_zeros) == 10

    def test_first_riemann_zero(self, op_small):
        """Test that first Riemann zero is approximately 14.135."""
        result = op_small.compute_hamiltonian(n_riemann_zeros=5)
        assert result.riemann_zeros[0] == pytest.approx(14.134725, rel=1e-4)

    def test_timestamp_format(self, op_small):
        """Test that timestamp is in ISO format."""
        result = op_small.compute_hamiltonian()
        assert "T" in result.timestamp
        assert "Z" in result.timestamp

    def test_computation_time_positive(self, op_small):
        """Test that computation time is positive."""
        result = op_small.compute_hamiltonian()
        assert result.computation_time_ms > 0


# =============================================================================
# Tests: Spectral Density
# =============================================================================


class TestSpectralDensity:
    """Test spectral density computation."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        H_result = op_small.compute_hamiltonian()
        result = op_small.compute_spectral_density(H_result.eigenvalues_H)
        assert isinstance(result, SpectralDensityResult)

    def test_density_non_negative(self, op_small):
        """Test that ρ(E) ≥ 0 (sum of Gaussians)."""
        H_result = op_small.compute_hamiltonian()
        result = op_small.compute_spectral_density(H_result.eigenvalues_H)
        assert np.all(result.density >= 0.0)

    def test_density_normalization(self, op_small):
        """Test that ∫ρ(E)dE ≈ n_eigenvalues."""
        H_result = op_small.compute_hamiltonian()
        result = op_small.compute_spectral_density(
            H_result.eigenvalues_H, n_points=500
        )
        dE = result.energies[1] - result.energies[0]
        try:
            total = np.trapezoid(result.density, dx=dE)
        except AttributeError:
            total = np.sum(result.density) * dE  # fallback
        assert total == pytest.approx(result.n_eigenvalues, rel=0.05), (
            f"Density not normalized: integral={total:.3f}, N={result.n_eigenvalues}"
        )

    def test_energy_axis_length(self, op_small):
        """Test energy axis has correct number of points."""
        H_result = op_small.compute_hamiltonian()
        n_pts = 100
        result = op_small.compute_spectral_density(
            H_result.eigenvalues_H, n_points=n_pts
        )
        assert len(result.energies) == n_pts
        assert len(result.density) == n_pts
        assert len(result.weyl_law) == n_pts

    def test_oscillatory_part(self, op_small):
        """Test that oscillatory part = density - Weyl law."""
        H_result = op_small.compute_hamiltonian()
        result = op_small.compute_spectral_density(H_result.eigenvalues_H)
        np.testing.assert_allclose(
            result.oscillatory_part,
            result.density - result.weyl_law,
            atol=1e-12,
        )

    def test_n_eigenvalues_correct(self, op_small):
        """Test n_eigenvalues matches input."""
        H_result = op_small.compute_hamiltonian()
        result = op_small.compute_spectral_density(H_result.eigenvalues_H)
        assert result.n_eigenvalues == len(H_result.eigenvalues_H)

    def test_custom_energy_range(self, op_small):
        """Test custom E_min/E_max respected."""
        H_result = op_small.compute_hamiltonian()
        result = op_small.compute_spectral_density(
            H_result.eigenvalues_H, E_min=-5.0, E_max=5.0, n_points=50
        )
        assert result.energies[0] == pytest.approx(-5.0, abs=1e-10)
        assert result.energies[-1] == pytest.approx(5.0, rel=1e-6)


# =============================================================================
# Tests: Validation Certificate
# =============================================================================


class TestValidationCertificate:
    """Test full validation certificate."""

    def test_returns_correct_type(self, op_small):
        """Test return type."""
        cert = op_small.validate()
        assert isinstance(cert, XiOmegaCertificate)

    def test_module_name(self, op_small):
        """Test module name is XI-OMEGA."""
        cert = op_small.validate()
        assert cert.module_name == "XI-OMEGA"

    def test_T_self_adjoint_flag(self, op_small):
        """Test that T self-adjointness flag is True."""
        cert = op_small.validate()
        assert cert.T_self_adjoint

    def test_T_positive_flag(self, op_small):
        """Test that T positivity flag is True."""
        cert = op_small.validate()
        assert cert.T_positive

    def test_H_real_spectrum_flag(self, op_small):
        """Test that H real spectrum flag is True."""
        cert = op_small.validate()
        assert cert.H_real_spectrum

    def test_psi_in_range(self, op_small):
        """Test QCAL Ψ is in [0, 1]."""
        cert = op_small.validate()
        assert 0.0 <= cert.psi <= 1.0

    def test_qcal_frequency(self, op_small):
        """Test QCAL frequency is F₀ = 141.7001 Hz."""
        cert = op_small.validate()
        assert cert.qcal_frequency_hz == pytest.approx(141.7001, rel=1e-6)

    def test_validation_passed(self, op_small):
        """Test that overall validation passes."""
        cert = op_small.validate()
        assert cert.validation_passed

    def test_timestamp_present(self, op_small):
        """Test that timestamp is present."""
        cert = op_small.validate()
        assert len(cert.timestamp) > 0


# =============================================================================
# Tests: Riemann Zero Connection
# =============================================================================


class TestRiemannZeroConnection:
    """Test connection between H spectrum and Riemann zeros."""

    def test_first_zero_retrieval(self, op_small):
        """Test that first Riemann zero is returned with high precision."""
        zeros = op_small._get_riemann_zeros(5)
        assert zeros[0] == pytest.approx(14.134725142, rel=1e-5)

    def test_zeros_increasing(self, op_small):
        """Test that returned zeros are monotone increasing."""
        zeros = op_small._get_riemann_zeros(10)
        assert np.all(np.diff(zeros) > 0), "Riemann zeros should be increasing"

    def test_zeros_count(self, op_small):
        """Test that exact count of zeros is returned."""
        for n in [1, 5, 10, 20, 30]:
            zeros = op_small._get_riemann_zeros(n)
            assert len(zeros) == n

    def test_spectral_correlation_in_range(self, op_small):
        """Test that spectral correlation is in [-1, 1]."""
        H_result = op_small.compute_hamiltonian(n_riemann_zeros=15)
        assert -1.0 <= H_result.spectral_correlation <= 1.0

    def test_spacing_correlation_computed(self, op_small):
        """Test that correlation between spacings is computed and not NaN."""
        H_result = op_small.compute_hamiltonian(n_riemann_zeros=15)
        assert not np.isnan(H_result.spectral_correlation)


# =============================================================================
# Tests: Mathematical Properties
# =============================================================================


class TestMathematicalProperties:
    """Test core mathematical properties of the operator chain."""

    def test_T_commutes_with_shift(self, op_small):
        """Test translation invariance of circulant T."""
        T_result = op_small.compute_operator_T()
        T = T_result.T_matrix
        N = op_small.n_grid

        # Shift matrix: S[i,j] = δ_{i, (j+1) mod N}
        S = np.roll(np.eye(N), 1, axis=0)

        # [T, S] should be ~ 0 for circulant T
        commutator = T @ S - S @ T
        assert np.linalg.norm(commutator) / (np.linalg.norm(T) + 1e-30) < 1e-8, (
            "T should commute with circular shift (circulant matrix)"
        )

    def test_H_defined_via_log(self, op_small):
        """Test that exp(-H) ≈ T (functional calculus consistency)."""
        T_result = op_small.compute_operator_T(enforce_positivity=True)
        H_result = op_small.compute_hamiltonian()

        # exp(-H) should recover T
        # Use eigendecomposition for numerical stability
        eigs_H, vecs_H = np.linalg.eigh(H_result.H_matrix)
        T_reconstructed = vecs_H @ np.diag(np.exp(-eigs_H)) @ vecs_H.T

        # Compare relative error
        T_norm = np.linalg.norm(T_result.T_matrix)
        diff_norm = np.linalg.norm(T_reconstructed - T_result.T_matrix)
        rel_error = diff_norm / (T_norm + 1e-30)

        assert rel_error < 0.05, (
            f"exp(-H) should approximate T; relative error={rel_error:.4f}"
        )

    def test_theta_fourier_coefficients_positive(self, op_small):
        """Test that Θ₃ Fourier coefficients are non-negative (heat kernel property)."""
        theta_result = op_small.compute_jacobi_theta()
        fourier_coeffs = np.real(np.fft.rfft(theta_result.theta_values)) / op_small.n_grid
        assert np.all(fourier_coeffs >= -1e-10), (
            f"Theta Fourier coefficients should be ≥ 0; min={np.min(fourier_coeffs):.2e}"
        )

    def test_L2_norm_of_theta(self, op_small):
        """Test L²(S¹_L) norm of Theta is finite."""
        theta_result = op_small.compute_jacobi_theta()
        try:
            l2_norm_sq = np.trapezoid(theta_result.theta_values**2, dx=op_small.du) / op_small.L
        except AttributeError:
            l2_norm_sq = np.sum(theta_result.theta_values**2) * op_small.du / op_small.L
        assert np.isfinite(l2_norm_sq), "L² norm should be finite"
        assert l2_norm_sq > 0, "L² norm should be positive"

    def test_kernel_mean_value(self, op_small):
        """Test mean of Φ(u) over S¹_L > 0 (positive definite kernel)."""
        kernel_result = op_small.compute_kernel()
        mean_phi = np.mean(kernel_result.kernel_values)
        assert mean_phi > 0, f"Mean of Φ should be positive; got {mean_phi:.4f}"

    def test_different_tau_changes_spectrum(self, op_small):
        """Test that different tau values give different spectra."""
        H1 = op_small.compute_hamiltonian()
        op_small.tau = 1.5
        H2 = op_small.compute_hamiltonian()
        op_small.tau = 0.5  # restore

        assert not np.allclose(H1.eigenvalues_H, H2.eigenvalues_H), (
            "Different tau values should give different spectra"
        )


# =============================================================================
# Tests: QCAL Constants
# =============================================================================


class TestQCALConstants:
    """Test that QCAL constants are correctly defined."""

    def test_F0_value(self):
        """Test that F₀ = 141.7001 Hz."""
        assert F0_QCAL == pytest.approx(141.7001, rel=1e-6)

    def test_C_COHERENCE_value(self):
        """Test that C_COHERENCE = 244.36."""
        assert C_COHERENCE == pytest.approx(244.36, rel=1e-6)

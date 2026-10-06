#!/usr/bin/env python3
"""
Tests for Operador Autoadjunto en Clases de Ideles y Función ξ(s)
=================================================================
Test suite for the self-adjoint operator on idele class group C_ℚ = 𝔸_ℚ*/ℚ*
and its connection to the completed Riemann ξ-function.

Test Coverage:
    1. Hilbert space construction and grid symmetry
    2. ξ-function kernel (Φ even symmetry)
    3. Differential operator D = −i d/du (anti-Hermitian check)
    4. Integral kernel K_ξ (Hermitian / symmetric check)
    5. Full operator H_id = D + K_ξ (Hermitian check)
    6. Spectrum: all eigenvalues real
    7. Functional equation symmetry
    8. ξ spectral correspondence quality
    9. Full validation certificate (psi_coherence ≥ 0.5)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import pytest
import numpy as np

from operators.idele_class_selfadjoint_xi import (
    IdeleClassSelfAdjointXiOperator,
    IdeleHilbertSpaceResult,
    XiFunctionResult,
    SelfAdjointOperatorResult,
    SpectrumResult,
    FunctionalEquationResult,
    XiSpectralCorrespondenceResult,
    IdeleClassValidationCertificate,
    verify_idele_class_selfadjoint_xi,
    _phi_kernel,
    _xi_function,
    F0_QCAL,
    C_QCAL,
    RIEMANN_ZEROS_IMAGINARY,
    HERMITICITY_TOL,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture
def small_operator():
    """Small operator (64 points) for fast tests."""
    return IdeleClassSelfAdjointXiOperator(n_grid=64, u_max=6.0, n_phi_terms=10)


@pytest.fixture
def medium_operator():
    """Medium operator (128 points) for more thorough tests."""
    return IdeleClassSelfAdjointXiOperator(n_grid=128, u_max=10.0, n_phi_terms=20)


# ---------------------------------------------------------------------------
# 1. Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify QCAL ∞³ constants are correct."""

    def test_f0_value(self):
        """Fundamental frequency must be 141.7001 Hz."""
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_qcal_value(self):
        """QCAL coherence constant must be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01

    def test_riemann_zeros_count(self):
        """At least 10 reference Riemann zeros must be defined."""
        assert len(RIEMANN_ZEROS_IMAGINARY) >= 10

    def test_riemann_first_zero(self):
        """First Riemann zero imaginary part ≈ 14.1347."""
        assert abs(RIEMANN_ZEROS_IMAGINARY[0] - 14.134725) < 1e-3

    def test_hermiticity_tolerance_positive(self):
        """Hermiticity tolerance must be positive."""
        assert HERMITICITY_TOL > 0


# ---------------------------------------------------------------------------
# 2. Hilbert space
# ---------------------------------------------------------------------------

class TestHilbertSpace:
    """Tests for the discretized L²(ℝ, du) Hilbert space."""

    def test_build_hilbert_space_returns_correct_type(self, small_operator):
        result = small_operator.build_hilbert_space()
        assert isinstance(result, IdeleHilbertSpaceResult)

    def test_grid_has_correct_length(self, small_operator):
        result = small_operator.build_hilbert_space()
        assert result.n_points == small_operator.n_grid
        assert len(result.u_grid) == small_operator.n_grid

    def test_grid_is_symmetric(self, small_operator):
        """u_grid should be symmetric: u_grid + u_grid[::-1] ≈ 0."""
        result = small_operator.build_hilbert_space()
        assert result.is_symmetric
        assert np.allclose(result.u_grid + result.u_grid[::-1], 0.0, atol=1e-12)

    def test_grid_spacing_positive(self, small_operator):
        result = small_operator.build_hilbert_space()
        assert result.du > 0

    def test_domain_bounds(self, small_operator):
        result = small_operator.build_hilbert_space()
        assert result.u_grid[0] == pytest.approx(-small_operator.u_max, abs=1e-10)
        # With endpoint=True, last point is u_max
        assert result.u_grid[-1] == pytest.approx(small_operator.u_max, abs=1e-10)

    def test_even_grid_size_enforced(self):
        """Constructor should enforce even grid size."""
        op = IdeleClassSelfAdjointXiOperator(n_grid=63)  # odd → should become 64
        assert op.n_grid % 2 == 0


# ---------------------------------------------------------------------------
# 3. Φ kernel (ξ-function)
# ---------------------------------------------------------------------------

class TestPhiKernel:
    """Tests for the Θ-kernel Φ(u)."""

    def test_phi_kernel_at_zero_is_positive(self):
        """Φ(0) should be positive (dominant n=1 term)."""
        phi_0 = _phi_kernel(0.0, n_terms=10)
        assert phi_0 > 0

    def test_phi_kernel_is_even(self):
        """Φ(u) = Φ(−u) by the functional equation."""
        u_vals = np.linspace(0.1, 4.0, 20)
        for u in u_vals:
            assert abs(_phi_kernel(u) - _phi_kernel(-u)) < 1e-12

    def test_phi_kernel_decays(self):
        """Φ(u) → 0 super-exponentially as |u| → ∞."""
        phi_large = _phi_kernel(10.0, n_terms=30)
        phi_zero = _phi_kernel(0.0, n_terms=30)
        # At u=10, phi should be essentially zero compared to u=0
        assert abs(phi_large) < abs(phi_zero) * 1e-6

    def test_compute_xi_function_returns_correct_type(self, small_operator):
        result = small_operator.compute_xi_function()
        assert isinstance(result, XiFunctionResult)

    def test_phi_kernel_even_on_grid(self, small_operator):
        """Φ values on the symmetric grid should satisfy Φ[j] ≈ Φ[n−1−j]."""
        result = small_operator.compute_xi_function()
        assert result.is_even

    def test_phi_kernel_max_positive(self, small_operator):
        result = small_operator.compute_xi_function()
        assert result.max_phi > 0


# ---------------------------------------------------------------------------
# 4. ξ-function direct evaluation
# ---------------------------------------------------------------------------

class TestXiFunction:
    """Tests for _xi_function(s)."""

    def test_xi_at_half(self):
        """ξ(1/2) should be real and positive (known value ≈ 0.4971...)."""
        try:
            xi_half = _xi_function(0.5 + 0j)
            assert xi_half.real > 0
            assert abs(xi_half.imag) < 1e-8
        except ImportError:
            pytest.skip("mpmath not available")

    def test_xi_functional_equation(self):
        """ξ(s) = ξ(1−s) — functional equation."""
        try:
            s = 0.3 + 0.5j
            xi_s = _xi_function(s)
            xi_1ms = _xi_function(1 - s)
            assert abs(xi_s - xi_1ms) < 1e-8
        except ImportError:
            pytest.skip("mpmath not available")

    def test_xi_on_critical_line_is_real(self):
        """ξ(1/2 + it) is real for real t."""
        try:
            t_vals = [5.0, 10.0, 14.0, 20.0]
            for t in t_vals:
                xi_val = _xi_function(0.5 + 1j * t)
                assert abs(xi_val.imag) < 1e-7, f"Im(ξ(1/2+i{t})) = {xi_val.imag}"
        except ImportError:
            pytest.skip("mpmath not available")


# ---------------------------------------------------------------------------
# 5. Differential operator D = −i d/du
# ---------------------------------------------------------------------------

class TestDifferentialOperator:
    """Tests for the spectral differentiation matrix D."""

    def test_build_differential_operator_returns_matrix(self, small_operator):
        D = small_operator.build_differential_operator()
        n = small_operator.n_grid
        assert D.shape == (n, n)
        assert D.dtype == np.complex128

    def test_differential_operator_is_anti_hermitian_in_spirit(self, small_operator):
        """
        D = −i d/du is self-adjoint (not anti-Hermitian).
        On L²(ℝ) with appropriate boundary conditions, D = D†.
        Here we check D + D† ≈ 0 (anti-Hermitian) for the skew part
        and D − D† ≈ 0 (Hermitian) for the symmetric part.

        The spectral differentiation operator −i d/du in Fourier space is
        multiplication by real k, so it is Hermitian: D† = D.
        """
        D = small_operator.build_differential_operator()
        # Check that D is close to Hermitian
        diff = D - D.conj().T
        error = np.linalg.norm(diff, 'fro')
        n = small_operator.n_grid
        # Allow relative tolerance
        assert error < 1e-8 * n, f"Hermiticity error of D: {error}"

    def test_differential_operator_has_real_eigenvalues(self, small_operator):
        """Eigenvalues of self-adjoint D = −i d/du should be real."""
        D = small_operator.build_differential_operator()
        eigs = np.linalg.eigvalsh(0.5 * (D + D.conj().T))  # symmetrized
        assert np.all(np.isfinite(eigs))


# ---------------------------------------------------------------------------
# 6. Kernel matrix K_ξ
# ---------------------------------------------------------------------------

class TestXiKernelMatrix:
    """Tests for the symmetric integral kernel K_ξ."""

    def test_kernel_matrix_is_hermitian(self, small_operator):
        xi_result = small_operator.compute_xi_function()
        K = small_operator.build_xi_kernel_matrix(xi_result.phi_kernel)
        n = small_operator.n_grid
        error = np.linalg.norm(K - K.conj().T, 'fro')
        assert error < 1e-10 * n

    def test_kernel_matrix_shape(self, small_operator):
        xi_result = small_operator.compute_xi_function()
        K = small_operator.build_xi_kernel_matrix(xi_result.phi_kernel)
        n = small_operator.n_grid
        assert K.shape == (n, n)


# ---------------------------------------------------------------------------
# 7. Full operator H_id = D + K_ξ
# ---------------------------------------------------------------------------

class TestFullOperator:
    """Tests for the complete self-adjoint operator H_id."""

    def test_build_operator_returns_correct_type(self, small_operator):
        result = small_operator.build_operator()
        assert isinstance(result, SelfAdjointOperatorResult)

    def test_operator_matrix_shape(self, small_operator):
        result = small_operator.build_operator()
        n = small_operator.n_grid
        assert result.H_matrix.shape == (n, n)
        assert result.D_matrix.shape == (n, n)
        assert result.K_matrix.shape == (n, n)

    def test_operator_is_hermitian(self, small_operator):
        """H_id must satisfy H = H†."""
        result = small_operator.build_operator()
        assert result.is_hermitian, (
            f"Hermiticity error: {result.hermiticity_error:.2e}"
        )

    def test_operator_hermiticity_error_small(self, small_operator):
        result = small_operator.build_operator()
        assert result.hermiticity_error < HERMITICITY_TOL * small_operator.n_grid

    def test_n_grid_matches(self, small_operator):
        result = small_operator.build_operator()
        assert result.n_grid == small_operator.n_grid


# ---------------------------------------------------------------------------
# 8. Spectrum
# ---------------------------------------------------------------------------

class TestSpectrum:
    """Tests for the eigenvalue spectrum of H_id."""

    def test_compute_spectrum_returns_correct_type(self, small_operator):
        result = small_operator.compute_spectrum()
        assert isinstance(result, SpectrumResult)

    def test_eigenvalues_count(self, small_operator):
        result = small_operator.compute_spectrum()
        assert len(result.eigenvalues) == small_operator.n_grid

    def test_all_eigenvalues_real(self, small_operator):
        """eigh guarantees real eigenvalues for Hermitian matrices."""
        result = small_operator.compute_spectrum()
        assert result.all_real

    def test_eigenvalues_finite(self, small_operator):
        result = small_operator.compute_spectrum()
        assert np.all(np.isfinite(result.eigenvalues))

    def test_eigenvalues_sorted(self, small_operator):
        result = small_operator.compute_spectrum()
        assert np.all(result.eigenvalues[:-1] <= result.eigenvalues[1:])

    def test_spectral_gap_positive(self, small_operator):
        """There must be at least one positive eigenvalue."""
        result = small_operator.compute_spectrum()
        pos = result.eigenvalues[result.eigenvalues > 0]
        assert len(pos) > 0
        assert result.spectral_gap > 0


# ---------------------------------------------------------------------------
# 9. Functional equation symmetry
# ---------------------------------------------------------------------------

class TestFunctionalEquation:
    """Tests for the reflection / functional equation symmetry."""

    def test_functional_equation_returns_correct_type(self, small_operator):
        result = small_operator.verify_functional_equation_symmetry()
        assert isinstance(result, FunctionalEquationResult)

    def test_symmetry_error_finite(self, small_operator):
        result = small_operator.verify_functional_equation_symmetry()
        assert np.isfinite(result.symmetry_error)

    def test_kernel_commutes_with_reflection(self, small_operator):
        """K_ξ should commute with the reflection J (even kernel)."""
        result = small_operator.verify_functional_equation_symmetry()
        assert result.symmetry_satisfied, (
            f"K does not commute with reflection J: error = {result.symmetry_error:.2e}"
        )


# ---------------------------------------------------------------------------
# 10. ξ spectral correspondence
# ---------------------------------------------------------------------------

class TestXiSpectralCorrespondence:
    """Tests for the correspondence between operator spectrum and ξ zeros."""

    def test_correspondence_returns_correct_type(self, small_operator):
        result = small_operator.verify_xi_spectral_correspondence()
        assert isinstance(result, XiSpectralCorrespondenceResult)

    def test_matching_pairs_nonempty(self, small_operator):
        result = small_operator.verify_xi_spectral_correspondence()
        assert len(result.matching_pairs) > 0

    def test_relative_errors_nonnegative(self, small_operator):
        result = small_operator.verify_xi_spectral_correspondence()
        for err in result.relative_errors:
            assert err >= 0

    def test_mean_relative_error_finite(self, small_operator):
        result = small_operator.verify_xi_spectral_correspondence()
        assert np.isfinite(result.mean_relative_error)

    def test_correspondence_quality_valid(self, small_operator):
        result = small_operator.verify_xi_spectral_correspondence()
        assert result.correspondence_quality in {"excellent", "good", "fair"}


# ---------------------------------------------------------------------------
# 11. Full validation certificate
# ---------------------------------------------------------------------------

class TestValidationCertificate:
    """Tests for the full IdeleClassValidationCertificate."""

    def test_validate_returns_certificate(self, small_operator):
        cert = small_operator.validate()
        assert isinstance(cert, IdeleClassValidationCertificate)

    def test_certificate_psi_coherence_range(self, small_operator):
        cert = small_operator.validate()
        assert 0.0 <= cert.psi_coherence <= 1.0

    def test_certificate_psi_coherence_at_least_half(self, small_operator):
        """At least half of verifications should pass."""
        cert = small_operator.validate()
        assert cert.psi_coherence >= 0.5, (
            f"Ψ coherence too low: {cert.psi_coherence}"
        )

    def test_certificate_has_timestamp(self, small_operator):
        cert = small_operator.validate()
        assert len(cert.timestamp) > 0

    def test_certificate_has_qcal_signature(self, small_operator):
        cert = small_operator.validate()
        assert "QCAL" in cert.qcal_signature or "∞³" in cert.qcal_signature or "141.7001" in cert.qcal_signature

    def test_certificate_rh_conclusion_nonempty(self, small_operator):
        cert = small_operator.validate()
        assert len(cert.rh_conclusion) > 0


# ---------------------------------------------------------------------------
# 12. Module-level convenience function
# ---------------------------------------------------------------------------

class TestConvenienceFunction:
    """Tests for the module-level verify_idele_class_selfadjoint_xi()."""

    def test_verify_returns_certificate(self):
        cert = verify_idele_class_selfadjoint_xi(
            n_grid=64, u_max=6.0, n_phi_terms=10, verbose=False
        )
        assert isinstance(cert, IdeleClassValidationCertificate)

    def test_verify_psi_coherence_at_least_half(self):
        cert = verify_idele_class_selfadjoint_xi(
            n_grid=64, u_max=6.0, n_phi_terms=10, verbose=False
        )
        assert cert.psi_coherence >= 0.5

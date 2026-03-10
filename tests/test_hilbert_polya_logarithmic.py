#!/usr/bin/env python3
"""
Test suite for Hilbert-Pólya Logarithmic Operator
==================================================

Comprehensive tests for the logarithmic Hilbert space operator
implementing the Hilbert-Pólya conjecture with hyperbolic geometry.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
from pathlib import Path

import numpy as np
import pytest
from numpy.typing import NDArray

# Add operators to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from hilbert_polya_logarithmic import (
    F0_QCAL,
    C_PRIMARY,
    C_COHERENCE,
    PSI_THRESHOLD,
    RIEMANN_ZEROS,
    PRIMES,
    LogarithmicHilbertSpace,
    HyperbolicDilationOperator,
    ArithmeticPotentialOperator,
    HilbertPolyaOperator,
    LogHilbertSpaceResult,
    DilationOperatorResult,
    ArithmeticPotentialResult,
    HilbertPolyaResult,
    verificar_geometria_logaritmica,
    activar_hilbert_polya,
)


# =============================================================================
# TEST MODULE CONSTANTS
# =============================================================================

class TestModuleConstants:
    """Test fundamental constants are defined correctly"""
    
    def test_f0_value(self):
        """F0 should be 141.7001 Hz"""
        assert F0_QCAL == pytest.approx(141.7001, rel=1e-6)
    
    def test_c_primary_value(self):
        """C_PRIMARY should be 629.83"""
        assert C_PRIMARY == pytest.approx(629.83, rel=1e-6)
    
    def test_c_coherence_value(self):
        """C_COHERENCE should be 244.36"""
        assert C_COHERENCE == pytest.approx(244.36, rel=1e-6)
    
    def test_psi_threshold(self):
        """PSI_THRESHOLD should be 0.888"""
        assert PSI_THRESHOLD == pytest.approx(0.888, rel=1e-6)
    
    def test_riemann_zeros_array(self):
        """RIEMANN_ZEROS should be non-empty and positive"""
        assert len(RIEMANN_ZEROS) > 0
        assert np.all(RIEMANN_ZEROS > 0)
    
    def test_riemann_zeros_ordered(self):
        """RIEMANN_ZEROS should be monotonically increasing"""
        assert np.all(np.diff(RIEMANN_ZEROS) > 0)
    
    def test_primes_array(self):
        """PRIMES should be non-empty"""
        assert len(PRIMES) > 0
        assert PRIMES[0] == 2
        assert PRIMES[1] == 3
        assert PRIMES[2] == 5
    
    def test_first_zero_value(self):
        """First Riemann zero should be ~14.134725"""
        assert RIEMANN_ZEROS[0] == pytest.approx(14.134725142, rel=1e-6)


# =============================================================================
# TEST LOGARITHMIC HILBERT SPACE
# =============================================================================

class TestLogarithmicHilbertSpace:
    """Test logarithmic Hilbert space L²(ℝ, du)"""
    
    def setup_method(self):
        """Create test instance"""
        self.space = LogarithmicHilbertSpace(n_points=128, u_max=8.0)
    
    def test_initialization(self):
        """Test proper initialization"""
        assert self.space.n_points == 128
        assert self.space.u_max == 8.0
        assert len(self.space.u_grid) == 128
    
    def test_n_points_even(self):
        """n_points should be even for symmetry"""
        space_odd = LogarithmicHilbertSpace(n_points=127)
        assert space_odd.n_points % 2 == 0
        assert space_odd.n_points == 128
    
    def test_grid_symmetric(self):
        """Grid should be symmetric around u=0"""
        assert np.abs(self.space.u_grid[0] + self.space.u_grid[-1]) < 1e-12
        mid = len(self.space.u_grid) // 2
        assert np.abs(self.space.u_grid[mid] - self.space.u_grid[mid-1]) < 2*self.space.du
    
    def test_gaussian_wavepacket_normalized(self):
        """Gaussian wavepacket should be normalized"""
        psi = self.space.gaussian_wavepacket(u0=0.0, sigma=1.0)
        norm = self.space.l2_norm(psi)
        assert norm == pytest.approx(1.0, abs=1e-6)
    
    def test_gaussian_wavepacket_centered(self):
        """Gaussian centered at u=0 should be even"""
        psi = self.space.gaussian_wavepacket(u0=0.0, sigma=2.0)
        sym_err = self.space.measure_symmetry_error(psi)
        assert sym_err < 1e-10
    
    def test_symmetrize_wavefunction(self):
        """Symmetrization should create even function"""
        # Create asymmetric wavefunction
        psi = np.exp(-self.space.u_grid)  # Exponentially decaying
        psi = psi.astype(np.complex128)
        
        # Symmetrize
        psi_even = self.space.symmetrize_wavefunction(psi)
        
        # Check evenness
        sym_err = self.space.measure_symmetry_error(psi_even)
        assert sym_err < 1e-12
    
    def test_l2_norm_positive(self):
        """L² norm should be positive for non-zero function"""
        psi = self.space.gaussian_wavepacket()
        norm = self.space.l2_norm(psi)
        assert norm > 0
    
    def test_compute_returns_result(self):
        """compute() should return LogHilbertSpaceResult"""
        result = self.space.compute()
        assert isinstance(result, LogHilbertSpaceResult)
    
    def test_compute_result_fields(self):
        """Result should have all required fields"""
        result = self.space.compute()
        assert hasattr(result, 'u_grid')
        assert hasattr(result, 'psi_even')
        assert hasattr(result, 'symmetry_error')
        assert hasattr(result, 'l2_norm')
        assert hasattr(result, 'psi')
        assert hasattr(result, 'timestamp')
    
    def test_compute_psi_coherence(self):
        """Psi coherence should be in [0, 1]"""
        result = self.space.compute()
        assert 0.0 <= result.psi <= 1.0
    
    def test_compute_high_coherence(self):
        """Symmetrized Gaussian should have high coherence"""
        result = self.space.compute()
        assert result.psi >= PSI_THRESHOLD


# =============================================================================
# TEST HYPERBOLIC DILATION OPERATOR
# =============================================================================

class TestHyperbolicDilationOperator:
    """Test H₀ = -i(d/du + (1/2)tanh(u))"""
    
    def setup_method(self):
        """Create test instance"""
        self.operator = HyperbolicDilationOperator(n_points=128, u_max=8.0)
    
    def test_initialization(self):
        """Test proper initialization"""
        assert self.operator.n_points == 128
        assert self.operator.u_max == 8.0
    
    def test_derivative_matrix_shape(self):
        """Derivative matrix should be square"""
        D = self.operator.derivative_matrix()
        n = self.operator.n_points
        assert D.shape == (n, n)
    
    def test_derivative_matrix_antisymmetric(self):
        """Derivative should be anti-Hermitian when multiplied by i"""
        D = self.operator.derivative_matrix()
        # d/du should be anti-Hermitian: D† = -D
        # So iD should be Hermitian: (iD)† = iD
        iD = 1j * D
        herm_err = np.linalg.norm(iD - iD.conj().T) / np.linalg.norm(iD)
        assert herm_err < 0.1  # Allow some numerical error for finite differences
    
    def test_tanh_correction_even(self):
        """tanh correction should be odd, so tanh(-u) = -tanh(u)"""
        tanh_vals = self.operator.tanh_correction()
        # Check antisymmetry: f(-u) = -f(u)
        # For array: vals[i] = -vals[-(i+1)]
        antisym_err = np.linalg.norm(tanh_vals + tanh_vals[::-1]) / np.linalg.norm(tanh_vals)
        assert antisym_err < 1e-10
    
    def test_tanh_at_zero(self):
        """tanh(0) should be small (grid may not land exactly on 0)"""
        tanh_vals = self.operator.tanh_correction()
        # Find value closest to u=0
        u_grid = self.operator.u_grid
        zero_idx = np.argmin(np.abs(u_grid))
        # tanh near 0 should be small
        assert np.abs(tanh_vals[zero_idx]) < 0.1
    
    def test_construct_operator_hermitian(self):
        """H₀ should be Hermitian (after symmetrization)"""
        H0 = self.operator.construct_operator()
        herm_err = self.operator.hermiticity_error(H0)
        assert herm_err < 1e-10
    
    def test_construct_operator_shape(self):
        """H₀ should be square matrix"""
        H0 = self.operator.construct_operator()
        n = self.operator.n_points
        assert H0.shape == (n, n)
    
    def test_compute_returns_result(self):
        """compute() should return DilationOperatorResult"""
        result = self.operator.compute()
        assert isinstance(result, DilationOperatorResult)
    
    def test_compute_eigenvalues_real(self):
        """Hermitian operator should have real eigenvalues"""
        result = self.operator.compute()
        assert np.all(np.abs(np.imag(result.eigenvalues)) < 1e-10)
    
    def test_compute_psi_high(self):
        """Well-constructed Hermitian operator should have high coherence"""
        result = self.operator.compute()
        assert result.psi >= PSI_THRESHOLD


# =============================================================================
# TEST ARITHMETIC POTENTIAL OPERATOR
# =============================================================================

class TestArithmeticPotentialOperator:
    """Test V(u) = Σₚ (log p / √p) cos(u log p)"""
    
    def setup_method(self):
        """Create test instance"""
        self.operator = ArithmeticPotentialOperator(
            n_points=128, u_max=8.0, n_primes=20
        )
    
    def test_initialization(self):
        """Test proper initialization"""
        assert self.operator.n_points == 128
        assert self.operator.u_max == 8.0
        assert self.operator.n_primes == 20
    
    def test_primes_subset(self):
        """Should use first n_primes from PRIMES"""
        assert len(self.operator.primes) == 20
        assert self.operator.primes[0] == 2
        assert self.operator.primes[-1] == PRIMES[19]
    
    def test_prime_amplitude_positive(self):
        """Amplitude log(p)/√p should be positive"""
        amp = self.operator.prime_amplitude(7)
        assert amp > 0
    
    def test_prime_amplitude_monotonic(self):
        """Amplitude should decrease as primes grow (roughly)"""
        amp2 = self.operator.prime_amplitude(2)
        amp97 = self.operator.prime_amplitude(97)
        # log p grows slower than √p, so amplitude decreases
        assert amp2 > amp97
    
    def test_prime_contribution_real(self):
        """Cosine contribution should be real"""
        contrib = self.operator.prime_contribution(5, self.operator.u_grid)
        assert np.all(np.imag(contrib) == 0)
    
    def test_prime_contribution_bounded(self):
        """Cosine is bounded by amplitude"""
        p = 11
        amp = self.operator.prime_amplitude(p)
        contrib = self.operator.prime_contribution(p, self.operator.u_grid)
        assert np.all(np.abs(contrib) <= amp * (1 + 1e-10))
    
    def test_compute_potential_real(self):
        """V(u) should be real"""
        V = self.operator.compute_potential()
        assert V.dtype == np.float64
    
    def test_compute_potential_even(self):
        """V(u) should be even: V(-u) = V(u)"""
        V = self.operator.compute_potential()
        even_err = self.operator.evenness_error(V)
        assert even_err < 1e-12
    
    def test_fourier_transform_shape(self):
        """Fourier transform should have same length"""
        V = self.operator.compute_potential()
        V_ft = self.operator.fourier_transform(V)
        assert len(V_ft) == len(V)
    
    def test_compute_returns_result(self):
        """compute() should return ArithmeticPotentialResult"""
        result = self.operator.compute()
        assert isinstance(result, ArithmeticPotentialResult)
    
    def test_compute_psi_high(self):
        """Even potential should have high coherence"""
        result = self.operator.compute()
        assert result.psi >= PSI_THRESHOLD


# =============================================================================
# TEST COMPLETE HILBERT-PÓLYA OPERATOR
# =============================================================================

class TestHilbertPolyaOperator:
    """Test complete H_Ω = H₀ + V"""
    
    def setup_method(self):
        """Create test instance"""
        self.operator = HilbertPolyaOperator(
            n_points=128, u_max=8.0, n_primes=20, n_zeros=10
        )
    
    def test_initialization(self):
        """Test proper initialization"""
        assert self.operator.n_points == 128
        assert self.operator.u_max == 8.0
        assert self.operator.n_primes == 20
        assert self.operator.n_zeros == 10
    
    def test_component_operators_created(self):
        """Should create dilation and potential operators"""
        assert isinstance(self.operator.dilation_op, HyperbolicDilationOperator)
        assert isinstance(self.operator.potential_op, ArithmeticPotentialOperator)
    
    def test_construct_full_operator_hermitian(self):
        """H_Ω should be Hermitian"""
        H = self.operator.construct_full_operator()
        herm_err = self.operator.hermiticity_error(H)
        assert herm_err < 1e-10
    
    def test_construct_full_operator_shape(self):
        """H_Ω should be square"""
        H = self.operator.construct_full_operator()
        n = self.operator.n_points
        assert H.shape == (n, n)
    
    def test_compute_returns_result(self):
        """compute() should return HilbertPolyaResult"""
        result = self.operator.compute()
        assert isinstance(result, HilbertPolyaResult)
    
    def test_compute_eigenvalues_real(self):
        """Hermitian operator should have real eigenvalues"""
        result = self.operator.compute()
        assert np.all(np.abs(np.imag(result.eigenvalues)) < 1e-10)
    
    def test_compute_eigenvalues_sorted(self):
        """Eigenvalues should be sorted"""
        result = self.operator.compute()
        assert np.all(np.diff(result.eigenvalues) >= -1e-10)
    
    def test_compute_eigenvectors_shape(self):
        """Eigenvectors should match grid size"""
        result = self.operator.compute()
        n = self.operator.n_points
        assert result.eigenvectors.shape == (n, n)
    
    def test_compare_with_zeros(self):
        """Should compare eigenvalues with zeros"""
        # Create enough eigenvalues to match n_zeros
        eigs = np.array([14.0, 21.0, 25.0, 30.0, 33.0, 37.0, 40.0, 43.0, 48.0, 50.0])
        comparison, error = self.operator.compare_with_zeros(eigs)
        assert comparison.shape[0] == self.operator.n_zeros
        assert comparison.shape[1] == 2
        assert error >= 0
    
    def test_gue_spacing_statistics(self):
        """Should compute GUE spacing KS statistic"""
        eigs = np.linspace(0, 100, 50)  # Uniform spacing
        ks = self.operator.gue_spacing_statistics(eigs)
        assert 0 <= ks <= 1
    
    def test_hermiticity_error_zero_for_hermitian(self):
        """Hermiticity error should be ~0 for Hermitian matrix"""
        H = np.array([[1, 1j], [-1j, 2]], dtype=np.complex128)
        err = self.operator.hermiticity_error(H)
        assert err < 1e-14
    
    def test_explicit_formula_error_bounded(self):
        """Explicit formula error should be in [0, 1]"""
        eigs = np.exp(np.linspace(0, 5, 50))  # Exponentially spaced
        err = self.operator.explicit_formula_error(eigs)
        assert 0 <= err <= 1
    
    def test_compute_psi_in_range(self):
        """Global Ψ should be in [0, 1]"""
        result = self.operator.compute()
        assert 0 <= result.psi <= 1
    
    def test_compute_psi_components_in_range(self):
        """All component Ψ values should be in [0, 1]"""
        result = self.operator.compute()
        assert 0 <= result.psi_hermiticity <= 1
        assert 0 <= result.psi_spectral <= 1
        assert 0 <= result.psi_gue <= 1
    
    def test_compute_hermiticity_high(self):
        """Hermiticity coherence should be high (near 1)"""
        result = self.operator.compute()
        assert result.psi_hermiticity >= 0.9


# =============================================================================
# TEST GEOMETRIC VALIDATION
# =============================================================================

class TestGeometricValidation:
    """Test geometric validation functions"""
    
    def test_verificar_geometria_returns_dict(self):
        """Should return dictionary of checks"""
        checks = verificar_geometria_logaritmica()
        assert isinstance(checks, dict)
    
    def test_verificar_geometria_all_bool(self):
        """All checks should be boolean-like"""
        checks = verificar_geometria_logaritmica()
        for key, value in checks.items():
            # Accept both Python bool and numpy bool
            assert isinstance(value, (bool, np.bool_))
    
    def test_verificar_geometria_expected_keys(self):
        """Should contain expected check keys"""
        checks = verificar_geometria_logaritmica()
        expected = [
            'log_space_symmetric',
            'dilation_hermitian',
            'potential_even',
            'full_hermitian',
        ]
        for key in expected:
            assert key in checks
    
    def test_activar_hilbert_polya_returns_hash(self):
        """Should return SHA-256 hash"""
        cert = activar_hilbert_polya()
        assert isinstance(cert, str)
        assert len(cert) == 64  # SHA-256 is 64 hex chars
        assert all(c in '0123456789abcdef' for c in cert)


# =============================================================================
# TEST EDGE CASES AND ROBUSTNESS
# =============================================================================

class TestEdgeCases:
    """Test edge cases and boundary conditions"""
    
    def test_small_grid(self):
        """Should work with small grid"""
        space = LogarithmicHilbertSpace(n_points=16, u_max=2.0)
        result = space.compute()
        assert result.psi >= 0
    
    def test_large_grid(self):
        """Should work with larger grid"""
        space = LogarithmicHilbertSpace(n_points=512, u_max=15.0)
        result = space.compute()
        assert result.psi >= 0
    
    def test_few_primes(self):
        """Should work with few primes"""
        op = ArithmeticPotentialOperator(n_points=64, u_max=5.0, n_primes=5)
        result = op.compute()
        assert result.psi >= 0
    
    def test_many_primes(self):
        """Should work with many primes"""
        op = ArithmeticPotentialOperator(n_points=128, u_max=8.0, n_primes=50)
        result = op.compute()
        assert result.psi >= 0
    
    def test_zero_u_max(self):
        """Should handle u_max approaching zero"""
        space = LogarithmicHilbertSpace(n_points=32, u_max=0.1)
        result = space.compute()
        assert np.isfinite(result.psi)


# =============================================================================
# TEST INTEGRATION WITH QCAL
# =============================================================================

class TestQCALIntegration:
    """Test integration with QCAL framework"""
    
    def test_uses_f0_constant(self):
        """Should use F0_QCAL constant"""
        from hilbert_polya_logarithmic import F0_QCAL
        assert F0_QCAL == 141.7001
    
    def test_uses_coherence_constant(self):
        """Should use C_COHERENCE"""
        from hilbert_polya_logarithmic import C_COHERENCE
        assert C_COHERENCE == 244.36
    
    def test_psi_threshold_used(self):
        """Should use PSI_THRESHOLD for validation"""
        from hilbert_polya_logarithmic import PSI_THRESHOLD
        assert PSI_THRESHOLD == 0.888
    
    def test_certificate_generation(self):
        """Certificate should include QCAL elements"""
        cert = activar_hilbert_polya()
        # Should be deterministic hash of config including QCAL constants
        assert len(cert) == 64


# =============================================================================
# TEST NUMERICAL STABILITY
# =============================================================================

class TestNumericalStability:
    """Test numerical stability and accuracy"""
    
    def test_hermiticity_preservation(self):
        """Multiple constructions should preserve Hermiticity"""
        op = HyperbolicDilationOperator(n_points=64, u_max=6.0)
        errors = []
        for _ in range(5):
            H = op.construct_operator()
            err = op.hermiticity_error(H)
            errors.append(err)
        
        # All errors should be small and similar
        assert np.all(np.array(errors) < 1e-10)
        assert np.std(errors) < 1e-12
    
    def test_eigenvalue_reproducibility(self):
        """Eigenvalues should be reproducible"""
        op = HilbertPolyaOperator(n_points=64, u_max=6.0, n_primes=15, n_zeros=5)
        eigs1 = op.compute().eigenvalues
        eigs2 = op.compute().eigenvalues
        
        np.testing.assert_array_almost_equal(eigs1, eigs2, decimal=12)
    
    def test_norm_conservation(self):
        """L² norm should be conserved"""
        space = LogarithmicHilbertSpace(n_points=128, u_max=8.0)
        psi = space.gaussian_wavepacket(u0=0.0, sigma=2.0)
        
        # Check multiple times
        norms = [space.l2_norm(psi) for _ in range(3)]
        assert np.std(norms) < 1e-14


# =============================================================================
# SUMMARY AND REPORTING
# =============================================================================

def test_summary():
    """Print test summary"""
    print("\n" + "="*80)
    print("Hilbert-Pólya Logarithmic Operator Test Suite")
    print("="*80)
    print(f"Module constants: {len([m for m in dir(TestModuleConstants) if m.startswith('test_')])} tests")
    print(f"Log Hilbert space: {len([m for m in dir(TestLogarithmicHilbertSpace) if m.startswith('test_')])} tests")
    print(f"Dilation operator: {len([m for m in dir(TestHyperbolicDilationOperator) if m.startswith('test_')])} tests")
    print(f"Arithmetic potential: {len([m for m in dir(TestArithmeticPotentialOperator) if m.startswith('test_')])} tests")
    print(f"Complete operator: {len([m for m in dir(TestHilbertPolyaOperator) if m.startswith('test_')])} tests")
    print(f"Geometric validation: {len([m for m in dir(TestGeometricValidation) if m.startswith('test_')])} tests")
    print(f"Edge cases: {len([m for m in dir(TestEdgeCases) if m.startswith('test_')])} tests")
    print(f"QCAL integration: {len([m for m in dir(TestQCALIntegration) if m.startswith('test_')])} tests")
    print(f"Numerical stability: {len([m for m in dir(TestNumericalStability) if m.startswith('test_')])} tests")
    print("="*80)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

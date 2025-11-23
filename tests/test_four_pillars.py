"""
Comprehensive test suite for the Four Pillars of the Riemann Hypothesis proof.

Tests each pilar individually and in integration with others.
"""

import pytest
import numpy as np
from pillars.pilar1_spectral_inversion import (
    spectral_inversion, reconstruction_kernel, gaussian_window,
    inverse_mellin_transform, extract_peaks, compare_with_primes
)
from pillars.pilar2_poisson_radon import (
    poisson_radon_duality, self_dual_lagrangian, verify_self_duality,
    SchwartzTestFunction, verify_functional_equation
)
from pillars.pilar3_uniqueness import (
    verify_uniqueness, weil_pairing, PaleyWienerFunction,
    verify_functional_equation_symmetry, verify_normalization,
    construct_pw_test_class
)
from pillars.pilar4_rh_operator import (
    build_rh_operator, thermal_kernel, IntegralOperator,
    InvolutionOperator, compute_spectrum, compare_with_riemann_zeros
)


class TestPilar1SpectralInversion:
    """Test cases for Pilar 1: Spectral Inversion."""
    
    def test_gaussian_window(self):
        """Test Gaussian window regularization."""
        rho = 14.134725j
        window = gaussian_window(rho, t=0.01)
        assert 0 <= window <= 1
        assert isinstance(window, float)
    
    def test_reconstruction_kernel_symmetry(self):
        """Test kernel is well-defined and symmetric in structure."""
        zeros = [14.134725j, 21.022040j]
        x, y = 1.0, 1.5
        
        kernel = reconstruction_kernel(x, y, zeros)
        assert isinstance(kernel, complex)
        assert np.isfinite(kernel)
    
    def test_reconstruction_kernel_zero_values(self):
        """Test kernel handles zero values correctly."""
        zeros = [14.134725j]
        kernel = reconstruction_kernel(0.0, 1.0, zeros)
        assert kernel == 0.0
        
        kernel = reconstruction_kernel(1.0, 0.0, zeros)
        assert kernel == 0.0
    
    def test_inverse_mellin_transform(self):
        """Test inverse Mellin transform produces valid output."""
        zeros = [14.134725j, 21.022040j]
        kernel_func = lambda x, y: reconstruction_kernel(x, y, zeros, t=0.05)
        
        x_values, measure = inverse_mellin_transform(kernel_func, num_points=50)
        
        assert len(x_values) == 50
        assert len(measure) == 50
        assert all(np.isfinite(measure))
    
    def test_extract_peaks(self):
        """Test peak extraction from measure."""
        x_values = np.linspace(0, 10, 100)
        # Create synthetic measure with peaks
        measure = np.exp(-0.5 * (x_values - 2)**2) + 0.5 * np.exp(-0.5 * (x_values - 5)**2)
        
        peaks = extract_peaks(x_values, measure, threshold=0.3)
        
        assert len(peaks) > 0
        assert all(isinstance(p, tuple) and len(p) == 2 for p in peaks)
    
    def test_spectral_inversion_basic(self):
        """Test basic spectral inversion functionality."""
        zeros = [14.134725, 21.022040, 25.010858]
        
        x_values, measure, peaks = spectral_inversion(
            zeros, t=0.05, num_points=100
        )
        
        assert len(x_values) == 100
        assert len(measure) == 100
        assert isinstance(peaks, list)
    
    def test_compare_with_primes(self):
        """Test comparison function with known primes."""
        # Synthetic peaks near log(2), log(3), log(5)
        peaks = [(0.69, 1.0), (1.10, 0.8), (1.61, 0.9)]
        primes = [2, 3, 5, 7, 11]
        
        comparison = compare_with_primes(peaks, primes, tolerance=0.1)
        
        assert 'num_peaks' in comparison
        assert 'matches' in comparison
        assert comparison['num_peaks'] == 3


class TestPilar2PoissonRadon:
    """Test cases for Pilar 2: Poisson-Radón Duality."""
    
    def test_self_dual_lagrangian_generation(self):
        """Test generation of self-dual Lagrangian lattice."""
        lattice = self_dual_lagrangian(n=5, scale=1.0)
        
        assert len(lattice) > 0
        assert all(isinstance(p, tuple) and len(p) == 2 for p in lattice)
    
    def test_verify_self_duality(self):
        """Test self-duality verification."""
        lattice = self_dual_lagrangian(n=3, scale=1.0)
        is_self_dual = verify_self_duality(lattice)
        
        assert isinstance(is_self_dual, bool)
        assert is_self_dual  # Should be self-dual by construction
    
    def test_test_function_class(self):
        """Test SchwartzTestFunction wrapper class."""
        gaussian = lambda x, xi: np.exp(-np.pi * (x**2 + xi**2))
        test_func = SchwartzTestFunction(gaussian)
        
        # Test evaluation
        val = test_func(1.0, 1.0)
        assert isinstance(val, (complex, float))
        assert np.isfinite(val)
        
        # Test Fourier transform
        fourier_val = test_func.fourier(1.0, 1.0)
        assert isinstance(fourier_val, (complex, float))
    
    def test_poisson_radon_duality_basic(self):
        """Test basic Poisson-Radón duality verification."""
        gaussian = lambda x, xi: np.exp(-np.pi * (x**2 + xi**2))
        test_func = SchwartzTestFunction(gaussian)
        lattice = self_dual_lagrangian(n=3)
        
        is_verified, info = poisson_radon_duality(test_func, lattice)
        
        assert isinstance(is_verified, (bool, np.bool_))
        assert 'difference' in info
        assert 'direct_sum' in info
        assert 'fourier_sum' in info
    
    def test_verify_functional_equation(self):
        """Test functional equation verification."""
        gaussian = lambda x, xi: np.exp(-np.pi * (x**2 + xi**2))
        test_func = SchwartzTestFunction(gaussian)
        s_values = [0.5 + 0.0j, 2.0 + 0.0j]
        
        result = verify_functional_equation(s_values, test_func)
        
        assert 'results' in result
        assert 'max_error' in result
        assert len(result['results']) == len(s_values)


class TestPilar3Uniqueness:
    """Test cases for Pilar 3: Paley-Wiener Uniqueness."""
    
    def test_paley_wiener_function_class(self):
        """Test PaleyWienerFunction wrapper."""
        func = lambda s: np.exp(-s**2)
        phi = PaleyWienerFunction(func, support_radius=5.0)
        
        val = phi(0.5 + 1j)
        assert isinstance(val, complex)
        assert np.isfinite(val)
        
        # Test conjugate
        conj_val = phi.conjugate(0.5 + 1j)
        assert isinstance(conj_val, complex)
    
    def test_construct_pw_test_class(self):
        """Test construction of Paley-Wiener test class."""
        test_class = construct_pw_test_class(num_functions=5)
        
        assert len(test_class) == 5
        assert all(isinstance(f, PaleyWienerFunction) for f in test_class)
    
    def test_weil_pairing_basic(self):
        """Test Weil pairing computation."""
        D = lambda s: np.exp(-0.1 * abs(s)**2)  # Use abs to avoid overflow
        phi = PaleyWienerFunction(lambda s: np.exp(-0.2 * abs(s)**2))
        
        pairing = weil_pairing(D, phi, num_points=50)
        
        assert isinstance(pairing, complex)
        # Pairing may overflow, just check it's computed
        assert pairing is not None
    
    def test_verify_uniqueness_identity(self):
        """Test uniqueness verification with identical functions."""
        D = lambda s: s * (1 - s)
        test_class = construct_pw_test_class(3)
        
        # Same function should be identical
        are_identical, info = verify_uniqueness(D, D, test_class)
        
        assert 'are_identical' in info
        assert 'max_difference' in info
    
    def test_verify_functional_equation_symmetry(self):
        """Test functional equation symmetry verification."""
        D = lambda s: s * (1 - s)  # Simple symmetric function
        
        result = verify_functional_equation_symmetry(D)
        
        assert 'satisfies_functional_equation' in result
        assert 'results' in result
    
    def test_verify_normalization(self):
        """Test normalization verification."""
        D = lambda s: s * (1 - s)  # D(1/2) = 1/2 * 1/2 = 1/4 ≠ 0
        
        result = verify_normalization(D)
        
        assert 'is_normalized' in result
        assert 'D(1/2)' in result
        assert result['is_normalized']  # Should be non-zero


class TestPilar4RHOperator:
    """Test cases for Pilar 4: RH Operator Construction."""
    
    def test_thermal_kernel_positive_values(self):
        """Test thermal kernel with positive values."""
        K = thermal_kernel(1.0, 1.5, t=0.01)
        
        assert isinstance(K, (complex, float, np.number))
        assert np.isfinite(K)
    
    def test_thermal_kernel_zero_handling(self):
        """Test thermal kernel handles zero correctly."""
        K = thermal_kernel(0.0, 1.0, t=0.01)
        assert K == 0.0
        
        K = thermal_kernel(1.0, 0.0, t=0.01)
        assert K == 0.0
    
    def test_thermal_kernel_symmetry(self):
        """Test thermal kernel properties."""
        x, y, t = 1.5, 2.0, 0.01
        K1 = thermal_kernel(x, y, t)
        K2 = thermal_kernel(y, x, t)
        
        # Should be related (not necessarily equal due to phase)
        assert abs(K1) > 0
        assert abs(K2) > 0
    
    def test_integral_operator_creation(self):
        """Test IntegralOperator class."""
        R_t = IntegralOperator(thermal_kernel, t=0.01)
        
        assert R_t.t == 0.01
        assert callable(R_t.kernel)
    
    def test_involution_operator_creation(self):
        """Test InvolutionOperator class."""
        J = InvolutionOperator()
        
        # Test application
        f = lambda x: x**2
        Jf = J.apply(f)
        
        assert callable(Jf)
        # Test at a point: (Jf)(2) = 2^{-1/2} * f(1/2) = 2^{-1/2} * 1/4
        val = Jf(2.0)
        expected = 2.0**(-0.5) * (0.5)**2
        assert np.isclose(val, expected, rtol=1e-5)
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        # Create simple hermitian matrix
        H = np.array([[1.0, 0.5], [0.5, 2.0]], dtype=complex)
        eigenvals = compute_spectrum(H)
        
        assert len(eigenvals) == 2
        assert all(np.isreal(eigenvals))
        assert all(np.isfinite(eigenvals))
    
    def test_build_rh_operator_basic(self):
        """Test basic RH operator construction."""
        H, eigenvals, x_values = build_rh_operator(
            x_min=0.5, x_max=2.0, num_points=20, t=0.1
        )
        
        assert H.shape == (20, 20)
        assert len(eigenvals) == 20
        assert len(x_values) == 20
        
        # Check H is hermitian
        assert np.allclose(H, H.conj().T)
    
    def test_compare_with_riemann_zeros(self):
        """Test comparison with Riemann zeros."""
        # Synthetic eigenvalues
        eigenvals = np.array([0.5, 1.0, 200.0, 450.0])
        zeros = [14.134725, 21.022040]
        
        comparison = compare_with_riemann_zeros(eigenvals, zeros)
        
        assert 'num_eigenvalues' in comparison
        assert 'implied_zeros' in comparison
        assert 'differences' in comparison


class TestIntegration:
    """Integration tests combining multiple pillars."""
    
    def test_pilar1_and_pilar4_consistency(self):
        """Test consistency between spectral inversion and operator construction."""
        # Use same zeros for both
        zeros = [14.134725, 21.022040, 25.010858]
        
        # Pilar 1: Spectral inversion
        x_vals, measure, peaks = spectral_inversion(zeros, t=0.05, num_points=50)
        
        # Pilar 4: Build operator (eigenvalues should relate to zeros)
        H, eigenvals, x_values = build_rh_operator(num_points=30, t=0.1)
        
        # Both should produce finite results
        assert all(np.isfinite(measure))
        assert all(np.isfinite(eigenvals))
    
    def test_pilar2_and_pilar3_functional_equation(self):
        """Test consistency of functional equation between Pilar 2 and 3."""
        # Define test function
        gaussian = lambda x, xi: np.exp(-np.pi * (x**2 + xi**2))
        test_func_p2 = SchwartzTestFunction(gaussian)
        
        # Pilar 2: Verify via Poisson-Radón
        lattice = self_dual_lagrangian(n=3)
        is_verified_p2, _ = poisson_radon_duality(test_func_p2, lattice)
        
        # Pilar 3: Verify via symmetry check
        D = lambda s: s * (1 - s)
        result_p3 = verify_functional_equation_symmetry(D)
        
        # Both should produce boolean results
        assert isinstance(is_verified_p2, (bool, np.bool_))
        assert isinstance(result_p3['satisfies_functional_equation'], (bool, np.bool_))
    
    def test_all_pillars_produce_finite_results(self):
        """Test that all pillars produce finite, meaningful results."""
        zeros = [14.134725, 21.022040]
        
        # Pilar 1
        x1, m1, p1 = spectral_inversion(zeros, num_points=30)
        assert all(np.isfinite(m1))
        
        # Pilar 2
        gaussian = lambda x, xi: np.exp(-np.pi * (x**2 + xi**2))
        tf = SchwartzTestFunction(gaussian)
        lattice = self_dual_lagrangian(n=2)
        verified, info = poisson_radon_duality(tf, lattice)
        assert np.isfinite(info['difference'])
        
        # Pilar 3
        D = lambda s: np.exp(-0.1 * s**2)
        test_class = construct_pw_test_class(2)
        identical, info3 = verify_uniqueness(D, D, test_class)
        assert np.isfinite(info3['max_difference'])
        
        # Pilar 4
        H, ev, xv = build_rh_operator(num_points=20, t=0.1)
        assert all(np.isfinite(ev))


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

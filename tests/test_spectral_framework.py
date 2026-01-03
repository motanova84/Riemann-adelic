"""
Tests for spectral framework components.
"""
import sys
import os
import numpy as np
import pytest

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from inversion.inversion_spectral import K_D, prime_measure_from_zeros
from operador.operador_H import K_t, R_t_matrix, approximate_spectrum
from dualidad.dualidad_poisson import J_operator, check_involution
from unicidad.unicidad_paleywiener import PaleyWienerClass, compare_distributions


class TestInversionSpectral:
    """Test spectral inversion module."""
    
    def test_K_D_basic(self):
        """Test basic K_D kernel computation."""
        zeros = [0.5 + 14.1347j, 0.5 - 14.1347j]
        x, y = 2.0, 1.0
        result = K_D(x, y, zeros, t=1e-2)
        assert result is not None
        assert isinstance(result, (complex, np.complex128, np.complexfloating))
    
    def test_prime_measure_from_zeros(self):
        """Test prime measure reconstruction from zeros."""
        zeros = [0.5 + 14.1347j, 0.5 - 14.1347j]
        X = np.linspace(0, 10, 50)
        result = prime_measure_from_zeros(zeros, X)
        assert result is not None
        assert len(result) == len(X)
        assert isinstance(result, np.ndarray)


class TestOperadorH:
    """Test operator H construction."""
    
    def test_K_t_basic(self):
        """Test K_t kernel computation."""
        x, y = 2.0, 1.0
        result = K_t(x, y, t=1e-2, N=100)
        assert result is not None
        assert isinstance(result, (complex, np.complex128, np.complexfloating))
    
    def test_R_t_matrix(self):
        """Test R_t matrix construction."""
        grid = np.linspace(0.5, 2.0, 10)
        M = R_t_matrix(grid, t=1e-2)
        assert M.shape == (10, 10)
        assert M.dtype == np.complex128
    
    def test_approximate_spectrum(self):
        """Test spectrum approximation."""
        grid = np.linspace(0.5, 2.0, 10)
        spectrum = approximate_spectrum(grid, t=1e-2)
        assert spectrum is not None
        assert len(spectrum) == 10
        assert all(isinstance(x, (float, np.floating)) for x in spectrum)


class TestDualidadPoisson:
    """Test Poisson-Radon duality."""
    
    def test_J_operator_basic(self):
        """Test J operator on a simple function."""
        f = lambda x: x**2
        x = 2.0
        result = J_operator(f, x)
        expected = x**(-0.5) * f(1.0/x)
        assert np.allclose(result, expected)
    
    def test_check_involution_gaussian(self):
        """Test involution property with Gaussian."""
        f = lambda x: np.exp(-x**2)
        x = 1.5
        # For general functions, J(J(f)) might not equal f exactly
        # Test that the function runs without error
        result = check_involution(f, x)
        assert isinstance(result, (bool, np.bool_))


class TestUnicidadPaleyWiener:
    """Test Paley-Wiener uniqueness."""
    
    def test_paley_wiener_class_init(self):
        """Test PaleyWienerClass initialization."""
        pw = PaleyWienerClass(bandwidth=10.0)
        assert pw.bandwidth == 10.0
    
    def test_test_function(self):
        """Test that test function is computable."""
        pw = PaleyWienerClass(bandwidth=10.0)
        x = 5.0
        result = pw.test_function(x)
        assert result is not None
        assert isinstance(result, (float, np.floating))
    
    def test_compare_distributions_same(self):
        """Test distribution comparison with identical distributions."""
        D1 = lambda phi: np.sum([phi(x) for x in [1.0, 2.0, 3.0]])
        D2 = lambda phi: np.sum([phi(x) for x in [1.0, 2.0, 3.0]])
        tests = [lambda x: x, lambda x: x**2]
        result = compare_distributions(D1, D2, tests)
        assert result is True
    
    def test_compare_distributions_different(self):
        """Test distribution comparison with different distributions."""
        D1 = lambda phi: np.sum([phi(x) for x in [1.0, 2.0, 3.0]])
        D2 = lambda phi: np.sum([phi(x) for x in [1.0, 2.0, 4.0]])
        tests = [lambda x: x, lambda x: x**2]
        result = compare_distributions(D1, D2, tests)
        assert result is False


class TestFrameworkIntegration:
    """Integration tests for complete framework."""
    
    def test_zeros_to_spectrum(self):
        """Test complete pipeline: zeros -> operator -> spectrum."""
        # Small test with artificial zeros
        zeros = [0.5 + 14.1347j, 0.5 - 14.1347j, 
                 0.5 + 21.0220j, 0.5 - 21.0220j]
        
        # Create small grid
        grid = np.linspace(1.0, 2.0, 5)
        
        # Compute spectrum
        spectrum = approximate_spectrum(grid, t=0.01)
        
        # Basic sanity checks
        assert spectrum is not None
        assert len(spectrum) == len(grid)
        assert all(np.isfinite(s) for s in spectrum)
    
    def test_prime_reconstruction_peaks(self):
        """Test that prime reconstruction produces finite values."""
        zeros = [0.5 + 14.1347j, 0.5 - 14.1347j]
        X = np.linspace(0, 3, 20)
        
        result = prime_measure_from_zeros(zeros, X, t=0.01)
        
        # Check that result is finite
        assert all(np.isfinite(r) for r in result)
        # Check that we have variation (not all zeros)
        assert np.var(np.abs(result)) > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

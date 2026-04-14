"""
Test file for the explicit GL(1) construction and spectral operators.
"""

import pytest
import numpy as np
import sys
import os

# Add the project root to the path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from foundational_gl1 import ExplicitGL1Construction
from spectral_operators import ExplicitTraceClassOperator, AdelicSpectralConstruction


class TestExplicitGL1Construction:
    """Test cases for the explicit GL(1) construction."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.gl1_constructor = ExplicitGL1Construction()
    
    def test_initialization(self):
        """Test proper initialization of GL(1) constructor."""
        assert len(self.gl1_constructor.prime_list) == 10
        assert self.gl1_constructor.prime_list[0] == 2
        assert self.gl1_constructor.prime_list[-1] == 29
    
    def test_explicit_haar_measure(self):
        """Test explicit Haar measure for finite primes."""
        for p in [2, 3, 5, 7]:
            measure = self.gl1_constructor.explicit_haar_measure_finite(p)
            assert measure == 1.0, f"Haar measure should be 1.0 for prime {p}"
    
    def test_explicit_test_function_finite(self):
        """Test the explicit test function for finite primes."""
        p = 3
        # Test function should be non-zero at 1
        val_at_1 = self.gl1_constructor.explicit_test_function_finite(p, 1.0)
        expected = 1.0 / (1 - p**(-2))
        assert abs(val_at_1 - expected) < 1e-10
        
        # Test function should be zero away from 1
        val_away = self.gl1_constructor.explicit_test_function_finite(p, 2.0)
        assert val_away == 0.0
    
    def test_explicit_test_function_archimedean(self):
        """Test the archimedean test function."""
        # Test at zero
        val_0 = self.gl1_constructor.explicit_test_function_archimedean(0)
        assert val_0 == 1.0
        
        # Test decay property
        val_large = self.gl1_constructor.explicit_test_function_archimedean(10)
        assert val_large < 1e-10  # Should decay rapidly
    
    def test_local_trace_computation(self):
        """Test the local trace computation for unramified characters."""
        s = 2.0
        p = 2
        trace = self.gl1_constructor.compute_local_trace_unramified(p, s)
        
        # Should be positive and finite
        assert np.isfinite(trace)
        assert trace > 0
    
    def test_archimedean_trace_computation(self):
        """Test the archimedean trace computation."""
        s = 2.0
        arch_trace = self.gl1_constructor.compute_archimedean_trace_explicit(s)
        
        # Should be positive and finite
        assert np.isfinite(arch_trace)
        assert arch_trace > 0
    
    def test_trace_identity_verification(self):
        """Test the complete trace identity verification."""
        s = 2.0
        total_trace = self.gl1_constructor.verify_trace_identity_gl1(s)
        
        # Should produce a finite result
        assert np.isfinite(total_trace)
        assert total_trace > 0


class TestExplicitTraceClassOperator:
    """Test cases for explicit trace class operators."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.operator = ExplicitTraceClassOperator(dimension=50)
        self.primes = [2, 3, 5, 7, 11]
        self.weights = [1.0, 0.8, 0.6, 0.4, 0.2]
    
    def test_initialization(self):
        """Test proper initialization."""
        assert self.operator.dimension == 50
        assert self.operator.matrix is None
    
    def test_explicit_operator_construction(self):
        """Test explicit operator construction."""
        matrix = self.operator.build_explicit_operator(self.primes, self.weights)
        
        # Matrix should be created
        assert matrix is not None
        assert matrix.shape == (50, 50)
        
        # Matrix should be real
        assert np.all(np.isreal(matrix))
        
        # Matrix should be symmetric (approximately)
        assert np.allclose(matrix, matrix.T, atol=1e-10)
    
    def test_trace_computation(self):
        """Test explicit trace computation."""
        self.operator.build_explicit_operator(self.primes, self.weights)
        trace = self.operator.compute_explicit_trace()
        
        # Trace should be finite and positive
        assert np.isfinite(trace)
        assert trace > 0
    
    def test_eigenvalue_computation(self):
        """Test explicit eigenvalue computation."""
        self.operator.build_explicit_operator(self.primes, self.weights)
        eigenvalues = self.operator.compute_eigenvalues_explicit()
        
        # Should have the right number of eigenvalues
        assert len(eigenvalues) == 50
        
        # All eigenvalues should be real and finite
        assert np.all(np.isreal(eigenvalues))
        assert np.all(np.isfinite(eigenvalues))
    
    def test_trace_class_verification(self):
        """Test trace class property verification."""
        self.operator.build_explicit_operator(self.primes, self.weights)
        is_trace_class, nuclear_norm = self.operator.verify_trace_class_property()
        
        # Should be trace class
        assert is_trace_class
        assert np.isfinite(nuclear_norm)
        assert nuclear_norm > 0
    
    def test_spectral_density(self):
        """Test spectral density computation."""
        self.operator.build_explicit_operator(self.primes, self.weights)
        bin_centers, hist = self.operator.explicit_spectral_density()
        
        # Should produce valid histogram data
        assert len(bin_centers) == len(hist)
        assert np.all(hist >= 0)  # Density should be non-negative


class TestAdelicSpectralConstruction:
    """Test cases for adelic spectral construction."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.primes = [2, 3, 5]
        self.arch_data = 1.0
        self.adelic_constructor = AdelicSpectralConstruction(self.primes, self.arch_data)
    
    def test_initialization(self):
        """Test proper initialization."""
        assert self.adelic_constructor.primes == self.primes
        assert self.adelic_constructor.arch_data == self.arch_data
        assert self.adelic_constructor.operators == {}
    
    def test_local_operator_construction(self):
        """Test construction of local operators."""
        operators = self.adelic_constructor.build_local_operators()
        
        # Should have one operator per prime
        assert len(operators) == len(self.primes)
        
        # Each operator should be an ExplicitTraceClassOperator
        for p in self.primes:
            assert p in operators
            assert isinstance(operators[p], ExplicitTraceClassOperator)
    
    def test_global_trace_formula(self):
        """Test the global trace formula computation."""
        self.adelic_constructor.build_local_operators()
        global_trace, local_traces = self.adelic_constructor.compute_global_trace_formula()
        
        # Should produce finite results
        assert np.isfinite(global_trace)
        assert len(local_traces) == len(self.primes)
        
        # All local traces should be finite
        for p in self.primes:
            assert p in local_traces
            assert np.isfinite(local_traces[p])


class TestIntegration:
    """Integration tests for the complete construction."""
    
    def test_gl1_and_operators_integration(self):
        """Test integration between GL(1) construction and trace operators."""
        # GL(1) construction
        gl1_constructor = ExplicitGL1Construction()
        trace_gl1 = gl1_constructor.verify_trace_identity_gl1(2.0)
        
        # Operator construction
        operator = ExplicitTraceClassOperator(dimension=20)
        primes = [2, 3, 5]
        weights = [1.0, 0.8, 0.6]
        operator.build_explicit_operator(primes, weights)
        trace_op = operator.compute_explicit_trace()
        
        # Both should produce finite, positive results
        assert np.isfinite(trace_gl1) and trace_gl1 > 0
        assert np.isfinite(trace_op) and trace_op > 0
    
    def test_riemann_zeros_connection(self):
        """Test connection to Riemann zeros."""
        operator = ExplicitTraceClassOperator(dimension=20)
        primes = [2, 3, 5, 7]
        weights = [1.0, 0.8, 0.6, 0.4]
        operator.build_explicit_operator(primes, weights)
        
        # Mock some Riemann zeros (first few known values)
        riemann_zeros = [14.134725, 21.022040, 25.010856, 30.424878]
        
        implied_zeros, avg_diff = operator.connect_to_riemann_zeros(riemann_zeros)
        
        # Should produce some implied zeros
        assert len(implied_zeros) > 0
        assert all(z > 0 for z in implied_zeros)
        
        # Average difference should be finite
        if avg_diff is not None:
            assert np.isfinite(avg_diff)


# Run tests when module is executed directly
if __name__ == "__main__":
    pytest.main([__file__, "-v"])
#!/usr/bin/env python3
"""
Tests for Riemann Zeros Frequency Computation Module

This test suite validates the ZerosFrequencyComputation class and its methods
for computing frequency from Riemann zeros with golden ratio scaling.

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import sys
from pathlib import Path
import pytest

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

# Direct import to avoid utils/__init__.py issues
import importlib.util
spec = importlib.util.spec_from_file_location(
    "zeros_frequency_computation",
    Path(__file__).parent.parent / "utils" / "zeros_frequency_computation.py"
)
zfc_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(zfc_module)
ZerosFrequencyComputation = zfc_module.ZerosFrequencyComputation

from mpmath import mp


class TestZerosFrequencyComputation:
    """Test suite for ZerosFrequencyComputation class"""
    
    def setup_method(self):
        """Setup test instance with standard precision"""
        self.computation = ZerosFrequencyComputation(dps=50)
        
    def test_initialization(self):
        """Test that initialization sets up constants correctly"""
        assert self.computation.dps == 50
        
        # Check constants are mpmath objects
        assert isinstance(self.computation.phi, type(mp.mpf(1)))
        assert isinstance(self.computation.gamma, type(mp.mpf(1)))
        assert isinstance(self.computation.pi, type(mp.mpf(1)))
        
        # Check approximate values
        assert abs(float(self.computation.phi) - 1.618033988749895) < 1e-10
        assert abs(float(self.computation.gamma) - 0.5772156649015329) < 1e-10
        assert abs(float(self.computation.pi) - 3.141592653589793) < 1e-10
        
    def test_derived_constants(self):
        """Test that derived constants are computed correctly"""
        # e^(gamma*pi) should be approximately 6.131114182
        assert abs(float(self.computation.e_gamma_pi) - 6.131114182) < 1e-6
        
        # phi*400 should be approximately 647.2135955
        assert abs(float(self.computation.phi_400) - 647.2135955) < 1e-6
        
        # target should be approximately 105.562
        assert abs(float(self.computation.target) - 105.562) < 1e-3
        
    def test_get_riemann_zeros_loads_data(self):
        """Test that get_riemann_zeros loads data from file"""
        zeros = self.computation.get_riemann_zeros(limit=100)
        
        # Should load some zeros
        assert len(zeros) > 0
        assert len(zeros) <= 100
        
        # First zero should be approximately 14.134725
        assert abs(float(zeros[0]) - 14.134725) < 1e-5
        
        # All zeros should be positive
        for z in zeros:
            assert float(z) > 0
            
    def test_get_riemann_zeros_respects_T_limit(self):
        """Test that get_riemann_zeros respects height limit T"""
        T = 100.0
        zeros = self.computation.get_riemann_zeros(T=T, limit=1000)
        
        # All zeros should be less than T
        for z in zeros:
            assert float(z) < T
            
    def test_get_riemann_zeros_respects_count_limit(self):
        """Test that get_riemann_zeros respects count limit"""
        limit = 50
        zeros = self.computation.get_riemann_zeros(limit=limit)
        
        # Should not exceed limit
        assert len(zeros) <= limit
        
    def test_get_riemann_zeros_sorted(self):
        """Test that returned zeros are sorted"""
        zeros = self.computation.get_riemann_zeros(limit=100)
        
        # Check if sorted
        for i in range(len(zeros) - 1):
            assert float(zeros[i]) <= float(zeros[i + 1])
            
    def test_compute_zeros_sum_returns_positive(self):
        """Test that compute_zeros_sum returns positive value"""
        S = self.computation.compute_zeros_sum(T=1000, alpha=0.5, limit=100)
        
        # Sum should be positive
        assert float(S) > 0
        
    def test_compute_zeros_sum_decreases_with_alpha(self):
        """Test that sum decreases as alpha increases"""
        S1 = self.computation.compute_zeros_sum(T=1000, alpha=0.3, limit=100)
        S2 = self.computation.compute_zeros_sum(T=1000, alpha=0.5, limit=100)
        S3 = self.computation.compute_zeros_sum(T=1000, alpha=0.7, limit=100)
        
        # Sum should decrease as alpha increases (more decay)
        assert float(S1) > float(S2)
        assert float(S2) > float(S3)
        
    def test_compute_zeros_sum_with_different_T(self):
        """Test compute_zeros_sum with different height limits"""
        # More zeros (higher T) should give different sum
        S1 = self.computation.compute_zeros_sum(T=100, alpha=0.5, limit=1000)
        S2 = self.computation.compute_zeros_sum(T=500, alpha=0.5, limit=1000)
        
        # Sums might be very close but should differ in high precision
        # Use string comparison to check they differ at high precision
        assert str(S1) != str(S2) or abs(float(S1 - S2)) >= 1e-50
        
    def test_validate_sum_returns_tuple(self):
        """Test that validate_sum returns correct tuple structure"""
        S, result, passed = self.computation.validate_sum(
            T=1000, alpha=0.5, limit=100
        )
        
        # Check types
        assert isinstance(S, type(mp.mpf(1)))
        assert isinstance(result, type(mp.mpf(1)))
        assert isinstance(passed, bool)
        
        # Check that result = S * e_gamma_pi (approximately)
        expected_result = S * self.computation.e_gamma_pi
        assert abs(float(result - expected_result)) < 1e-10
        
    def test_compute_frequency_returns_positive(self):
        """Test that compute_frequency returns positive value"""
        f = self.computation.compute_frequency()
        
        # Frequency should be positive
        assert float(f) > 0
        
    def test_compute_frequency_has_reasonable_magnitude(self):
        """Test that computed frequency has reasonable magnitude"""
        f = self.computation.compute_frequency()
        
        # Frequency should be in reasonable range (not extremely large or small)
        # Expected to be in range [0.1, 1000] Hz based on the formula
        assert 0.1 < float(f) < 1000
        
    def test_compute_frequency_with_different_precision(self):
        """Test frequency computation with different precision levels"""
        comp30 = ZerosFrequencyComputation(dps=30)
        comp100 = ZerosFrequencyComputation(dps=100)
        
        f30 = comp30.compute_frequency()
        f100 = comp100.compute_frequency()
        
        # Results should be close but not identical due to precision
        assert abs(float(f30) - float(f100)) < 1e-5
        
    def test_run_complete_computation_returns_dict(self):
        """Test that run_complete_computation returns proper dictionary"""
        results = self.computation.run_complete_computation(
            T=500, alpha=0.5, limit=100, verbose=False
        )
        
        # Check dictionary keys
        assert 'sum' in results
        assert 'validation_result' in results
        assert 'target' in results
        assert 'validation_passed' in results
        assert 'frequency_hz' in results
        assert 'parameters' in results
        
        # Check types
        assert isinstance(results['sum'], float)
        assert isinstance(results['validation_result'], float)
        assert isinstance(results['target'], float)
        assert isinstance(results['validation_passed'], bool)
        assert isinstance(results['frequency_hz'], float)
        assert isinstance(results['parameters'], dict)
        
    def test_run_complete_computation_parameters(self):
        """Test that parameters are stored correctly in results"""
        T = 750
        alpha = 0.6
        limit = 150
        
        results = self.computation.run_complete_computation(
            T=T, alpha=alpha, limit=limit, verbose=False
        )
        
        # Check parameters are stored
        assert results['parameters']['T'] == T
        assert results['parameters']['alpha'] == alpha
        assert results['parameters']['limit'] == limit
        assert results['parameters']['precision'] == self.computation.dps
        
    def test_high_precision_computation(self):
        """Test computation with very high precision"""
        high_prec = ZerosFrequencyComputation(dps=200)
        
        # Should work without errors
        f = high_prec.compute_frequency()
        assert float(f) > 0
        
    def test_golden_ratio_properties(self):
        """Test mathematical properties of golden ratio"""
        phi = self.computation.phi
        
        # Golden ratio satisfies: phi^2 = phi + 1
        phi_squared = phi * phi
        phi_plus_one = phi + 1
        assert abs(float(phi_squared - phi_plus_one)) < 1e-10
        
        # Also: 1/phi = phi - 1
        one_over_phi = 1 / phi
        phi_minus_one = phi - 1
        assert abs(float(one_over_phi - phi_minus_one)) < 1e-10


class TestIntegrationWithExistingValidation:
    """Test integration with existing validation framework"""
    
    def test_constants_match_repository_standards(self):
        """Test that constants match those used elsewhere in repository"""
        computation = ZerosFrequencyComputation(dps=30)
        
        # Compare with mpmath's built-in constants
        mp.dps = 30
        mp_phi = (1 + mp.sqrt(5)) / 2
        mp_gamma = mp.euler
        mp_pi = mp.pi
        
        # Should match mpmath constants
        assert abs(float(computation.phi - mp_phi)) < 1e-20
        assert abs(float(computation.gamma - mp_gamma)) < 1e-20
        assert abs(float(computation.pi - mp_pi)) < 1e-20


class TestEdgeCases:
    """Test edge cases and error handling"""
    
    def test_zero_alpha_gives_large_sum(self):
        """Test that alpha=0 gives sum equal to number of zeros"""
        computation = ZerosFrequencyComputation(dps=30)
        
        # With alpha=0, exp(-alpha*gamma) = 1 for all gamma
        # So sum should equal number of zeros
        limit = 50
        S = computation.compute_zeros_sum(T=1000, alpha=0.0, limit=limit)
        
        # Should be approximately equal to the number of loaded zeros
        # (may be less than limit if T constraint is tighter)
        assert 0 < float(S) <= limit
        
    def test_large_alpha_gives_small_sum(self):
        """Test that very large alpha gives very small sum"""
        computation = ZerosFrequencyComputation(dps=30)
        
        # With large alpha, exp(-alpha*gamma) becomes very small
        S = computation.compute_zeros_sum(T=1000, alpha=10.0, limit=100)
        
        # Sum should be very small
        assert float(S) < 1e-10
        
    def test_low_precision_computation(self):
        """Test that low precision still works"""
        low_prec = ZerosFrequencyComputation(dps=15)
        
        # Should work without errors
        f = low_prec.compute_frequency()
        assert float(f) > 0


if __name__ == '__main__':
    # Run tests
    pytest.main([__file__, '-v'])

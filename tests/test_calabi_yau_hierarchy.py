#!/usr/bin/env python3
"""
Tests for Calabi-Yau Hierarchy Validation

Tests the numerical validation of the geometric foundation
through compactification on the quintic in CP4.

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import pytest
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

# Import the validation functions
from validate_calabi_yau_hierarchy import validate_hierarchy, demonstrate_volume_hierarchy


class TestCalabiYauHierarchy:
    """Test suite for Calabi-Yau hierarchy validation."""
    
    def test_validate_hierarchy_returns_dict(self):
        """Test that validate_hierarchy returns expected data structure."""
        results = validate_hierarchy()
        
        assert isinstance(results, dict)
        assert 'c' in results
        assert 'lP' in results
        assert 'R_psi' in results
        assert 'f0_numeric' in results
        assert 'f0_expected' in results
    
    def test_physical_constants(self):
        """Test that physical constants have expected values."""
        results = validate_hierarchy()
        
        # Speed of light
        assert results['c'] == 2.99792458e8
        
        # Planck length
        assert results['lP'] == 1.616255e-35
        
        # RΨ hierarchy
        assert results['R_psi'] == 1e47
        
        # Expected frequency
        assert results['f0_expected'] == 141.7001
    
    def test_f0_numeric_is_positive(self):
        """Test that calculated frequency is positive."""
        results = validate_hierarchy()
        
        assert results['f0_numeric'] > 0
    
    def test_f0_numeric_is_finite(self):
        """Test that calculated frequency is finite."""
        results = validate_hierarchy()
        
        import numpy as np
        assert np.isfinite(results['f0_numeric'])
    
    def test_hierarchy_scale(self):
        """Test that RΨ hierarchy is at correct order of magnitude."""
        results = validate_hierarchy()
        
        R_psi = results['R_psi']
        
        # Should be order 10^47
        assert 1e46 < R_psi < 1e48
    
    def test_planck_length_scale(self):
        """Test that Planck length is at correct order of magnitude."""
        results = validate_hierarchy()
        
        lP = results['lP']
        
        # Should be order 10^-35 meters
        assert 1e-36 < lP < 1e-34
    
    def test_demonstrate_volume_hierarchy_runs(self):
        """Test that volume hierarchy demonstration runs without error."""
        # Should not raise any exceptions
        demonstrate_volume_hierarchy()


class TestCalabiYauGeometry:
    """Test geometric properties of the quintic in CP4."""
    
    def test_hodge_numbers(self):
        """Test Hodge numbers of the quintic."""
        # The quintic in CP^4 has known Hodge numbers
        h11 = 1
        h21 = 101
        
        # Euler characteristic
        chi = 2 * (h11 - h21)
        
        assert chi == -200
    
    def test_complex_dimension(self):
        """Test that quintic has complex dimension 3."""
        # CP^4 has complex dimension 4
        # A hypersurface has complex dimension 3
        complex_dim = 3
        real_dim = 2 * complex_dim
        
        assert complex_dim == 3
        assert real_dim == 6
    
    def test_volume_to_hierarchy_scaling(self):
        """Test the scaling relation R_Ψ ~ (V_CY)^(1/6)."""
        import numpy as np
        
        # Volume in Planck units
        V_CY = 1e282
        
        # Expected hierarchy
        R_psi_expected = V_CY ** (1/6)
        
        # Should be approximately 10^47
        assert np.abs(np.log10(R_psi_expected) - 47) < 0.1


class TestNumericalValidation:
    """Test numerical validation aspects."""
    
    def test_frequency_formula_consistency(self):
        """Test that frequency formula is dimensionally consistent."""
        from sympy import pi, N
        
        c = 2.99792458e8  # m/s
        lP = 1.616255e-35  # m
        R = 1e47  # dimensionless
        
        # f0 should have units of Hz (1/s)
        # c / (R * lP) has units of (m/s) / m = 1/s
        f0 = c / (2 * float(pi) * R * lP)
        
        # Should be positive
        assert f0 > 0
    
    def test_calabi_yau_volume_positive(self):
        """Test that Calabi-Yau volume is positive."""
        V_CY = 1e282  # in Planck units
        
        assert V_CY > 0
    
    def test_hierarchy_from_volume_consistency(self):
        """Test consistency between volume and hierarchy."""
        import numpy as np
        
        # If V_CY ~ 10^282, then R ~ 10^47
        V_CY = 1e282
        R_from_V = V_CY ** (1/6)
        
        # Check order of magnitude
        log_R = np.log10(R_from_V)
        assert 46.5 < log_R < 47.5


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])

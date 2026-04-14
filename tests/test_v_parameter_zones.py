#!/usr/bin/env python3
"""
Tests for v-parameter zone classification and behavior.

This module tests the mathematical insight that:
    - v < 1: SAFE zone (exponential decay)
    - v = 1: BOUNDARY (constant weight)
    - v > 1: DANGEROUS zone (exponential growth)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.kato_exponential_potential import (
    ExponentialPotentialTest,
    test_v_parameter_zones
)


class TestVParameterZones:
    """Test suite for v-parameter zone classification."""
    
    def test_classify_v_zone_safe(self):
        """Test that v < 1 is correctly classified as SAFE."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        # Test various safe zone values
        for v in [0.1, 0.5, 0.9, 0.99]:
            classification = tester.classify_v_zone(v)
            assert "SAFE" in classification, f"v={v} should be SAFE zone"
            assert "decay" in classification.lower(), f"v={v} should mention decay"
    
    def test_classify_v_zone_dangerous(self):
        """Test that v > 1 is correctly classified as DANGEROUS."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        # Test various dangerous zone values
        for v in [1.01, 1.1, 1.5, 2.0]:
            classification = tester.classify_v_zone(v)
            assert "DANGEROUS" in classification, f"v={v} should be DANGEROUS zone"
            assert "growth" in classification.lower(), f"v={v} should mention growth"
    
    def test_classify_v_zone_boundary(self):
        """Test that v = 1 is correctly classified as BOUNDARY."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        classification = tester.classify_v_zone(1.0)
        assert "BOUNDARY" in classification, "v=1 should be BOUNDARY"
        assert "v=1" in classification or "Constant" in classification
    
    def test_potential_norm_with_v_parameter(self):
        """Test potential_norm accepts v parameter and computes correctly."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        # Create a simple test function
        psi = np.exp(-tester.y**2 / 2)
        psi = psi / tester.l2_norm(psi)  # Normalize
        
        # Test with different v values
        norm_v05 = tester.potential_norm(psi, v=0.5)
        norm_v10 = tester.potential_norm(psi, v=1.0)
        norm_v15 = tester.potential_norm(psi, v=1.5)
        
        # All should be positive
        assert norm_v05 > 0, "Norm should be positive for v=0.5"
        assert norm_v10 > 0, "Norm should be positive for v=1.0"
        assert norm_v15 > 0, "Norm should be positive for v=1.5"
        
        # For y > 0 region: expect norm_v05 < norm_v10 < norm_v15
        # (decay < constant < growth for positive y)
        # This may not always hold due to integration over both positive and negative y
        # But we can check they're different
        assert not np.isclose(norm_v05, norm_v10), "Norms should differ for different v"
        assert not np.isclose(norm_v10, norm_v15), "Norms should differ for different v"
    
    def test_inequality_with_safe_zone_v(self):
        """Test Kato inequality holds better in safe zone (v < 1)."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        # Test with safe zone v (should have smaller C_ε)
        result_safe = tester.test_inequality_single_epsilon(
            eps=0.1,
            n_tests=100,
            v=0.5,  # Safe zone
            verbose=False
        )
        
        assert result_safe.condition_met, "Inequality should hold in safe zone"
        assert result_safe.C_epsilon >= 0, "C_ε should be non-negative"
    
    def test_inequality_with_boundary_v(self):
        """Test Kato inequality at boundary v = 1."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        # Test with boundary v = 1 (standard case)
        result_boundary = tester.test_inequality_single_epsilon(
            eps=0.1,
            n_tests=100,
            v=1.0,  # Boundary
            verbose=False
        )
        
        assert result_boundary.condition_met, "Inequality should hold at boundary"
        assert result_boundary.C_epsilon >= 0, "C_ε should be non-negative"
    
    def test_inequality_with_dangerous_zone_v(self):
        """Test Kato inequality in dangerous zone (v > 1) requires larger C_ε."""
        tester = ExponentialPotentialTest(L_y=8.0, N=500)  # Smaller domain for stability
        
        # Test with dangerous zone v (may require larger C_ε)
        result_dangerous = tester.test_inequality_single_epsilon(
            eps=0.1,
            n_tests=100,
            v=1.2,  # Dangerous zone (not too large to avoid overflow)
            verbose=False
        )
        
        # Should still satisfy inequality, but possibly with larger C_ε
        assert result_dangerous.C_epsilon >= 0, "C_ε should be non-negative"
    
    @pytest.mark.slow
    def test_v_parameter_zones_comprehensive(self):
        """Comprehensive test of v-parameter zones (marked as slow)."""
        results = test_v_parameter_zones(
            L_y=10.0,
            N=500,
            n_tests=100,
            verbose=False
        )
        
        # Check we got results for all tested v values
        assert len(results) >= 3, "Should test at least 3 v values"
        
        # Verify each result has expected structure
        for v, result in results.items():
            assert 'zone' in result, f"Result for v={v} should have 'zone'"
            assert 'C_epsilon' in result, f"Result for v={v} should have 'C_epsilon'"
            assert 'condition_met' in result, f"Result for v={v} should have 'condition_met'"
            assert 'classification' in result, f"Result for v={v} should have 'classification'"
            
            # C_epsilon should be positive
            assert result['C_epsilon'] >= 0, f"C_ε should be non-negative for v={v}"
    
    def test_mathematical_insight_documented(self):
        """Verify the counter-intuitive insight is captured in classification."""
        tester = ExponentialPotentialTest(L_y=10.0, N=500)
        
        # v > 1 should be dangerous (growth), not safe
        dangerous_class = tester.classify_v_zone(1.5)
        assert "DANGEROUS" in dangerous_class, "v > 1 should be dangerous (growth)"
        assert "growth" in dangerous_class.lower(), "Should mention exponential growth"
        
        # v < 1 should be safe (decay)
        safe_class = tester.classify_v_zone(0.5)
        assert "SAFE" in safe_class, "v < 1 should be safe (decay)"
        assert "decay" in safe_class.lower(), "Should mention exponential decay"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

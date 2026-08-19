#!/usr/bin/env python3
"""
Test Suite: Logarithmic Operator Birman-Solomyak Analysis
==========================================================

Validates the modified operator in logarithmic coordinates including:
- Potential V(y) asymptotic behavior
- Resolvent kernel computation
- Volterra L² test for compactness
- Birman-Solomyak trace-class property
- BKS program applicability

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent.parent / "operators"))

from logarithmic_operator_birman_solomyak import (
    LogarithmicOperatorBirmanSolomyak,
    AsymptoticAnalysis,
    VolterraTest,
    BirmanSolomyakTest,
    LogarithmicOperatorResult
)


class TestPotential:
    """Test potential V(y) = log(1 + e^y) computation and properties."""
    
    def test_potential_positive(self):
        """Test that V(y) > 0 for all y."""
        operator = LogarithmicOperatorBirmanSolomyak()
        y_test = np.linspace(-10, 10, 100)
        V = operator.potential(y_test)
        assert np.all(V > 0), "Potential should be positive everywhere"
    
    def test_potential_monotonic(self):
        """Test that V(y) is monotonically increasing."""
        operator = LogarithmicOperatorBirmanSolomyak()
        y_test = np.linspace(-10, 10, 100)
        V = operator.potential(y_test)
        dV = np.diff(V)
        assert np.all(dV > 0), "Potential should be monotonically increasing"
    
    def test_potential_left_asymptotic(self):
        """Test V(y) ∼ e^y as y → -∞."""
        operator = LogarithmicOperatorBirmanSolomyak(y_min=-10.0)
        y_left = -8.0
        V = operator.potential(y_left)
        V_asym = np.exp(y_left)
        relative_error = np.abs(V - V_asym) / V_asym
        assert relative_error < 0.01, f"V(y) should match e^y at y={y_left}"
    
    def test_potential_right_asymptotic(self):
        """Test V(y) ∼ y as y → +∞."""
        operator = LogarithmicOperatorBirmanSolomyak(y_max=10.0)
        y_right = 8.0
        V = operator.potential(y_right)
        # V(y) = y + log(1 + e^{-y}) ≈ y for large y
        V_asym = y_right
        error = np.abs(V - V_asym)
        assert error < 0.01, f"V(y) - y should be small at y={y_right}"
    
    def test_potential_numerical_stability(self):
        """Test numerical stability for extreme y values."""
        operator = LogarithmicOperatorBirmanSolomyak(y_min=-20.0, y_max=20.0)
        
        # Very negative y
        y_neg = np.array([-15.0, -10.0, -5.0])
        V_neg = operator.potential(y_neg)
        assert np.all(np.isfinite(V_neg)), "Potential should be finite for negative y"
        
        # Very positive y
        y_pos = np.array([5.0, 10.0, 15.0])
        V_pos = operator.potential(y_pos)
        assert np.all(np.isfinite(V_pos)), "Potential should be finite for positive y"


class TestResolventKernels:
    """Test resolvent kernel computations."""
    
    def test_kernel_causality(self):
        """Test that kernel is zero for y ≤ t (causality)."""
        operator = LogarithmicOperatorBirmanSolomyak()
        
        # Test y < t
        G = operator.resolvent_kernel(1.0, 2.0)
        assert G == 0.0, "Kernel should be zero for y < t"
        
        # Test y = t
        G = operator.resolvent_kernel(1.0, 1.0)
        assert G == 0.0, "Kernel should be zero for y = t"
    
    def test_kernel_nonzero(self):
        """Test that kernel is nonzero for y > t."""
        operator = LogarithmicOperatorBirmanSolomyak()
        G = operator.resolvent_kernel(2.0, 1.0)
        assert np.abs(G) > 0.0, "Kernel should be nonzero for y > t"
    
    def test_free_kernel_exponential(self):
        """Test free kernel matches exp(-z(y-t))."""
        operator = LogarithmicOperatorBirmanSolomyak(z=1.0+0.5j)
        y, t = 3.0, 1.0
        G0 = operator.free_resolvent_kernel(y, t)
        expected = np.exp(-operator.z * (y - t))
        assert np.abs(G0 - expected) < 1e-10, "Free kernel should match exponential"
    
    def test_difference_kernel_structure(self):
        """Test that difference kernel has expected structure."""
        operator = LogarithmicOperatorBirmanSolomyak()
        y, t = 3.0, 1.0
        
        K_z = operator.resolvent_difference_kernel(y, t)
        G_z = operator.resolvent_kernel(y, t)
        G0_z = operator.free_resolvent_kernel(y, t)
        
        # Should match G_z - G0_z
        expected = G_z - G0_z
        assert np.abs(K_z - expected) < 1e-10, "Difference should match G_z - G0_z"
    
    def test_kernel_decay(self):
        """Test that kernel decays with increasing (y-t) for Re(z) > 0."""
        operator = LogarithmicOperatorBirmanSolomyak(z=1.0+0.0j)
        
        y_fixed = 5.0
        t_values = np.array([0.0, 1.0, 2.0, 3.0, 4.0])
        K_z_values = [np.abs(operator.resolvent_difference_kernel(y_fixed, t)) 
                      for t in t_values]
        
        # Should generally decrease (though not strictly due to integral)
        # At least the last values should be smaller than the first
        assert K_z_values[-1] < K_z_values[0], "Kernel should decay overall"


class TestAsymptoticAnalysis:
    """Test asymptotic behavior analysis."""
    
    def test_singularity_vanished(self):
        """Test that singularity at x→0 (y→-∞) has vanished."""
        operator = LogarithmicOperatorBirmanSolomyak(y_min=-10.0)
        asymptotic = operator.analyze_asymptotic_behavior()
        
        assert asymptotic.singularity_vanished, "Singularity should have vanished"
        assert asymptotic.V_left < 1.0, "V(y) should be small for y → -∞"
    
    def test_left_asymptotic_accuracy(self):
        """Test accuracy of left asymptotic approximation."""
        operator = LogarithmicOperatorBirmanSolomyak(y_min=-10.0)
        asymptotic = operator.analyze_asymptotic_behavior()
        
        assert asymptotic.left_error < 0.1, "Left asymptotic error should be small"
    
    def test_right_asymptotic_linear(self):
        """Test that right asymptotic is approximately linear."""
        operator = LogarithmicOperatorBirmanSolomyak(y_max=10.0)
        asymptotic = operator.analyze_asymptotic_behavior()
        
        # V(y) - y should be small
        difference = asymptotic.V_right - asymptotic.V_asym_right
        assert difference < 1.0, "V(y) should be close to y for large y"


class TestVolterraL2Test:
    """Test Volterra L² test for compactness."""
    
    def test_volterra_convergence(self):
        """Test that Volterra integral I(y) converges."""
        operator = LogarithmicOperatorBirmanSolomyak()
        volterra = operator.volterra_L2_test(num_y_points=20)
        
        assert volterra.convergent, "Volterra integral should converge"
        assert np.isfinite(volterra.I_sup), "sup I(y) should be finite"
    
    def test_volterra_bounded(self):
        """Test that sup_y I(y) is bounded."""
        operator = LogarithmicOperatorBirmanSolomyak()
        volterra = operator.volterra_L2_test(num_y_points=20)
        
        assert volterra.I_sup < 1e6, "sup I(y) should be reasonably bounded"
    
    def test_compactness_satisfied(self):
        """Test that compactness condition is satisfied."""
        operator = LogarithmicOperatorBirmanSolomyak()
        volterra = operator.volterra_L2_test(num_y_points=20)
        
        assert volterra.compactness_satisfied, "Compactness should be satisfied"
    
    def test_volterra_positive(self):
        """Test that I(y) ≥ 0 everywhere."""
        operator = LogarithmicOperatorBirmanSolomyak()
        volterra = operator.volterra_L2_test(num_y_points=20)
        
        assert np.all(volterra.I_values >= 0), "I(y) should be non-negative"


class TestBirmanSolomyakTest:
    """Test Birman-Solomyak trace-class property."""
    
    def test_coefficient_bounded(self):
        """Test that B_z coefficient is bounded."""
        operator = LogarithmicOperatorBirmanSolomyak()
        bs_test = operator.birman_solomyak_test(num_y_points=10, num_t_points=10)
        
        assert bs_test.uniformly_bounded, "B_z should be uniformly bounded"
        assert bs_test.B_z_max < 1e3, "B_z max should be reasonably bounded"
    
    def test_coefficient_decay(self):
        """Test that B_z decays exponentially."""
        operator = LogarithmicOperatorBirmanSolomyak(z=1.0+0.0j)
        bs_test = operator.birman_solomyak_test(num_y_points=10, num_t_points=10)
        
        assert bs_test.exponentially_decaying, "B_z should decay exponentially"
        assert bs_test.B_z_decay_rate > 0, "Decay rate should be positive"
    
    def test_trace_class_property(self):
        """Test that K_z ∈ S_{1,∞} (trace-class)."""
        operator = LogarithmicOperatorBirmanSolomyak()
        bs_test = operator.birman_solomyak_test(num_y_points=10, num_t_points=10)
        
        assert bs_test.trace_class, "Trace-class property should hold"
        assert bs_test.K_z_in_S1_infinity, "K_z should be in S_{1,∞}"
    
    def test_coefficient_computation(self):
        """Test coefficient computation for specific values."""
        operator = LogarithmicOperatorBirmanSolomyak()
        
        # Test a specific point
        y, t = 3.0, 1.0
        B_z = operator.birman_solomyak_coefficient(y, t)
        
        # Should be finite
        assert np.isfinite(B_z), "B_z should be finite"
        
        # Should match K_z / (y-t)
        K_z = operator.resolvent_difference_kernel(y, t)
        expected = K_z / (y - t)
        assert np.abs(B_z - expected) < 1e-10, "B_z should match K_z/(y-t)"


class TestCompleteAnalysis:
    """Test complete 7-step analysis."""
    
    def test_complete_analysis_runs(self):
        """Test that complete analysis runs without errors."""
        operator = LogarithmicOperatorBirmanSolomyak(
            y_min=-8.0,
            y_max=8.0,
            N=300
        )
        
        # Should not raise any exceptions
        result = operator.complete_analysis()
        
        assert isinstance(result, LogarithmicOperatorResult)
    
    def test_bks_program_applicable(self):
        """Test that BKS program is applicable."""
        operator = LogarithmicOperatorBirmanSolomyak()
        result = operator.complete_analysis()
        
        assert result.bks_program_applicable, "BKS program should be applicable"
    
    def test_riemann_hypothesis_path(self):
        """Test that Riemann Hypothesis path is validated."""
        operator = LogarithmicOperatorBirmanSolomyak()
        result = operator.complete_analysis()
        
        assert result.riemann_hypothesis_path, "RH path should be validated"
    
    def test_all_conditions_satisfied(self):
        """Test that all conditions are satisfied."""
        operator = LogarithmicOperatorBirmanSolomyak()
        result = operator.complete_analysis()
        
        # All three main conditions
        assert result.asymptotic.singularity_vanished, "Singularity should vanish"
        assert result.volterra.compactness_satisfied, "Compactness should be satisfied"
        assert result.birman_solomyak.K_z_in_S1_infinity, "Trace-class should hold"
    
    def test_result_structure(self):
        """Test that result has expected structure."""
        operator = LogarithmicOperatorBirmanSolomyak()
        result = operator.complete_analysis()
        
        assert hasattr(result, 'asymptotic')
        assert hasattr(result, 'volterra')
        assert hasattr(result, 'birman_solomyak')
        assert hasattr(result, 'bks_program_applicable')
        assert hasattr(result, 'riemann_hypothesis_path')


class TestParameterDependence:
    """Test dependence on various parameters."""
    
    def test_z_parameter_effect(self):
        """Test effect of different z values."""
        z_values = [0.5+0.5j, 1.0+0.5j, 1.5+0.5j]
        
        for z in z_values:
            operator = LogarithmicOperatorBirmanSolomyak(z=z, y_min=-5.0, y_max=5.0)
            result = operator.complete_analysis()
            
            # Should still satisfy conditions for Re(z) > 0
            assert result.bks_program_applicable, f"Should work for z={z}"
    
    def test_domain_size_effect(self):
        """Test effect of different domain sizes."""
        domains = [(-5.0, 5.0), (-10.0, 10.0), (-15.0, 15.0)]
        
        for y_min, y_max in domains:
            operator = LogarithmicOperatorBirmanSolomyak(
                y_min=y_min,
                y_max=y_max,
                N=300
            )
            result = operator.complete_analysis()
            
            # Should still satisfy conditions
            assert result.asymptotic.singularity_vanished, \
                f"Should work for domain [{y_min}, {y_max}]"
    
    def test_resolution_effect(self):
        """Test effect of different grid resolutions."""
        N_values = [200, 400, 600]
        
        for N in N_values:
            operator = LogarithmicOperatorBirmanSolomyak(N=N)
            result = operator.complete_analysis()
            
            # Should still satisfy conditions
            assert result.bks_program_applicable, f"Should work for N={N}"


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_potential_integral_stability(self):
        """Test stability of potential integral computation."""
        operator = LogarithmicOperatorBirmanSolomyak()
        
        # Various (t, y) pairs
        pairs = [(-5.0, 0.0), (-2.0, 2.0), (0.0, 5.0), (-8.0, 8.0)]
        
        for t, y in pairs:
            integral = operator.potential_integral(t, y)
            assert np.isfinite(integral), f"Integral should be finite for ({t}, {y})"
    
    def test_kernel_stability_extreme_values(self):
        """Test kernel stability for extreme parameter values."""
        operator = LogarithmicOperatorBirmanSolomyak(
            y_min=-15.0,
            y_max=15.0
        )
        
        # Test extreme separations
        y, t = 10.0, -10.0
        K_z = operator.resolvent_difference_kernel(y, t)
        assert np.isfinite(K_z), "Kernel should be finite for large separation"
    
    def test_coefficient_limit_behavior(self):
        """Test B_z behavior as (y-t) → 0."""
        operator = LogarithmicOperatorBirmanSolomyak()
        
        y = 2.0
        t_values = np.array([1.9, 1.95, 1.99, 1.999])
        
        B_z_values = [operator.birman_solomyak_coefficient(y, t) for t in t_values]
        
        # Should all be finite
        assert all(np.isfinite(B) for B in B_z_values), \
            "B_z should be finite as (y-t) → 0"


@pytest.mark.slow
class TestPerformance:
    """Performance tests (marked as slow)."""
    
    def test_large_domain_analysis(self):
        """Test analysis with large domain."""
        operator = LogarithmicOperatorBirmanSolomyak(
            y_min=-20.0,
            y_max=20.0,
            N=1000
        )
        
        result = operator.complete_analysis()
        assert result.bks_program_applicable
    
    def test_high_resolution_volterra(self):
        """Test Volterra test with high resolution."""
        operator = LogarithmicOperatorBirmanSolomyak(N=800)
        volterra = operator.volterra_L2_test(num_y_points=50)
        
        assert volterra.compactness_satisfied


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

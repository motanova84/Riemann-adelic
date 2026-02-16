#!/usr/bin/env python3
"""
Test Suite for H_mod Smoothed Potential Operator
================================================

Unit tests for the improved H_mod operator with smoothed potential.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
from operators.h_mod_smoothed_potential import (
    HModSmoothedPotential,
    PotentialAsymptotics,
    ResolventKernel
)


class TestPotentialFunction:
    """Tests for the potential V(y) = log(1+e^y)."""
    
    def test_potential_at_zero(self):
        """Test potential at y = 0."""
        op = HModSmoothedPotential()
        V_0 = op.potential(0.0)
        expected = np.log(2.0)  # log(1 + 1) = log(2)
        assert np.abs(V_0 - expected) < 1e-10
    
    def test_potential_positive_values(self):
        """Test that potential is always positive."""
        op = HModSmoothedPotential()
        y_vals = np.linspace(-10, 10, 100)
        V_vals = op.potential(y_vals)
        assert np.all(V_vals > 0)
    
    def test_potential_monotonic(self):
        """Test that potential is monotonically increasing."""
        op = HModSmoothedPotential()
        y_vals = np.linspace(-10, 10, 100)
        V_vals = op.potential(y_vals)
        # Check that differences are all positive
        assert np.all(np.diff(V_vals) > 0)
    
    def test_potential_asymptotic_left(self):
        """Test exponential decay as y → -∞."""
        op = HModSmoothedPotential()
        y = -10.0
        V_y = op.potential(y)
        # Should be approximately e^y for large negative y
        expected = np.exp(y)
        rel_error = np.abs(V_y - expected) / expected
        assert rel_error < 0.1  # Within 10%
    
    def test_potential_asymptotic_right(self):
        """Test linear growth as y → +∞."""
        op = HModSmoothedPotential()
        y = 10.0
        V_y = op.potential(y)
        # Should be approximately y for large positive y
        rel_error = np.abs(V_y - y) / y
        assert rel_error < 0.1  # Within 10%
    
    def test_potential_derivative(self):
        """Test that derivative V'(y) = e^y/(1+e^y) is correct."""
        op = HModSmoothedPotential()
        y = 0.0
        V_prime = op.potential_derivative(y)
        expected = 0.5  # e^0/(1+e^0) = 1/2
        assert np.abs(V_prime - expected) < 1e-10
    
    def test_potential_derivative_bounds(self):
        """Test that 0 < V'(y) < 1 for all y."""
        op = HModSmoothedPotential()
        y_vals = np.linspace(-10, 10, 100)
        V_prime = op.potential_derivative(y_vals)
        assert np.all(V_prime > 0)
        assert np.all(V_prime < 1)


class TestAsymptoticAnalysis:
    """Tests for asymptotic behavior analysis."""
    
    def test_analyze_asymptotics_returns_correct_type(self):
        """Test that analyze_asymptotics returns PotentialAsymptotics."""
        op = HModSmoothedPotential()
        result = op.analyze_asymptotics()
        assert isinstance(result, PotentialAsymptotics)
    
    def test_exponential_fit_left_region(self):
        """Test exponential fit in left region."""
        op = HModSmoothedPotential()
        asymptotics = op.analyze_asymptotics()
        a, b = asymptotics.exp_fit_left
        # Exponent should be close to 1
        assert np.abs(b - 1.0) < 0.2
        # Coefficient should be positive
        assert a > 0
    
    def test_linear_fit_right_region(self):
        """Test linear fit in right region."""
        op = HModSmoothedPotential()
        asymptotics = op.analyze_asymptotics()
        m, c = asymptotics.linear_fit_right
        # Slope should be close to 1
        assert np.abs(m - 1.0) < 0.2
    
    def test_asymptotics_data_shapes(self):
        """Test that asymptotic data has correct shapes."""
        op = HModSmoothedPotential()
        asymptotics = op.analyze_asymptotics(n_points_left=50, n_points_right=50)
        assert len(asymptotics.y_left) == 50
        assert len(asymptotics.V_left) == 50
        assert len(asymptotics.y_right) == 50
        assert len(asymptotics.V_right) == 50


class TestResolventKernel:
    """Tests for resolvent kernel computation."""
    
    def test_compute_resolvent_returns_correct_type(self):
        """Test that compute_resolvent_kernel returns ResolventKernel."""
        op = HModSmoothedPotential()
        result = op.compute_resolvent_kernel(n_y=20, n_t=20)
        assert isinstance(result, ResolventKernel)
    
    def test_resolvent_kernel_volterra_structure(self):
        """Test that kernel has Volterra structure (zero for t >= y)."""
        op = HModSmoothedPotential()
        kernel = op.compute_resolvent_kernel(n_y=30, n_t=30)
        
        # Check that B_z(y,t) = 0 for t >= y
        for i, y in enumerate(kernel.y_grid):
            for j, t in enumerate(kernel.t_grid):
                if t >= y:
                    assert np.abs(kernel.B_kernel[i, j]) < 1e-10
    
    def test_resolvent_kernel_finiteness(self):
        """Test that kernel values are finite."""
        op = HModSmoothedPotential()
        kernel = op.compute_resolvent_kernel(n_y=30, n_t=30)
        assert np.all(np.isfinite(kernel.B_kernel))
        assert np.all(np.isfinite(kernel.G_full))
        assert np.all(np.isfinite(kernel.G_free))
    
    def test_resolvent_kernel_shapes(self):
        """Test that kernel arrays have correct shapes."""
        op = HModSmoothedPotential()
        n_y, n_t = 25, 30
        kernel = op.compute_resolvent_kernel(n_y=n_y, n_t=n_t)
        assert kernel.B_kernel.shape == (n_y, n_t)
        assert kernel.G_full.shape == (n_y, n_t)
        assert kernel.G_free.shape == (n_y, n_t)
    
    def test_free_resolvent_decay(self):
        """Test that free resolvent decays with Re(z) > 0."""
        op = HModSmoothedPotential(z=0.5)
        kernel = op.compute_resolvent_kernel(n_y=30, n_t=30)
        
        # For fixed y, |G_0(y,t)| should decrease as t decreases (y-t increases)
        mid_idx = len(kernel.y_grid) // 2
        y_mid = kernel.y_grid[mid_idx]
        G0_row = np.abs(kernel.G_free[mid_idx, :])
        
        # Find indices where t < y_mid
        mask = kernel.t_grid < y_mid
        t_vals = kernel.t_grid[mask]
        G0_vals = G0_row[mask]
        
        if len(G0_vals) > 1:
            # Check that G0 increases as t approaches y (from left)
            assert np.all(np.diff(G0_vals) >= -1e-10)  # Allow small numerical errors


class TestVolterraProperty:
    """Tests for Volterra property and compactness."""
    
    def test_volterra_test_returns_dict(self):
        """Test that volterra test returns a dictionary."""
        op = HModSmoothedPotential()
        kernel = op.compute_resolvent_kernel(n_y=20, n_t=20)
        result = op.test_volterra_property(kernel)
        assert isinstance(result, dict)
        assert 'sup_norm' in result
        assert 'is_finite' in result
    
    def test_volterra_integral_finite(self):
        """Test that Volterra integral is finite."""
        op = HModSmoothedPotential(z=0.5)
        kernel = op.compute_resolvent_kernel(n_y=40, n_t=40)
        result = op.test_volterra_property(kernel, power=2.0)
        assert result['is_finite']
        assert np.isfinite(result['sup_norm'])
    
    def test_volterra_integral_positive(self):
        """Test that Volterra integral is non-negative."""
        op = HModSmoothedPotential(z=0.5)
        kernel = op.compute_resolvent_kernel(n_y=30, n_t=30)
        result = op.test_volterra_property(kernel, power=2.0)
        assert result['sup_norm'] >= 0
    
    def test_volterra_different_powers(self):
        """Test Volterra property with different powers."""
        op = HModSmoothedPotential(z=0.5)
        kernel = op.compute_resolvent_kernel(n_y=30, n_t=30)
        
        for p in [1.0, 2.0, 3.0]:
            result = op.test_volterra_property(kernel, power=p)
            assert result['is_finite']
            assert result['power'] == p


class TestCompactnessCriteria:
    """Tests for compactness criteria verification."""
    
    def test_verify_compactness_returns_dict(self):
        """Test that verify_compactness_criteria returns a dictionary."""
        op = HModSmoothedPotential()
        result = op.verify_compactness_criteria()
        assert isinstance(result, dict)
        assert 'is_volterra' in result
        assert 'compactness_plausible' in result
    
    def test_volterra_structure_verified(self):
        """Test that Volterra structure is verified."""
        op = HModSmoothedPotential()
        result = op.verify_compactness_criteria()
        assert result['is_volterra'] is True
    
    def test_kernel_bounded(self):
        """Test that kernel is bounded."""
        op = HModSmoothedPotential()
        result = op.verify_compactness_criteria()
        assert result['is_bounded']
        assert np.isfinite(result['sup_norm_B'])
    
    def test_compactness_plausible(self):
        """Test that compactness is plausible."""
        op = HModSmoothedPotential(z=0.5)
        result = op.verify_compactness_criteria()
        # This is the key test - compactness should be plausible
        assert result['compactness_plausible']


class TestCertificateGeneration:
    """Tests for QCAL certificate generation."""
    
    def test_generate_certificate_returns_dict(self):
        """Test that generate_certificate returns a dictionary."""
        op = HModSmoothedPotential()
        cert = op.generate_certificate()
        assert isinstance(cert, dict)
    
    def test_certificate_has_required_fields(self):
        """Test that certificate has all required QCAL fields."""
        op = HModSmoothedPotential()
        cert = op.generate_certificate()
        
        required_fields = [
            'protocol', 'version', 'signature',
            'qcal_constants', 'asymptotics',
            'compactness_analysis', 'verdict'
        ]
        
        for field in required_fields:
            assert field in cert
    
    def test_certificate_qcal_constants(self):
        """Test that certificate contains correct QCAL constants."""
        op = HModSmoothedPotential()
        cert = op.generate_certificate()
        
        qcal = cert['qcal_constants']
        assert qcal['f0_hz'] == 141.7001
        assert qcal['C'] == 244.36
        assert np.abs(qcal['kappa_pi'] - 2.577310) < 1e-6
        assert qcal['seal'] == 14170001
        assert qcal['code'] == 888
    
    def test_certificate_verdict_structure(self):
        """Test that certificate verdict has correct structure."""
        op = HModSmoothedPotential()
        cert = op.generate_certificate()
        
        verdict = cert['verdict']
        assert 'structural_blockage_removed' in verdict
        assert 'path_to_compactness' in verdict
        assert 'status' in verdict
        
        # Key claims should be validated
        assert verdict['structural_blockage_removed'] is True
        assert verdict['path_to_compactness'] == 'OPEN'


class TestIntegrationPotential:
    """Integration tests for potential integral."""
    
    def test_integral_potential_positive(self):
        """Test that integral of potential is positive for y > t."""
        op = HModSmoothedPotential()
        integral = op.integral_potential(-5.0, 0.0)
        assert integral > 0
    
    def test_integral_potential_zero_for_equal_limits(self):
        """Test that integral is zero when t = y."""
        op = HModSmoothedPotential()
        integral = op.integral_potential(0.0, 0.0)
        assert np.abs(integral) < 1e-10
    
    def test_integral_potential_monotonic(self):
        """Test that integral increases with upper limit."""
        op = HModSmoothedPotential()
        t = -2.0
        y_vals = np.linspace(t, 5.0, 10)
        integrals = [op.integral_potential(t, y) for y in y_vals]
        
        # Should be increasing
        assert np.all(np.diff(integrals) > 0)


@pytest.mark.slow
class TestNumericalConvergence:
    """Tests for numerical convergence with varying resolution."""
    
    def test_potential_convergence_with_resolution(self):
        """Test that potential values converge with finer grid."""
        y_test = 0.5
        
        N_values = [100, 200, 500]
        V_values = []
        
        for N in N_values:
            op = HModSmoothedPotential(N=N)
            V = op.potential(y_test)
            V_values.append(V)
        
        # Values should be similar (converged)
        rel_diffs = [abs(V_values[i+1] - V_values[i]) / V_values[i] 
                     for i in range(len(V_values)-1)]
        assert all(rd < 0.01 for rd in rel_diffs)
    
    def test_kernel_convergence_with_resolution(self):
        """Test that kernel sup norm converges with finer grid."""
        z_test = 0.5
        
        N_values = [20, 40, 60]
        sup_norms = []
        
        for N in N_values:
            op = HModSmoothedPotential(z=z_test)
            kernel = op.compute_resolvent_kernel(n_y=N, n_t=N)
            sup_norm = np.max(np.abs(kernel.B_kernel))
            sup_norms.append(sup_norm)
        
        # Should not vary too much
        rel_var = np.std(sup_norms) / np.mean(sup_norms)
        assert rel_var < 0.3  # Less than 30% variation


def test_main_function_runs():
    """Test that main() function executes without errors."""
    from operators.h_mod_smoothed_potential import main
    
    # Should complete without raising exceptions
    certificate = main()
    assert isinstance(certificate, dict)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

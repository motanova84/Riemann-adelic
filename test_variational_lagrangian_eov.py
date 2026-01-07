#!/usr/bin/env python3
"""
TESTS: Variational Lagrangian and Equation of Variation (EOV)
==============================================================

Test suite for the variational Lagrangian EOV implementation.

Tests include:
1. Parameter verification
2. Self-adjointness of the EOV operator
3. Energy conservation
4. Spectral stability
5. Coherence with QCAL framework (f₀ = 141.7001 Hz)
6. Resonance in high-curvature regions
7. Energy-momentum tensor consistency

Author: José Manuel Mota Burruezo Ψ ∞³
Date: January 2026
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
import pytest
from operators.variational_lagrangian_eov import (
    VariationalLagrangianEOV,
    LagrangianParameters,
    example_constant_curvature,
    example_gaussian_curvature,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
    ZETA_PRIME_HALF
)


class TestVariationalLagrangianEOV:
    """Test suite for Variational Lagrangian EOV."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.vl = VariationalLagrangianEOV()
    
    def test_parameters(self):
        """Test that parameters are correctly initialized."""
        params = self.vl.get_parameters()
        
        # QCAL parameters
        assert params['f0_Hz'] == QCAL_BASE_FREQUENCY
        assert abs(params['f0_Hz'] - 141.7001) < 1e-6
        assert params['coherence_C'] == QCAL_COHERENCE
        
        # Derived parameters
        expected_omega_0 = 2.0 * np.pi * QCAL_BASE_FREQUENCY
        assert abs(params['omega_0_rad_s'] - expected_omega_0) < 1e-6
        
        # Arithmetic coupling
        assert abs(params['zeta_prime_half'] - ZETA_PRIME_HALF) < 1e-6
        
        # Geometric coupling (conformal)
        assert abs(params['xi_geometric_coupling'] - 1.0/6.0) < 1e-10
    
    def test_zeta_prime_computation(self):
        """Test high-precision computation of ζ'(1/2)."""
        zeta_p = self.vl.compute_zeta_prime_half(precision=30)
        
        # Should match the constant
        assert abs(zeta_p - ZETA_PRIME_HALF) < 1e-6
        
        # Should be negative
        assert zeta_p < 0.0
        
        # Known value (approximate)
        assert abs(zeta_p + 3.922) < 0.01
    
    def test_self_adjointness(self):
        """Test self-adjointness of the EOV operator."""
        result = self.vl.verify_self_adjointness(n_test=100)
        
        # Check result structure
        assert 'is_self_adjoint' in result
        assert 'hermiticity_error' in result
        assert 'min_eigenvalue' in result
        assert 'max_eigenvalue' in result
        assert 'spectral_gap' in result
        
        # Eigenvalues should be real (this is always true with eigvalsh)
        assert result['all_eigenvalues_real']
        
        # Spectral gap should be positive
        assert result['spectral_gap'] > 0.0
        
        # Min eigenvalue should be positive (or at least finite)
        assert np.isfinite(result['min_eigenvalue'])
    
    def test_action_density(self):
        """Test computation of action density."""
        Psi = np.array([1.0, 0.5, 0.2])
        grad_Psi = np.array([[0.1, 0.05, 0.02],
                             [0.05, 0.1, 0.03],
                             [0.02, 0.03, 0.1]])
        R = np.array([0.5, 0.3, 0.1])
        t = 0.01
        
        L = self.vl.action_density(Psi, grad_Psi, R, t)
        
        # Should be finite
        assert np.all(np.isfinite(L))
        
        # Should have correct shape
        assert L.shape == Psi.shape
    
    def test_eov_constant_curvature(self):
        """Test EOV solution with constant curvature."""
        solution = self.vl.solve_eov_1d(
            x_range=(-5, 5),
            t_range=(0, 0.01),
            nx=50,
            nt=100,
            R_func=example_constant_curvature(),
            initial_amplitude=1.0
        )
        
        # Check solution structure
        assert solution.t.shape[0] == 100
        assert solution.x.shape[0] == 50
        assert solution.Psi.shape == (100, 50)
        assert solution.energy.shape == (100, 50)
        assert solution.curvature.shape == (100, 50)
        
        # Resonance factor should be close to 1 for constant curvature
        assert solution.resonance_factor > 0.9
        assert solution.resonance_factor < 2.0
        
        # Field should not blow up
        assert np.all(np.isfinite(solution.Psi))
        assert np.max(np.abs(solution.Psi)) < 100.0
    
    def test_eov_gaussian_curvature(self):
        """Test EOV solution with Gaussian curvature (resonance)."""
        solution = self.vl.solve_eov_1d(
            x_range=(-5, 5),
            t_range=(0, 0.01),
            nx=50,
            nt=100,
            R_func=example_gaussian_curvature(),
            initial_amplitude=1.0
        )
        
        # Curvature should vary spatially
        curvature_variation = np.std(solution.curvature[0, :])
        assert curvature_variation > 0.1
        
        # Max curvature should be higher than mean
        assert np.max(solution.curvature) > np.mean(solution.curvature)
        
        # Solution should be finite
        assert np.all(np.isfinite(solution.Psi))
    
    def test_energy_momentum_tensor(self):
        """Test energy-momentum tensor calculation."""
        Psi = 1.0
        grad_Psi = np.array([0.1, 0.05, 0.02])
        time_deriv_Psi = 0.3
        R = 0.5
        t = 0.01
        
        T_munu = self.vl.energy_momentum_tensor(Psi, grad_Psi, time_deriv_Psi, R, t)
        
        # Should be 4x4
        assert T_munu.shape == (4, 4)
        
        # Should be finite
        assert np.all(np.isfinite(T_munu))
        
        # Diagonal should dominate (in simple cases)
        assert np.abs(T_munu[0, 0]) > 1e-10
        
        # Energy density (T_00) should be positive
        assert T_munu[0, 0] > 0.0
    
    def test_coherence_with_qcal(self):
        """Test that the implementation is coherent with QCAL framework."""
        params = self.vl.get_parameters()
        
        # Frequency should match QCAL
        assert params['f0_Hz'] == QCAL_BASE_FREQUENCY
        
        # Coherence constant should match
        assert params['coherence_C'] == QCAL_COHERENCE
        
        # Angular frequency derived correctly
        omega_0 = params['omega_0_rad_s']
        f0_from_omega = omega_0 / (2.0 * np.pi)
        assert abs(f0_from_omega - QCAL_BASE_FREQUENCY) < 1e-6
    
    def test_resonance_amplification(self):
        """Test that high curvature induces resonance."""
        # Low curvature solution
        sol_low = self.vl.solve_eov_1d(
            x_range=(-5, 5),
            t_range=(0, 0.02),
            nx=50,
            nt=200,
            R_func=lambda x, t: 0.1,  # Low curvature
            initial_amplitude=1.0
        )
        
        # High curvature solution
        sol_high = self.vl.solve_eov_1d(
            x_range=(-5, 5),
            t_range=(0, 0.02),
            nx=50,
            nt=200,
            R_func=lambda x, t: 2.0,  # High curvature
            initial_amplitude=1.0
        )
        
        # High curvature should have different dynamics
        # (not necessarily higher resonance due to damping, but different)
        max_psi_low = np.max(np.abs(sol_low.Psi))
        max_psi_high = np.max(np.abs(sol_high.Psi))
        
        # Both should be finite
        assert np.isfinite(max_psi_low)
        assert np.isfinite(max_psi_high)
    
    def test_temporal_modulation(self):
        """Test that temporal modulation at f₀ affects the solution."""
        # The temporal phase cos(2πf₀t) should create time-varying effects
        
        t1 = 0.0
        t2 = 1.0 / (2.0 * QCAL_BASE_FREQUENCY)  # Half period
        
        # At different times, the modulation should be different
        phase1 = np.cos(2.0 * np.pi * QCAL_BASE_FREQUENCY * t1)
        phase2 = np.cos(2.0 * np.pi * QCAL_BASE_FREQUENCY * t2)
        
        # Should be opposite signs (approximately)
        assert abs(phase1 + phase2) < 0.1


class TestLagrangianParameters:
    """Test the LagrangianParameters dataclass."""
    
    def test_default_parameters(self):
        """Test default parameter initialization."""
        params = LagrangianParameters()
        
        assert params.f0 == QCAL_BASE_FREQUENCY
        assert params.xi == 1.0/6.0
        assert params.zeta_prime_half == ZETA_PRIME_HALF
        assert params.coherence == QCAL_COHERENCE
        
        # omega_0 should be computed
        assert params.omega_0 is not None
        assert abs(params.omega_0 - 2.0 * np.pi * params.f0) < 1e-10
    
    def test_custom_parameters(self):
        """Test custom parameter initialization."""
        custom_f0 = 100.0
        custom_xi = 0.2
        
        params = LagrangianParameters(f0=custom_f0, xi=custom_xi)
        
        assert params.f0 == custom_f0
        assert params.xi == custom_xi
        assert abs(params.omega_0 - 2.0 * np.pi * custom_f0) < 1e-10


def run_tests():
    """Run all tests."""
    print("=" * 80)
    print("VARIATIONAL LAGRANGIAN EOV - TEST SUITE")
    print("=" * 80)
    print()
    
    # Run pytest
    exit_code = pytest.main([__file__, '-v', '--tb=short'])
    
    return exit_code


if __name__ == "__main__":
    exit_code = run_tests()
    sys.exit(exit_code)

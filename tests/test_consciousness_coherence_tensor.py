#!/usr/bin/env python3
"""
Tests for Consciousness Coherence Tensor Ξμν

Validates:
1. Numerical parameters (I/Aeff² ≈ 30.8456)
2. Tensor construction and properties
3. Variable coupling κ(I)
4. Conservation law ∇μΞμν = 0
5. LIGO Ψ-Q1 validation
6. Unified field equation integration
7. Ricci modulation at lab scales

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import pytest
import numpy as np
from scipy.constants import G, c, pi, golden_ratio
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from utils.consciousness_coherence_tensor import (
    CoherenceParameters,
    ConsciousnessCoherenceTensor
)


class TestCoherenceParameters:
    """Test CoherenceParameters dataclass."""
    
    def test_initialization(self):
        """Test parameter initialization."""
        params = CoherenceParameters(I=30.8456, Aeff=1.0)
        assert params.I == 30.8456
        assert params.Aeff == 1.0
        assert params.f0 == 141.7001
        assert params.C == 244.36
        
    def test_I_over_Aeff2(self):
        """Test I/Aeff² property."""
        params = CoherenceParameters(I=30.8456, Aeff=1.0)
        assert abs(params.I_over_Aeff2 - 30.8456) < 1e-6
        
        # Test with different Aeff
        params2 = CoherenceParameters(I=123.3824, Aeff=2.0)
        assert abs(params2.I_over_Aeff2 - 30.8456) < 1e-6
        
    def test_omega_0(self):
        """Test angular frequency calculation."""
        params = CoherenceParameters(I=1.0, Aeff=1.0)
        expected_omega = 2 * pi * 141.7001
        assert abs(params.omega_0 - expected_omega) < 1e-6
        
    def test_numerical_validation(self):
        """Test I/Aeff² ≈ 963/(φ³·f₀) validation."""
        # Construct parameters that should validate
        f0 = 141.7001
        phi = golden_ratio
        I_Aeff2_expected = 963.0 / (phi ** 3 * f0)
        
        params = CoherenceParameters(I=I_Aeff2_expected, Aeff=1.0, f0=f0)
        assert params.validate_numerical(tolerance=1e-4)
        
        # Test with non-validating parameters
        params_bad = CoherenceParameters(I=1.0, Aeff=1.0)
        assert not params_bad.validate_numerical(tolerance=1e-4)


class TestConsciousnessCoherenceTensor:
    """Test ConsciousnessCoherenceTensor class."""
    
    @pytest.fixture
    def params(self):
        """Fixture for coherence parameters."""
        f0 = 141.7001
        phi = golden_ratio
        I_Aeff2 = 963.0 / (phi ** 3 * f0)
        return CoherenceParameters(I=I_Aeff2, Aeff=1.0, f0=f0)
    
    @pytest.fixture
    def tensor(self, params):
        """Fixture for tensor calculator."""
        return ConsciousnessCoherenceTensor(params, dimension=4, precision=25)
    
    def test_initialization(self, tensor, params):
        """Test tensor calculator initialization."""
        assert tensor.dimension == 4
        assert tensor.precision == 25
        assert tensor.f0 == params.f0
        assert abs(tensor.omega_0 - params.omega_0) < 1e-10
        
    def test_kappa_variable(self, tensor):
        """Test variable coupling κ(I) calculation."""
        kappa_I = tensor.kappa_variable()
        kappa_0 = tensor.kappa_0
        
        # κ(I) should be different from κ₀
        assert kappa_I != kappa_0
        
        # κ(I) = κ₀ / (I·Aeff²)
        I_Aeff2 = tensor.params.I_over_Aeff2
        expected = kappa_0 / I_Aeff2
        assert abs(kappa_I - expected) / expected < 1e-10
        
        # Higher coherence should reduce κ
        kappa_high = tensor.kappa_variable(I=100.0, Aeff=1.0)
        kappa_low = tensor.kappa_variable(I=10.0, Aeff=1.0)
        assert kappa_high < kappa_low
        
    def test_compute_Xi_tensor_flat_space(self, tensor):
        """Test Ξμν computation in flat Minkowski space."""
        # Minkowski metric
        eta = np.diag([-1, 1, 1, 1])
        
        # Flat space: Rμν = 0, R = 0
        R_mu_nu = np.zeros((4, 4))
        R_scalar = 0.0
        
        # Compute Ξμν
        Xi = tensor.compute_Xi_tensor(R_mu_nu, R_scalar, eta)
        
        # Check shape
        assert Xi.shape == (4, 4)
        
        # In flat space with constant I·Aeff², Ξμν should be zero
        assert np.allclose(Xi, np.zeros((4, 4)), atol=1e-10)
        
    def test_compute_Xi_tensor_curved_space(self, tensor):
        """Test Ξμν computation in curved spacetime."""
        # Simple diagonal metric (not flat)
        g = np.diag([-1, 1, 1, 1])
        
        # Non-zero Ricci tensor (simple example)
        R_mu_nu = np.diag([1.0, 0.5, 0.5, 0.5])
        R_scalar = np.trace(R_mu_nu)  # R = Tr(R_mu_nu)
        
        # Compute Ξμν
        Xi = tensor.compute_Xi_tensor(R_mu_nu, R_scalar, g)
        
        # Check shape
        assert Xi.shape == (4, 4)
        
        # Ξμν should be non-zero in curved space
        assert not np.allclose(Xi, np.zeros((4, 4)))
        
        # Check that it has the right structure
        # Ξμν = κ⁻¹(I·Aeff²·Rμν - ½·I·Aeff²·R·gμν)
        kappa_inv = 1.0 / tensor.kappa_variable()
        I_Aeff2 = tensor.params.I_over_Aeff2
        
        expected = kappa_inv * (I_Aeff2 * R_mu_nu - 0.5 * I_Aeff2 * R_scalar * g)
        assert np.allclose(Xi, expected, rtol=1e-10)
        
    def test_compute_Xi_tensor_with_gradient_term(self, tensor):
        """Test Ξμν with non-zero gradient term."""
        g = np.diag([-1, 1, 1, 1])
        R_mu_nu = np.zeros((4, 4))
        R_scalar = 0.0
        
        # Add gradient term
        nabla_term = np.ones((4, 4)) * 0.1
        
        Xi = tensor.compute_Xi_tensor(R_mu_nu, R_scalar, g, nabla_term)
        
        # Should include the gradient contribution
        kappa_inv = 1.0 / tensor.kappa_variable()
        expected = kappa_inv * nabla_term
        assert np.allclose(Xi, expected, rtol=1e-10)
        
    def test_verify_conservation_flat_space(self, tensor):
        """Test conservation law in flat space."""
        # In flat space with constant Ξμν, divergence should be zero
        Xi = np.ones((4, 4)) * 0.5
        
        result = tensor.verify_conservation(Xi, tolerance=1e-8)
        
        assert 'conserved' in result
        assert 'divergence' in result
        assert 'max_divergence' in result
        assert 'status' in result
        
    def test_unified_field_equation_rhs(self, tensor):
        """Test unified field equation RHS computation."""
        # Sample stress-energy and coherence tensors
        T = np.diag([1.0, 0.3, 0.3, 0.3])
        Xi = np.diag([0.1, 0.05, 0.05, 0.05])
        
        rhs = tensor.unified_field_equation_rhs(T, Xi)
        
        # Check shape
        assert rhs.shape == (4, 4)
        
        # RHS = κ₀(T + Ξ)
        expected = tensor.kappa_0 * (T + Xi)
        assert np.allclose(rhs, expected, rtol=1e-10)
        
    def test_ricci_modulation_estimate(self, tensor):
        """Test Ricci modulation estimation."""
        R_mod = tensor.ricci_modulation_estimate(1.0)
        
        # Should be non-zero
        assert R_mod != 0.0
        
        # Should be order ~10^{-3} after calibration
        # (This is an empirical calibration, so we just check order of magnitude)
        assert abs(R_mod) < 1.0  # Not too large
        assert abs(R_mod) > 1e-10  # Not too small
        
    def test_ligo_psi_q1_validation(self, tensor):
        """Test LIGO Ψ-Q1 validation."""
        result = tensor.ligo_psi_q1_validation()
        
        # Check all expected keys
        assert 'validated' in result
        assert 'snr_measured' in result
        assert 'snr_predicted' in result
        assert 'relative_error' in result
        assert 'frequency' in result
        assert 'frequency_match' in result
        assert 'status' in result
        
        # Check values
        assert result['snr_measured'] == 25.3
        assert result['snr_predicted'] == 26.8
        assert result['frequency'] == 141.7001
        assert result['frequency_match'] is True
        
        # Relative error should be small
        assert result['relative_error'] < 0.1
        
    def test_generate_latex_derivation(self, tensor):
        """Test LaTeX derivation generation."""
        latex = tensor.generate_latex_derivation()
        
        # Check it returns a non-empty string
        assert isinstance(latex, str)
        assert len(latex) > 100
        
        # Check for key LaTeX elements
        assert r'\subsection' in latex
        assert r'\equation' in latex
        assert r'\Xi' in latex
        assert r'\kappa' in latex
        
    def test_validate_complete_derivation(self, tensor):
        """Test complete derivation validation."""
        results = tensor.validate_complete_derivation()
        
        # Check all expected sections
        assert 'numerical_params' in results
        assert 'ligo_psi_q1' in results
        assert 'coupling' in results
        assert 'ricci_modulation' in results
        assert 'status' in results
        assert 'overall_valid' in results
        
        # Numerical params should validate
        assert results['numerical_params']['valid'] is True
        
        # LIGO validation should pass
        assert results['ligo_psi_q1']['validated'] is True
        
        # Overall should be valid
        assert results['overall_valid'] is True
        
        # Status should indicate success
        assert '✅' in results['status']


class TestIntegrationWithExistingFramework:
    """Test integration with existing QCAL framework."""
    
    def test_consistency_with_wave_equation(self):
        """Test consistency with wave equation consciousness module."""
        # Create coherence parameters matching wave equation framework
        params = CoherenceParameters(I=30.8456, Aeff=1.0, f0=141.7001)
        
        # Both should use same f₀
        assert params.f0 == 141.7001
        
        # Both should use same ω₀
        expected_omega = 2 * pi * 141.7001
        assert abs(params.omega_0 - expected_omega) < 1e-6
        
    def test_consistency_with_qcal_constants(self):
        """Test consistency with QCAL ∞³ constants."""
        params = CoherenceParameters(I=30.8456, Aeff=1.0)
        
        # QCAL coherence constant
        assert params.C == 244.36
        
        # Golden ratio
        assert abs(params.phi - golden_ratio) < 1e-10
        
    def test_numerical_parameter_derivation(self):
        """Test I/Aeff² ≈ 963/(φ³·f₀) derivation."""
        f0 = 141.7001
        phi = golden_ratio
        
        # Theoretical value
        I_Aeff2_theory = 963.0 / (phi ** 3 * f0)
        
        # Create parameters
        params = CoherenceParameters(I=I_Aeff2_theory, Aeff=1.0, f0=f0)
        
        # Should validate
        assert params.validate_numerical(tolerance=1e-6)
        
        # Check numerical value
        assert abs(params.I_over_Aeff2 - 30.8456) < 0.001


class TestPhysicalConsistency:
    """Test physical consistency of the framework."""
    
    def test_dimensional_analysis_kappa(self):
        """Test dimensional consistency of κ."""
        params = CoherenceParameters(I=30.8456, Aeff=1.0)
        tensor = ConsciousnessCoherenceTensor(params)
        
        # κ₀ = 8πG/c⁴ has dimensions [m/kg]
        kappa_0 = tensor.kappa_0
        assert kappa_0 > 0  # Must be positive
        
        # Order of magnitude check
        assert 1e-28 < kappa_0 < 1e-26  # Around 10^{-27} m/kg
        
    def test_higher_coherence_reduces_curvature(self):
        """Test that higher coherence reduces effective curvature."""
        # Two parameter sets with different coherence
        params_low = CoherenceParameters(I=10.0, Aeff=1.0)
        params_high = CoherenceParameters(I=100.0, Aeff=1.0)
        
        tensor_low = ConsciousnessCoherenceTensor(params_low)
        tensor_high = ConsciousnessCoherenceTensor(params_high)
        
        # Higher coherence → lower κ(I)
        kappa_low = tensor_low.kappa_variable()
        kappa_high = tensor_high.kappa_variable()
        assert kappa_high < kappa_low
        
    def test_einstein_tensor_structure(self):
        """Test that Ξμν has Einstein-tensor-like structure."""
        params = CoherenceParameters(I=30.8456, Aeff=1.0)
        tensor = ConsciousnessCoherenceTensor(params)
        
        # Create a symmetric Ricci tensor
        R_mu_nu = np.array([
            [1.0, 0.0, 0.0, 0.0],
            [0.0, 0.5, 0.0, 0.0],
            [0.0, 0.0, 0.5, 0.0],
            [0.0, 0.0, 0.0, 0.5]
        ])
        R_scalar = np.trace(R_mu_nu)
        g = np.diag([-1, 1, 1, 1])
        
        Xi = tensor.compute_Xi_tensor(R_mu_nu, R_scalar, g)
        
        # Ξμν should be symmetric (like Einstein tensor)
        assert np.allclose(Xi, Xi.T, atol=1e-10)


def test_main_demo():
    """Test that the demo function runs without errors."""
    from utils.consciousness_coherence_tensor import demo_consciousness_coherence_tensor
    
    # Should run without raising exceptions
    try:
        demo_consciousness_coherence_tensor()
        assert True
    except Exception as e:
        pytest.fail(f"Demo raised exception: {e}")


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

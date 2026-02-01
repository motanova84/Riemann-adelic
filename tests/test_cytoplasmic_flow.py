"""
Tests for Cytoplasmic Flow Model

This test suite validates the cytoplasmic flow model implementation,
including Navier-Stokes equations in the Stokes regime, Reynolds number
calculations, and the Hilbert-Pólya operator construction.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
from utils.cytoplasmic_flow_model import (
    CytoplasmicFlowModel,
    FlowParameters,
    FlowRegime,
    HilbertPolyaOperator,
    F0_FREQUENCY
)


class TestFlowParameters:
    """Tests for FlowParameters dataclass."""
    
    def test_reynolds_number_calculation(self):
        """Test Reynolds number calculation."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=1e-6,
            length_scale=1e-6,
            velocity=1e-8
        )
        
        Re = params.reynolds_number
        expected_Re = 1e-8  # (1e-8 * 1e-6) / 1e-6
        
        assert abs(Re - expected_Re) < 1e-15
    
    def test_dynamic_viscosity(self):
        """Test dynamic viscosity calculation."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=1e-6,
            length_scale=1e-6,
            velocity=1e-8
        )
        
        mu = params.dynamic_viscosity
        expected_mu = 1000.0 * 1e-6  # ρ * ν
        
        assert abs(mu - expected_mu) < 1e-10
    
    def test_flow_regime_stokes(self):
        """Test Stokes regime identification."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=1e-6,
            length_scale=1e-6,
            velocity=1e-8
        )
        
        assert params.regime == FlowRegime.STOKES
    
    def test_flow_regime_laminar(self):
        """Test laminar regime identification."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=1e-3,
            length_scale=0.1,
            velocity=1.0
        )
        
        # Re = (1.0 * 0.1) / 1e-3 = 100
        assert params.regime == FlowRegime.LAMINAR
    
    def test_flow_regime_turbulent(self):
        """Test turbulent regime identification."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=1e-6,
            length_scale=1.0,
            velocity=10.0
        )
        
        # Re = (10.0 * 1.0) / 1e-6 = 1e7 >> 4000
        assert params.regime == FlowRegime.TURBULENT


class TestCytoplasmicFlowModel:
    """Tests for CytoplasmicFlowModel class."""
    
    @pytest.fixture
    def cytoplasmic_model(self):
        """Create a standard cytoplasmic flow model."""
        return CytoplasmicFlowModel(
            density=1000.0,
            kinematic_viscosity=1e-6,
            length_scale=1e-6,
            velocity=1e-8
        )
    
    def test_initialization(self, cytoplasmic_model):
        """Test model initialization."""
        assert cytoplasmic_model.params.density == 1000.0
        assert cytoplasmic_model.params.kinematic_viscosity == 1e-6
        assert cytoplasmic_model.params.length_scale == 1e-6
        assert cytoplasmic_model.params.velocity == 1e-8
    
    def test_reynolds_number(self, cytoplasmic_model):
        """Test Reynolds number for cytoplasmic flow."""
        Re = cytoplasmic_model.get_reynolds_number()
        
        # Should be very small (Stokes regime)
        assert Re < 0.1
        assert Re > 0
    
    def test_regime_is_stokes(self, cytoplasmic_model):
        """Test that cytoplasm is in Stokes regime."""
        regime = cytoplasmic_model.params.regime
        assert regime == FlowRegime.STOKES
    
    def test_smooth_solution_exists(self, cytoplasmic_model):
        """Test that smooth solution exists in Stokes regime."""
        has_smooth = cytoplasmic_model.has_smooth_solution()
        assert has_smooth is True
    
    def test_flow_coherence_high(self, cytoplasmic_model):
        """Test that flow coherence is high in Stokes regime."""
        coherence = cytoplasmic_model.compute_flow_coherence()
        
        # In Stokes regime, coherence should be very close to 1
        assert coherence > 0.99
        assert coherence <= 1.0
    
    def test_flow_coherence_decreases_with_reynolds(self):
        """Test that coherence decreases as Reynolds number increases."""
        # Low Re model
        low_re_model = CytoplasmicFlowModel(
            velocity=1e-8
        )
        
        # Higher Re model (but still laminar)
        high_re_model = CytoplasmicFlowModel(
            velocity=1e-6
        )
        
        low_coherence = low_re_model.compute_flow_coherence()
        high_coherence = high_re_model.compute_flow_coherence()
        
        assert low_coherence > high_coherence
    
    def test_eigenfrequencies_count(self, cytoplasmic_model):
        """Test that correct number of eigenfrequencies are computed."""
        freqs = cytoplasmic_model.compute_eigenfrequencies(n_modes=5)
        assert len(freqs) == 5
        
        freqs_10 = cytoplasmic_model.compute_eigenfrequencies(n_modes=10)
        assert len(freqs_10) == 10
    
    def test_eigenfrequencies_positive(self, cytoplasmic_model):
        """Test that all eigenfrequencies are positive."""
        freqs = cytoplasmic_model.compute_eigenfrequencies(n_modes=10)
        
        for freq in freqs:
            assert freq > 0
    
    def test_eigenfrequencies_increasing(self, cytoplasmic_model):
        """Test that eigenfrequencies are in increasing order."""
        freqs = cytoplasmic_model.compute_eigenfrequencies(n_modes=10)
        
        for i in range(len(freqs) - 1):
            assert freqs[i+1] > freqs[i]
    
    def test_fundamental_frequency(self, cytoplasmic_model):
        """Test that fundamental frequency matches expected value."""
        freqs = cytoplasmic_model.compute_eigenfrequencies(n_modes=5)
        
        # First frequency should be f0
        expected_f0 = float(F0_FREQUENCY)
        assert abs(freqs[0] - expected_f0) < 0.01
    
    def test_hilbert_polya_operator_exists(self, cytoplasmic_model):
        """Test that Hilbert-Pólya operator exists in Stokes regime."""
        operator = cytoplasmic_model.construct_hilbert_polya_operator()
        
        assert operator.exists is True
        assert operator.is_hermitian is True
    
    def test_hilbert_polya_medium(self, cytoplasmic_model):
        """Test that operator is identified as biological."""
        operator = cytoplasmic_model.construct_hilbert_polya_operator()
        
        assert "BIOLÓGICO" in operator.medium or "TEJIDO" in operator.medium
    
    def test_riemann_connection(self, cytoplasmic_model):
        """Test Riemann connection verification."""
        operator = cytoplasmic_model.construct_hilbert_polya_operator()
        
        # Should verify connection through fundamental frequency
        assert operator.verify_riemann_connection() is True
    
    def test_demonstrate_riemann_connection(self, cytoplasmic_model):
        """Test demonstration results structure."""
        results = cytoplasmic_model.demonstrate_riemann_connection()
        
        # Check all expected keys are present
        expected_keys = [
            "reynolds_number",
            "regime",
            "smooth_solution_exists",
            "flow_coherence",
            "hilbert_polya_exists",
            "is_hermitian",
            "medium",
            "fundamental_frequency",
            "eigenfrequencies",
            "riemann_connection_verified"
        ]
        
        for key in expected_keys:
            assert key in results
    
    def test_demonstration_reynolds_matches(self, cytoplasmic_model):
        """Test that demonstration Reynolds matches direct calculation."""
        results = cytoplasmic_model.demonstrate_riemann_connection()
        direct_re = cytoplasmic_model.get_reynolds_number()
        
        assert abs(results["reynolds_number"] - direct_re) < 1e-15
    
    def test_demonstration_coherence_matches(self, cytoplasmic_model):
        """Test that demonstration coherence matches direct calculation."""
        results = cytoplasmic_model.demonstrate_riemann_connection()
        direct_coherence = cytoplasmic_model.compute_flow_coherence()
        
        assert abs(results["flow_coherence"] - direct_coherence) < 1e-10


class TestHilbertPolyaOperator:
    """Tests for HilbertPolyaOperator."""
    
    def test_riemann_verification_passes(self):
        """Test that verification passes with correct frequency."""
        operator = HilbertPolyaOperator(
            exists=True,
            is_hermitian=True,
            medium="Test medium",
            fundamental_frequency=141.7001,
            eigenfrequencies=[141.7001, 210.7, 250.7]
        )
        
        assert operator.verify_riemann_connection() is True
    
    def test_riemann_verification_fails(self):
        """Test that verification fails with wrong frequency."""
        operator = HilbertPolyaOperator(
            exists=True,
            is_hermitian=True,
            medium="Test medium",
            fundamental_frequency=100.0,  # Wrong frequency
            eigenfrequencies=[100.0, 200.0, 300.0]
        )
        
        assert operator.verify_riemann_connection() is False


class TestEdgeCases:
    """Tests for edge cases and boundary conditions."""
    
    def test_zero_velocity(self):
        """Test model with zero velocity."""
        model = CytoplasmicFlowModel(velocity=0.0)
        
        Re = model.get_reynolds_number()
        assert Re == 0.0
        assert model.has_smooth_solution() is True
    
    def test_very_high_viscosity(self):
        """Test model with very high viscosity."""
        model = CytoplasmicFlowModel(
            kinematic_viscosity=1.0  # Very viscous
        )
        
        Re = model.get_reynolds_number()
        assert Re < 1e-5
        assert model.params.regime == FlowRegime.STOKES
    
    def test_print_demonstration_runs(self, capsys):
        """Test that print_demonstration runs without errors."""
        model = CytoplasmicFlowModel()
        
        # Should not raise any exceptions
        model.print_demonstration()
        
        # Check that output was produced
        captured = capsys.readouterr()
        assert len(captured.out) > 0
        assert "NAVIER-STOKES" in captured.out
        assert "HILBERT-PÓLYA" in captured.out


class TestIntegration:
    """Integration tests."""
    
    def test_full_workflow(self):
        """Test complete workflow from creation to demonstration."""
        # Create model
        model = CytoplasmicFlowModel()
        
        # Check Reynolds number
        Re = model.get_reynolds_number()
        assert Re < 0.1
        
        # Check smooth solution
        assert model.has_smooth_solution()
        
        # Check coherence
        coherence = model.compute_flow_coherence()
        assert coherence > 0.99
        
        # Construct operator
        operator = model.construct_hilbert_polya_operator()
        assert operator.exists
        assert operator.is_hermitian
        
        # Verify connection
        assert operator.verify_riemann_connection()
        
        # Get full results
        results = model.demonstrate_riemann_connection()
        assert results["riemann_connection_verified"]


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

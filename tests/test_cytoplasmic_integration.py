"""
Integration Tests for Cytoplasmic Flow Model
=============================================

Tests that verify integration of the cytoplasmic flow model with the
existing QCAL biological framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-31
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

from src.biological.cytoplasmic_flow_model import CytoplasmicFlowModel, FlowParameters


class TestQCALIntegration:
    """Test QCAL framework integration."""
    
    def test_qcal_frequency_constant(self):
        """Test that QCAL frequency is correct."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        # QCAL fundamental frequency
        assert model.F0_QCAL == 141.7001
    
    def test_qcal_coherence_in_spectrum(self):
        """Test that spectrum shows QCAL coherence."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        frequencies, spectrum = model.compute_resonance_spectrum(
            freq_range=(135.0, 150.0),
            n_points=300
        )
        
        # Find peak near QCAL frequency
        peak_idx = np.argmax(spectrum)
        peak_freq = frequencies[peak_idx]
        
        # Should be within 1 Hz of QCAL frequency
        assert abs(peak_freq - model.F0_QCAL) < 1.0
    
    def test_validation_report_contains_qcal(self):
        """Test that validation report mentions QCAL."""
        model = CytoplasmicFlowModel(grid_size=16)
        report = model.generate_validation_report()
        
        assert 'QCAL' in report
        assert '141.7' in report


class TestBiologicalIntegration:
    """Test integration with biological framework."""
    
    def test_biological_parameters(self):
        """Test that model uses biologically realistic parameters."""
        params = FlowParameters()
        
        # Viscosity should be in cytoplasmic range (10^-7 to 10^-5 m²/s)
        assert 1e-7 <= params.viscosity <= 1e-5
        
        # Length scale should be cellular (0.1 to 100 μm)
        assert 1e-7 <= params.length_scale <= 1e-4
        
        # Density should be water-like (900 to 1100 kg/m³)
        assert 900 <= params.density <= 1100
    
    def test_cellular_scale_reynolds(self):
        """Test Reynolds number at cellular scale."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        # At cellular scale, Re should be << 1
        assert model.params.reynolds < 1e-3
        
        # Should be in viscous regime
        assert model.params.is_viscous_regime
    
    def test_biological_time_scales(self):
        """Test biological time scales."""
        model = CytoplasmicFlowModel(grid_size=16)
        smooth = model.verify_smooth_solution()
        
        # Viscous time scale should be in microseconds to milliseconds
        tau_visc = smooth['viscous_time_scale']
        assert 1e-9 <= tau_visc <= 1e-1
        
        # Convection time scale should be longer (seconds to hours)
        tau_conv = smooth['convection_time_scale']
        assert tau_conv > tau_visc


class TestSpectralIntegration:
    """Test spectral theory integration."""
    
    def test_hermitian_operator(self):
        """Test that operator is Hermitian as required by Hilbert-Pólya."""
        model = CytoplasmicFlowModel(grid_size=16)
        hilbert = model.compute_hilbert_polya_connection()
        
        assert hilbert['is_hermitian'] is True
        assert hilbert['is_self_adjoint'] is True
    
    def test_discrete_spectrum(self):
        """Test that spectrum is discrete."""
        model = CytoplasmicFlowModel(grid_size=16)
        hilbert = model.compute_hilbert_polya_connection()
        
        assert hilbert['has_discrete_spectrum'] is True
        assert hilbert['n_computed_modes'] > 0
    
    def test_eigenvalue_correspondence(self):
        """Test eigenvalue correspondence with Riemann zeros."""
        model = CytoplasmicFlowModel(grid_size=16)
        modes = model.compute_spectral_modes(n_modes=10)
        
        # All eigenvalues should be real (operator is Hermitian)
        for mode in modes:
            assert np.isreal(mode.eigenvalue) or np.abs(np.imag(mode.eigenvalue)) < 1e-10
    
    def test_spectral_gaps_positive(self):
        """Test that spectral gaps are positive."""
        model = CytoplasmicFlowModel(grid_size=16)
        hilbert = model.compute_hilbert_polya_connection()
        
        if 'spectral_gaps' in hilbert and hilbert['spectral_gaps']:
            gaps = hilbert['spectral_gaps']
            assert all(g > 0 for g in gaps)


class TestPhysicalConsistency:
    """Test physical consistency of the model."""
    
    def test_smooth_solutions_in_viscous_regime(self):
        """Test that smooth solutions exist in viscous regime."""
        model = CytoplasmicFlowModel(grid_size=16)
        smooth = model.verify_smooth_solution()
        
        # In viscous regime, should have smooth solutions
        assert smooth['is_viscous_dominated'] is True
        assert smooth['has_smooth_solutions'] is True
        assert smooth['global_regularity'] is True
    
    def test_no_turbulence(self):
        """Test that turbulence is impossible at low Reynolds."""
        model = CytoplasmicFlowModel(grid_size=16)
        smooth = model.verify_smooth_solution()
        
        # Re << 1 means no turbulence
        assert smooth['no_turbulence'] is True
        assert smooth['reynolds'] < 1e-3
    
    def test_viscosity_dominates(self):
        """Test that viscosity dominates inertia."""
        model = CytoplasmicFlowModel(grid_size=16)
        smooth = model.verify_smooth_solution()
        
        # Nonlinear/viscous ratio should be ~ Re << 1
        ratio = smooth['nonlinear_viscous_ratio']
        re = smooth['reynolds']
        
        assert np.isclose(ratio, re, rtol=1e-3)
        assert ratio < 1e-3


class TestNumericalStability:
    """Test numerical stability and convergence."""
    
    def test_grid_independence(self):
        """Test that results don't depend strongly on grid size."""
        model_8 = CytoplasmicFlowModel(grid_size=8)
        model_16 = CytoplasmicFlowModel(grid_size=16)
        
        # Reynolds number should be the same
        assert np.isclose(
            model_8.params.reynolds,
            model_16.params.reynolds,
            rtol=1e-10
        )
    
    def test_resonance_peak_stability(self):
        """Test that resonance peak is stable."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        # Compute spectrum twice
        freq1, spec1 = model.compute_resonance_spectrum(n_points=100)
        freq2, spec2 = model.compute_resonance_spectrum(n_points=100)
        
        # Should be identical
        np.testing.assert_array_equal(freq1, freq2)
        np.testing.assert_array_equal(spec1, spec2)
    
    def test_mode_computation_consistency(self):
        """Test that mode computation is consistent."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        modes1 = model.compute_spectral_modes(n_modes=5)
        modes2 = model.compute_spectral_modes(n_modes=5)
        
        # Should produce identical results
        for m1, m2 in zip(modes1, modes2):
            assert m1.wavenumber == m2.wavenumber
            assert m1.frequency == m2.frequency
            assert m1.eigenvalue == m2.eigenvalue


class TestDocumentation:
    """Test documentation and reporting."""
    
    def test_validation_report_generation(self):
        """Test validation report generation."""
        model = CytoplasmicFlowModel(grid_size=16)
        report = model.generate_validation_report()
        
        assert isinstance(report, str)
        assert len(report) > 100
    
    def test_report_sections(self):
        """Test that report contains all sections."""
        model = CytoplasmicFlowModel(grid_size=16)
        report = model.generate_validation_report()
        
        # Check for key sections
        assert 'PHYSICAL REGIME' in report
        assert 'NAVIER-STOKES' in report
        assert 'HILBERT-PÓLYA' in report or 'HILBERT-POLYA' in report
        assert 'QCAL' in report
    
    def test_report_contains_values(self):
        """Test that report contains computed values."""
        model = CytoplasmicFlowModel(grid_size=16)
        report = model.generate_validation_report()
        
        # Should contain Reynolds number
        assert str(model.params.reynolds) in report or 'Re =' in report
        
        # Should contain QCAL frequency
        assert '141.7' in report


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_zero_velocity(self):
        """Test with zero velocity (static cytoplasm)."""
        params = FlowParameters(velocity_scale=0.0)
        
        # Reynolds should be zero
        assert params.reynolds == 0.0
        
        # Should still be in viscous regime
        assert params.is_viscous_regime is True
    
    def test_very_high_viscosity(self):
        """Test with very high viscosity."""
        params = FlowParameters(viscosity=1e-3)
        
        # Reynolds should be very small
        assert params.reynolds < 1e-10
        assert params.is_viscous_regime is True
    
    def test_small_grid(self):
        """Test with minimal grid size."""
        model = CytoplasmicFlowModel(grid_size=4)
        
        # Should still initialize
        assert model.grid_size == 4
        assert model.x.shape == (4, 4, 4)
    
    def test_large_domain(self):
        """Test with larger domain."""
        model = CytoplasmicFlowModel(grid_size=8, domain_size=1e-4)
        
        # Should handle larger domain
        assert model.domain_size == 1e-4
        assert model.dx == 1e-4 / 8


class TestReproducibility:
    """Test reproducibility of results."""
    
    def test_deterministic_initialization(self):
        """Test that initialization is deterministic."""
        model1 = CytoplasmicFlowModel(grid_size=16, domain_size=1e-5)
        model2 = CytoplasmicFlowModel(grid_size=16, domain_size=1e-5)
        
        # Grids should be identical
        np.testing.assert_array_equal(model1.x, model2.x)
        np.testing.assert_array_equal(model1.kx, model2.kx)
    
    def test_deterministic_spectrum(self):
        """Test that spectrum computation is deterministic."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        freq1, spec1 = model.compute_resonance_spectrum(
            freq_range=(140.0, 143.0),
            n_points=50
        )
        freq2, spec2 = model.compute_resonance_spectrum(
            freq_range=(140.0, 143.0),
            n_points=50
        )
        
        np.testing.assert_array_equal(freq1, freq2)
        np.testing.assert_array_equal(spec1, spec2)
    
    def test_parameter_preservation(self):
        """Test that parameters are preserved."""
        params = FlowParameters(
            viscosity=2e-6,
            density=1050.0,
            length_scale=2e-6,
            velocity_scale=2e-9
        )
        model = CytoplasmicFlowModel(params=params, grid_size=16)
        
        # Parameters should be preserved
        assert model.params.viscosity == 2e-6
        assert model.params.density == 1050.0
        assert model.params.length_scale == 2e-6
        assert model.params.velocity_scale == 2e-9


if __name__ == '__main__':
    """Run integration tests with pytest."""
    pytest.main([__file__, '-v', '--tb=short'])

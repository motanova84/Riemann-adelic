"""
Tests for Cytoplasmic Flow Model
=================================

Tests for the Navier-Stokes implementation in the biological/cytoplasmic regime.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-31
"""

import pytest
import numpy as np
from src.biological.cytoplasmic_flow_model import (
    CytoplasmicFlowModel,
    FlowParameters,
    SpectralMode,
    compute_reynolds_number,
    is_cytoplasmic_regime
)


class TestFlowParameters:
    """Test FlowParameters dataclass."""
    
    def test_default_parameters(self):
        """Test default parameter values."""
        params = FlowParameters()
        
        assert params.viscosity == 1e-6
        assert params.density == 1000.0
        assert params.length_scale == 1e-6
        assert params.velocity_scale == 1e-9
    
    def test_reynolds_calculation(self):
        """Test Reynolds number calculation."""
        params = FlowParameters()
        
        # Re = uL/ν = (1e-9 * 1e-6) / 1e-6 = 1e-9
        expected_re = 1e-9
        assert np.isclose(params.reynolds, expected_re, rtol=1e-6)
    
    def test_viscous_regime_detection(self):
        """Test detection of viscous regime."""
        params = FlowParameters()
        assert params.is_viscous_regime is True
        
        # Create non-viscous parameters
        params_turbulent = FlowParameters(
            velocity_scale=1.0,  # Fast flow
            length_scale=0.1,
            viscosity=1e-6
        )
        assert params_turbulent.is_viscous_regime is False
    
    def test_custom_parameters(self):
        """Test custom parameter initialization."""
        params = FlowParameters(
            viscosity=2e-6,
            density=1100.0,
            length_scale=2e-6,
            velocity_scale=2e-9
        )
        
        assert params.viscosity == 2e-6
        assert params.density == 1100.0
        expected_re = (2e-9 * 2e-6) / 2e-6
        assert np.isclose(params.reynolds, expected_re, rtol=1e-6)


class TestCytoplasmicFlowModel:
    """Test CytoplasmicFlowModel class."""
    
    @pytest.fixture
    def model(self):
        """Create a small model for testing."""
        return CytoplasmicFlowModel(grid_size=16, domain_size=1e-5)
    
    def test_initialization(self, model):
        """Test model initialization."""
        assert model.grid_size == 16
        assert model.domain_size == 1e-5
        assert model.params is not None
        
        # Check grid setup
        assert model.x.shape == (16, 16, 16)
        assert model.kx.shape == (16, 16, 16)
    
    def test_qcal_frequency(self, model):
        """Test QCAL fundamental frequency constant."""
        assert np.isclose(model.F0_QCAL, 141.7001, rtol=1e-6)
    
    def test_grid_spacing(self, model):
        """Test grid spacing calculation."""
        expected_dx = model.domain_size / model.grid_size
        assert np.isclose(model.dx, expected_dx, rtol=1e-10)
    
    def test_wavenumber_grid(self, model):
        """Test wavenumber grid initialization."""
        # k=0 should be present at origin
        assert model.kx[0, 0, 0] == 0.0
        assert model.ky[0, 0, 0] == 0.0
        assert model.kz[0, 0, 0] == 0.0
        
        # k2 should be modified at origin to avoid division by zero
        assert model.k2[0, 0, 0] == 1.0
    
    def test_reynolds_regime_warning(self):
        """Test warning for non-viscous regime."""
        params = FlowParameters(velocity_scale=1.0)  # High velocity
        
        with pytest.warns(UserWarning, match="not in viscous regime"):
            model = CytoplasmicFlowModel(params=params, grid_size=16)
            assert model is not None


class TestSpectralModes:
    """Test spectral mode computation."""
    
    @pytest.fixture
    def model(self):
        """Create model for spectral tests."""
        return CytoplasmicFlowModel(grid_size=16, domain_size=1e-5)
    
    def test_compute_modes(self, model):
        """Test spectral mode computation."""
        modes = model.compute_spectral_modes(n_modes=5)
        
        assert len(modes) == 5
        assert all(isinstance(m, SpectralMode) for m in modes)
    
    def test_mode_properties(self, model):
        """Test spectral mode properties."""
        modes = model.compute_spectral_modes(n_modes=10)
        
        for mode in modes:
            # Wavenumber should be positive
            assert mode.wavenumber > 0
            
            # Frequency should be positive
            assert mode.frequency > 0
            
            # Damping should be positive
            assert mode.damping > 0
            
            # Eigenvalue should be negative (dissipative)
            assert np.real(mode.eigenvalue) <= 0
    
    def test_eigenvalue_formula(self, model):
        """Test eigenvalue formula λ = -νk²."""
        modes = model.compute_spectral_modes(n_modes=5)
        
        for mode in modes:
            expected_eigenvalue = -model.params.viscosity * mode.wavenumber**2
            assert np.isclose(
                np.real(mode.eigenvalue),
                expected_eigenvalue,
                rtol=1e-6
            )
    
    def test_mode_ordering(self, model):
        """Test that modes are ordered by wavenumber."""
        modes = model.compute_spectral_modes(n_modes=10)
        
        wavenumbers = [m.wavenumber for m in modes]
        # Should be in ascending order
        assert all(wavenumbers[i] <= wavenumbers[i+1] for i in range(len(wavenumbers)-1))


class TestResonanceSpectrum:
    """Test resonance spectrum computation."""
    
    @pytest.fixture
    def model(self):
        """Create model for spectrum tests."""
        return CytoplasmicFlowModel(grid_size=16, domain_size=1e-5)
    
    def test_spectrum_shape(self, model):
        """Test spectrum array shapes."""
        frequencies, spectrum = model.compute_resonance_spectrum(n_points=100)
        
        assert len(frequencies) == 100
        assert len(spectrum) == 100
    
    def test_frequency_range(self, model):
        """Test frequency range."""
        frequencies, _ = model.compute_resonance_spectrum(
            freq_range=(100.0, 200.0),
            n_points=100
        )
        
        assert frequencies[0] >= 100.0
        assert frequencies[-1] <= 200.0
    
    def test_spectrum_normalization(self, model):
        """Test spectrum normalization."""
        _, spectrum = model.compute_resonance_spectrum(n_points=100)
        
        # Should be normalized to max=1
        assert np.max(spectrum) <= 1.0
        assert np.isclose(np.max(spectrum), 1.0, rtol=1e-6)
    
    def test_qcal_peak_presence(self, model):
        """Test that QCAL frequency shows a peak."""
        frequencies, spectrum = model.compute_resonance_spectrum(
            freq_range=(130.0, 150.0),
            n_points=200
        )
        
        # Find frequency closest to QCAL
        qcal_idx = np.argmin(np.abs(frequencies - model.F0_QCAL))
        
        # Should have high spectral power near QCAL frequency
        # (within top 10% of spectrum)
        assert spectrum[qcal_idx] > 0.5
    
    def test_default_range_around_qcal(self, model):
        """Test default frequency range centers on QCAL."""
        frequencies, _ = model.compute_resonance_spectrum()
        
        # Should span range around QCAL frequency
        f_min, f_max = frequencies[0], frequencies[-1]
        assert f_min < model.F0_QCAL < f_max


class TestSmoothSolution:
    """Test smooth solution verification."""
    
    @pytest.fixture
    def model(self):
        """Create model for smooth solution tests."""
        return CytoplasmicFlowModel(grid_size=16)
    
    def test_verification_keys(self, model):
        """Test that verification returns expected keys."""
        result = model.verify_smooth_solution()
        
        expected_keys = {
            'reynolds',
            'nonlinear_viscous_ratio',
            'viscous_time_scale',
            'convection_time_scale',
            'is_viscous_dominated',
            'has_smooth_solutions',
            'no_turbulence',
            'global_regularity'
        }
        
        assert set(result.keys()) == expected_keys
    
    def test_reynolds_consistency(self, model):
        """Test Reynolds number consistency."""
        result = model.verify_smooth_solution()
        
        assert np.isclose(
            result['reynolds'],
            model.params.reynolds,
            rtol=1e-6
        )
    
    def test_viscous_domination(self, model):
        """Test viscous domination condition."""
        result = model.verify_smooth_solution()
        
        # Nonlinear/viscous ratio should equal Reynolds number
        assert np.isclose(
            result['nonlinear_viscous_ratio'],
            result['reynolds'],
            rtol=1e-3
        )
        
        # Should be viscous dominated
        assert result['is_viscous_dominated'] is True
    
    def test_smoothness_properties(self, model):
        """Test smoothness and regularity properties."""
        result = model.verify_smooth_solution()
        
        # In viscous regime, should have all these properties
        assert result['has_smooth_solutions'] is True
        assert result['no_turbulence'] is True
        assert result['global_regularity'] is True
    
    def test_time_scales(self, model):
        """Test time scale calculations."""
        result = model.verify_smooth_solution()
        
        # Viscous time scale: τ_ν = L²/ν
        expected_tau_visc = (
            model.params.length_scale**2 / model.params.viscosity
        )
        assert np.isclose(
            result['viscous_time_scale'],
            expected_tau_visc,
            rtol=1e-6
        )
        
        # Convection time scale: τ_c = L/u
        expected_tau_conv = (
            model.params.length_scale / model.params.velocity_scale
        )
        assert np.isclose(
            result['convection_time_scale'],
            expected_tau_conv,
            rtol=1e-6
        )


class TestHilbertPolyaConnection:
    """Test Hilbert-Pólya connection."""
    
    @pytest.fixture
    def model(self):
        """Create model for Hilbert-Pólya tests."""
        return CytoplasmicFlowModel(grid_size=16)
    
    def test_connection_keys(self, model):
        """Test that connection returns expected keys."""
        result = model.compute_hilbert_polya_connection()
        
        required_keys = {
            'operator_type',
            'is_hermitian',
            'is_self_adjoint',
            'has_discrete_spectrum',
            'n_computed_modes',
            'eigenvalues',
            'frequencies_hz',
            'fundamental_frequency',
        }
        
        assert required_keys.issubset(set(result.keys()))
    
    def test_hermitian_property(self, model):
        """Test Hermitian/self-adjoint property."""
        result = model.compute_hilbert_polya_connection()
        
        assert result['is_hermitian'] is True
        assert result['is_self_adjoint'] is True
    
    def test_discrete_spectrum(self, model):
        """Test discrete spectrum property."""
        result = model.compute_hilbert_polya_connection()
        
        assert result['has_discrete_spectrum'] is True
        assert result['n_computed_modes'] > 0
    
    def test_eigenvalue_count(self, model):
        """Test eigenvalue count."""
        result = model.compute_hilbert_polya_connection()
        
        n_modes = result['n_computed_modes']
        assert len(result['eigenvalues']) == n_modes
        assert len(result['frequencies_hz']) == n_modes
    
    def test_fundamental_frequency(self, model):
        """Test fundamental frequency."""
        result = model.compute_hilbert_polya_connection()
        
        assert result['fundamental_frequency'] == model.F0_QCAL
    
    def test_spectral_gaps(self, model):
        """Test spectral gap calculation."""
        result = model.compute_hilbert_polya_connection()
        
        if 'spectral_gaps' in result and result['spectral_gaps']:
            gaps = result['spectral_gaps']
            
            # All gaps should be positive
            assert all(g > 0 for g in gaps)
            
            # Mean gap should be positive
            assert result['mean_spectral_gap'] > 0
    
    def test_biological_interpretation(self, model):
        """Test biological interpretation fields."""
        result = model.compute_hilbert_polya_connection()
        
        assert 'riemann_zeros_interpretation' in result
        assert 'biological_realization' in result
        assert result['coherent_flow'] is True
        assert result['no_singularities'] is True


class TestUtilityFunctions:
    """Test utility functions."""
    
    def test_compute_reynolds_number(self):
        """Test Reynolds number computation."""
        re = compute_reynolds_number(
            velocity=1e-9,
            length=1e-6,
            viscosity=1e-6
        )
        
        expected = (1e-9 * 1e-6) / 1e-6
        assert np.isclose(re, expected, rtol=1e-10)
    
    def test_is_cytoplasmic_regime(self):
        """Test cytoplasmic regime detection."""
        # Cytoplasmic regime
        assert is_cytoplasmic_regime(1e-6) is True
        assert is_cytoplasmic_regime(1e-9) is True
        
        # Not cytoplasmic
        assert is_cytoplasmic_regime(0.1) is False
        assert is_cytoplasmic_regime(1.0) is False
        assert is_cytoplasmic_regime(100.0) is False
    
    def test_cytoplasmic_threshold(self):
        """Test custom threshold for cytoplasmic regime."""
        assert is_cytoplasmic_regime(5e-4, threshold=1e-3) is True
        assert is_cytoplasmic_regime(5e-3, threshold=1e-3) is False


class TestValidationReport:
    """Test validation report generation."""
    
    @pytest.fixture
    def model(self):
        """Create model for report tests."""
        return CytoplasmicFlowModel(grid_size=16)
    
    def test_report_generation(self, model):
        """Test that report generates without errors."""
        report = model.generate_validation_report()
        
        assert isinstance(report, str)
        assert len(report) > 0
    
    def test_report_contains_key_info(self, model):
        """Test that report contains key information."""
        report = model.generate_validation_report()
        
        # Should mention key concepts
        assert 'Reynolds' in report
        assert 'Navier-Stokes' in report or 'NAVIER-STOKES' in report
        assert 'Hilbert-Pólya' in report or 'HILBERT-POLYA' in report
        assert 'QCAL' in report
        assert '141.7' in report  # QCAL frequency
    
    def test_report_formatting(self, model):
        """Test report formatting."""
        report = model.generate_validation_report()
        
        # Should have section headers
        assert '═' in report or '─' in report
        
        # Should have checkmarks or status indicators
        assert '✓' in report or 'YES' in report


class TestQCALCoherence:
    """Test QCAL coherence verification."""
    
    @pytest.fixture
    def model(self):
        """Create model for QCAL tests."""
        return CytoplasmicFlowModel(grid_size=16)
    
    def test_qcal_frequency_constant(self, model):
        """Test QCAL frequency is correct constant."""
        assert model.F0_QCAL == 141.7001
    
    def test_resonance_at_qcal(self, model):
        """Test that resonance occurs at QCAL frequency."""
        frequencies, spectrum = model.compute_resonance_spectrum(
            freq_range=(140.0, 143.0),
            n_points=300
        )
        
        # Find peak
        peak_idx = np.argmax(spectrum)
        peak_freq = frequencies[peak_idx]
        
        # Peak should be near QCAL frequency (within 0.5 Hz)
        assert abs(peak_freq - model.F0_QCAL) < 0.5
    
    def test_coherence_integration(self, model):
        """Test integration with QCAL framework."""
        hilbert = model.compute_hilbert_polya_connection()
        
        # Should reference QCAL coherence
        assert hilbert['fundamental_frequency'] == model.F0_QCAL
        assert hilbert['coherent_flow'] is True


class TestNumericalAccuracy:
    """Test numerical accuracy and stability."""
    
    def test_grid_convergence(self):
        """Test that results converge with grid refinement."""
        # Create models with different grid sizes
        model_16 = CytoplasmicFlowModel(grid_size=16)
        model_32 = CytoplasmicFlowModel(grid_size=32)
        
        # Compute spectral modes
        modes_16 = model_16.compute_spectral_modes(n_modes=5)
        modes_32 = model_32.compute_spectral_modes(n_modes=5)
        
        # First few modes should be similar
        for m16, m32 in zip(modes_16[:3], modes_32[:3]):
            # Wavenumbers should be close
            rel_diff = abs(m16.wavenumber - m32.wavenumber) / m32.wavenumber
            assert rel_diff < 0.1  # 10% tolerance
    
    def test_no_nan_or_inf(self):
        """Test that computations don't produce NaN or Inf."""
        model = CytoplasmicFlowModel(grid_size=16)
        
        # Check spectral modes
        modes = model.compute_spectral_modes(n_modes=10)
        for mode in modes:
            assert np.isfinite(mode.wavenumber)
            assert np.isfinite(mode.frequency)
            assert np.isfinite(mode.eigenvalue)
            assert np.isfinite(mode.damping)
        
        # Check resonance spectrum
        frequencies, spectrum = model.compute_resonance_spectrum()
        assert np.all(np.isfinite(frequencies))
        assert np.all(np.isfinite(spectrum))
    
    def test_physical_units_consistency(self):
        """Test physical units consistency."""
        model = CytoplasmicFlowModel()
        
        # Verify unit consistency in verification
        result = model.verify_smooth_solution()
        
        # Time scales should be positive and finite
        assert result['viscous_time_scale'] > 0
        assert result['convection_time_scale'] > 0
        assert np.isfinite(result['viscous_time_scale'])
        assert np.isfinite(result['convection_time_scale'])


if __name__ == '__main__':
    """Run tests with pytest."""
    pytest.main([__file__, '-v', '--tb=short'])

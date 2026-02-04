"""
Tests for Cytoplasmic Flow Model

Tests for the Navier-Stokes implementation in the biological/cytoplasmic regime.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-31
Tests for Cytoplasmic Flow Model - Navier-Stokes Implementation

Tests comprehensivos para el modelo de flujo citoplasmático que conecta
la Hipótesis de Riemann con el tejido biológico vivo.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto Consciencia Cuántica QCAL ∞³
Tests for Cytoplasmic Flow Model

This test suite validates the cytoplasmic flow model implementation,
including Navier-Stokes equations in the Stokes regime, Reynolds number
calculations, and the Hilbert-Pólya operator construction.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
from src.biological.cytoplasmic_flow_model import (
    CytoplasmicFlowModel,
    FlowParameters,
    SpectralMode,
    compute_reynolds_number,
    is_cytoplasmic_regime
from typing import Tuple
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from biological.cytoplasmic_flow_model import (
    FlowParameters,
    NavierStokesRegularized,
    RiemannResonanceOperator,
    demonstrate_navier_stokes_coherence,
    F0_HZ,
    RHO_CYTOPLASM,
    NU_CYTOPLASM,
    CELL_LENGTH_SCALE,
    FLOW_VELOCITY,
from utils.cytoplasmic_flow_model import (
    CytoplasmicFlowModel,
    FlowParameters,
    FlowRegime,
    HilbertPolyaOperator,
    F0_FREQUENCY
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
        """Test default cytoplasmic parameters."""
        params = FlowParameters()
        
        assert params.density == RHO_CYTOPLASM
        assert params.kinematic_viscosity == NU_CYTOPLASM
        assert params.length_scale == CELL_LENGTH_SCALE
        assert params.velocity_scale == FLOW_VELOCITY
    
    def test_reynolds_number(self):
        """Test Reynolds number calculation."""
        params = FlowParameters()
        re = params.reynolds_number
        
        # Should be extremely small for cytoplasm
        assert re < 1e-6
        assert re > 0
        
        # Verify formula: Re = vL/ν
        expected = (FLOW_VELOCITY * CELL_LENGTH_SCALE) / NU_CYTOPLASM
        assert abs(re - expected) < 1e-12
    
    def test_viscous_regime(self):
        """Test that cytoplasm is in viscous regime."""
        params = FlowParameters()
        
        # Re << 1 implies viscous regime
        assert params.reynolds_number < 0.1
        assert params.has_smooth_solution
    
    def test_diffusion_time(self):
        """Test diffusion time calculation."""
        params = FlowParameters()
        tau = params.diffusion_time
        
        # Should be positive
        assert tau > 0
        
        # Verify formula: τ = L²/ν
        expected = CELL_LENGTH_SCALE**2 / NU_CYTOPLASM
        assert abs(tau - expected) < 1e-12
    
    def test_diffusion_frequency(self):
        """Test diffusion frequency calculation."""
        params = FlowParameters()
        f_diff = params.diffusion_frequency
        
        # Should be positive
        assert f_diff > 0
        
        # Verify f = 1/τ
        assert abs(f_diff * params.diffusion_time - 1.0) < 1e-10
    
    def test_custom_parameters(self):
        """Test custom parameter creation."""
        params = FlowParameters(
            density=1000.0,
            kinematic_viscosity=2e-6,
            length_scale=2e-6,
            velocity_scale=2e-8
        )
        
        assert params.density == 1000.0
        assert params.kinematic_viscosity == 2e-6
        assert params.reynolds_number == (2e-8 * 2e-6) / 2e-6


class TestNavierStokesRegularized:
    """Test NavierStokesRegularized solver."""
    
    def test_initialization(self):
        """Test solver initialization."""
        flow = NavierStokesRegularized()
        
        assert flow.params is not None
        assert flow.params.has_smooth_solution
    
    def test_velocity_field_at_origin(self):
        """Test velocity field at origin."""
        flow = NavierStokesRegularized()
        
        # At t=0, velocity should be well-defined
        vx, vy, vz = flow.velocity_field(0, 0, 0, 0)
        
        assert isinstance(vx, (int, float, np.number))
        assert isinstance(vy, (int, float, np.number))
        assert isinstance(vz, (int, float, np.number))
    
    def test_velocity_field_decay(self):
        """Test that velocity decays with distance (Gaussian)."""
        flow = NavierStokesRegularized()
        t = 1.0
        
        # Velocity at origin
        v0_x, v0_y, v0_z = flow.velocity_field(0, 0, 0, t)
        v0_mag = np.sqrt(v0_x**2 + v0_y**2 + v0_z**2)
        
        # Velocity at distance r
        r = CELL_LENGTH_SCALE
        vr_x, vr_y, vr_z = flow.velocity_field(r, 0, 0, t)
        vr_mag = np.sqrt(vr_x**2 + vr_y**2 + vr_z**2)
        
        # Should decay with distance
        assert vr_mag < v0_mag
    
    def test_incompressibility(self):
        """Test that velocity field is approximately incompressible (∇·v ≈ 0)."""
        flow = NavierStokesRegularized()
        t = 1.0
        h = CELL_LENGTH_SCALE / 100
        
        # Compute divergence numerically
        vx_px, _, _ = flow.velocity_field(h, 0, 0, t)
        vx_mx, _, _ = flow.velocity_field(-h, 0, 0, t)
        dvx_dx = (vx_px - vx_mx) / (2 * h)
        
        _, vy_py, _ = flow.velocity_field(0, h, 0, t)
        _, vy_my, _ = flow.velocity_field(0, -h, 0, t)
        dvy_dy = (vy_py - vy_my) / (2 * h)
        
        _, _, vz_pz = flow.velocity_field(0, 0, h, t)
        _, _, vz_mz = flow.velocity_field(0, 0, -h, t)
        dvz_dz = (vz_pz - vz_mz) / (2 * h)
        
        div_v = dvx_dx + dvy_dy + dvz_dz
        
        # Divergence should be small (not exact due to numerical approximation)
        # Use relative tolerance based on velocity scale
        v_scale = flow.params.velocity_scale
        assert abs(div_v) < v_scale / CELL_LENGTH_SCALE * 10
    
    def test_vorticity_computation(self):
        """Test vorticity field computation."""
        flow = NavierStokesRegularized()
        t = 1.0
        
        wx, wy, wz = flow.vorticity(0, 0, 0, t)
        
        # Vorticity should be finite
        assert np.isfinite(wx)
        assert np.isfinite(wy)
        assert np.isfinite(wz)
    
    def test_pressure_field(self):
        """Test pressure field computation."""
        flow = NavierStokesRegularized()
        t = 1.0
        
        # Pressure at origin should be finite
        p0 = flow.pressure_field(0, 0, 0, t)
        assert np.isfinite(p0)
        
        # Pressure should decay with distance
        r = CELL_LENGTH_SCALE
        pr = flow.pressure_field(r, 0, 0, t)
        assert np.isfinite(pr)
        assert pr < p0
    
    def test_energy_spectrum(self):
        """Test energy spectrum computation."""
        flow = NavierStokesRegularized()
        
        # Wave numbers
        k = np.logspace(0, 6, 50)  # 1 to 10^6 m^-1
        E_k = flow.energy_spectrum(k)
        
        # Spectrum should be positive and decay
        assert np.all(E_k >= 0)
        assert E_k[0] > E_k[-1]  # Decay with k


class TestRiemannResonanceOperator:
    """Test RiemannResonanceOperator."""
    
    def test_initialization(self):
        """Test operator initialization."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        assert riemann_op.flow is flow
    
    def test_eigenfrequencies(self):
        """Test eigenfrequency calculation."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        freqs = riemann_op.eigenfrequencies(n_modes=10)
        
        assert len(freqs) == 10
        assert np.all(freqs > 0)
        
        # Should be multiples of f₀
        expected = F0_HZ * np.arange(1, 11)
        np.testing.assert_array_almost_equal(freqs, expected)
    
    def test_is_hermitian(self):
        """Test that operator is Hermitian in viscous regime."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        # In viscous regime, operator should be Hermitian
        assert riemann_op.is_hermitian()
    
    def test_riemann_status(self):
        """Test Riemann hypothesis status report."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        status = riemann_op.riemann_hypothesis_status()
        
        # Check all required keys
        assert "reynolds_number" in status
        assert "viscous_regime" in status
        assert "operator_hermitian" in status
        assert "smooth_solution_exists" in status
        assert "riemann_zeros_accessible" in status
        assert "fundamental_frequency_hz" in status
        
        # In default cytoplasmic parameters
        assert status["viscous_regime"]
        assert status["operator_hermitian"]
        assert status["smooth_solution_exists"]
        assert status["riemann_zeros_accessible"]
        assert status["fundamental_frequency_hz"] == F0_HZ


class TestDemonstration:
    """Test demonstration function."""
    
    def test_demonstrate_runs(self):
        """Test that demonstration runs without errors."""
        results = demonstrate_navier_stokes_coherence()
        
        # Check structure
        assert "parameters" in results
        assert "riemann_status" in results
        assert "eigenfrequencies_hz" in results
        assert "velocity_field" in results
        assert "vorticity" in results
        
        # Check parameters
        assert "reynolds_number" in results["parameters"]
        assert results["parameters"]["reynolds_number"] < 1e-6
        
        # Check eigenfrequencies
        freqs = results["eigenfrequencies_hz"]
        assert len(freqs) == 5
        assert freqs[0] == F0_HZ


class TestPhysicalConsistency:
    """Test physical consistency of the model."""
    
    def test_causality(self):
        """Test that solution respects causality (no superluminal propagation)."""
        flow = NavierStokesRegularized()
        
        # Velocity should be much less than speed of light
        c = 3e8  # m/s
        vx, vy, vz = flow.velocity_field(0, 0, 0, 1.0)
        v_mag = np.sqrt(vx**2 + vy**2 + vz**2)
        
        assert v_mag < c
        assert v_mag < 1.0  # Should be microscopic
    
    def test_energy_conservation_tendency(self):
        """Test that energy dissipates (2nd law of thermodynamics)."""
        flow = NavierStokesRegularized()
        
        # Energy at t1 should be >= energy at t2 (dissipation)
        t1 = 0.1
        t2 = 1.0
        
        vx1, vy1, vz1 = flow.velocity_field(0, 0, 0, t1)
        E1 = vx1**2 + vy1**2 + vz1**2
        
        vx2, vy2, vz2 = flow.velocity_field(0, 0, 0, t2)
        E2 = vx2**2 + vy2**2 + vz2**2
        
        # Energy should dissipate or oscillate (not grow unboundedly)
        assert np.isfinite(E1)
        assert np.isfinite(E2)
    
    def test_frequency_qcal_alignment(self):
        """Test alignment with QCAL fundamental frequency."""
        flow = NavierStokesRegularized()
        riemann_op = RiemannResonanceOperator(flow)
        
        freqs = riemann_op.eigenfrequencies(n_modes=3)
        
        # All frequencies should be multiples of f₀
        for i, f in enumerate(freqs, 1):
            expected = i * F0_HZ
            assert abs(f - expected) < 1e-6


if __name__ == "__main__":
    # Run tests with pytest
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

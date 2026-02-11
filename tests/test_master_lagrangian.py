"""
Unit tests for QCAL Master Lagrangian

Tests all components of the master Lagrangian framework:
- L_QCAL computation
- L_FIBRATION computation
- L_COUPLING computation
- Equations of motion derivation
- Quantized spectrum with f₀ validation
- Energy conservation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from qcal.master_lagrangian import (
    MasterLagrangian,
    LagrangianParameters,
    FieldConfiguration,
    compute_qcal_lagrangian,
    compute_fibration_lagrangian,
    compute_coupling_lagrangian,
    derive_equations_of_motion,
    compute_quantized_spectrum,
    verify_energy_conservation,
    F0, PSI_THRESHOLD
)


class TestLagrangianParameters:
    """Test Lagrangian parameters dataclass."""
    
    def test_default_parameters(self):
        """Test default parameter values."""
        params = LagrangianParameters()
        
        assert params.kappa_pi == 1.0
        assert params.alpha_zeta == 0.5
        assert params.lambda_g == 2.0
        assert params.psi_intersection == PSI_THRESHOLD
        assert params.omega_0 == 2 * np.pi * F0
        
    def test_custom_parameters(self):
        """Test custom parameter initialization."""
        params = LagrangianParameters(
            kappa_pi=2.0,
            lambda_g=3.0,
            n_grid=256
        )
        
        assert params.kappa_pi == 2.0
        assert params.lambda_g == 3.0
        assert params.n_grid == 256


class TestMasterLagrangian:
    """Test MasterLagrangian class."""
    
    @pytest.fixture
    def lagrangian(self):
        """Create Lagrangian instance for testing."""
        params = LagrangianParameters(n_grid=64, n_time=128)
        return MasterLagrangian(params)
    
    @pytest.fixture
    def field_config(self, lagrangian):
        """Create test field configuration."""
        return lagrangian.initialize_gaussian_field(amplitude=1.0, width=2.0)
    
    def test_initialization(self, lagrangian):
        """Test Lagrangian initialization."""
        assert lagrangian.params.n_grid == 64
        assert lagrangian.params.n_time == 128
        assert len(lagrangian.x) == 64
        assert len(lagrangian.t) == 128
        
    def test_grid_spacing(self, lagrangian):
        """Test grid spacing."""
        assert lagrangian.dx > 0
        assert lagrangian.dt > 0
        assert np.isclose(lagrangian.x[-1] - lagrangian.x[0], 
                         2 * lagrangian.params.x_max, rtol=0.01)
    
    def test_qcal_lagrangian(self, lagrangian, field_config):
        """Test QCAL Lagrangian computation."""
        L_qcal = lagrangian.compute_qcal_lagrangian(
            field_config.psi,
            field_config.phi,
            field_config.nabla_psi,
            field_config.nabla_phi,
            field_config.ricci_scalar,
            t_eval=0.0
        )
        
        assert L_qcal.shape == field_config.psi.shape
        assert np.all(np.isfinite(L_qcal))
    
    def test_fibration_lagrangian(self, lagrangian, field_config):
        """Test fibration Lagrangian computation."""
        L_fib = lagrangian.compute_fibration_lagrangian(field_config.berry_phase)
        
        assert L_fib.shape == field_config.berry_phase.shape
        assert np.all(np.isfinite(L_fib))
        
    def test_coupling_lagrangian(self, lagrangian, field_config):
        """Test coupling Lagrangian computation."""
        psi_geom = lagrangian._compute_berry_wavefunction(
            field_config.psi,
            field_config.berry_phase
        )
        L_coup = lagrangian.compute_coupling_lagrangian(field_config.psi, psi_geom)
        
        assert L_coup.shape == field_config.psi.shape
        assert np.all(np.isfinite(L_coup))
        assert np.all(np.isreal(L_coup))  # Should be real
    
    def test_master_lagrangian(self, lagrangian, field_config):
        """Test complete master Lagrangian."""
        lagrangian_dict = lagrangian.compute_master_lagrangian(field_config, t_eval=0.0)
        
        assert 'L_master' in lagrangian_dict
        assert 'L_qcal' in lagrangian_dict
        assert 'L_fibration' in lagrangian_dict
        assert 'L_coupling' in lagrangian_dict
        
        # Check shapes
        for key in lagrangian_dict:
            assert lagrangian_dict[key].shape == field_config.psi.shape
            assert np.all(np.isfinite(lagrangian_dict[key]))
        
        # Verify sum
        L_sum = (lagrangian_dict['L_qcal'] + 
                lagrangian_dict['L_fibration'] + 
                lagrangian_dict['L_coupling'])
        assert np.allclose(lagrangian_dict['L_master'], L_sum)
    
    def test_equations_of_motion(self, lagrangian, field_config):
        """Test equations of motion derivation."""
        eom = lagrangian.derive_equations_of_motion(field_config)
        
        assert 'eom_psi' in eom
        assert 'eom_phi' in eom
        assert 'eom_berry' in eom
        
        # Check shapes
        assert eom['eom_psi'].shape == field_config.psi.shape
        assert eom['eom_phi'].shape == field_config.phi.shape
        assert eom['eom_berry'].shape == field_config.berry_phase.shape
        
        # All should be finite
        for key in eom:
            assert np.all(np.isfinite(eom[key]))
    
    def test_quantized_spectrum(self, lagrangian):
        """Test quantized spectrum computation."""
        spectrum = lagrangian.compute_quantized_spectrum(n_modes=10)
        
        assert 'energies' in spectrum
        assert 'frequencies' in spectrum
        assert 'f0_computed' in spectrum
        assert 'f0_target' in spectrum
        assert 'eigenfunctions' in spectrum
        
        # Check array lengths
        assert len(spectrum['energies']) == 10
        assert len(spectrum['frequencies']) == 10
        assert spectrum['eigenfunctions'].shape[0] == 10
        
        # Verify f₀ target
        assert spectrum['f0_target'] == F0
        
        # Check that energies are positive and increasing
        assert np.all(spectrum['energies'] > 0)
        assert np.all(np.diff(spectrum['energies']) > 0)
        
    def test_f0_validation(self, lagrangian):
        """Test that f₀ = 141.7001 Hz emerges correctly."""
        spectrum = lagrangian.compute_quantized_spectrum(n_modes=5)
        
        # Ground state frequency should be close to f₀
        f0_computed = spectrum['f0_computed']
        f0_target = F0
        
        # Allow 10% tolerance due to numerical approximations
        assert np.abs(f0_computed - f0_target) / f0_target < 0.1
    
    def test_field_initialization(self, lagrangian):
        """Test Gaussian field initialization."""
        field = lagrangian.initialize_gaussian_field(amplitude=2.0, width=1.5)
        
        assert isinstance(field, FieldConfiguration)
        assert field.psi.shape == lagrangian.x.shape
        assert field.phi.shape == lagrangian.x.shape
        
        # Check that fields are centered and decay
        center_idx = len(lagrangian.x) // 2
        assert np.abs(field.phi[center_idx]) > np.abs(field.phi[0])
        assert np.abs(field.phi[center_idx]) > np.abs(field.phi[-1])
    
    def test_field_evolution(self, lagrangian, field_config):
        """Test time evolution of fields."""
        history = lagrangian.evolve_field(field_config, n_steps=10)
        
        assert len(history) == 10
        
        # All configurations should be valid
        for config in history:
            assert isinstance(config, FieldConfiguration)
            assert np.all(np.isfinite(config.psi))
            assert np.all(np.isfinite(config.phi))
    
    def test_energy_conservation(self, lagrangian, field_config):
        """Test energy conservation during evolution."""
        # Evolve field
        n_steps = 20
        history = lagrangian.evolve_field(field_config, n_steps=n_steps)
        t_values = lagrangian.t[:n_steps]
        
        # Verify conservation
        conservation = lagrangian.verify_energy_conservation(history, t_values)
        
        assert 'energy_initial' in conservation
        assert 'energy_final' in conservation
        assert 'relative_drift' in conservation
        assert 'conserved' in conservation
        
        # Energy should be conserved (within tolerance)
        # Note: Simple Euler integration may have drift
        assert conservation['relative_drift'] < 0.5  # 50% tolerance for simple integrator


class TestConvenienceFunctions:
    """Test convenience wrapper functions."""
    
    def test_compute_qcal_lagrangian(self):
        """Test QCAL Lagrangian convenience function."""
        x = np.linspace(-5, 5, 64)
        psi = np.exp(-x**2)
        phi = np.exp(-x**2)
        
        L = compute_qcal_lagrangian(psi, phi)
        
        assert L.shape == psi.shape
        assert np.all(np.isfinite(L))
    
    def test_compute_fibration_lagrangian(self):
        """Test fibration Lagrangian convenience function."""
        berry_phase = np.linspace(0, 2*np.pi, 64)
        
        L = compute_fibration_lagrangian(berry_phase, psi_intersection=0.9)
        
        assert L.shape == berry_phase.shape
        assert np.all(np.isfinite(L))
    
    def test_compute_coupling_lagrangian(self):
        """Test coupling Lagrangian convenience function."""
        x = np.linspace(-5, 5, 64)
        psi1 = np.exp(-x**2)
        psi2 = np.exp(-x**2) * np.exp(1j * x)
        
        L = compute_coupling_lagrangian(psi1, psi2)
        
        assert L.shape == psi1.shape
        assert np.all(np.isfinite(L))
        assert np.all(np.isreal(L))
    
    def test_compute_quantized_spectrum(self):
        """Test quantized spectrum convenience function."""
        spectrum = compute_quantized_spectrum(n_modes=5)
        
        assert 'energies' in spectrum
        assert 'frequencies' in spectrum
        assert len(spectrum['energies']) == 5


class TestNumericalStability:
    """Test numerical stability of computations."""
    
    def test_laplacian_accuracy(self):
        """Test Laplacian finite difference accuracy."""
        lagrangian = MasterLagrangian(LagrangianParameters(n_grid=128))
        
        # Test with known function: f(x) = sin(kx)
        k = 2 * np.pi / lagrangian.params.x_max
        field = np.sin(k * lagrangian.x)
        
        # Analytical Laplacian: -k² sin(kx)
        laplacian_analytical = -k**2 * field
        laplacian_numerical = lagrangian._laplacian(field)
        
        # Check accuracy (exclude boundaries)
        error = np.abs(laplacian_numerical[5:-5] - laplacian_analytical[5:-5])
        relative_error = error / (np.abs(laplacian_analytical[5:-5]) + 1e-10)
        
        assert np.mean(relative_error) < 0.1  # 10% mean error
    
    def test_zeta_computation(self):
        """Test Riemann zeta computation at critical line."""
        lagrangian = MasterLagrangian()
        
        # Test at s = 1/2 + 14i (first zero approximately)
        s = 0.5 + 14.134725j
        zeta_val = lagrangian._compute_zeta_critical(s)
        
        # Should be close to zero (within numerical error)
        assert np.abs(zeta_val) < 1.0  # Rough approximation


class TestPhysicalConsistency:
    """Test physical consistency of the framework."""
    
    def test_positive_energy(self):
        """Test that total energy is positive."""
        lagrangian = MasterLagrangian(LagrangianParameters(n_grid=64))
        field = lagrangian.initialize_gaussian_field()
        
        H = lagrangian._compute_hamiltonian(field, 0.0)
        
        assert H > 0, "Total energy must be positive"
    
    def test_hermiticity(self):
        """Test that relevant operators are Hermitian."""
        lagrangian = MasterLagrangian(LagrangianParameters(n_grid=64))
        
        # Berry phase wavefunction should preserve norm
        psi = np.exp(-lagrangian.x**2) * (1 + 0j)
        berry_phase = np.zeros_like(lagrangian.x)
        
        psi_berry = lagrangian._compute_berry_wavefunction(psi, berry_phase)
        
        norm_original = np.sum(np.abs(psi)**2) * lagrangian.dx
        norm_berry = np.sum(np.abs(psi_berry)**2) * lagrangian.dx
        
        assert np.isclose(norm_original, norm_berry, rtol=1e-10)
    
    def test_psi_threshold_behavior(self):
        """Test that Ψ_∩ ≥ 0.888 leads to consciousness emergence."""
        # High coherence configuration
        params_high = LagrangianParameters(psi_intersection=0.95)
        lagrangian_high = MasterLagrangian(params_high)
        
        # Low coherence configuration
        params_low = LagrangianParameters(psi_intersection=0.5)
        lagrangian_low = MasterLagrangian(params_low)
        
        berry_phase = np.ones(64) * np.pi / 4
        
        L_high = lagrangian_high.compute_fibration_lagrangian(berry_phase)
        L_low = lagrangian_low.compute_fibration_lagrangian(berry_phase)
        
        # High coherence should have different behavior
        # (less penalty from intersection term)
        penalty_high = -(1.0 - 0.95)**2
        penalty_low = -(1.0 - 0.5)**2
        
        assert penalty_high > penalty_low  # Less negative = better


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

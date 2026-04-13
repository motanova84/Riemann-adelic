#!/usr/bin/env python3
"""
Tests for Wave Energy Balance implementation.

Tests the energy balance equation:
    dE/dt(t) = ⟨ζ'(1/2)·π·∇²Φ(t), ∂Ψ/∂t(t)⟩_{L²}

where:
    E(t) = (1/2)‖∂Ψ/∂t(t)‖²_{L²} + (1/2)ω₀²‖Ψ(t)‖²_{L²}

Author: José Manuel Mota Burruezo
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: November 2025
"""

import pytest
import numpy as np
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from utils.wave_energy_balance import WaveEnergyBalance, create_test_solution


class TestWaveEnergyBalanceInit:
    """Tests for WaveEnergyBalance initialization."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.tolerance = 1e-6
        
    def test_initialization(self):
        """Test proper initialization."""
        assert self.wave_balance.f0 == 141.7001
        assert self.wave_balance.precision == 15
        assert self.wave_balance.omega_0 > 0
        
    def test_omega_0_calculation(self):
        """Test that ω₀ = 2πf₀."""
        expected_omega = 2 * np.pi * 141.7001
        assert abs(self.wave_balance.omega_0 - expected_omega) < self.tolerance
        
    def test_omega_0_squared(self):
        """Test that ω₀² is correctly computed."""
        expected = self.wave_balance.omega_0 ** 2
        assert abs(self.wave_balance.omega_0_squared - expected) < self.tolerance
        
    def test_zeta_prime_half_value(self):
        """Test that ζ'(1/2) is correct."""
        zeta_p = self.wave_balance.zeta_prime_half
        
        # ζ'(1/2) should be negative
        assert zeta_p < 0, "ζ'(1/2) should be negative"
        
        # Known approximate value
        expected_value = -3.9226461392
        assert abs(zeta_p - expected_value) < 0.01
        
    def test_source_factor(self):
        """Test source factor ζ'(1/2)·π."""
        expected = self.wave_balance.zeta_prime_half * np.pi
        assert abs(self.wave_balance.source_factor - expected) < self.tolerance
        
    def test_qcal_coherence(self):
        """Test QCAL coherence constant."""
        assert self.wave_balance.qcal_coherence == 244.36
        
    def test_get_parameters(self):
        """Test parameter retrieval."""
        params = self.wave_balance.get_parameters()
        
        assert 'f0_Hz' in params
        assert 'omega_0_rad_s' in params
        assert 'omega_0_squared' in params
        assert 'zeta_prime_half' in params
        assert 'source_factor' in params
        assert 'qcal_coherence' in params
        
        assert params['f0_Hz'] == 141.7001


class TestEnergyCalculations:
    """Tests for energy calculation functions."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 100)
        
    def test_kinetic_energy_positive(self):
        """Test that kinetic energy is non-negative."""
        dPsi_dt = np.random.randn(100)
        E_k = self.wave_balance.kinetic_energy(dPsi_dt)
        assert E_k >= 0
        
    def test_kinetic_energy_zero_for_zero_input(self):
        """Test kinetic energy is zero when dPsi/dt = 0."""
        dPsi_dt = np.zeros(100)
        E_k = self.wave_balance.kinetic_energy(dPsi_dt)
        assert abs(E_k) < 1e-15
        
    def test_potential_energy_positive(self):
        """Test that potential energy is non-negative."""
        Psi = np.random.randn(100)
        E_p = self.wave_balance.potential_energy(Psi)
        assert E_p >= 0
        
    def test_potential_energy_zero_for_zero_input(self):
        """Test potential energy is zero when Psi = 0."""
        Psi = np.zeros(100)
        E_p = self.wave_balance.potential_energy(Psi)
        assert abs(E_p) < 1e-15
        
    def test_total_energy_sum(self):
        """Test that total energy is sum of kinetic and potential."""
        Psi = np.random.randn(100)
        dPsi_dt = np.random.randn(100)
        
        E_total = self.wave_balance.total_energy(Psi, dPsi_dt)
        E_k = self.wave_balance.kinetic_energy(dPsi_dt)
        E_p = self.wave_balance.potential_energy(Psi)
        
        assert abs(E_total - (E_k + E_p)) < 1e-10
        
    def test_total_energy_nonnegative(self):
        """Test total energy is always non-negative."""
        Psi = np.random.randn(100)
        dPsi_dt = np.random.randn(100)
        
        E_total = self.wave_balance.total_energy(Psi, dPsi_dt)
        assert E_total >= 0


class TestSourceTerm:
    """Tests for source term calculation."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        
    def test_source_term_scaling(self):
        """Test that source term scales correctly."""
        laplacian_Phi = np.array([1.0, 2.0, 3.0])
        
        source = self.wave_balance.source_term(laplacian_Phi)
        expected = self.wave_balance.source_factor * laplacian_Phi
        
        assert np.allclose(source, expected)
        
    def test_source_term_zero(self):
        """Test source term is zero when ∇²Φ = 0."""
        laplacian_Phi = np.zeros(100)
        source = self.wave_balance.source_term(laplacian_Phi)
        
        assert np.allclose(source, 0)
        
    def test_source_term_sign(self):
        """Test source term preserves sign structure."""
        # ζ'(1/2) is negative, so source has opposite sign to laplacian
        laplacian_Phi = np.array([1.0, -1.0])
        source = self.wave_balance.source_term(laplacian_Phi)
        
        # source_factor = ζ'(1/2)·π is negative
        assert source[0] < 0  # positive input becomes negative
        assert source[1] > 0  # negative input becomes positive


class TestPowerInput:
    """Tests for power input calculation."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 100)
        
    def test_power_input_zero_no_source(self):
        """Test power is zero when source is zero."""
        laplacian_Phi = np.zeros(100)
        dPsi_dt = np.random.randn(100)
        
        P = self.wave_balance.power_input(laplacian_Phi, dPsi_dt)
        assert abs(P) < 1e-10
        
    def test_power_input_zero_no_velocity(self):
        """Test power is zero when dPsi/dt is zero."""
        laplacian_Phi = np.random.randn(100)
        dPsi_dt = np.zeros(100)
        
        P = self.wave_balance.power_input(laplacian_Phi, dPsi_dt)
        assert abs(P) < 1e-10
        
    def test_power_input_symmetric(self):
        """Test power input calculation is consistent."""
        laplacian_Phi = np.cos(self.x)
        dPsi_dt = np.sin(self.x)
        
        P = self.wave_balance.power_input(laplacian_Phi, dPsi_dt, self.x)
        
        # Power should be finite
        assert np.isfinite(P)


class TestEnergyConservation:
    """Tests for energy conservation in homogeneous case."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 200)
        
    def test_energy_conservation_homogeneous(self):
        """Test energy conservation when Φ = 0."""
        # Create homogeneous solution at different times
        energies = []
        times = [0.0, 0.0001, 0.0002, 0.0003]
        
        for t in times:
            Psi, dPsi_dt, _ = create_test_solution(self.x, t, self.wave_balance)
            result = self.wave_balance.energy_conservation_check(Psi, dPsi_dt, self.x)
            energies.append(result['energy'])
        
        # Energy should be nearly constant
        energy_variation = max(energies) - min(energies)
        relative_variation = energy_variation / np.mean(energies)
        
        assert relative_variation < 0.01, "Energy should be conserved"
        
    def test_power_zero_homogeneous(self):
        """Test power input is zero for homogeneous case."""
        t = 0.001
        Psi, dPsi_dt, _ = create_test_solution(self.x, t, self.wave_balance)
        
        result = self.wave_balance.energy_conservation_check(Psi, dPsi_dt, self.x)
        
        # Power input should be zero (no source)
        assert abs(result['power_input']) < 1e-10


class TestEnergyBalance:
    """Tests for the energy balance equation."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 200)
        
    def test_energy_balance_verification(self):
        """Test energy balance verification returns correct fields."""
        t = 0.001
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(self.x, t, self.wave_balance)
        laplacian_Phi = np.zeros_like(Psi)
        
        result = self.wave_balance.verify_energy_balance(
            Psi, dPsi_dt, d2Psi_dt2, laplacian_Phi, self.x
        )
        
        assert 'energy' in result
        assert 'power_input' in result
        assert 'dE_dt_numerical' in result
        assert 'residual' in result
        assert 'balance_verified' in result
        assert 'kinetic_energy' in result
        assert 'potential_energy' in result
        
    def test_energy_positive(self):
        """Test that computed energy is positive."""
        t = 0.001
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(self.x, t, self.wave_balance)
        laplacian_Phi = np.zeros_like(Psi)
        
        result = self.wave_balance.verify_energy_balance(
            Psi, dPsi_dt, d2Psi_dt2, laplacian_Phi, self.x
        )
        
        assert result['energy'] > 0
        assert result['kinetic_energy'] >= 0
        assert result['potential_energy'] >= 0


class TestTestSolution:
    """Tests for the test solution generator."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 100)
        
    def test_solution_shapes(self):
        """Test that generated solutions have correct shapes."""
        t = 0.0
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(self.x, t, self.wave_balance)
        
        assert Psi.shape == self.x.shape
        assert dPsi_dt.shape == self.x.shape
        assert d2Psi_dt2.shape == self.x.shape
        
    def test_solution_at_t_zero(self):
        """Test solution at t=0."""
        t = 0.0
        A, k = 1.0, 1.0
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(
            self.x, t, self.wave_balance, A=A, k=k
        )
        
        # At t=0: Ψ = A·cos(kx)·cos(0) = A·cos(kx)
        expected_Psi = A * np.cos(k * self.x)
        assert np.allclose(Psi, expected_Psi)
        
        # At t=0: ∂Ψ/∂t = -A·ω·cos(kx)·sin(0) = 0
        assert np.allclose(dPsi_dt, 0, atol=1e-10)
        
    def test_solution_satisfies_homogeneous_equation(self):
        """Test that solution satisfies ∂²Ψ/∂t² = -ω₀²Ψ."""
        t = 0.001
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(self.x, t, self.wave_balance)
        
        # d2Psi_dt2 should equal -ω₀²Ψ
        expected = -self.wave_balance.omega_0_squared * Psi
        assert np.allclose(d2Psi_dt2, expected)


class TestNumericalStability:
    """Tests for numerical stability."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 200)
        
    def test_large_amplitude_stability(self):
        """Test stability with large amplitudes."""
        t = 0.001
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(
            self.x, t, self.wave_balance, A=1e6
        )
        
        E = self.wave_balance.total_energy(Psi, dPsi_dt, self.x)
        
        assert np.isfinite(E), "Energy should be finite for large amplitudes"
        assert E > 0, "Energy should be positive"
        
    def test_small_amplitude_stability(self):
        """Test stability with small amplitudes."""
        t = 0.001
        Psi, dPsi_dt, d2Psi_dt2 = create_test_solution(
            self.x, t, self.wave_balance, A=1e-10
        )
        
        E = self.wave_balance.total_energy(Psi, dPsi_dt, self.x)
        
        assert np.isfinite(E), "Energy should be finite for small amplitudes"
        assert E >= 0, "Energy should be non-negative"


class TestPhysicalConsistency:
    """Tests for physical consistency."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_balance = WaveEnergyBalance(f0=141.7001, precision=15)
        self.x = np.linspace(-np.pi, np.pi, 200)
        
    def test_energy_equipartition(self):
        """Test energy equipartition at average over period."""
        # Over a full period, average kinetic ≈ average potential
        T = 2 * np.pi / self.wave_balance.omega_0
        n_samples = 100
        times = np.linspace(0, T, n_samples)
        
        kinetic_energies = []
        potential_energies = []
        
        for t in times:
            Psi, dPsi_dt, _ = create_test_solution(self.x, t, self.wave_balance)
            kinetic_energies.append(self.wave_balance.kinetic_energy(dPsi_dt, self.x))
            potential_energies.append(self.wave_balance.potential_energy(Psi, self.x))
        
        avg_kinetic = np.mean(kinetic_energies)
        avg_potential = np.mean(potential_energies)
        
        # For harmonic oscillator, average kinetic ≈ average potential
        # Allow some tolerance due to numerical integration
        ratio = avg_kinetic / avg_potential if avg_potential > 0 else 0
        assert 0.5 < ratio < 2.0, "Energy should be roughly equipartitioned"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

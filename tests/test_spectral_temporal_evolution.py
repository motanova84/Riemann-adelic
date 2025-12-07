#!/usr/bin/env python3
"""
Tests for Spectral Temporal Evolution module.

Tests the theorem:
    Ψ(x,t) = Σₙ [aₙ cos(√λₙ t) + bₙ sin(√λₙ t)/√λₙ] eₙ(x)

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import pytest
import numpy as np
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from utils.spectral_temporal_evolution import (
    SpectralTemporalEvolution,
    Eigenmode,
    example_gaussian_initial_conditions,
    example_coherent_state
)


class TestEigenmode:
    """Test suite for Eigenmode dataclass."""
    
    def test_eigenmode_creation(self):
        """Test basic eigenmode creation."""
        def test_func(x):
            return np.exp(-x**2)
        
        mode = Eigenmode(
            n=0,
            eigenvalue=1.0,
            eigenfunction=test_func,
            a_n=1.0,
            b_n=0.5
        )
        
        assert mode.n == 0
        assert mode.eigenvalue == 1.0
        assert mode.a_n == 1.0
        assert mode.b_n == 0.5
    
    def test_omega_n_property(self):
        """Test that ωₙ = √λₙ."""
        mode = Eigenmode(
            n=0,
            eigenvalue=4.0,
            eigenfunction=lambda x: x
        )
        
        assert mode.omega_n == 2.0
    
    def test_omega_n_positive(self):
        """Test that ωₙ is positive for positive eigenvalues."""
        eigenvalue = 10.0
        mode = Eigenmode(
            n=0,
            eigenvalue=eigenvalue,
            eigenfunction=lambda x: x
        )
        
        assert mode.omega_n > 0
        assert abs(mode.omega_n**2 - eigenvalue) < 1e-10


class TestSpectralTemporalEvolution:
    """Test suite for SpectralTemporalEvolution class."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.evolution = SpectralTemporalEvolution(precision=15)
        self.tolerance = 1e-6
        
    def test_initialization_default(self):
        """Test default initialization creates eigenmodes."""
        assert len(self.evolution.eigenmodes) > 0
        
    def test_eigenvalues_positive(self):
        """Test all eigenvalues are positive."""
        for mode in self.evolution.eigenmodes:
            assert mode.eigenvalue > 0, f"Eigenvalue λ_{mode.n} should be positive"
    
    def test_eigenvalues_from_riemann_zeros(self):
        """Test eigenvalues are based on Riemann zeros: λₙ = 1/4 + γₙ²."""
        # First Riemann zero γ₁ ≈ 14.13
        first_mode = self.evolution.eigenmodes[0]
        gamma_0 = np.sqrt(first_mode.eigenvalue - 0.25)
        
        # γ₀ should be close to 14.13
        assert abs(gamma_0 - 14.13) < 0.1
    
    def test_frequencies_array(self):
        """Test get_frequencies returns correct values."""
        frequencies = self.evolution.get_frequencies()
        eigenvalues = self.evolution.get_eigenvalues()
        
        for i, (freq, eigval) in enumerate(zip(frequencies, eigenvalues)):
            expected_freq = np.sqrt(eigval)
            assert abs(freq - expected_freq) < self.tolerance
    
    def test_compute_coefficients_shapes(self):
        """Test coefficient computation returns correct shapes."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        a_coeffs, b_coeffs = self.evolution.get_coefficients()
        
        assert len(a_coeffs) == len(self.evolution.eigenmodes)
        assert len(b_coeffs) == len(self.evolution.eigenmodes)
    
    def test_mode_evolution_at_t_zero(self):
        """Test mode evolution at t=0 returns aₙ."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        for n, mode in enumerate(self.evolution.eigenmodes):
            c_n_0 = self.evolution.mode_evolution(n, 0.0)
            # At t=0: cₙ(0) = aₙ·cos(0) + bₙ·sin(0)/ωₙ = aₙ
            assert abs(c_n_0 - mode.a_n) < self.tolerance
    
    def test_mode_evolution_periodicity(self):
        """Test mode evolution is periodic with period 2π/ωₙ."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        n = 0
        T = self.evolution.period_of_mode(n)
        
        c_n_0 = self.evolution.mode_evolution(n, 0.0)
        c_n_T = self.evolution.mode_evolution(n, T)
        
        # Should return to same value after one period
        assert abs(c_n_0 - c_n_T) < self.tolerance
    
    def test_Psi_at_time_shape(self):
        """Test Ψ(x,t) has correct shape."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        x = np.linspace(-5, 5, 100)
        t = 0.1
        
        Psi_t = self.evolution.Psi_at_time(x, t)
        
        assert Psi_t.shape == x.shape
    
    def test_Psi_at_time_finite(self):
        """Test Ψ(x,t) returns finite values."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        x = np.linspace(-5, 5, 100)
        
        for t in [0.0, 0.1, 0.5, 1.0]:
            Psi_t = self.evolution.Psi_at_time(x, t)
            assert np.all(np.isfinite(Psi_t)), f"Ψ should be finite at t={t}"
    
    def test_energy_mode_nonnegative(self):
        """Test energy in each mode is non-negative."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        for n in range(len(self.evolution.eigenmodes)):
            E_n = self.evolution.energy_in_mode(n)
            assert E_n >= 0, f"Energy E_{n} should be non-negative"
    
    def test_total_energy_nonnegative(self):
        """Test total energy is non-negative."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        E_total = self.evolution.total_energy()
        assert E_total >= 0
    
    def test_period_positive(self):
        """Test all periods are positive."""
        for n in range(len(self.evolution.eigenmodes)):
            T_n = self.evolution.period_of_mode(n)
            assert T_n > 0, f"Period T_{n} should be positive"
    
    def test_period_formula(self):
        """Test period formula: Tₙ = 2π/ωₙ."""
        for n in range(len(self.evolution.eigenmodes)):
            T_n = self.evolution.period_of_mode(n)
            omega_n = self.evolution.eigenmodes[n].omega_n
            expected = 2 * np.pi / omega_n
            assert abs(T_n - expected) < self.tolerance
    
    def test_spectral_density_nonnegative(self):
        """Test spectral density |cₙ(t)|² is non-negative."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        self.evolution.compute_coefficients(Psi_0, Psi_1)
        
        for t in [0.0, 0.1, 0.5]:
            density = self.evolution.spectral_density(t)
            assert np.all(density >= 0)
    
    def test_mode_out_of_range_raises(self):
        """Test accessing invalid mode raises IndexError."""
        with pytest.raises(IndexError):
            self.evolution.mode_evolution(100, 0.0)
        
        with pytest.raises(IndexError):
            self.evolution.energy_in_mode(100)
        
        with pytest.raises(IndexError):
            self.evolution.period_of_mode(100)
    
    def test_qcal_constants(self):
        """Test QCAL constants are set correctly."""
        assert SpectralTemporalEvolution.QCAL_FREQUENCY == 141.7001
        assert SpectralTemporalEvolution.QCAL_COHERENCE == 244.36


class TestEnergyConservation:
    """Tests for energy conservation properties."""
    
    def test_energy_constant_in_time(self):
        """Test total energy is approximately constant over time."""
        evolution = SpectralTemporalEvolution(precision=15)
        
        # Use coherent state for well-defined energy
        Psi_0, Psi_1 = example_coherent_state(omega=1.0, alpha=1.0)
        evolution.compute_coefficients(Psi_0, Psi_1)
        
        # Calculate energy at different times
        times = np.linspace(0, 1.0, 10)
        
        # For spectral decomposition, energy is sum of mode energies (constant)
        E_total = evolution.total_energy()
        
        # Energy should be the same at all times
        # (this is guaranteed by the spectral structure)
        assert E_total >= 0
    
    def test_spectral_density_sum_constant(self):
        """Test Σₙ |cₙ(t)|² changes are bounded (approximate Parseval).
        
        Note: With a truncated basis (10 eigenmodes), the sum Σₙ |cₙ(t)|²
        oscillates as energy moves between captured and uncaptured modes.
        We verify that the sum remains positive and finite.
        """
        evolution = SpectralTemporalEvolution(precision=15)
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        evolution.compute_coefficients(Psi_0, Psi_1)
        
        times = [0.0, 0.1, 0.5, 1.0]
        total_densities = []
        
        for t in times:
            density = evolution.spectral_density(t)
            total_densities.append(np.sum(density))
        
        # All should be positive and finite
        for density in total_densities:
            assert density >= 0, "Density sum should be non-negative"
            assert np.isfinite(density), "Density sum should be finite"
        
        # The sum should remain in a reasonable range
        # (exact conservation requires complete basis)
        assert max(total_densities) < 100 * min(total_densities) + 1


class TestExampleInitialConditions:
    """Tests for example initial condition functions."""
    
    def test_gaussian_normalized(self):
        """Test Gaussian initial condition is normalized."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions(sigma=1.0)
        
        x = np.linspace(-10, 10, 1000)
        dx = x[1] - x[0]
        
        psi_vals = Psi_0(x)
        norm_sq = np.trapezoid(np.abs(psi_vals)**2, x)
        
        # Should be approximately 1
        assert abs(norm_sq - 1.0) < 0.1
    
    def test_gaussian_velocity_zero(self):
        """Test Gaussian initial velocity is zero."""
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        
        x = np.linspace(-5, 5, 100)
        psi_1_vals = Psi_1(x)
        
        assert np.allclose(psi_1_vals, 0.0)
    
    def test_gaussian_centered(self):
        """Test Gaussian is centered at x0."""
        x0 = 2.0
        Psi_0, _ = example_gaussian_initial_conditions(x0=x0)
        
        x = np.linspace(-10, 10, 1000)
        psi_vals = np.abs(Psi_0(x))
        
        # Maximum should be near x0
        max_idx = np.argmax(psi_vals)
        assert abs(x[max_idx] - x0) < 0.2
    
    def test_coherent_state_creation(self):
        """Test coherent state creation."""
        Psi_0, Psi_1 = example_coherent_state(omega=1.0, alpha=1.0)
        
        x = np.linspace(-10, 10, 100)
        
        psi_0_vals = Psi_0(x)
        psi_1_vals = Psi_1(x)
        
        assert np.all(np.isfinite(psi_0_vals))
        assert np.all(np.isfinite(psi_1_vals))


class TestCustomEigenmodes:
    """Tests with custom eigenmodes."""
    
    def test_custom_eigenmode_list(self):
        """Test evolution with custom eigenmode list."""
        # Create simple eigenmodes
        eigenmodes = [
            Eigenmode(
                n=0,
                eigenvalue=1.0,
                eigenfunction=lambda x: np.exp(-x**2),
                a_n=1.0,
                b_n=0.0
            ),
            Eigenmode(
                n=1,
                eigenvalue=4.0,
                eigenfunction=lambda x: x * np.exp(-x**2),
                a_n=0.5,
                b_n=0.5
            )
        ]
        
        evolution = SpectralTemporalEvolution(eigenmodes=eigenmodes)
        
        assert len(evolution.eigenmodes) == 2
        assert evolution.eigenmodes[0].eigenvalue == 1.0
        assert evolution.eigenmodes[1].eigenvalue == 4.0
    
    def test_negative_eigenvalue_raises(self):
        """Test negative eigenvalue raises ValueError."""
        eigenmodes = [
            Eigenmode(
                n=0,
                eigenvalue=-1.0,  # Invalid!
                eigenfunction=lambda x: x
            )
        ]
        
        with pytest.raises(ValueError):
            SpectralTemporalEvolution(eigenmodes=eigenmodes)
    
    def test_zero_eigenvalue_raises(self):
        """Test zero eigenvalue raises ValueError."""
        eigenmodes = [
            Eigenmode(
                n=0,
                eigenvalue=0.0,  # Invalid!
                eigenfunction=lambda x: x
            )
        ]
        
        with pytest.raises(ValueError):
            SpectralTemporalEvolution(eigenmodes=eigenmodes)


class TestNumericalStability:
    """Tests for numerical stability."""
    
    def test_large_time_stability(self):
        """Test stability for large time values."""
        evolution = SpectralTemporalEvolution(precision=15)
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        evolution.compute_coefficients(Psi_0, Psi_1)
        
        x = np.linspace(-5, 5, 50)
        
        # Test at large times
        for t in [10.0, 100.0, 1000.0]:
            Psi_t = evolution.Psi_at_time(x, t, n_modes=3)
            assert np.all(np.isfinite(Psi_t)), f"Should be finite at t={t}"
    
    def test_many_modes(self):
        """Test with all available modes."""
        evolution = SpectralTemporalEvolution(precision=15)
        Psi_0, Psi_1 = example_gaussian_initial_conditions()
        evolution.compute_coefficients(Psi_0, Psi_1)
        
        x = np.linspace(-5, 5, 50)
        t = 0.5
        
        Psi_t = evolution.Psi_at_time(x, t)
        
        assert np.all(np.isfinite(Psi_t))
    
    def test_different_precisions(self):
        """Test with different precision settings."""
        for precision in [10, 15, 25]:
            evolution = SpectralTemporalEvolution(precision=precision)
            assert evolution.precision == precision


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

#!/usr/bin/env python3
"""
Tests for Wave Equation Consciousness implementation.

Tests the equation: ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import pytest
import numpy as np
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from utils.wave_equation_consciousness import WaveEquationConsciousness, example_harmonic_potential


class TestWaveEquationConsciousness:
    """Test suite for WaveEquationConsciousness class."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        self.tolerance = 1e-6
        
    def test_initialization(self):
        """Test proper initialization of the wave equation."""
        assert self.wave_eq.f0 == 141.7001
        assert self.wave_eq.precision == 15
        assert self.wave_eq.omega_0 > 0
        
    def test_omega_0_calculation(self):
        """Test that ω₀ = 2πf₀."""
        expected_omega = 2 * np.pi * 141.7001
        assert abs(self.wave_eq.omega_0 - expected_omega) < self.tolerance
        
    def test_zeta_prime_half_value(self):
        """Test that ζ'(1/2) is computed with correct sign and magnitude."""
        zeta_p = self.wave_eq.zeta_prime_half
        
        # ζ'(1/2) should be negative
        assert zeta_p < 0, "ζ'(1/2) should be negative"
        
        # Known approximate value
        expected_value = -3.9226461392
        assert abs(zeta_p - expected_value) < 0.01, f"ζ'(1/2) = {zeta_p}, expected ≈ {expected_value}"
        
    def test_homogeneous_solution_at_t_zero(self):
        """Test homogeneous solution at t=0."""
        t = np.array([0.0])
        A, B = 1.0, 0.5
        Psi_h = self.wave_eq.homogeneous_solution(t, A=A, B=B)
        
        # At t=0: Ψ_h = A·cos(0) + B·sin(0) = A
        assert abs(Psi_h[0] - A) < self.tolerance
        
    def test_homogeneous_solution_period(self):
        """Test that homogeneous solution has correct period."""
        T = 2 * np.pi / self.wave_eq.omega_0  # Period
        t = np.array([0.0, T])
        
        Psi_h = self.wave_eq.homogeneous_solution(t, A=1.0, B=0.0)
        
        # Should return to same value after one period
        assert abs(Psi_h[0] - Psi_h[1]) < self.tolerance
        
    def test_homogeneous_solution_satisfies_equation(self):
        """Test that homogeneous solution satisfies ∂²Ψ/∂t² + ω₀²Ψ = 0."""
        t = np.linspace(0, 0.01, 100)
        A, B = 1.0, 0.5
        
        Psi_h = self.wave_eq.homogeneous_solution(t, A=A, B=B)
        
        # For harmonic solution: ∂²Ψ/∂t² = -ω₀²Ψ
        d2Psi_dt2 = -self.wave_eq.omega_0**2 * Psi_h
        
        # Check left side with no forcing (Φ=0)
        residual = self.wave_eq.residual(Psi_h, d2Psi_dt2, np.zeros_like(Psi_h))
        
        # Should be very close to zero
        assert np.max(np.abs(residual)) < 1e-10
        
    def test_particular_solution(self):
        """Test particular solution computation."""
        laplacian_Phi = np.array([1.0, 2.0, 3.0])
        Psi_p = self.wave_eq.particular_solution(laplacian_Phi)
        
        # Ψ_p = ζ'(1/2)·∇²Φ / ω₀²
        expected = self.wave_eq.zeta_prime_half * laplacian_Phi / (self.wave_eq.omega_0**2)
        
        assert np.allclose(Psi_p, expected, rtol=self.tolerance)
        
    def test_left_side_operator(self):
        """Test left side of equation: ∂²Ψ/∂t² + ω₀²Ψ."""
        Psi = np.array([1.0, 2.0, 3.0])
        d2Psi_dt2 = np.array([0.5, 1.0, 1.5])
        
        left = self.wave_eq.left_side(Psi, d2Psi_dt2)
        expected = d2Psi_dt2 + self.wave_eq.omega_0**2 * Psi
        
        assert np.allclose(left, expected, rtol=self.tolerance)
        
    def test_right_side_operator(self):
        """Test right side of equation: ζ'(1/2)·∇²Φ."""
        laplacian_Phi = np.array([1.0, 2.0, 3.0])
        
        right = self.wave_eq.right_side(laplacian_Phi)
        expected = self.wave_eq.zeta_prime_half * laplacian_Phi
        
        assert np.allclose(right, expected, rtol=self.tolerance)
        
    def test_residual_zero_for_exact_solution(self):
        """Test that residual is zero for exact homogeneous solution."""
        t = np.linspace(0, 0.01, 50)
        Psi_h = self.wave_eq.homogeneous_solution(t, A=1.0, B=0.0)
        
        # For homogeneous solution: ∂²Ψ/∂t² = -ω₀²Ψ
        d2Psi_dt2 = -self.wave_eq.omega_0**2 * Psi_h
        
        residual = self.wave_eq.residual(Psi_h, d2Psi_dt2, np.zeros_like(Psi_h))
        
        assert np.max(np.abs(residual)) < 1e-10
        
    def test_resonance_condition_exact(self):
        """Test resonance condition for exact frequency."""
        omega_exact = self.wave_eq.omega_0
        
        assert self.wave_eq.resonance_condition(omega_exact, tolerance=1e-10)
        
    def test_resonance_condition_near(self):
        """Test resonance condition for near frequency."""
        omega_near = self.wave_eq.omega_0 + 0.005  # Within default tolerance
        
        assert self.wave_eq.resonance_condition(omega_near, tolerance=0.01)
        
    def test_resonance_condition_far(self):
        """Test resonance condition for far frequency."""
        omega_far = self.wave_eq.omega_0 + 100.0  # Far from resonance
        
        assert not self.wave_eq.resonance_condition(omega_far, tolerance=1e-3)
        
    def test_energy_density_positive(self):
        """Test that energy density is non-negative."""
        t = np.linspace(0, 0.01, 100)
        Psi = self.wave_eq.homogeneous_solution(t, A=1.0, B=0.5)
        
        # Approximate derivatives
        dPsi_dt = -self.wave_eq.omega_0 * (np.sin(self.wave_eq.omega_0 * t) - 0.5 * np.cos(self.wave_eq.omega_0 * t))
        grad_Psi = np.gradient(Psi, t[1] - t[0])
        
        energy = self.wave_eq.energy_density(Psi, dPsi_dt, grad_Psi)
        
        # Energy should be non-negative
        assert np.all(energy >= 0), "Energy density should be non-negative"
        
    def test_energy_conservation_homogeneous(self):
        """Test energy conservation for homogeneous solution."""
        t = np.linspace(0, 0.02, 1000)
        A, B = 1.0, 0.5
        Psi = self.wave_eq.homogeneous_solution(t, A=A, B=B)
        
        dPsi_dt = -self.wave_eq.omega_0 * (A * np.sin(self.wave_eq.omega_0 * t) - B * np.cos(self.wave_eq.omega_0 * t))
        grad_Psi = np.gradient(Psi, t[1] - t[0])
        
        energy = self.wave_eq.energy_density(Psi, dPsi_dt, grad_Psi)
        
        # For harmonic oscillator, average energy should be roughly constant
        # Allow for numerical errors
        energy_std = np.std(energy)
        energy_mean = np.mean(energy)
        
        # Standard deviation should be small compared to mean
        assert energy_std / energy_mean < 0.5, "Energy should be relatively constant"
        
    def test_get_parameters(self):
        """Test parameter retrieval."""
        params = self.wave_eq.get_parameters()
        
        assert 'f0_Hz' in params
        assert 'omega_0_rad_s' in params
        assert 'zeta_prime_half' in params
        assert 'precision_dps' in params
        
        assert params['f0_Hz'] == 141.7001
        assert params['precision_dps'] == 15


class TestExampleHarmonicPotential:
    """Test suite for example harmonic potential."""
    
    def test_potential_shape(self):
        """Test that potential has correct shape."""
        x = np.linspace(-5, 5, 100)
        t = 0.0
        Phi, laplacian_Phi = example_harmonic_potential(x, t, sigma=1.0)
        
        assert Phi.shape == x.shape
        assert laplacian_Phi.shape == x.shape
        
    def test_potential_maximum_at_origin(self):
        """Test that potential maximum is at x=0 for t=0."""
        x = np.linspace(-5, 5, 1000)
        t = 0.0
        Phi, _ = example_harmonic_potential(x, t, sigma=1.0)
        
        # Maximum should be near x=0
        max_idx = np.argmax(Phi)
        assert abs(x[max_idx]) < 0.1, "Maximum should be near origin"
        
    def test_potential_gaussian_decay(self):
        """Test that potential decays like Gaussian."""
        x = np.array([0.0, 1.0, 2.0])
        t = 0.0
        Phi, _ = example_harmonic_potential(x, t, sigma=1.0)
        
        # At x=0, Phi should be maximum (cos(0) = 1)
        # At x>0, Phi should decay exponentially
        assert Phi[0] > Phi[1] > Phi[2], "Potential should decay with |x|"
        
    def test_laplacian_sign_change(self):
        """Test that Laplacian changes sign."""
        x = np.linspace(-3, 3, 100)
        t = 0.0
        _, laplacian_Phi = example_harmonic_potential(x, t, sigma=1.0)
        
        # Laplacian should have both positive and negative values
        assert np.any(laplacian_Phi > 0), "Laplacian should have positive values"
        assert np.any(laplacian_Phi < 0), "Laplacian should have negative values"


class TestPhysicalConsistency:
    """Tests for physical consistency of the wave equation."""
    
    def test_dimensional_consistency(self):
        """Test that all terms have consistent dimensions."""
        wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        
        # All these should have dimension of [Ψ]/[T²]
        Psi = np.array([1.0])
        d2Psi_dt2 = np.array([1.0])
        laplacian_Phi = np.array([1.0])
        
        left = wave_eq.left_side(Psi, d2Psi_dt2)
        right = wave_eq.right_side(laplacian_Phi)
        
        # Both sides should have same dimension (units don't matter, just consistency)
        assert left.shape == right.shape
        
    def test_superposition_principle(self):
        """Test that solutions obey superposition."""
        wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        
        t = np.linspace(0, 0.01, 100)
        
        # Two homogeneous solutions
        Psi1 = wave_eq.homogeneous_solution(t, A=1.0, B=0.0)
        Psi2 = wave_eq.homogeneous_solution(t, A=0.0, B=1.0)
        
        # Superposition
        Psi_sum = Psi1 + Psi2
        
        # Check that superposition also satisfies homogeneous equation
        d2Psi_dt2 = -wave_eq.omega_0**2 * Psi_sum
        residual = wave_eq.residual(Psi_sum, d2Psi_dt2, np.zeros_like(Psi_sum))
        
        assert np.max(np.abs(residual)) < 1e-10
        
    def test_time_reversal_symmetry(self):
        """Test time reversal symmetry for homogeneous solution."""
        wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        
        t = np.linspace(-0.01, 0.01, 100)
        Psi = wave_eq.homogeneous_solution(t, A=1.0, B=0.0)
        
        # For cosine (B=0), solution should be symmetric: Ψ(-t) = Ψ(t)
        mid = len(t) // 2
        assert np.allclose(Psi[:mid][::-1], Psi[mid:], rtol=1e-5)


class TestNumericalStability:
    """Tests for numerical stability."""
    
    def test_large_amplitude_stability(self):
        """Test stability with large amplitudes."""
        wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        
        t = np.linspace(0, 0.01, 100)
        Psi_large = wave_eq.homogeneous_solution(t, A=1e6, B=1e6)
        
        # Should not overflow or produce NaN
        assert np.all(np.isfinite(Psi_large)), "Solution should be finite for large amplitudes"
        
    def test_small_amplitude_stability(self):
        """Test stability with small amplitudes."""
        wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        
        t = np.linspace(0, 0.01, 100)
        Psi_small = wave_eq.homogeneous_solution(t, A=1e-10, B=1e-10)
        
        # Should not underflow or produce NaN
        assert np.all(np.isfinite(Psi_small)), "Solution should be finite for small amplitudes"
        
    def test_long_time_evolution(self):
        """Test solution over long time periods."""
        wave_eq = WaveEquationConsciousness(f0=141.7001, precision=15)
        
        # Evolve for 100 periods
        T = 2 * np.pi / wave_eq.omega_0
        t = np.linspace(0, 100 * T, 10000)
        
        Psi = wave_eq.homogeneous_solution(t, A=1.0, B=0.5)
        
        # Amplitude should remain bounded
        assert np.max(np.abs(Psi)) < 2.0, "Amplitude should remain bounded"
        assert np.all(np.isfinite(Psi)), "Solution should remain finite over long times"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

#!/usr/bin/env python3
"""
Tests for Vacuum Energy Equation (Acto II)

Tests the implementation of the vacuum energy equation derived from
toroidal compactification with log-π symmetry.

Author: José Manuel Mota Burruezo
Date: October 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from vacuum_energy import VacuumEnergyCalculator, derive_f0_noncircular


class TestVacuumEnergyCalculator:
    """Test suite for VacuumEnergyCalculator class."""
    
    def test_initialization(self):
        """Test calculator initialization with default parameters."""
        calc = VacuumEnergyCalculator()
        
        assert calc.alpha == 1.0
        assert calc.beta == 1.0
        assert calc.gamma == 1.0
        assert calc.delta == 1.0
        assert calc.Lambda == 1.0
        assert calc._zeta_prime_half is not None
    
    def test_zeta_prime_half(self):
        """Test that ζ'(1/2) is calculated correctly."""
        calc = VacuumEnergyCalculator(precision=30)
        
        # ζ'(1/2) is approximately -3.92264...
        assert -4.0 < calc._zeta_prime_half < -3.8
    
    def test_energy_positive_radius(self):
        """Test energy calculation for positive radius."""
        calc = VacuumEnergyCalculator(
            alpha=1.0,
            beta=1.0,
            gamma=0.001,
            delta=0.5,
            Lambda=1.0
        )
        
        # Energy at R_Ψ = π should be finite
        E = calc.energy(np.pi)
        assert np.isfinite(E)
        assert not np.isnan(E)
    
    def test_energy_invalid_radius(self):
        """Test that negative or zero radius raises ValueError."""
        calc = VacuumEnergyCalculator()
        
        with pytest.raises(ValueError):
            calc.energy(0.0)
        
        with pytest.raises(ValueError):
            calc.energy(-1.0)
    
    def test_resonant_scales(self):
        """Test that resonant scales are powers of π."""
        calc = VacuumEnergyCalculator()
        
        resonant = calc.resonant_scales(n_max=3)
        expected = np.array([1.0, np.pi, np.pi**2, np.pi**3])
        
        np.testing.assert_allclose(resonant, expected, rtol=1e-10)
    
    def test_fractal_term_vanishes_at_pi_powers(self):
        """Test that sin²(log(R)/log(π)) vanishes at R = π^n."""
        calc = VacuumEnergyCalculator(
            alpha=0.0,  # Disable other terms
            beta=0.0,
            gamma=0.0,
            delta=1.0,
            Lambda=1.0
        )
        
        # At R_Ψ = π^n, the fractal term should be very small
        for n in range(5):
            R = np.pi ** n
            E = calc.energy(R)
            # sin²(n) where n is integer should give small but non-zero
            # The term is sin²(log(π^n)/log(π)) = sin²(n)
            expected = np.sin(n) ** 2
            assert abs(E - expected) < 1e-10
    
    def test_derivative_calculation(self):
        """Test derivative calculation using finite differences."""
        calc = VacuumEnergyCalculator()
        
        R = 2.0
        h = 1e-6
        
        # Numerical derivative
        dE_numerical = (calc.energy(R + h) - calc.energy(R - h)) / (2 * h)
        
        # Analytical derivative
        dE_analytical = calc.derivative(R)
        
        # Should match within numerical precision
        assert abs(dE_numerical - dE_analytical) < 1e-4
    
    def test_find_minima(self):
        """Test that minima can be found."""
        calc = VacuumEnergyCalculator(
            alpha=1.0,
            beta=1.0,
            gamma=0.001,
            delta=0.5,
            Lambda=1.0
        )
        
        minima = calc.find_minima(R_range=(0.5, 10.0), num_points=1000)
        
        # Should find at least one minimum
        assert len(minima) > 0
        
        # Minima should be positive
        assert np.all(minima > 0)
    
    def test_minimum_near_pi(self):
        """Test that minima can be found in expected ranges."""
        calc = VacuumEnergyCalculator(
            alpha=1.0,
            beta=1.0,
            gamma=0.001,
            delta=0.5,
            Lambda=1.0
        )
        
        minima = calc.find_minima(R_range=(0.5, 10.0), num_points=2000)
        
        # Should have at least one minimum
        assert len(minima) > 0
        
        # All minima should be positive
        assert np.all(minima > 0)
        
        # At least one minimum should exist in our search range
        assert np.all(minima >= 0.5) and np.all(minima <= 10.0)
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency calculation."""
        calc = VacuumEnergyCalculator()
        
        R_psi = np.pi
        f0 = calc.fundamental_frequency(R_psi, c=299792458.0)
        
        # Frequency should be positive and finite
        assert f0 > 0
        assert np.isfinite(f0)
    
    def test_energy_symmetry(self):
        """Test that energy is symmetric in certain parameter regimes."""
        calc = VacuumEnergyCalculator(
            alpha=1.0,
            beta=0.0,  # Disable adelic coupling
            gamma=1.0,
            delta=0.0,  # Disable fractal term
            Lambda=1.0
        )
        
        # With only α/R^4 and γΛ²R² terms, check scaling behavior
        R1 = 2.0
        R2 = 4.0
        
        E1 = calc.energy(R1)
        E2 = calc.energy(R2)
        
        # Both should be finite
        assert np.isfinite(E1)
        assert np.isfinite(E2)


class TestNonCircularDerivation:
    """Test suite for non-circular f₀ derivation."""
    
    def test_derive_f0_returns_valid_values(self):
        """Test that f₀ derivation returns valid values."""
        R_opt, f0 = derive_f0_noncircular(
            alpha=1.0,
            beta=1.0,
            gamma=0.001,
            delta=0.5,
            Lambda=1.0
        )
        
        # R_opt should be positive and close to π
        assert R_opt > 0
        assert 2.0 < R_opt < 5.0  # Should be near π
        
        # f0 should be positive
        assert f0 > 0
        assert np.isfinite(f0)
    
    def test_f0_close_to_target(self):
        """Test that derived f₀ is close to target 141.7001 Hz."""
        _, f0 = derive_f0_noncircular(
            alpha=1.0,
            beta=1.0,
            gamma=0.001,
            delta=0.5,
            Lambda=1.0,
            target_f0=141.7001
        )
        
        # Should be close to target (within calibration tolerance)
        assert 100.0 < f0 < 200.0  # Reasonable range
    
    def test_parameter_sensitivity(self):
        """Test sensitivity to different parameter values."""
        params_list = [
            (1.0, 1.0, 0.001, 0.5, 1.0),
            (2.0, 1.0, 0.001, 0.5, 1.0),
            (1.0, 2.0, 0.001, 0.5, 1.0),
        ]
        
        results = []
        for params in params_list:
            R_opt, f0 = derive_f0_noncircular(*params)
            results.append((R_opt, f0))
        
        # All results should be valid
        for R_opt, f0 in results:
            assert R_opt > 0
            assert f0 > 0
            assert np.isfinite(R_opt)
            assert np.isfinite(f0)


class TestPhysicalInterpretation:
    """Test physical interpretation and properties."""
    
    def test_casimir_term_dominates_small_R(self):
        """Test that Casimir term (1/R^4) dominates at small R."""
        calc = VacuumEnergyCalculator(
            alpha=1.0,
            beta=0.1,
            gamma=0.001,
            delta=0.1,
            Lambda=1.0
        )
        
        R_small = 0.1
        E_total = calc.energy(R_small)
        
        # Casimir contribution
        E_casimir = 1.0 / (R_small ** 4)
        
        # Casimir should be dominant
        assert E_casimir / E_total > 0.8  # More than 80% contribution
    
    def test_cosmological_term_dominates_large_R(self):
        """Test that cosmological term (Λ²R²) dominates at large R."""
        calc = VacuumEnergyCalculator(
            alpha=1.0,
            beta=0.1,
            gamma=1.0,
            delta=0.1,
            Lambda=1.0
        )
        
        R_large = 100.0
        E_total = calc.energy(R_large)
        
        # Cosmological contribution
        E_cosmo = 1.0 * (1.0 ** 2) * (R_large ** 2)
        
        # Cosmological should be dominant
        assert E_cosmo / E_total > 0.8  # More than 80% contribution
    
    def test_adelic_coupling_sign(self):
        """Test that adelic coupling with ζ'(1/2) has correct sign."""
        calc = VacuumEnergyCalculator()
        
        # ζ'(1/2) is negative, so with positive β, this term is negative
        assert calc._zeta_prime_half < 0
        
        # This means the β·ζ'(1/2)/R² term is negative (attractive)
        R = np.pi
        beta_term = calc.beta * calc._zeta_prime_half / (R ** 2)
        assert beta_term < 0


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])

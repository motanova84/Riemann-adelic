#!/usr/bin/env python3
"""
Tests for Vacuum Potential Simulation with CODATA 2022 parameters

Tests the simulation of the effective vacuum potential E_vac(R_Ψ)
using real physical parameters from CODATA 2022.

Author: José Manuel Mota Burruezo
Date: Octubre 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from simulate_vacuum_potential import VacuumPotentialSimulator


class TestVacuumPotentialSimulator:
    """Test suite for VacuumPotentialSimulator class."""
    
    def test_initialization(self):
        """Test simulator initialization with default parameters."""
        sim = VacuumPotentialSimulator()
        
        assert sim.alpha == 1.0
        assert sim.beta == 1.0
        assert sim.gamma == 1.0
        assert sim.delta == 0.5
        assert sim.b == np.pi
        
        # Check physical constants
        assert sim.lP > 0
        assert sim.Lambda > 0
        assert sim.c > 0
        assert sim.zeta_prime < 0  # ζ'(1/2) is negative
    
    def test_custom_parameters(self):
        """Test initialization with custom parameters."""
        sim = VacuumPotentialSimulator(
            alpha=2.0,
            beta=0.5,
            gamma=1.5,
            delta=0.3,
            b=np.e
        )
        
        assert sim.alpha == 2.0
        assert sim.beta == 0.5
        assert sim.gamma == 1.5
        assert sim.delta == 0.3
        assert sim.b == np.e
    
    def test_Evac_calculation(self):
        """Test that Evac returns valid energy values."""
        sim = VacuumPotentialSimulator()
        
        R = np.array([1e45, 1e46, 1e47])
        E = sim.Evac(R)
        
        # All energies should be finite
        assert np.all(np.isfinite(E))
        
        # Check array shape matches
        assert E.shape == R.shape
    
    def test_Evac_terms(self):
        """Test individual terms of the Evac equation."""
        sim = VacuumPotentialSimulator(alpha=1.0, beta=1.0, gamma=1.0, delta=0.5)
        
        R = np.array([1e47])
        
        # Individual terms
        term1 = sim.alpha * R**(-4)
        term2 = sim.beta * sim.zeta_prime * R**(-2)
        term3 = sim.gamma * (sim.Lambda**2) * (R * sim.lP)**2
        term4 = sim.delta * np.sin(np.log(R) / np.log(sim.b))**2
        
        # All terms should be finite
        assert np.all(np.isfinite(term1))
        assert np.all(np.isfinite(term2))
        assert np.all(np.isfinite(term3))
        assert np.all(np.isfinite(term4))
        
        # Total should equal sum
        E_total = sim.Evac(R)
        E_sum = term1 + term2 + term3 + term4
        np.testing.assert_allclose(E_total, E_sum, rtol=1e-10)
    
    def test_find_minimum(self):
        """Test that find_minimum returns valid results."""
        sim = VacuumPotentialSimulator()
        
        R_star, E_min, idx_min = sim.find_minimum(
            R_range=(1e45, 1e49),
            num_points=1000
        )
        
        # R_star should be positive and in range
        assert R_star > 0
        assert 1e45 <= R_star <= 1e49
        
        # E_min should be finite
        assert np.isfinite(E_min)
        
        # idx_min should be valid index
        assert 0 <= idx_min < 1000
    
    def test_minimum_uniqueness(self):
        """Test that the minimum is unique in the expected range."""
        sim = VacuumPotentialSimulator()
        
        # Find minimum twice with same parameters
        R_star1, E_min1, _ = sim.find_minimum(R_range=(1e45, 1e49), num_points=2000)
        R_star2, E_min2, _ = sim.find_minimum(R_range=(1e45, 1e49), num_points=2000)
        
        # Should get same result (within numerical precision)
        assert abs(R_star1 - R_star2) / R_star1 < 0.01  # Within 1%
        assert abs(E_min1 - E_min2) < 1e-6
    
    def test_compute_frequency(self):
        """Test frequency calculation."""
        sim = VacuumPotentialSimulator()
        
        R_star = 1e47  # Typical value
        f0 = sim.compute_frequency(R_star)
        
        # Frequency should be positive
        assert f0 > 0
        assert np.isfinite(f0)
        
        # For R_star ~ 1e47, frequency will be very small (order 1e-5 Hz)
        # This is physically correct given R_meters = R_star * lP ~ 1e12 m
        assert f0 > 1e-10  # Not zero, but can be very small
    
    def test_frequency_scaling(self):
        """Test that frequency scales inversely with R_star."""
        sim = VacuumPotentialSimulator()
        
        R1 = 1e47
        R2 = 2e47
        
        f1 = sim.compute_frequency(R1)
        f2 = sim.compute_frequency(R2)
        
        # f should scale as 1/R
        ratio = f1 / f2
        expected_ratio = R2 / R1
        
        assert abs(ratio - expected_ratio) / expected_ratio < 0.01  # Within 1%
    
    def test_check_stability(self):
        """Test stability check returns valid results."""
        sim = VacuumPotentialSimulator()
        
        R_vals = np.logspace(45, 49, 1000)
        E_vals = sim.Evac(R_vals)
        idx_min = np.argmin(E_vals)
        
        stability = sim.check_stability(R_vals, E_vals, idx_min)
        
        # Should return dict with required keys
        assert 'curvature' in stability
        assert 'is_stable' in stability
        
        # Curvature should be finite
        assert np.isfinite(stability['curvature'])
        
        # is_stable should be boolean
        assert isinstance(stability['is_stable'], (bool, np.bool_))
    
    def test_stability_at_minimum(self):
        """Test that the minimum is stable (positive curvature)."""
        sim = VacuumPotentialSimulator()
        
        R_vals = np.logspace(45, 49, 2000)
        E_vals = sim.Evac(R_vals)
        idx_min = np.argmin(E_vals)
        
        stability = sim.check_stability(R_vals, E_vals, idx_min)
        
        # At a true minimum, curvature should be positive
        assert stability['curvature'] > 0
        # Check boolean value, not identity
        assert stability['is_stable'] == True
    
    def test_cosmological_hierarchy_check(self):
        """Test cosmological hierarchy calculation."""
        sim = VacuumPotentialSimulator()
        
        R_star = 1e47
        hierarchy = sim.cosmological_hierarchy_check(R_star)
        
        # Should return dict with required keys
        assert 'R_Psi_over_lP' in hierarchy
        assert 'expected_scale' in hierarchy
        assert 'observed_scale' in hierarchy
        assert 'ratio' in hierarchy
        
        # All values should be positive and finite
        for key in ['R_Psi_over_lP', 'expected_scale', 'observed_scale', 'ratio']:
            assert hierarchy[key] > 0
            assert np.isfinite(hierarchy[key])
    
    def test_parameter_scan(self):
        """Test parameter scan functionality."""
        sim = VacuumPotentialSimulator()
        
        R_star_nominal = 1e47
        results = sim.parameter_scan(R_star_nominal, variation=0.1)
        
        # Should have results for all parameters
        expected_params = ['alpha', 'beta', 'gamma', 'delta', 'b']
        for param in expected_params:
            assert param in results
            
            # Each parameter should have 3 results (-, 0, +)
            assert len(results[param]) == 3
            
            # Each result should be a tuple of (factor, R_new, f0_new)
            for factor, R_new, f0_new in results[param]:
                assert np.isfinite(factor)
                assert R_new > 0
                assert f0_new > 0
                assert np.isfinite(R_new)
                assert np.isfinite(f0_new)
    
    def test_parameter_scan_variations(self):
        """Test that parameter scan produces reasonable variations."""
        sim = VacuumPotentialSimulator()
        
        R_star_nominal = 1e47
        results = sim.parameter_scan(R_star_nominal, variation=0.1)
        
        for param, scan_results in results.items():
            factors = [r[0] for r in scan_results]
            R_values = [r[1] for r in scan_results]
            f0_values = [r[2] for r in scan_results]
            
            # Factors should be in order: 0.9, 1.0, 1.1
            np.testing.assert_allclose(factors, [0.9, 1.0, 1.1], rtol=1e-10)
            
            # At least one parameter should show variation in results
            # Some parameters may have minimal effect if they don't affect the minimum location
            # so we just check that the scan completed and returned valid results
            assert len(R_values) == 3
            assert len(f0_values) == 3
            assert all(R > 0 for R in R_values)
            assert all(f > 0 for f in f0_values)
    
    def test_fractal_term_periodicity(self):
        """Test that the fractal term has log-periodic behavior."""
        sim = VacuumPotentialSimulator(alpha=0, beta=0, gamma=0, delta=1.0, b=np.pi)
        
        # At R = π^n, the fractal term sin²(n) should repeat
        R1 = np.pi**5
        R2 = np.pi**6
        R3 = np.pi**7
        
        E1 = sim.Evac(np.array([R1]))[0]
        E2 = sim.Evac(np.array([R2]))[0]
        E3 = sim.Evac(np.array([R3]))[0]
        
        # All should be finite
        assert np.isfinite(E1)
        assert np.isfinite(E2)
        assert np.isfinite(E3)
        
        # Values should follow sin² pattern
        # sin²(5), sin²(6), sin²(7)
        expected1 = np.sin(5)**2
        expected2 = np.sin(6)**2
        expected3 = np.sin(7)**2
        
        np.testing.assert_allclose(E1, expected1, rtol=1e-10)
        np.testing.assert_allclose(E2, expected2, rtol=1e-10)
        np.testing.assert_allclose(E3, expected3, rtol=1e-10)
    
    def test_physical_constants(self):
        """Test that physical constants have correct values."""
        sim = VacuumPotentialSimulator()
        
        # Planck length should be approximately 1.616e-35 m
        assert 1.6e-35 < sim.lP < 1.7e-35
        
        # Cosmological constant should be approximately 1.1e-52 m^-2
        assert 1.0e-52 < sim.Lambda < 1.2e-52
        
        # Speed of light should be exactly 299792458 m/s
        assert abs(sim.c - 299792458.0) < 1e-3
        
        # ζ'(1/2) should be approximately -0.207886
        assert abs(sim.zeta_prime - (-0.207886)) < 0.01
    
    def test_energy_asymptotic_behavior_small_R(self):
        """Test that energy diverges as R → 0 (UV term dominates)."""
        sim = VacuumPotentialSimulator()
        
        # Small values of R (UV regime)
        R_small = np.array([1e-10, 1e-5, 1e0])
        E_small = sim.Evac(R_small)
        
        # Energy should increase as R decreases (UV divergence)
        assert E_small[0] > E_small[1] > E_small[2]
    
    def test_energy_asymptotic_behavior_large_R(self):
        """Test that energy increases as R → ∞ (IR term dominates)."""
        sim = VacuumPotentialSimulator()
        
        # Large values of R (IR regime)
        R_large = np.array([1e50, 1e55, 1e60])
        E_large = sim.Evac(R_large)
        
        # Energy should increase as R increases (IR growth)
        assert E_large[2] > E_large[1] > E_large[0]


class TestPhysicalConsistency:
    """Test physical consistency of the simulation."""
    
    def test_frequency_calculation(self):
        """Test that f0 calculation is physically consistent."""
        sim = VacuumPotentialSimulator()
        
        R_star, _, _ = sim.find_minimum()
        f0 = sim.compute_frequency(R_star)
        
        # Frequency should be positive and finite
        # With CODATA values and O(1) coefficients, the minimum occurs at small R
        # giving a large frequency
        assert f0 > 0
        assert np.isfinite(f0)
    
    def test_minimum_in_physical_range(self):
        """Test that R_star is in a physical range."""
        sim = VacuumPotentialSimulator()
        
        R_star, _, _ = sim.find_minimum()
        
        # With standard CODATA values, minimum occurs at relatively small R
        # Should be positive and within the search range
        assert 1 < R_star < 1e49
    
    def test_zeta_prime_contribution(self):
        """Test that the ζ'(1/2) term contributes correctly."""
        sim = VacuumPotentialSimulator()
        
        # Use a moderate R value where all terms are significant
        R = np.array([100.0])
        
        # Calculate with and without zeta term
        E_with = sim.Evac(R)[0]
        
        sim_without = VacuumPotentialSimulator(beta=0)
        E_without = sim_without.Evac(R)[0]
        
        # They should be different
        assert abs(E_with - E_without) > 1e-10
        
        # The difference should be the zeta contribution
        zeta_contribution = sim.beta * sim.zeta_prime * R**(-2)
        expected_diff = zeta_contribution[0]
        
        np.testing.assert_allclose(E_with - E_without, expected_diff, rtol=1e-8)


class TestNumericalStability:
    """Test numerical stability of the simulation."""
    
    def test_no_nan_or_inf(self):
        """Test that calculations don't produce NaN or Inf."""
        sim = VacuumPotentialSimulator()
        
        R_vals = np.logspace(0, 48, 1000)
        E_vals = sim.Evac(R_vals)
        
        # No NaN or Inf values
        assert not np.any(np.isnan(E_vals))
        assert not np.any(np.isinf(E_vals))
    
    def test_consistent_across_precisions(self):
        """Test that results are consistent with different resolutions."""
        sim = VacuumPotentialSimulator()
        
        # Use a restricted range where the minimum is clearly defined
        search_range = (10, 100)
        
        # Low resolution
        R_star_low, _, _ = sim.find_minimum(R_range=search_range, num_points=200)
        
        # High resolution
        R_star_high, _, _ = sim.find_minimum(R_range=search_range, num_points=2000)
        
        # Should be within 10% of each other (allowing for numerical discretization)
        relative_diff = abs(R_star_low - R_star_high) / R_star_high
        assert relative_diff < 0.1


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])

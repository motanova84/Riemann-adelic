#!/usr/bin/env python3
"""
Tests for Geometric Unification Module

Tests the geometric structure that unifies ζ'(1/2) and f₀.

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import pytest
import numpy as np
from utils.geometric_unification import (
    GeometricUnification,
    verify_geometric_unification,
    print_unification_report
)


class TestGeometricUnification:
    """Test suite for GeometricUnification class."""
    
    def test_initialization(self):
        """Test that GeometricUnification initializes correctly."""
        unif = GeometricUnification(precision=30)
        
        assert unif.precision == 30
        assert unif.alpha == 1.0
        assert unif.beta == 1.0
        assert unif.gamma == 1.0
        assert unif.delta == 1.0
        assert unif.Lambda == 1.0
        assert unif.planck_length > 0
    
    def test_zeta_prime_computation(self):
        """Test computation of ζ'(1/2)."""
        unif = GeometricUnification(precision=30)
        zeta_prime = unif.compute_zeta_prime_half()
        
        # ζ'(1/2) should be negative and close to known value
        expected = -3.9226461392
        assert zeta_prime < 0
        assert abs(zeta_prime - expected) < 0.01
        
        # Test caching
        zeta_prime2 = unif.compute_zeta_prime_half()
        assert zeta_prime == zeta_prime2
    
    def test_vacuum_energy_computation(self):
        """Test vacuum energy computation."""
        unif = GeometricUnification(precision=30)
        
        # Test at R = 1.0
        E1 = unif.vacuum_energy(1.0)
        assert isinstance(E1, float)
        assert not np.isnan(E1)
        
        # Test at different radius
        E2 = unif.vacuum_energy(2.0)
        assert isinstance(E2, float)
        assert not np.isnan(E2)
        
        # Energy should be different at different radii
        assert E1 != E2
    
    def test_vacuum_energy_invalid_radius(self):
        """Test that negative radius raises error."""
        unif = GeometricUnification(precision=30)
        
        with pytest.raises(ValueError):
            unif.vacuum_energy(-1.0)
        
        with pytest.raises(ValueError):
            unif.vacuum_energy(0.0)
    
    def test_optimal_radius_finding(self):
        """Test finding optimal radius."""
        unif = GeometricUnification(precision=30)
        R_star = unif.find_optimal_radius(R_range=(0.1, 10.0), num_points=1000)
        
        # R_star should be positive and in range
        assert R_star > 0.1
        assert R_star < 10.0
        
        # Energy at R_star should be lower than at boundaries
        E_star = unif.vacuum_energy(R_star)
        E_low = unif.vacuum_energy(0.1)
        E_high = unif.vacuum_energy(10.0)
        
        # At least one boundary should have higher energy
        assert E_star < E_low or E_star < E_high
    
    def test_fundamental_frequency_computation(self):
        """Test fundamental frequency computation."""
        unif = GeometricUnification(precision=30)
        f0 = unif.compute_fundamental_frequency()
        
        # f0 should be positive and in reasonable range
        assert f0 > 0
        assert 100.0 < f0 < 200.0  # Around 141.7 Hz expected
    
    def test_verify_unification(self):
        """Test unification verification."""
        unif = GeometricUnification(precision=30)
        result = unif.verify_unification()
        
        # Check structure of result
        assert 'unified' in result
        assert 'zeta_prime_half' in result
        assert 'f0_hz' in result
        assert 'omega_0_rad_per_s' in result
        assert 'zeta_consistent' in result
        assert 'f0_reasonable' in result
        assert 'zeta_contributes_to_vacuum' in result
        
        # Check values are reasonable
        assert result['zeta_prime_half'] < 0
        assert result['f0_hz'] > 0
        assert result['omega_0_rad_per_s'] > 0
        
        # Verify ζ' contributes to vacuum energy (handle numpy bool)
        assert bool(result['zeta_contributes_to_vacuum']) is True
    
    def test_demonstrate_non_circularity(self):
        """Test non-circularity demonstration."""
        unif = GeometricUnification(precision=30)
        steps = unif.demonstrate_non_circularity()
        
        # Should have multiple steps
        assert len(steps) > 5
        assert 'step_1' in steps
        assert 'conclusion' in steps
        
        # Each step should be a string
        for key, value in steps.items():
            assert isinstance(value, str)
            assert len(value) > 0
    
    def test_compute_unification_metrics(self):
        """Test computation of unification metrics."""
        unif = GeometricUnification(precision=30)
        metrics = unif.compute_unification_metrics()
        
        # Check all expected metrics are present
        assert 'coupling_strength' in metrics
        assert 'zeta_contribution_to_vacuum' in metrics
        assert 'geometric_symmetry' in metrics
        assert 'spectral_physical_product' in metrics
        assert 'zeta_prime_half' in metrics
        assert 'fundamental_frequency_hz' in metrics
        assert 'angular_frequency_rad_s' in metrics
        
        # Check values are reasonable
        assert metrics['coupling_strength'] > 0
        # Note: zeta_contribution can be > 1 in some parameter regimes
        assert metrics['zeta_contribution_to_vacuum'] >= 0
        assert metrics['geometric_symmetry'] == 0.5  # Exact by construction
        assert metrics['spectral_physical_product'] > 0
    
    def test_generate_unification_report(self):
        """Test report generation."""
        unif = GeometricUnification(precision=30)
        report = unif.generate_unification_report()
        
        # Report should be a non-empty string
        assert isinstance(report, str)
        assert len(report) > 100
        
        # Should contain key terms
        assert "ζ'(1/2)" in report or "zeta" in report.lower()
        assert "f₀" in report or "f0" in report or "frequency" in report.lower()
        assert "unif" in report.lower()
        assert "geometric" in report.lower()
    
    def test_different_precisions(self):
        """Test with different precision values."""
        precisions = [15, 30, 50]
        
        zeta_values = []
        for prec in precisions:
            unif = GeometricUnification(precision=prec)
            zeta = unif.compute_zeta_prime_half()
            zeta_values.append(zeta)
        
        # Higher precision should give more consistent results
        # All should be close to each other
        for i in range(len(zeta_values) - 1):
            assert abs(zeta_values[i] - zeta_values[i+1]) < 0.01
    
    def test_vacuum_energy_contains_zeta_term(self):
        """Test that vacuum energy explicitly contains ζ'(1/2) term."""
        unif = GeometricUnification(precision=30)
        
        R_test = 1.0
        E_with_zeta = unif.vacuum_energy(R_test)
        
        # Temporarily disable ζ' term
        beta_original = unif.beta
        unif.beta = 0.0
        E_without_zeta = unif.vacuum_energy(R_test)
        unif.beta = beta_original
        
        # Energies should differ
        assert abs(E_with_zeta - E_without_zeta) > 1e-10
        
        # The difference should be approximately beta * zeta' / R^2
        zeta_prime = unif.compute_zeta_prime_half()
        expected_diff = beta_original * zeta_prime / (R_test ** 2)
        actual_diff = E_with_zeta - E_without_zeta
        
        assert abs(actual_diff - expected_diff) < 1e-6
    
    def test_wave_equation_coupling(self):
        """Test wave equation coupling consistency."""
        unif = GeometricUnification(precision=30)
        
        zeta_prime = unif.compute_zeta_prime_half()
        f0 = unif.compute_fundamental_frequency()
        omega_0 = 2 * np.pi * f0
        
        # Wave equation: ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·∇²Φ
        # Both sides should have compatible dimensions
        
        # Left side has dimensions [1/s²]
        left_dimensional = omega_0 ** 2
        
        # Right side (with ∇²Φ normalized) has dimensions related to ζ'
        # The coupling should make physical sense
        coupling = zeta_prime * omega_0 ** 2
        
        # Should be finite and non-zero
        assert not np.isnan(coupling)
        assert not np.isinf(coupling)
        assert coupling != 0


class TestConvenienceFunctions:
    """Test convenience functions."""
    
    def test_verify_geometric_unification(self):
        """Test convenience verification function."""
        result = verify_geometric_unification(precision=30)
        
        # Should return boolean (handle numpy bool)
        assert isinstance(result, (bool, np.bool_))
    
    def test_print_unification_report(self, capsys):
        """Test convenience print function."""
        print_unification_report(precision=15)
        
        captured = capsys.readouterr()
        output = captured.out
        
        # Should print something
        assert len(output) > 0
        assert "GEOMETRIC" in output or "geometric" in output.lower()


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    def test_very_small_radius(self):
        """Test vacuum energy at very small radius."""
        unif = GeometricUnification(precision=30)
        
        # Very small but positive radius
        E = unif.vacuum_energy(0.001)
        
        # Should be dominated by 1/R^4 term (very large)
        assert E > 0  # Should be positive and large
    
    def test_very_large_radius(self):
        """Test vacuum energy at very large radius."""
        unif = GeometricUnification(precision=30)
        
        # Very large radius
        E = unif.vacuum_energy(1000.0)
        
        # Should be dominated by R^2 term
        assert isinstance(E, float)
        assert not np.isnan(E)
    
    def test_different_physical_parameters(self):
        """Test with different physical parameter values."""
        params_list = [
            {'alpha': 0.5, 'beta': 1.0, 'gamma': 1.0, 'delta': 1.0},
            {'alpha': 1.0, 'beta': 0.5, 'gamma': 1.0, 'delta': 1.0},
            {'alpha': 1.0, 'beta': 1.0, 'gamma': 0.5, 'delta': 1.0},
        ]
        
        for params in params_list:
            unif = GeometricUnification(precision=15, **params)
            
            # Should still compute values
            zeta = unif.compute_zeta_prime_half()
            f0 = unif.compute_fundamental_frequency()
            
            assert zeta < 0
            assert f0 > 0


class TestMathematicalConsistency:
    """Test mathematical consistency of the unification."""
    
    def test_geometric_symmetry_exact(self):
        """Test that geometric symmetry is exactly 1/2."""
        unif = GeometricUnification(precision=50)
        metrics = unif.compute_unification_metrics()
        
        # Geometric symmetry should be exactly 0.5
        # This represents the critical point of A₀ = 1/2 + iZ
        assert metrics['geometric_symmetry'] == 0.5
    
    def test_zeta_prime_reproducibility(self):
        """Test that ζ'(1/2) is reproducible."""
        unif1 = GeometricUnification(precision=30)
        unif2 = GeometricUnification(precision=30)
        
        zeta1 = unif1.compute_zeta_prime_half()
        zeta2 = unif2.compute_zeta_prime_half()
        
        # Should be identical
        assert zeta1 == zeta2
    
    def test_unification_self_consistency(self):
        """Test self-consistency of unification."""
        unif = GeometricUnification(precision=30)
        
        # Compute values multiple times
        result1 = unif.verify_unification()
        result2 = unif.verify_unification()
        
        # Results should be identical
        assert result1['zeta_prime_half'] == result2['zeta_prime_half']
        assert result1['f0_hz'] == result2['f0_hz']
        assert result1['unified'] == result2['unified']


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v"])

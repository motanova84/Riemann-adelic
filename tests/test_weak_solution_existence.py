#!/usr/bin/env python3
"""
Tests for Weak Solution Existence and Uniqueness Theorem.

Tests the theorem for the equation:
    ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·π·∇²Φ

Author: José Manuel Mota Burruezo
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from utils.weak_solution_existence import (
    WeakSolutionExistence,
    validate_weak_solution_theorem
)


class TestWeakSolutionExistence:
    """Test suite for WeakSolutionExistence class."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence(precision=15)
        self.tolerance = 1e-6
        
    def test_initialization(self):
        """Test proper initialization."""
        assert self.validator.omega_0 > 0
        assert self.validator.omega_0_squared > 0
        assert self.validator.precision == 15
        assert self.validator.spatial_dim == 1
        
    def test_omega_0_default_value(self):
        """Test default ω₀ = 2πf₀ with f₀ = 141.7001 Hz."""
        expected = 2 * np.pi * 141.7001
        assert abs(self.validator.omega_0 - expected) < self.tolerance
        
    def test_zeta_prime_half_negative(self):
        """Test that ζ'(1/2) is negative."""
        assert self.validator.zeta_prime_half < 0, "ζ'(1/2) should be negative"
        
    def test_zeta_prime_half_approximate_value(self):
        """Test ζ'(1/2) ≈ -3.9226461392."""
        expected = -3.9226461392
        assert abs(self.validator.zeta_prime_half - expected) < 0.01
        
    def test_coupling_constant_value(self):
        """Test coupling constant = ζ'(1/2)·π."""
        expected = self.validator.zeta_prime_half * np.pi
        assert abs(self.validator.coupling_constant - expected) < self.tolerance
        
    def test_coupling_constant_negative(self):
        """Test that coupling constant is negative (since ζ'(1/2) < 0)."""
        assert self.validator.coupling_constant < 0


class TestBilinearFormCoercivity:
    """Tests for bilinear form coercivity verification."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_coercivity_returns_tuple(self):
        """Test that bilinear_form_coercivity returns correct type."""
        result = self.validator.bilinear_form_coercivity()
        assert isinstance(result, tuple)
        assert len(result) == 2
        assert isinstance(result[0], (float, np.floating))
        assert isinstance(result[1], (bool, np.bool_))
        
    def test_coercivity_is_positive(self):
        """Test that coercivity constant is positive."""
        alpha, is_coercive = self.validator.bilinear_form_coercivity()
        assert alpha > 0, f"Coercivity constant should be positive, got {alpha}"
        assert is_coercive, "Form should be coercive"
        
    def test_coercivity_with_different_grid_sizes(self):
        """Test coercivity with different grid discretizations."""
        for N in [50, 100, 200]:
            alpha, is_coercive = self.validator.bilinear_form_coercivity(N=N)
            assert is_coercive, f"Form should be coercive with N={N}"
            assert alpha > 0.5, f"Coercivity constant too small: {alpha}"


class TestLaxMilgramConditions:
    """Tests for Lax-Milgram theorem conditions."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_lax_milgram_returns_dict(self):
        """Test that lax_milgram_conditions returns dictionary."""
        result = self.validator.lax_milgram_conditions()
        assert isinstance(result, dict)
        
    def test_bilinear_continuous(self):
        """Test that bilinear form is continuous."""
        conditions = self.validator.lax_milgram_conditions()
        assert conditions['bilinear_continuous'], "Bilinear form should be continuous"
        
    def test_bilinear_coercive(self):
        """Test that bilinear form is coercive."""
        conditions = self.validator.lax_milgram_conditions()
        assert conditions['bilinear_coercive'], "Bilinear form should be coercive"
        
    def test_rhs_continuous(self):
        """Test that RHS functional is continuous."""
        conditions = self.validator.lax_milgram_conditions()
        assert conditions['rhs_continuous'], "RHS should be continuous"
        
    def test_lax_milgram_satisfied(self):
        """Test that all Lax-Milgram conditions are satisfied."""
        conditions = self.validator.lax_milgram_conditions()
        assert conditions['lax_milgram_satisfied'], "Lax-Milgram should be satisfied"
        
    def test_continuity_constant_finite(self):
        """Test that continuity constant is finite."""
        conditions = self.validator.lax_milgram_conditions()
        assert np.isfinite(conditions['continuity_constant'])
        
    def test_coercivity_constant_positive(self):
        """Test that coercivity constant is positive."""
        conditions = self.validator.lax_milgram_conditions()
        assert conditions['coercivity_constant'] > 0


class TestWeakSolutionTheorem:
    """Tests for the main weak solution theorem."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_theorem_returns_dict(self):
        """Test that theorem returns dictionary."""
        result = self.validator.weak_solution_exists_unique()
        assert isinstance(result, dict)
        
    def test_theorem_holds(self):
        """Test that theorem conclusion holds."""
        result = self.validator.weak_solution_exists_unique()
        assert result['theorem_holds'], "Theorem should hold"
        
    def test_solution_exists(self):
        """Test that solution exists."""
        result = self.validator.weak_solution_exists_unique()
        assert result['exists'], "Solution should exist"
        
    def test_solution_unique(self):
        """Test that solution is unique."""
        result = self.validator.weak_solution_exists_unique()
        assert result['unique'], "Solution should be unique"
        
    def test_regularity_temporal_C0(self):
        """Test temporal C⁰ regularity."""
        result = self.validator.weak_solution_exists_unique()
        assert result['regularity']['temporal_C0']
        
    def test_regularity_temporal_C1(self):
        """Test temporal C¹ regularity."""
        result = self.validator.weak_solution_exists_unique()
        assert result['regularity']['temporal_C1']
        
    def test_regularity_spatial_H1(self):
        """Test spatial H¹ regularity."""
        result = self.validator.weak_solution_exists_unique()
        assert result['regularity']['spatial_H1']
        
    def test_regularity_spatial_L2(self):
        """Test spatial L² regularity."""
        result = self.validator.weak_solution_exists_unique()
        assert result['regularity']['spatial_L2']
        
    def test_solution_space_correct(self):
        """Test correct solution space description."""
        result = self.validator.weak_solution_exists_unique()
        expected_space = 'C⁰([0,T], H¹(ℝⁿ)) ∩ C¹([0,T], L²(ℝⁿ))'
        assert result['solution_space'] == expected_space
        
    def test_hypotheses_satisfied(self):
        """Test that all hypotheses are satisfied."""
        result = self.validator.weak_solution_exists_unique()
        for key, value in result['hypotheses'].items():
            assert value, f"Hypothesis {key} should be satisfied"
            
    def test_justification_present(self):
        """Test that justification is provided."""
        result = self.validator.weak_solution_exists_unique()
        assert 'justification' in result
        assert 'method' in result['justification']
        assert 'Lax-Milgram' in result['justification']['method']
        
    def test_parameters_present(self):
        """Test that parameters are included."""
        result = self.validator.weak_solution_exists_unique()
        assert 'parameters' in result
        assert 'omega_0' in result['parameters']
        assert 'zeta_prime_half' in result['parameters']


class TestEnergyEstimate:
    """Tests for energy estimate calculations."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_energy_nonnegative(self):
        """Test that energy is non-negative."""
        N = 50
        dx = 0.1
        dt = 0.01
        
        # Create test data
        Psi = np.sin(np.linspace(0, 2*np.pi, N))
        dPsi_dt = np.cos(np.linspace(0, 2*np.pi, N))
        grad_Psi = np.gradient(Psi, dx)
        
        energy = self.validator.energy_estimate(Psi, dPsi_dt, grad_Psi, dx, dt)
        assert energy >= 0, "Energy should be non-negative"
        
    def test_energy_zero_for_zero_field(self):
        """Test that energy is zero for zero field."""
        N = 50
        dx = 0.1
        dt = 0.01
        
        Psi = np.zeros(N)
        dPsi_dt = np.zeros(N)
        grad_Psi = np.zeros(N)
        
        energy = self.validator.energy_estimate(Psi, dPsi_dt, grad_Psi, dx, dt)
        assert abs(energy) < 1e-10, "Energy should be zero for zero field"
        
    def test_energy_increases_with_amplitude(self):
        """Test that energy increases with field amplitude."""
        N = 50
        dx = 0.1
        dt = 0.01
        x = np.linspace(0, 2*np.pi, N)
        
        Psi1 = np.sin(x)
        Psi2 = 2 * np.sin(x)  # Double amplitude
        
        dPsi_dt1 = np.cos(x)
        dPsi_dt2 = 2 * np.cos(x)
        
        grad_Psi1 = np.gradient(Psi1, dx)
        grad_Psi2 = np.gradient(Psi2, dx)
        
        energy1 = self.validator.energy_estimate(Psi1, dPsi_dt1, grad_Psi1, dx, dt)
        energy2 = self.validator.energy_estimate(Psi2, dPsi_dt2, grad_Psi2, dx, dt)
        
        assert energy2 > energy1, "Energy should increase with amplitude"


class TestWeakFormulation:
    """Tests for weak formulation verification."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_verify_weak_formulation_returns_tuple(self):
        """Test that weak formulation returns tuple."""
        # Define simple test functions
        def Psi(X, T): return np.exp(-X**2) * np.cos(self.validator.omega_0 * T)
        def Phi(X, T): return np.exp(-X**2)
        def test_fn(X, T): return np.exp(-X**2) * np.exp(-T**2)
        
        result = self.validator.verify_weak_formulation(
            Psi, Phi, test_fn,
            x_range=(-5, 5),
            t_range=(0, 0.1),
            Nx=30, Nt=30
        )
        
        assert isinstance(result, tuple)
        assert len(result) == 2


class TestLean4Statement:
    """Tests for Lean 4 statement generation."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_lean4_statement_returns_string(self):
        """Test that Lean 4 statement returns string."""
        result = self.validator.get_lean4_statement()
        assert isinstance(result, str)
        
    def test_lean4_statement_contains_theorem(self):
        """Test that Lean 4 statement contains theorem declaration."""
        result = self.validator.get_lean4_statement()
        assert 'theorem' in result
        assert 'weak_solution_exists_unique' in result
        
    def test_lean4_statement_contains_omega(self):
        """Test that Lean 4 statement contains omega definition."""
        result = self.validator.get_lean4_statement()
        assert 'omega' in result.lower()
        
    def test_lean4_statement_contains_zeta(self):
        """Test that Lean 4 statement contains zeta reference."""
        result = self.validator.get_lean4_statement()
        assert 'zeta' in result.lower()


class TestValidateFunction:
    """Tests for the validate_weak_solution_theorem function."""
    
    def test_validate_returns_dict(self):
        """Test that validate function returns dictionary."""
        result = validate_weak_solution_theorem(verbose=False)
        assert isinstance(result, dict)
        
    def test_validate_with_custom_omega(self):
        """Test validation with custom omega."""
        custom_omega = 2 * np.pi * 100  # Different frequency
        result = validate_weak_solution_theorem(omega_0=custom_omega, verbose=False)
        assert result['parameters']['omega_0'] == custom_omega
        
    def test_validate_theorem_holds(self):
        """Test that validation confirms theorem holds."""
        result = validate_weak_solution_theorem(verbose=False)
        assert result['theorem_holds']


class TestNumericalStability:
    """Tests for numerical stability of the implementation."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        self.validator = WeakSolutionExistence()
        
    def test_stability_high_precision(self):
        """Test with high precision calculations."""
        validator_hp = WeakSolutionExistence(precision=50)
        result = validator_hp.weak_solution_exists_unique()
        assert result['theorem_holds']
        
    def test_stability_low_precision(self):
        """Test with lower precision."""
        validator_lp = WeakSolutionExistence(precision=10)
        result = validator_lp.weak_solution_exists_unique()
        assert result['theorem_holds']
        
    def test_stability_different_dimensions(self):
        """Test with different spatial dimensions."""
        for dim in [1, 2, 3]:
            validator = WeakSolutionExistence(spatial_dim=dim)
            result = validator.weak_solution_exists_unique()
            assert result['theorem_holds'], f"Should hold for dim={dim}"
            
    def test_stability_extreme_omega(self):
        """Test with extreme omega values."""
        for omega in [1.0, 1000.0, 1e6]:
            validator = WeakSolutionExistence(omega_0=omega)
            result = validator.weak_solution_exists_unique()
            assert result['theorem_holds'], f"Should hold for omega={omega}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

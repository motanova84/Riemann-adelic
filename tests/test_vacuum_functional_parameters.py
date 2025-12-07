#!/usr/bin/env python3
"""
Tests for Vacuum Functional Parameters Module

Tests the deep interpretation and implementation of vacuum energy
functional parameters α, β, γ, δ.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: December 2025
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent.parent / "utils"))

from vacuum_functional_parameters import (
    VacuumFunctionalParameters,
    VacuumFunctional,
    ParameterInterpretation,
    ParameterDomain,
    PARAMETER_REGISTRY,
    ALPHA_INTERPRETATION,
    BETA_INTERPRETATION,
    GAMMA_INTERPRETATION,
    DELTA_INTERPRETATION,
    ZETA_PRIME_HALF,
    generate_parameter_summary_table,
    print_parameter_details,
)


class TestParameterInterpretations:
    """Test suite for parameter interpretation objects."""
    
    def test_alpha_interpretation_exists(self):
        """Test that alpha interpretation is properly defined."""
        assert ALPHA_INTERPRETATION is not None
        assert ALPHA_INTERPRETATION.symbol == "α"
        assert ALPHA_INTERPRETATION.domain == ParameterDomain.UV
    
    def test_beta_interpretation_exists(self):
        """Test that beta interpretation is properly defined."""
        assert BETA_INTERPRETATION is not None
        assert BETA_INTERPRETATION.symbol == "β"
        assert BETA_INTERPRETATION.domain == ParameterDomain.ADELIC
    
    def test_gamma_interpretation_exists(self):
        """Test that gamma interpretation is properly defined."""
        assert GAMMA_INTERPRETATION is not None
        assert GAMMA_INTERPRETATION.symbol == "γ"
        assert GAMMA_INTERPRETATION.domain == ParameterDomain.HARMONIC
    
    def test_delta_interpretation_exists(self):
        """Test that delta interpretation is properly defined."""
        assert DELTA_INTERPRETATION is not None
        assert DELTA_INTERPRETATION.symbol == "δ"
        assert DELTA_INTERPRETATION.domain == ParameterDomain.FRACTAL
    
    def test_parameter_registry_contains_all(self):
        """Test that parameter registry has all expected entries."""
        expected_keys = ["α", "alpha", "β", "beta", "γ", "gamma", "δ", "delta"]
        for key in expected_keys:
            assert key in PARAMETER_REGISTRY
    
    def test_interpretation_has_required_fields(self):
        """Test that interpretations have all required fields."""
        for interp in [ALPHA_INTERPRETATION, BETA_INTERPRETATION,
                       GAMMA_INTERPRETATION, DELTA_INTERPRETATION]:
            assert hasattr(interp, 'symbol')
            assert hasattr(interp, 'name')
            assert hasattr(interp, 'latex')
            assert hasattr(interp, 'scaling')
            assert hasattr(interp, 'domain')
            assert hasattr(interp, 'physical_meaning')
            assert hasattr(interp, 'mathematical_meaning')
            assert hasattr(interp, 'symbolic_meaning')
            assert hasattr(interp, 'typical_value')
    
    def test_interpretation_meanings_not_empty(self):
        """Test that interpretation meanings contain content."""
        for interp in [ALPHA_INTERPRETATION, BETA_INTERPRETATION,
                       GAMMA_INTERPRETATION, DELTA_INTERPRETATION]:
            assert len(interp.physical_meaning) > 100
            assert len(interp.mathematical_meaning) > 100
            assert len(interp.symbolic_meaning) > 100


class TestVacuumFunctionalParameters:
    """Test suite for VacuumFunctionalParameters dataclass."""
    
    def test_default_initialization(self):
        """Test default parameter values."""
        params = VacuumFunctionalParameters()
        
        assert params.alpha == 1.0
        assert params.beta == 1.0
        assert params.gamma == 1.0
        assert params.delta == 0.5
        assert params.eta == np.pi
    
    def test_custom_initialization(self):
        """Test custom parameter values."""
        params = VacuumFunctionalParameters(
            alpha=2.0,
            beta=0.5,
            gamma=0.01,
            delta=1.0,
            eta=2.71828
        )
        
        assert params.alpha == 2.0
        assert params.beta == 0.5
        assert params.gamma == 0.01
        assert params.delta == 1.0
        assert abs(params.eta - 2.71828) < 1e-5
    
    def test_invalid_eta_zero(self):
        """Test that eta=0 raises ValueError."""
        with pytest.raises(ValueError):
            VacuumFunctionalParameters(eta=0)
    
    def test_invalid_eta_one(self):
        """Test that eta=1 raises ValueError."""
        with pytest.raises(ValueError):
            VacuumFunctionalParameters(eta=1)
    
    def test_invalid_eta_negative(self):
        """Test that negative eta raises ValueError."""
        with pytest.raises(ValueError):
            VacuumFunctionalParameters(eta=-1)
    
    def test_get_interpretation(self):
        """Test getting interpretations from parameters object."""
        params = VacuumFunctionalParameters()
        
        interp = params.get_interpretation("alpha")
        assert interp.symbol == "α"
        
        interp = params.get_interpretation("β")
        assert interp.symbol == "β"
    
    def test_get_unknown_interpretation_raises(self):
        """Test that unknown parameter raises KeyError."""
        params = VacuumFunctionalParameters()
        
        with pytest.raises(KeyError):
            params.get_interpretation("unknown")


class TestVacuumFunctional:
    """Test suite for VacuumFunctional class."""
    
    def test_initialization_default(self):
        """Test default initialization."""
        func = VacuumFunctional()
        
        assert func.params is not None
        assert func.zeta_prime_half == ZETA_PRIME_HALF
    
    def test_initialization_custom_params(self):
        """Test initialization with custom parameters."""
        params = VacuumFunctionalParameters(alpha=2.0, gamma=0.1)
        func = VacuumFunctional(params)
        
        assert func.params.alpha == 2.0
        assert func.params.gamma == 0.1
    
    def test_casimir_term(self):
        """Test Casimir term calculation."""
        func = VacuumFunctional(VacuumFunctionalParameters(alpha=1.0))
        
        R = 2.0
        expected = 1.0 / (R ** 4)
        actual = func.casimir_term(R)
        
        assert abs(actual - expected) < 1e-10
    
    def test_adelic_term(self):
        """Test adelic coupling term calculation."""
        params = VacuumFunctionalParameters(beta=1.0)
        func = VacuumFunctional(params)
        
        R = 2.0
        expected = 1.0 * ZETA_PRIME_HALF / (R ** 2)
        actual = func.adelic_term(R)
        
        assert abs(actual - expected) < 1e-10
    
    def test_harmonic_term(self):
        """Test harmonic curvature term calculation."""
        func = VacuumFunctional(VacuumFunctionalParameters(gamma=1.0))
        
        R = 2.0
        expected = 1.0 * (R ** 2)
        actual = func.harmonic_term(R)
        
        assert abs(actual - expected) < 1e-10
    
    def test_fractal_term(self):
        """Test fractal modulation term calculation."""
        params = VacuumFunctionalParameters(delta=1.0, eta=np.pi)
        func = VacuumFunctional(params)
        
        R = np.pi  # At R = π, log(π)/log(π) = 1, sin²(1) ≠ 0
        expected = 1.0 * (np.sin(1.0) ** 2)
        actual = func.fractal_term(R)
        
        assert abs(actual - expected) < 1e-10
    
    def test_fractal_term_at_eta_powers(self):
        """Test fractal term at R = η^n gives sin²(n)."""
        params = VacuumFunctionalParameters(delta=1.0, eta=np.pi)
        func = VacuumFunctional(params)
        
        for n in [0, 1, 2, 3]:
            R = np.pi ** n
            expected = np.sin(n) ** 2
            actual = func.fractal_term(R)
            assert abs(actual - expected) < 1e-10
    
    def test_total_energy_positive_radius(self):
        """Test total energy at positive radius."""
        func = VacuumFunctional()
        
        R = np.pi
        E = func.energy(R)
        
        assert np.isfinite(E)
        assert not np.isnan(E)
    
    def test_energy_invalid_radius_zero(self):
        """Test that zero radius raises ValueError."""
        func = VacuumFunctional()
        
        with pytest.raises(ValueError):
            func.energy(0.0)
    
    def test_energy_invalid_radius_negative(self):
        """Test that negative radius raises ValueError."""
        func = VacuumFunctional()
        
        with pytest.raises(ValueError):
            func.energy(-1.0)
    
    def test_decompose_energy(self):
        """Test energy decomposition."""
        func = VacuumFunctional()
        
        R = 2.0
        decomp = func.decompose_energy(R)
        
        assert 'casimir' in decomp
        assert 'adelic' in decomp
        assert 'harmonic' in decomp
        assert 'fractal' in decomp
        assert 'total' in decomp
        
        # Check total is sum of components
        component_sum = (decomp['casimir'] + decomp['adelic'] + 
                        decomp['harmonic'] + decomp['fractal'])
        assert abs(decomp['total'] - component_sum) < 1e-10
    
    def test_derivative_calculation(self):
        """Test derivative using finite differences."""
        func = VacuumFunctional()
        
        R = 2.0
        h = 1e-6
        
        # Numerical derivative
        dE_numerical = (func.energy(R + h) - func.energy(R - h)) / (2 * h)
        
        # Analytical derivative
        dE_analytical = func.derivative(R)
        
        assert abs(dE_numerical - dE_analytical) < 1e-4
    
    def test_second_derivative_calculation(self):
        """Test second derivative using finite differences."""
        func = VacuumFunctional()
        
        R = 2.0
        h = 1e-4
        
        # Numerical second derivative
        d2E_numerical = (func.energy(R + h) - 2*func.energy(R) + 
                        func.energy(R - h)) / (h ** 2)
        
        # Analytical second derivative
        d2E_analytical = func.second_derivative(R)
        
        # Slightly looser tolerance due to numerical precision
        assert abs(d2E_numerical - d2E_analytical) < 0.1
    
    def test_find_minima(self):
        """Test that minima can be found."""
        params = VacuumFunctionalParameters(
            alpha=1.0,
            beta=1.0,
            gamma=0.01,
            delta=0.5,
            eta=np.pi
        )
        func = VacuumFunctional(params)
        
        minima = func.find_minima(R_range=(0.5, 10.0), num_points=1000)
        
        # Should find at least one minimum
        assert len(minima) > 0
        
        # Minima should be positive
        assert np.all(minima > 0)


class TestPhysicalBehavior:
    """Test physical behavior of vacuum functional."""
    
    def test_casimir_dominates_small_R(self):
        """Test that Casimir term dominates at small R."""
        params = VacuumFunctionalParameters(
            alpha=1.0,
            beta=0.1,
            gamma=0.01,
            delta=0.1
        )
        func = VacuumFunctional(params)
        
        R_small = 0.1
        decomp = func.decompose_energy(R_small)
        
        # Casimir should be largest contribution
        assert abs(decomp['casimir']) > abs(decomp['adelic'])
        assert abs(decomp['casimir']) > abs(decomp['harmonic'])
    
    def test_harmonic_dominates_large_R(self):
        """Test that harmonic term dominates at large R."""
        params = VacuumFunctionalParameters(
            alpha=1.0,
            beta=0.1,
            gamma=1.0,
            delta=0.1
        )
        func = VacuumFunctional(params)
        
        R_large = 100.0
        decomp = func.decompose_energy(R_large)
        
        # Harmonic should be largest contribution
        assert decomp['harmonic'] > abs(decomp['casimir'])
        assert decomp['harmonic'] > abs(decomp['adelic'])
    
    def test_adelic_term_negative(self):
        """Test that adelic term is negative (attractive)."""
        params = VacuumFunctionalParameters(beta=1.0)
        func = VacuumFunctional(params)
        
        R = 2.0
        adelic = func.adelic_term(R)
        
        # ζ'(1/2) is negative, so with positive β, term is negative
        assert adelic < 0
    
    def test_fractal_term_bounded(self):
        """Test that fractal term is bounded [0, δ]."""
        params = VacuumFunctionalParameters(delta=0.5)
        func = VacuumFunctional(params)
        
        # Test at various R values
        for R in [0.1, 1.0, np.pi, 10.0, 100.0]:
            fractal = func.fractal_term(R)
            assert 0 <= fractal <= params.delta + 1e-10


class TestDocumentationGeneration:
    """Test documentation generation functions."""
    
    def test_generate_summary_table(self):
        """Test that summary table is generated."""
        table = generate_parameter_summary_table()
        
        assert isinstance(table, str)
        assert "α" in table
        assert "β" in table
        assert "γ" in table
        assert "δ" in table
        assert "Casimir" in table
        assert "Adèlic" in table
    
    def test_print_parameter_details_runs(self, capsys):
        """Test that print_parameter_details executes without error."""
        print_parameter_details("alpha")
        captured = capsys.readouterr()
        
        assert "α" in captured.out
        assert "Casimir" in captured.out
    
    def test_print_unknown_parameter(self, capsys):
        """Test handling of unknown parameter."""
        print_parameter_details("unknown")
        captured = capsys.readouterr()
        
        assert "Unknown parameter" in captured.out


class TestZetaPrimeHalf:
    """Test zeta prime at 1/2 value."""
    
    def test_zeta_prime_half_value(self):
        """Test that ζ'(1/2) is approximately correct."""
        # Known value: ζ'(1/2) ≈ -3.9226...
        assert -4.0 < ZETA_PRIME_HALF < -3.8
    
    def test_zeta_prime_half_precision(self):
        """Test precision of stored value."""
        # Should have at least 6 decimal places of precision
        expected = -3.9226461392
        assert abs(ZETA_PRIME_HALF - expected) < 1e-6


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

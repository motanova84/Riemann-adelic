#!/usr/bin/env python3
"""
Tests for Adelic Viscosity Operator — Navier-Stokes Aritmético Framework

This module validates the Adelic Viscosity implementation for
controlling the remainder R(t) via Vladimirov Laplacian.

Test Coverage:
    1. Vladimirov Laplacian construction for various primes
    2. Spectral gap positivity λ_{p,1} > 0
    3. Heat kernel exponential decay bounds
    4. Adelic operator initialization
    5. Global spectral gap computation
    6. Remainder bound R(t) exponential decay
    7. Verification of decay constant
    8. Integration with QCAL constants

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.adelic_viscosity_operator import (
    # Constants
    F0,
    C_QCAL,
    KAPPA_PI,
    NU_ADELIC,
    # Functions
    is_prime,
    first_n_primes,
    # Classes
    VladimirLaplacian,
    AdelicViscosityOperator,
    demonstrate_remainder_control,
)


class TestConstants:
    """Test fundamental constants."""
    
    def test_f0_value(self):
        """Fundamental frequency should be 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-4
    
    def test_c_qcal_value(self):
        """QCAL coherence constant should be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01
    
    def test_kappa_pi_value(self):
        """Critical PT transition should be ~2.5773."""
        assert abs(KAPPA_PI - 2.5773) < 0.01
    
    def test_nu_adelic_value(self):
        """Adelic viscosity ν = 1/κ_Π."""
        expected_nu = 1.0 / KAPPA_PI
        assert abs(NU_ADELIC - expected_nu) < 1e-5


class TestPrimeHelpers:
    """Test prime number helper functions."""
    
    def test_is_prime_basic(self):
        """Test basic prime detection."""
        assert is_prime(2)
        assert is_prime(3)
        assert is_prime(5)
        assert is_prime(7)
        assert not is_prime(4)
        assert not is_prime(6)
        assert not is_prime(9)
    
    def test_is_prime_edge_cases(self):
        """Test edge cases."""
        assert not is_prime(0)
        assert not is_prime(1)
        assert not is_prime(-5)
    
    def test_first_n_primes(self):
        """Test first n primes generation."""
        primes_5 = first_n_primes(5)
        assert primes_5 == [2, 3, 5, 7, 11]
        
        primes_10 = first_n_primes(10)
        assert len(primes_10) == 10
        assert primes_10[-1] == 29


class TestVladimirLaplacian:
    """Test Vladimirov Laplacian for p-adic primes."""
    
    def test_initialization(self):
        """Test basic initialization."""
        lapl = VladimirLaplacian(p=2, n_levels=5)
        assert lapl.p == 2
        assert lapl.n_levels == 5
        assert lapl.spectral_gap > 0
    
    def test_initialization_requires_prime(self):
        """Test that initialization requires prime p."""
        with pytest.raises(ValueError):
            VladimirLaplacian(p=4, n_levels=5)
        
        with pytest.raises(ValueError):
            VladimirLaplacian(p=6, n_levels=5)
    
    def test_spectral_gap_positivity(self):
        """Test that spectral gap is always positive."""
        for p in [2, 3, 5, 7, 11, 13]:
            lapl = VladimirLaplacian(p=p)
            assert lapl.spectral_gap > 0, f"Gap for p={p} should be positive"
    
    def test_spectral_gap_formula(self):
        """Test spectral gap formula λ_{p,1} = (p-1)²/(p+1)."""
        for p in [2, 3, 5, 7]:
            lapl = VladimirLaplacian(p=p)
            expected = (p - 1.0)**2 / (p + 1.0)
            assert abs(lapl.spectral_gap - expected) < 1e-10
    
    def test_spectral_gap_increases_with_p(self):
        """Test that gap increases (roughly) with prime p."""
        gaps = []
        for p in [2, 3, 5, 7, 11, 13]:
            lapl = VladimirLaplacian(p=p)
            gaps.append(lapl.spectral_gap)
        
        # Generally increasing (with some fluctuations)
        assert gaps[-1] > gaps[0]
    
    def test_heat_kernel_bound_positive_time(self):
        """Test heat kernel bound for positive time."""
        lapl = VladimirLaplacian(p=5)
        
        bound_01 = lapl.heat_kernel_bound(0.1)
        bound_1 = lapl.heat_kernel_bound(1.0)
        bound_10 = lapl.heat_kernel_bound(10.0)
        
        # All should be positive
        assert bound_01 > 0
        assert bound_1 > 0
        assert bound_10 > 0
        
        # Should decay with time
        assert bound_01 > bound_1 > bound_10
    
    def test_heat_kernel_bound_zero_time(self):
        """Test that zero time raises error."""
        lapl = VladimirLaplacian(p=5)
        
        with pytest.raises(ValueError):
            lapl.heat_kernel_bound(0.0)
    
    def test_heat_kernel_bound_negative_time(self):
        """Test that negative time raises error."""
        lapl = VladimirLaplacian(p=5)
        
        with pytest.raises(ValueError):
            lapl.heat_kernel_bound(-1.0)
    
    def test_heat_kernel_exponential_decay(self):
        """Test that heat kernel decays exponentially."""
        lapl = VladimirLaplacian(p=7)
        
        # Sample at log-spaced times
        t_values = np.logspace(-1, 2, 20)
        bounds = [lapl.heat_kernel_bound(t) for t in t_values]
        
        # Fit exponential decay
        log_bounds = np.log(bounds)
        coeffs = np.polyfit(t_values, log_bounds, 1)
        decay_rate = -coeffs[0]
        
        # Decay rate should be close to spectral gap
        assert abs(decay_rate - lapl.spectral_gap) / lapl.spectral_gap < 0.2


class TestAdelicViscosityOperator:
    """Test Adelic Viscosity Operator."""
    
    def test_initialization_default(self):
        """Test initialization with defaults."""
        op = AdelicViscosityOperator()
        
        assert abs(op.nu - NU_ADELIC) < 1e-6
        assert len(op.primes) == 10  # Default n_primes
        assert op.global_gap > 0
    
    def test_initialization_custom(self):
        """Test initialization with custom parameters."""
        op = AdelicViscosityOperator(nu=0.5, n_primes=5, n_levels=3)
        
        assert abs(op.nu - 0.5) < 1e-6
        assert len(op.primes) == 5
    
    def test_laplacians_constructed(self):
        """Test that Vladimirov Laplacians are constructed."""
        op = AdelicViscosityOperator(n_primes=5)
        
        assert len(op.laplacians) == 5
        for p in op.primes:
            assert p in op.laplacians
            assert isinstance(op.laplacians[p], VladimirLaplacian)
    
    def test_global_gap_positivity(self):
        """Test that global gap is positive."""
        op = AdelicViscosityOperator(n_primes=10)
        assert op.global_gap > 0
    
    def test_global_gap_minimum_property(self):
        """Test that global gap is ν times minimum of local gaps."""
        op = AdelicViscosityOperator(n_primes=5)
        
        # Get all local gaps
        local_gaps = [lapl.spectral_gap for lapl in op.laplacians.values()]
        min_gap = min(local_gaps)
        
        expected_global = op.nu * min_gap
        assert abs(op.global_gap - expected_global) < 1e-10
    
    def test_remainder_bound_positive_time(self):
        """Test remainder bound for positive times."""
        op = AdelicViscosityOperator(n_primes=5)
        
        bound_01 = op.remainder_bound(0.1)
        bound_1 = op.remainder_bound(1.0)
        bound_10 = op.remainder_bound(10.0)
        
        # All positive
        assert bound_01 > 0
        assert bound_1 > 0
        assert bound_10 > 0
        
        # Monotonic decay
        assert bound_01 > bound_1
        assert bound_1 > bound_10
    
    def test_remainder_bound_zero_time(self):
        """Test that zero time raises error."""
        op = AdelicViscosityOperator(n_primes=5)
        
        with pytest.raises(ValueError):
            op.remainder_bound(0.0)
    
    def test_exponential_decay_constant(self):
        """Test decay constant equals global gap."""
        op = AdelicViscosityOperator(n_primes=5)
        
        decay_const = op.exponential_decay_constant()
        assert abs(decay_const - op.global_gap) < 1e-10
    
    def test_verify_exponential_decay(self):
        """Test verification of exponential decay."""
        op = AdelicViscosityOperator(n_primes=10)
        
        result = op.verify_exponential_decay()
        
        # Check structure
        assert 'decay_constant' in result
        assert 't_values' in result
        assert 'bounds' in result
        assert 'exponential_fit' in result
        assert 'verification' in result
        
        # Decay constant should be positive
        assert result['decay_constant'] > 0
        
        # Should have monotonic decay
        assert result['monotonic_decay']
    
    def test_verify_exponential_decay_custom_times(self):
        """Test verification with custom time values."""
        op = AdelicViscosityOperator(n_primes=5)
        
        t_vals = np.array([0.5, 1.0, 2.0, 5.0, 10.0])
        result = op.verify_exponential_decay(t_values=t_vals)
        
        assert len(result['t_values']) == len(t_vals)
        assert len(result['bounds']) == len(t_vals)


class TestDemonstration:
    """Test demonstration function."""
    
    def test_demonstrate_remainder_control(self):
        """Test the demonstration function runs."""
        result = demonstrate_remainder_control(n_primes=5)
        
        # Check structure
        assert 'decay_constant' in result
        assert 'verification' in result
        assert 'exponential_fit' in result
        
        # Decay constant should be positive
        assert result['decay_constant'] > 0


class TestNumericalStability:
    """Test numerical stability."""
    
    def test_different_n_primes(self):
        """Test stability with different number of primes."""
        for n in [3, 5, 10, 15]:
            op = AdelicViscosityOperator(n_primes=n)
            assert op.global_gap > 0
            
            bound = op.remainder_bound(1.0)
            assert bound > 0
            assert not np.isnan(bound)
            assert not np.isinf(bound)
    
    def test_different_viscosities(self):
        """Test stability with different viscosities."""
        for nu in [0.1, 0.5, 1.0, 2.0]:
            op = AdelicViscosityOperator(nu=nu, n_primes=5)
            assert op.global_gap > 0
            
            bound = op.remainder_bound(1.0)
            assert bound > 0
            assert not np.isnan(bound)
    
    def test_extreme_times(self):
        """Test behavior at extreme time values."""
        op = AdelicViscosityOperator(n_primes=5)
        
        # Very small time
        bound_small = op.remainder_bound(0.001)
        assert bound_small > 0
        assert not np.isinf(bound_small)
        
        # Very large time
        bound_large = op.remainder_bound(1000.0)
        assert bound_large > 0
        assert bound_large < 1e-10  # Should be very small


class TestQCALIntegration:
    """Test integration with QCAL framework."""
    
    def test_viscosity_from_kappa(self):
        """Test that ν = 1/κ_Π."""
        op = AdelicViscosityOperator()
        expected = 1.0 / KAPPA_PI
        assert abs(op.nu - expected) < 1e-6
    
    def test_frequency_alignment(self):
        """Test frequency alignment with F0."""
        # This is more conceptual, but we can verify F0 is defined
        assert F0 > 0
        assert abs(F0 - 141.7001) < 1e-4
    
    def test_coherence_constant(self):
        """Test coherence constant alignment."""
        assert C_QCAL > 0
        assert abs(C_QCAL - 244.36) < 0.01


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

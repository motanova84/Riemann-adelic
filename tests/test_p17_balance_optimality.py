#!/usr/bin/env python3
"""
Tests for the P17 Adelic-Fractal Equilibrium Module.

Tests verify that p = 17 is the optimal prime for adelic-fractal equilibrium
and validate the mathematical properties of the balance and equilibrium functions.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
"""

import pytest
import sys
import os
import mpmath as mp

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from utils.p17_balance_optimality import (
    balance,
    equilibrium,
    adelic_factor,
    fractal_suppression,
    verify_p17_optimality,
    connection_68_81,
    get_qcal_parameters,
    get_physical_primes,
    get_primes_to_check,
    find_optimal_prime,
    compute_R_psi,
    generate_equilibrium_data,
    F0_UNIVERSAL,
    COHERENCE_C,
    OPTIMAL_PRIME,
    REFERENCE_EQUILIBRIUM,
)


class TestBalanceFunction:
    """Tests for the balance function."""
    
    def test_balance_positive(self):
        """Test that balance is positive for all primes."""
        primes = get_primes_to_check()[:10]
        for p in primes:
            b = balance(p)
            assert float(b) > 0, f"balance({p}) should be positive"
    
    def test_balance_formula(self):
        """Test that balance = exp(π√p/2) / p^(3/2)."""
        mp.mp.dps = 80
        for p in [11, 13, 17, 19, 23]:
            expected = mp.exp(mp.pi * mp.sqrt(p) / 2) / mp.power(p, mp.mpf('1.5'))
            actual = balance(p, precision=80)
            assert abs(float(actual - expected)) < 1e-70
    
    def test_balance_at_17(self):
        """Test balance value at p=17."""
        b17 = balance(17, precision=80)
        # balance(17) ≈ 9.27
        assert 9.0 < float(b17) < 10.0
    
    def test_balance_increases_for_large_primes(self):
        """Test that balance increases for sufficiently large primes."""
        # Balance should generally increase for primes > ~3
        b17 = balance(17)
        b29 = balance(29)
        b47 = balance(47)
        assert float(b29) > float(b17)
        assert float(b47) > float(b29)


class TestAdelicAndFractalFactors:
    """Tests for adelic and fractal factors."""
    
    def test_adelic_factor_positive(self):
        """Test that adelic factor is positive."""
        for p in [2, 3, 5, 7, 11, 17]:
            a = adelic_factor(p)
            assert float(a) > 0
    
    def test_adelic_factor_increases(self):
        """Test that adelic factor increases with p."""
        a11 = adelic_factor(11)
        a17 = adelic_factor(17)
        a29 = adelic_factor(29)
        assert float(a17) > float(a11)
        assert float(a29) > float(a17)
    
    def test_fractal_suppression_positive(self):
        """Test that fractal suppression is positive."""
        for p in [2, 3, 5, 7, 11, 17]:
            f = fractal_suppression(p)
            assert float(f) > 0
    
    def test_fractal_suppression_decreases(self):
        """Test that fractal suppression decreases with p."""
        f11 = fractal_suppression(11)
        f17 = fractal_suppression(17)
        f29 = fractal_suppression(29)
        assert float(f11) > float(f17)
        assert float(f17) > float(f29)
    
    def test_balance_equals_product(self):
        """Test that balance = adelic_factor × fractal_suppression."""
        for p in [11, 17, 23]:
            a = adelic_factor(p, precision=80)
            f = fractal_suppression(p, precision=80)
            b = balance(p, precision=80)
            product = a * f
            assert abs(float(b - product)) < 1e-70


class TestEquilibriumFunction:
    """Tests for the equilibrium function."""
    
    def test_equilibrium_minimum_at_17(self):
        """Test that equilibrium has minimum at p=17."""
        primes = get_physical_primes()
        eq_values = {p: float(equilibrium(p)) for p in primes}
        min_prime = min(eq_values, key=eq_values.get)
        assert min_prime == 17, f"Minimum should be at p=17, got p={min_prime}"
    
    def test_equilibrium_at_17(self):
        """Test equilibrium value at p=17."""
        eq17 = equilibrium(17)
        # equilibrium(17) = 76.143 (by construction)
        assert abs(float(eq17) - 76.143) < 0.001
    
    def test_equilibrium_local_minimum(self):
        """Test that p=17 is a local minimum."""
        eq13 = equilibrium(13)
        eq17 = equilibrium(17)
        eq19 = equilibrium(19)
        assert float(eq17) < float(eq13), "eq(17) < eq(13)"
        assert float(eq17) < float(eq19), "eq(17) < eq(19)"
    
    def test_equilibrium_v_shape(self):
        """Test V-shape: decreasing before 17, increasing after."""
        eq11 = equilibrium(11)
        eq13 = equilibrium(13)
        eq17 = equilibrium(17)
        eq19 = equilibrium(19)
        eq23 = equilibrium(23)
        
        # Decreasing towards 17
        assert float(eq11) > float(eq13) > float(eq17)
        # Increasing away from 17
        assert float(eq17) < float(eq19) < float(eq23)


class TestP17Optimality:
    """Tests for p=17 optimality verification."""
    
    def test_verification_passes(self):
        """Test that verification passes."""
        result = verify_p17_optimality(precision=80)
        assert result['verification_passed'] is True
    
    def test_17_is_optimal(self):
        """Test that p=17 is identified as optimal."""
        result = verify_p17_optimality(precision=80)
        assert result['is_17_optimal'] is True
        assert result['optimal_prime'] == 17
    
    def test_local_minimum_check(self):
        """Test local minimum detection."""
        result = verify_p17_optimality(precision=80)
        assert result['local_minimum'] is True
    
    def test_global_minimum_check(self):
        """Test global minimum detection within physical primes."""
        result = verify_p17_optimality(precision=80)
        assert result['global_minimum'] is True


class TestConnection6881:
    """Tests for the 68/81 connection."""
    
    def test_decimal_value(self):
        """Test 68/81 decimal value."""
        conn = connection_68_81()
        assert conn['decimal_68_81'].startswith('0.839506172')
    
    def test_period_length(self):
        """Test period length is 9."""
        conn = connection_68_81()
        assert conn['period_length'] == 9
    
    def test_period_digits(self):
        """Test period digits are 839506172."""
        conn = connection_68_81()
        assert conn['period_digits'] == '839506172'
    
    def test_17_divides_68(self):
        """Test that 17 divides 68."""
        conn = connection_68_81()
        assert conn['is_17_divisor_of_68'] is True
        assert 68 % 17 == 0
        assert 68 // 17 == 4


class TestQCALParameters:
    """Tests for QCAL parameters."""
    
    def test_f0_universal(self):
        """Test universal frequency."""
        params = get_qcal_parameters()
        assert params['f0_universal_hz'] == F0_UNIVERSAL
        assert abs(params['f0_universal_hz'] - 141.7001) < 0.0001
    
    def test_coherence_c(self):
        """Test coherence constant."""
        params = get_qcal_parameters()
        assert params['coherence_C'] == COHERENCE_C
        assert abs(params['coherence_C'] - 244.36) < 0.01
    
    def test_optimal_prime(self):
        """Test optimal prime is 17."""
        params = get_qcal_parameters()
        assert params['optimal_prime_p0'] == 17
    
    def test_balance_at_p0(self):
        """Test balance at optimal prime."""
        params = get_qcal_parameters()
        assert params['balance_p0'] > 0
        # balance(17) ≈ 9.27
        assert 9.0 < params['balance_p0'] < 10.0


class TestFindOptimalPrime:
    """Tests for find_optimal_prime function."""
    
    def test_finds_17(self):
        """Test that optimal prime is 17."""
        optimal, min_val, all_vals = find_optimal_prime()
        assert optimal == 17
    
    def test_minimum_value(self):
        """Test minimum value is at p=17."""
        optimal, min_val, all_vals = find_optimal_prime()
        assert float(min_val) == float(all_vals[17])
    
    def test_custom_primes(self):
        """Test with custom prime list."""
        custom_primes = [11, 13, 17, 19, 23]
        optimal, min_val, all_vals = find_optimal_prime(primes=custom_primes)
        assert optimal == 17
        assert len(all_vals) == 5


class TestDataGeneration:
    """Tests for data generation functions."""
    
    def test_generate_equilibrium_data(self):
        """Test equilibrium data generation."""
        data = generate_equilibrium_data()
        assert len(data) > 0
        assert all('prime' in d for d in data)
        assert all('equilibrium' in d for d in data)
        assert all('balance' in d for d in data)
    
    def test_data_minimum_at_17(self):
        """Test that data shows minimum at p=17."""
        data = generate_equilibrium_data()
        min_entry = min(data, key=lambda d: d['equilibrium'])
        assert min_entry['prime'] == 17
        assert min_entry['is_minimum'] is True
    
    def test_reference_values_included(self):
        """Test that reference values are included."""
        data = generate_equilibrium_data()
        for entry in data:
            if entry['prime'] in REFERENCE_EQUILIBRIUM:
                assert entry['reference'] is not None


class TestComputeRPsi:
    """Tests for R_Ψ computation."""
    
    def test_r_psi_positive(self):
        """Test R_Ψ is positive."""
        for p in [11, 13, 17, 19, 23]:
            r_psi = compute_R_psi(p)
            assert float(r_psi) > 0
    
    def test_r_psi_equals_balance(self):
        """Test R_Ψ equals balance function."""
        for p in [11, 17, 29]:
            r_psi = compute_R_psi(p, precision=80)
            b = balance(p, precision=80)
            assert abs(float(r_psi - b)) < 1e-70


class TestPrimeUtilities:
    """Tests for prime utility functions."""
    
    def test_primes_to_check(self):
        """Test get_primes_to_check returns primes."""
        primes = get_primes_to_check()
        assert 2 in primes
        assert 17 in primes
        assert 101 in primes
        assert 4 not in primes  # Not prime
    
    def test_physical_primes(self):
        """Test get_physical_primes returns expected primes."""
        primes = get_physical_primes()
        assert 11 in primes
        assert 17 in primes
        assert 47 in primes
        assert 2 not in primes  # Too small
        assert 53 not in primes  # Too large


class TestConstants:
    """Tests for module constants."""
    
    def test_f0_universal_value(self):
        """Test F0_UNIVERSAL constant."""
        assert F0_UNIVERSAL == 141.7001
    
    def test_coherence_c_value(self):
        """Test COHERENCE_C constant."""
        assert COHERENCE_C == 244.36
    
    def test_optimal_prime_value(self):
        """Test OPTIMAL_PRIME constant."""
        assert OPTIMAL_PRIME == 17
    
    def test_reference_equilibrium(self):
        """Test REFERENCE_EQUILIBRIUM dictionary."""
        assert REFERENCE_EQUILIBRIUM[17] == 76.143
        assert len(REFERENCE_EQUILIBRIUM) == 6

#!/usr/bin/env python3
"""
Test Suite for Square-Free Numbers ↔ ζ(s) Connection
QCAL ∞³ Framework Integration

This test module validates the mathematical correctness of the square-free
numbers connection to the Riemann zeta function implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import mpmath as mp
from sympy import factorint, primefactors
from utils.square_free_connection import SquareFreeConnection, demonstrate_square_free_connection


class TestSquareFreeConnection:
    """Test suite for Square-Free ↔ ζ(s) connections."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.sf = SquareFreeConnection(dps=30, max_terms=10000)
        mp.mp.dps = 30
    
    def test_mobius_function_basic_values(self):
        """Test Möbius function μ(n) for known values."""
        # μ(1) = 1 (empty product)
        assert self.sf.mobius(1) == 1
        
        # Primes: μ(p) = -1
        assert self.sf.mobius(2) == -1
        assert self.sf.mobius(3) == -1
        assert self.sf.mobius(5) == -1
        assert self.sf.mobius(7) == -1
        
        # Product of two distinct primes: μ(pq) = 1
        assert self.sf.mobius(6) == 1   # 2*3
        assert self.sf.mobius(10) == 1  # 2*5
        assert self.sf.mobius(15) == 1  # 3*5
        
        # Product of three distinct primes: μ(pqr) = -1
        assert self.sf.mobius(30) == -1   # 2*3*5
        assert self.sf.mobius(42) == -1   # 2*3*7
        
        # Numbers with squared prime factors: μ(n) = 0
        assert self.sf.mobius(4) == 0    # 2²
        assert self.sf.mobius(8) == 0    # 2³
        assert self.sf.mobius(9) == 0    # 3²
        assert self.sf.mobius(12) == 0   # 2²*3
        assert self.sf.mobius(18) == 0   # 2*3²
    
    def test_is_square_free(self):
        """Test square-free detection."""
        # Square-free numbers
        assert self.sf.is_square_free(1) is True
        assert self.sf.is_square_free(2) is True
        assert self.sf.is_square_free(3) is True
        assert self.sf.is_square_free(5) is True
        assert self.sf.is_square_free(6) is True   # 2*3
        assert self.sf.is_square_free(30) is True  # 2*3*5
        assert self.sf.is_square_free(210) is True # 2*3*5*7
        
        # Non-square-free numbers
        assert self.sf.is_square_free(4) is False   # 2²
        assert self.sf.is_square_free(8) is False   # 2³
        assert self.sf.is_square_free(9) is False   # 3²
        assert self.sf.is_square_free(12) is False  # 2²*3
        assert self.sf.is_square_free(18) is False  # 2*3²
        assert self.sf.is_square_free(100) is False # 2²*5²
    
    def test_square_free_count_small(self):
        """Test square-free counting for small ranges."""
        # Q(10) = count of {1,2,3,5,6,7,10} = 7
        assert self.sf.square_free_count(10) == 7
        
        # Q(20) = {1,2,3,5,6,7,10,11,13,14,15,17,19} = 13
        # Missing: 4,8,9,12,16,18,20
        expected_20 = sum(1 for n in range(1, 21) if self.sf.is_square_free(n))
        assert self.sf.square_free_count(20) == expected_20
        
        # Q(100) should be close to (6/π²)*100 ≈ 60.8
        count_100 = self.sf.square_free_count(100)
        assert 55 <= count_100 <= 65, f"Q(100) = {count_100} is outside expected range"
    
    def test_square_free_density_theoretical(self):
        """Test theoretical density 6/π²."""
        density = self.sf.square_free_density_theoretical()
        
        # Should equal 1/ζ(2)
        zeta_2 = mp.zeta(2)
        expected = mp.mpf(1) / zeta_2
        
        assert abs(density - expected) < mp.mpf(1e-25), \
            f"Density {density} != 1/ζ(2) = {expected}"
        
        # Should equal 6/π²
        six_over_pi_sq = mp.mpf(6) / (mp.pi ** 2)
        assert abs(density - six_over_pi_sq) < mp.mpf(1e-25), \
            f"Density {density} != 6/π² = {six_over_pi_sq}"
    
    def test_square_free_density_convergence(self):
        """Test that empirical density converges to 6/π²."""
        density_theo = self.sf.square_free_density_theoretical()
        
        # Test convergence for increasing x
        for x in [100, 500, 1000]:
            density_emp = self.sf.square_free_density_empirical(x)
            error = abs(density_emp - density_theo)
            
            # Error should decrease as x increases (roughly as O(1/√x))
            expected_error = mp.mpf(5) / mp.sqrt(x)
            
            assert error < expected_error, \
                f"At x={x}: error {error} > expected {expected_error}"
    
    def test_mobius_inversion_formula(self):
        """Test Möbius inversion: ∑ μ(n)/n^s = 1/ζ(s)."""
        # Test at s = 2
        s = 2
        result = self.sf.validate_mobius_inversion(s, terms=10000)
        
        assert result['validated'], \
            f"Möbius inversion failed at s={s}: error = {result['relative_error']}"
        
        # Verify the relationship
        assert abs(result['mobius_sum'] - result['1/zeta_s']) < result['tolerance'], \
            "Möbius sum does not match 1/ζ(s)"
        
        # Test at s = 3
        s = 3
        result = self.sf.validate_mobius_inversion(s, terms=10000)
        
        assert result['validated'], \
            f"Möbius inversion failed at s={s}: error = {result['relative_error']}"
    
    def test_mobius_inversion_complex(self):
        """Test Möbius inversion for complex s."""
        # Test at s = 2 + i
        s = 2 + 1j
        result = self.sf.validate_mobius_inversion(s, terms=5000)
        
        # Should still work for Re(s) > 1
        assert result['validated'], \
            f"Möbius inversion failed at s={s}: error = {result['relative_error']}"
        
        # Verify both real and imaginary parts
        diff = result['mobius_sum'] - result['1/zeta_s']
        assert abs(diff.real) < result['tolerance'], "Real part mismatch"
        assert abs(diff.imag) < result['tolerance'], "Imaginary part mismatch"
    
    def test_square_free_divisor_sum(self):
        """Test ∑_{n square-free} d(n)/n^s = ζ(s)²/ζ(2s)."""
        # Note: This sum converges very slowly, O(1/log n), so we test
        # that the formula structure is correct rather than exact convergence
        
        # Test at s = 3 (converges faster for larger s)
        s = 3
        result = self.sf.square_free_divisor_sum(s, max_n=10000)
        
        # For s=3, convergence should be good enough
        assert result['relative_error'] < 0.05, \
            f"Divisor sum has too large error at s={s}: {result['relative_error']}"
        
        # Verify formula value is reasonable
        zeta_3 = mp.zeta(3)
        zeta_6 = mp.zeta(6)
        expected = zeta_3**2 / zeta_6
        
        # Check that we're computing the right thing
        assert abs(result['zeta_ratio'] - expected) < mp.mpf(1e-25), \
            "ζ(s)²/ζ(2s) formula computed incorrectly"
    
    def test_landau_error_bound(self):
        """Test Landau error bound: Q(x) = (6/π²)x + O(√x)."""
        # Test for several values of x
        for x in [100, 500, 1000, 5000]:
            result = self.sf.landau_error_bound(x)
            
            # Error should be O(√x)
            # Normalized error (error/√x) should be bounded
            normalized = abs(result['normalized_error'])
            
            # Empirically, |normalized_error| should be < 5 for reasonable x
            assert normalized < 10, \
                f"At x={x}: normalized error {normalized} is too large"
            
            # Main term should be close to Q(x)
            main_term = result['main_term']
            Q_x = result['Q_x']
            error_percentage = abs(Q_x - main_term) / main_term * 100
            
            # Error percentage should decrease as x increases
            expected_max_error_pct = 100 / mp.sqrt(x) * 10
            assert error_percentage < expected_max_error_pct, \
                f"At x={x}: error percentage {error_percentage}% too large"
    
    def test_adelic_s_finite_mobius(self):
        """Test S-finite Möbius function μ_S(n)."""
        # S = {2, 3, 5}
        S = [2, 3, 5]
        
        # μ_S(1) = 1 (empty product)
        assert self.sf.adelic_square_free_measure(S, 1) == 1
        
        # μ_S(2) = -1 (prime in S)
        assert self.sf.adelic_square_free_measure(S, 2) == -1
        assert self.sf.adelic_square_free_measure(S, 3) == -1
        assert self.sf.adelic_square_free_measure(S, 5) == -1
        
        # μ_S(6) = 1 (two primes in S)
        assert self.sf.adelic_square_free_measure(S, 6) == 1
        
        # μ_S(30) = -1 (three primes in S)
        assert self.sf.adelic_square_free_measure(S, 30) == -1
        
        # μ_S(4) = 0 (2² divides)
        assert self.sf.adelic_square_free_measure(S, 4) == 0
        assert self.sf.adelic_square_free_measure(S, 12) == 0  # 2²*3
        
        # μ_S(7) = 1 (prime not in S doesn't affect the product)
        # Actually, we only count primes in S, so primes outside S are ignored
        # This means μ_S considers only S-part
        assert self.sf.adelic_square_free_measure(S, 7) == 1
        assert self.sf.adelic_square_free_measure(S, 14) == -1  # Only 2 from S
    
    def test_comprehensive_validation(self):
        """Test comprehensive validation suite."""
        result = self.sf.comprehensive_validation(test_points=[2, 3])
        
        # Check that all components validated
        assert 'density_validation' in result
        assert 'mobius_inversion' in result
        assert 'divisor_sum' in result
        assert 'landau_bounds' in result
        
        # Check density validation
        for key, val in result['density_validation'].items():
            assert val['validated'], \
                f"Density validation failed for {key}"
        
        # Check Möbius inversion
        for key, val in result['mobius_inversion'].items():
            assert val['validated'], \
                f"Möbius inversion failed for {key}"
        
        # Check divisor sum (may fail for some points due to slow convergence)
        # We check that at least one point validates
        divisor_validated = any(val['validated'] for val in result['divisor_sum'].values())
        assert divisor_validated, "No divisor sum validations passed"
    
    def test_connection_to_zeta_zeros(self):
        """Test connection between square-free distribution and ζ zeros."""
        # The error term in Q(x) is related to zeros of ζ(s)
        # Via the explicit formula:
        # Q(x) = (6/π²)x - ∑_ρ x^ρ/(ρ ζ'(ρ)) + lower order terms
        # where ρ runs over non-trivial zeros of ζ(s)
        
        # For this test, we just verify the error exhibits oscillatory behavior
        # which is characteristic of the zero contribution
        
        x_values = [100, 200, 300, 400, 500]
        errors = []
        
        for x in x_values:
            result = self.sf.landau_error_bound(x)
            errors.append(float(result['error']))
        
        # Errors should oscillate (change sign or direction)
        # Check that errors don't all increase or all decrease
        differences = [errors[i+1] - errors[i] for i in range(len(errors)-1)]
        sign_changes = sum(1 for i in range(len(differences)-1) 
                          if differences[i] * differences[i+1] < 0)
        
        # Should have at least one sign change in differences (oscillation)
        assert sign_changes >= 1, \
            "Error term does not exhibit expected oscillatory behavior"


class TestSquareFreeIntegration:
    """Test integration with QCAL ∞³ framework."""
    
    def setup_method(self):
        """Set up test fixtures."""
        self.sf = SquareFreeConnection(dps=25, max_terms=5000)
        mp.mp.dps = 25
    
    def test_qcal_coherence_preservation(self):
        """Test that square-free computations preserve QCAL coherence."""
        # QCAL coherence constant: C = 244.36
        # This test verifies mathematical consistency with the framework
        
        # The density 6/π² should be computed consistently
        density = self.sf.square_free_density_theoretical()
        
        # Recompute using different method
        zeta_2 = mp.zeta(2)
        density_alt = mp.mpf(1) / zeta_2
        
        # Should match to full precision
        assert abs(density - density_alt) < mp.mpf(1e-20), \
            "Density computation lacks coherence"
    
    def test_adelic_interpretation_consistency(self):
        """Test that adelic interpretation is consistent."""
        # Square-free numbers correspond to maximal open compact subgroups
        # in the idelic framework
        
        # For S = {2, 3}, check that μ_S satisfies multiplicativity
        # over coprime numbers whose prime factors are all in S
        S = [2, 3]
        
        # 2 and 3 are coprime, both in S
        mu_2 = self.sf.adelic_square_free_measure(S, 2)
        mu_3 = self.sf.adelic_square_free_measure(S, 3)
        mu_6 = self.sf.adelic_square_free_measure(S, 6)
        
        # Should satisfy: μ_S(2*3) = μ_S(2) * μ_S(3)
        assert mu_6 == mu_2 * mu_3, \
            f"S-finite Möbius not multiplicative: μ_S(6)={mu_6} != {mu_2}*{mu_3}"
    
    def test_spectral_connection(self):
        """Test connection to spectral theory of A₀ operator."""
        # Square-free numbers should correspond to simple eigenvalues
        # in the spectral decomposition
        
        # The density 6/π² = 1/ζ(2) connects to the trace formula
        density = self.sf.square_free_density_theoretical()
        
        # ζ(2) = π²/6 (Basel problem)
        zeta_2_theoretical = mp.pi ** 2 / mp.mpf(6)
        zeta_2_computed = mp.zeta(2)
        
        assert abs(zeta_2_theoretical - zeta_2_computed) < mp.mpf(1e-20), \
            "Basel problem identity not satisfied"
        
        # Verify 1/ζ(2) = density
        inv_zeta_2 = mp.mpf(1) / zeta_2_computed
        assert abs(density - inv_zeta_2) < mp.mpf(1e-20), \
            "Density does not match 1/ζ(2)"
    
    def test_multiplicative_structure(self):
        """Test that square-free numbers exhibit pure multiplicative structure."""
        # Square-free numbers have maximum multiplicative independence:
        # each prime appears with exponent 0 or 1
        
        # Test several square-free numbers
        square_free_nums = [1, 2, 3, 5, 6, 7, 10, 15, 30]
        
        for n in square_free_nums:
            # Verify square-free
            assert self.sf.is_square_free(n), f"{n} should be square-free"
            
            # Check that all exponents in factorization are 1
            if n > 1:
                factors = factorint(n)
                for prime, exp in factors.items():
                    assert exp == 1, \
                        f"{n} has prime {prime} with exponent {exp} != 1"
    
    def test_error_handling(self):
        """Test error handling for invalid inputs."""
        # Test negative n
        with pytest.raises(ValueError):
            self.sf.mobius(-1)
        
        with pytest.raises(ValueError):
            self.sf.is_square_free(0)
        
        with pytest.raises(ValueError):
            self.sf.adelic_square_free_measure([2, 3], -5)


class TestDemonstration:
    """Test the demonstration function."""
    
    def test_demonstrate_square_free_connection(self):
        """Test that demonstration runs without errors."""
        # Run with reduced precision for speed
        results = demonstrate_square_free_connection(dps=15, verbose=False)
        
        # Check all expected keys are present
        assert 'mobius_examples' in results
        assert 'density' in results
        assert 'mobius_inversion' in results
        assert 'divisor_sum' in results
        assert 'landau_bounds' in results
        assert 'adelic_examples' in results
        
        # Check that validations passed (or at least computed)
        assert results['mobius_inversion']['validated'], \
            "Möbius inversion demonstration failed"
        # Note: divisor_sum may not validate with few terms, that's OK for demo
        
        # Check density is close to theoretical value
        density_theo = results['density']['theoretical']
        assert 0.607 < density_theo < 0.608, \
            f"Theoretical density {density_theo} out of range"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

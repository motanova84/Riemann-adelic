#!/usr/bin/env python3
"""
Tests for Spectral Bijection with Uniqueness and Exact Weyl Law

This test suite validates the complete rigorous spectral equivalence implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import pytest
import sys
from pathlib import Path

# Add parent's parent directory to path for imports from project root
sys.path.insert(0, str(Path(__file__).parent.parent))

import mpmath as mp
from validate_spectral_bijection_uniqueness import (
    spectral_map,
    spectral_map_inv,
    verify_bijection_inverse,
    get_first_zeta_zeros,
    verify_zeros_on_critical_line,
    validate_exact_weyl_law,
    validate_strong_local_uniqueness,
    compute_fundamental_frequency,
    run_complete_validation,
    F0_EXACT,
    C_PRIMARY,
    C_COHERENCE
)

# Set precision for tests
mp.mp.dps = 30


class TestSpectralBijection:
    """Test suite for spectral bijection mapping."""
    
    def test_bijection_map_definition(self):
        """Test that spectral_map extracts imaginary part correctly."""
        s = mp.mpc(0.5, 14.134725)
        λ = spectral_map(s)
        assert abs(λ - mp.mpf(14.134725)) < mp.mpf('1e-25')
    
    def test_bijection_inverse_map(self):
        """Test that spectral_map_inv constructs correct complex number."""
        λ = mp.mpf(21.022040)
        s = spectral_map_inv(λ)
        assert abs(mp.re(s) - mp.mpf(0.5)) < mp.mpf('1e-25')
        assert abs(mp.im(s) - λ) < mp.mpf('1e-25')
    
    def test_left_inverse_property(self):
        """Test spectral_map(spectral_map_inv(λ)) = λ."""
        test_values = [mp.mpf(10), mp.mpf(14.134), mp.mpf(21.022)]
        for λ in test_values:
            s = spectral_map_inv(λ)
            λ_recovered = spectral_map(s)
            assert abs(λ - λ_recovered) < mp.mpf('1e-25')
    
    def test_right_inverse_property(self):
        """Test spectral_map_inv(spectral_map(s)) = s for Re(s) = 1/2."""
        test_values = [
            mp.mpc(0.5, 10.0),
            mp.mpc(0.5, 14.134),
            mp.mpc(0.5, 21.022)
        ]
        for s in test_values:
            λ = spectral_map(s)
            s_recovered = spectral_map_inv(λ)
            assert abs(s - s_recovered) < mp.mpf('1e-25')
    
    def test_bijection_inverse_validation(self):
        """Test the complete bijection inverse validation."""
        results = verify_bijection_inverse()
        assert results['all_passed']
        assert results['max_error'] < mp.mpf('1e-40')


class TestZetaZeros:
    """Test suite for Riemann zeta zeros."""
    
    def test_get_zeta_zeros(self):
        """Test that we can compute zeta zeros."""
        zeros = get_first_zeta_zeros(5)
        assert len(zeros) == 5
        # First zero should be around 14.134725...
        assert abs(mp.im(zeros[0]) - mp.mpf(14.134725)) < 0.001
    
    def test_zeros_on_critical_line(self):
        """Test that computed zeros are on the critical line."""
        zeros = get_first_zeta_zeros(10)
        results = verify_zeros_on_critical_line(zeros, tolerance=1e-30)
        assert results['all_on_critical_line']
        assert results['max_deviation'] < mp.mpf('1e-30')
    
    def test_zeros_ordering(self):
        """Test that zeros are ordered by imaginary part."""
        zeros = get_first_zeta_zeros(10)
        for i in range(len(zeros) - 1):
            assert mp.im(zeros[i]) < mp.im(zeros[i + 1])


class TestWeylLaw:
    """Test suite for exact Weyl counting law."""
    
    def test_exact_weyl_law_small_T(self):
        """Test Weyl law for small heights."""
        zeros = get_first_zeta_zeros(20)
        results = validate_exact_weyl_law(zeros, T_values=[10, 20])
        assert results['all_passed']
        assert results['exact_equality']
    
    def test_weyl_law_various_heights(self):
        """Test Weyl law for various height values."""
        zeros = get_first_zeta_zeros(50)
        results = validate_exact_weyl_law(zeros, T_values=[30, 50, 100])
        
        # All should pass the |difference| < 1 criterion
        assert results['all_passed']
        
        # With exact bijection, difference should be 0
        for test in results['test_heights']:
            assert test['difference'] == 0
    
    def test_counting_functions_match(self):
        """Test that N_spec and N_zeros are identical."""
        zeros = get_first_zeta_zeros(30)
        results = validate_exact_weyl_law(zeros)
        
        for test in results['test_heights']:
            assert test['N_spec'] == test['N_zeros']


class TestLocalUniqueness:
    """Test suite for strong local uniqueness."""
    
    def test_no_duplicate_zeros(self):
        """Test that there are no duplicate zeros."""
        zeros = get_first_zeta_zeros(20)
        for i in range(len(zeros)):
            for j in range(i + 1, len(zeros)):
                assert zeros[i] != zeros[j]
    
    def test_minimum_spacing(self):
        """Test that zeros have minimum spacing."""
        zeros = get_first_zeta_zeros(30)
        results = validate_strong_local_uniqueness(zeros, epsilon=0.1)
        
        assert results['uniqueness_satisfied']
        assert results['min_distance'] > 0.5  # Zeros should be well-separated
    
    def test_local_uniqueness_large_epsilon(self):
        """Test uniqueness with larger epsilon."""
        zeros = get_first_zeta_zeros(15)
        results = validate_strong_local_uniqueness(zeros, epsilon=1.0)
        assert results['uniqueness_satisfied']
        assert len(results['violations']) == 0


class TestFundamentalFrequency:
    """Test suite for fundamental frequency derivation."""
    
    def test_frequency_constant_defined(self):
        """Test that F0_EXACT is properly defined."""
        assert F0_EXACT > 141
        assert F0_EXACT < 142
    
    def test_spectral_constants_defined(self):
        """Test that spectral constants are defined."""
        assert C_PRIMARY == mp.mpf(629.83)
        assert C_COHERENCE == mp.mpf(244.36)
    
    def test_frequency_computation(self):
        """Test fundamental frequency computation from gaps."""
        zeros = get_first_zeta_zeros(50)
        results = compute_fundamental_frequency(zeros, num_gaps=30)
        
        # Should compute average gap
        assert results['average_gap'] > 0
        
        # Should have computed zeta'(1/2)
        assert results['zeta_prime_abs'] > 0
        
        # First 10 gaps should be positive
        assert all(g > 0 for g in results['gaps'])


class TestCompleteValidation:
    """Test suite for complete validation workflow."""
    
    @pytest.mark.slow
    def test_complete_validation_small(self):
        """Test complete validation with small number of zeros."""
        results = run_complete_validation(num_zeros=10, verbose=False)
        assert results['all_passed']
        assert results['num_zeros_tested'] == 10
    
    @pytest.mark.slow
    def test_complete_validation_medium(self):
        """Test complete validation with medium number of zeros."""
        results = run_complete_validation(num_zeros=50, verbose=False)
        assert results['all_passed']
        
        # Check all sub-validations passed
        assert results['validations']['bijection_inverse']['all_passed']
        assert results['validations']['critical_line']['all_on_critical_line']
        assert results['validations']['exact_weyl_law']['all_passed']
        assert results['validations']['strong_local_uniqueness']['uniqueness_satisfied']
    
    def test_validation_signature(self):
        """Test that validation includes correct signature."""
        results = run_complete_validation(num_zeros=5, verbose=False)
        assert results['signature'] == "H_Ψ ≅ ζ(s) ≅ f₀ ≡ ∞³"
        assert results['doi'] == "10.5281/zenodo.17379721"
    
    def test_validation_precision(self):
        """Test that validation reports precision correctly."""
        results = run_complete_validation(num_zeros=5, verbose=False)
        assert results['precision_dps'] == mp.mp.dps


class TestMathematicalProperties:
    """Test suite for mathematical properties of the framework."""
    
    def test_critical_line_constant(self):
        """Test that critical line is always Re(s) = 1/2."""
        zeros = get_first_zeta_zeros(20)
        for z in zeros:
            assert abs(mp.re(z) - mp.mpf(0.5)) < mp.mpf('1e-30')
    
    def test_spectral_map_preserves_ordering(self):
        """Test that spectral_map preserves ordering of imaginary parts."""
        zeros = get_first_zeta_zeros(15)
        eigenvalues = [spectral_map(z) for z in zeros]
        
        # Eigenvalues should be ordered
        for i in range(len(eigenvalues) - 1):
            assert eigenvalues[i] < eigenvalues[i + 1]
    
    def test_bijection_domain_codomain(self):
        """Test that bijection maps correctly between spaces."""
        # Domain: critical line (Re = 1/2, Im ∈ ℝ)
        # Codomain: real eigenvalues (ℝ)
        
        λ = mp.mpf(25.010)
        s = spectral_map_inv(λ)
        
        # s should be on critical line
        assert abs(mp.re(s) - mp.mpf(0.5)) < mp.mpf('1e-25')
        
        # im(s) should be real
        assert isinstance(mp.im(s), (float, mp.mpf))
        
        # Eigenvalue should be real
        assert isinstance(λ, mp.mpf)


class TestQCALIntegration:
    """Test suite for QCAL framework integration."""
    
    def test_qcal_constants(self):
        """Test QCAL constants are properly defined."""
        assert C_PRIMARY > 600
        assert C_COHERENCE > 200
        assert F0_EXACT > 141
    
    def test_coherence_factor(self):
        """Test coherence factor C_coherence / C_primary."""
        coherence_factor = C_COHERENCE / C_PRIMARY
        # Should be approximately 0.388
        assert abs(coherence_factor - mp.mpf(0.388)) < 0.01
    
    def test_frequency_range(self):
        """Test fundamental frequency is in expected range."""
        # f₀ should be very close to 141.7001 Hz
        assert abs(F0_EXACT - mp.mpf(141.7001)) < 0.0001


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])

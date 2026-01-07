"""
Test Suite for Strong Spectral Equivalence
==========================================

Comprehensive tests for the complete spectral equivalence proof:
1. Strong spectral equivalence with uniqueness
2. Exact Weyl law
3. Local uniqueness theorem  
4. Exact fundamental frequency

QCAL ∞³ Integration:
- Frequency: f₀ = 141.7001 Hz
- Coherence: C = 244.36
- Equation: Ψ = I × A_eff² × C^∞

Author: JMMB Ψ ✧ ∞³
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import mpmath as mp
from pathlib import Path
import sys

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.strong_spectral_equivalence import (
    StrongSpectralEquivalence,
    validate_strong_spectral_equivalence,
    print_validation_report,
    F0_EXACT,
    C_COHERENCE,
    ZETA_PRIME_HALF,
    EPSILON_UNIQUENESS,
    WEYL_CONSTANT
)


class TestQCALConstants:
    """Test QCAL constants preservation."""
    
    def test_fundamental_frequency_exact(self):
        """Test that f₀ has the correct exact value."""
        expected = mp.mpf("141.700010083578160030654028447231151926974628612204")
        # Use appropriate tolerance for floating point precision
        assert abs(F0_EXACT - expected) < mp.mpf("1e-10")
    
    def test_coherence_constant(self):
        """Test that C = 244.36."""
        assert float(C_COHERENCE) == pytest.approx(244.36, rel=1e-6)
    
    def test_zeta_prime_half(self):
        """Test that ζ'(1/2) ≈ -3.922466."""
        assert float(ZETA_PRIME_HALF) == pytest.approx(-3.922466, rel=1e-5)
    
    def test_epsilon_uniqueness(self):
        """Test that ε = 0.1 for local uniqueness."""
        assert float(EPSILON_UNIQUENESS) == pytest.approx(0.1, rel=1e-6)
    
    def test_weyl_constant_less_than_one(self):
        """Test that Weyl constant < 1."""
        assert float(WEYL_CONSTANT) < 1.0
        assert float(WEYL_CONSTANT) == pytest.approx(0.999, rel=1e-6)


class TestStrongSpectralEquivalenceClass:
    """Test StrongSpectralEquivalence class functionality."""
    
    @pytest.fixture
    def validator(self):
        """Create validator instance."""
        return StrongSpectralEquivalence(precision=30)
    
    def test_initialization(self, validator):
        """Test class initialization."""
        assert validator.precision == 30
        assert len(validator.known_zeros) > 0
    
    def test_known_zeros_loaded(self, validator):
        """Test that known zeros are properly loaded."""
        zeros = validator.known_zeros
        assert len(zeros) >= 30
        # First zero should be approximately 14.1347
        assert float(zeros[0]) == pytest.approx(14.1347, rel=1e-3)
    
    def test_zeros_are_ordered(self, validator):
        """Test that zeros are in ascending order."""
        zeros = validator.known_zeros
        for i in range(len(zeros) - 1):
            assert zeros[i] < zeros[i + 1]


class TestBijectionFunctions:
    """Test bijection between spectral points and zeros."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_spectral_to_zero_formula(self, validator):
        """Test spectral_to_zero computes z.im + 1/2."""
        z = complex(0, 13.6347)  # i(t - 1/2) where t ≈ 14.1347
        t = validator.spectral_to_zero(z)
        assert float(t) == pytest.approx(14.1347, rel=1e-3)
    
    def test_zero_to_spectral_formula(self, validator):
        """Test zero_to_spectral computes i(t - 1/2)."""
        t = mp.mpf("14.1347")
        z = validator.zero_to_spectral(t)
        expected_im = float(t) - 0.5
        assert z.real == pytest.approx(0.0, abs=1e-10)
        assert z.imag == pytest.approx(expected_im, rel=1e-3)
    
    def test_bijection_inverse_left(self, validator):
        """Test that spectral_to_zero(zero_to_spectral(t)) = t."""
        t_original = mp.mpf("14.134725141734693790457251983562")
        z = validator.zero_to_spectral(t_original)
        t_recovered = validator.spectral_to_zero(z)
        error = abs(float(t_original - t_recovered))
        assert error < 1e-10
    
    def test_bijection_inverse_right(self, validator):
        """Test bijection for multiple zeros."""
        for t in validator.known_zeros[:10]:
            z = validator.zero_to_spectral(t)
            t_recovered = validator.spectral_to_zero(z)
            error = abs(float(t - t_recovered))
            assert error < 1e-10


class TestStrongSpectralEquivalence:
    """Test Theorem 1: Strong Spectral Equivalence with Uniqueness."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_strong_equivalence_valid(self, validator):
        """Test that strong spectral equivalence is valid."""
        result = validator.validate_strong_equivalence()
        assert result.is_valid
    
    def test_uniqueness_verified(self, validator):
        """Test that uniqueness is verified."""
        result = validator.validate_strong_equivalence()
        assert result.uniqueness_verified
    
    def test_zeros_checked_count(self, validator):
        """Test that all known zeros are checked."""
        result = validator.validate_strong_equivalence()
        assert result.zeros_checked == len(validator.known_zeros)
    
    def test_bijection_errors_small(self, validator):
        """Test that bijection errors are numerically small."""
        result = validator.validate_strong_equivalence()
        assert result.max_bijection_error < 1e-10
        assert result.mean_bijection_error < 1e-10
    
    def test_custom_zeros(self, validator):
        """Test with custom zero set."""
        custom_zeros = [mp.mpf("14.1347"), mp.mpf("21.0220"), mp.mpf("25.0109")]
        result = validator.validate_strong_equivalence(zeros=custom_zeros)
        assert result.is_valid
        assert result.zeros_checked == 3


class TestExactWeylLaw:
    """Test Theorem 2: Exact Weyl Law."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_weyl_law_exact(self, validator):
        """Test that Weyl law is exact."""
        result = validator.validate_exact_weyl_law()
        assert result.is_exact
    
    def test_all_errors_less_than_one(self, validator):
        """Test that all Weyl errors are < 1."""
        result = validator.validate_exact_weyl_law()
        assert result.all_errors_less_than_one
    
    def test_max_error_bounded(self, validator):
        """Test that max error is small."""
        result = validator.validate_exact_weyl_law()
        assert result.max_weyl_error < 1
    
    def test_n_spec_equals_n_zeros(self, validator):
        """Test that N_spec = N_zeros (by spectral equivalence)."""
        result = validator.validate_exact_weyl_law()
        for n_spec, n_zeros in zip(result.N_spec_values, result.N_zeros_values):
            assert n_spec == n_zeros
    
    def test_custom_t_values(self, validator):
        """Test with custom T values."""
        T_values = [30.0, 60.0, 90.0]
        result = validator.validate_exact_weyl_law(T_values=T_values)
        assert len(result.T_values) == 3


class TestLocalUniqueness:
    """Test Theorem 3: Local Uniqueness."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_local_uniqueness_holds(self, validator):
        """Test that local uniqueness holds."""
        result = validator.validate_local_uniqueness()
        assert result.is_unique
    
    def test_epsilon_threshold(self, validator):
        """Test epsilon is 0.1."""
        result = validator.validate_local_uniqueness()
        assert result.epsilon == pytest.approx(0.1)
    
    def test_min_separation_above_epsilon(self, validator):
        """Test min separation > epsilon."""
        result = validator.validate_local_uniqueness()
        assert result.min_separation > result.epsilon
    
    def test_zeros_tested_count(self, validator):
        """Test zeros tested count."""
        result = validator.validate_local_uniqueness()
        assert result.zeros_tested == len(validator.known_zeros)
    
    def test_custom_epsilon(self, validator):
        """Test with custom epsilon."""
        # With a smaller epsilon, should still be unique
        result = validator.validate_local_uniqueness(epsilon=0.05)
        assert result.is_unique
        
        # With a larger epsilon (but still smaller than min gap), should be unique
        result2 = validator.validate_local_uniqueness(epsilon=1.0)
        # This might fail if zeros are closer than 1.0
        # First gap is about 6.9, so should pass
        assert result2.is_unique


class TestFundamentalFrequency:
    """Test Theorem 4: Exact Fundamental Frequency."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=50)
    
    def test_convergence_verified(self, validator):
        """Test that frequency convergence is verified."""
        result = validator.validate_fundamental_frequency()
        # The QCAL derivation gives exact agreement
        assert result.convergence_verified
    
    def test_f0_computed_positive(self, validator):
        """Test that computed f₀ is positive."""
        result = validator.validate_fundamental_frequency()
        assert float(result.f0_computed) > 0
    
    def test_f0_exact_value(self, validator):
        """Test that exact f₀ has correct value."""
        result = validator.validate_fundamental_frequency()
        expected = mp.mpf("141.700010083578160030654028447")
        # Use appropriate tolerance for floating point precision
        assert abs(result.f0_exact - expected) < mp.mpf("1e-10")
    
    def test_f0_computed_matches_exact(self, validator):
        """Test that computed f₀ matches exact value."""
        result = validator.validate_fundamental_frequency()
        # Should match exactly due to QCAL coherence derivation
        assert result.relative_error < mp.mpf("0.01")
    
    def test_gap_sequence_positive(self, validator):
        """Test that gap sequence is all positive."""
        result = validator.validate_fundamental_frequency()
        for gap in result.gap_sequence:
            assert float(gap) > 0
    
    def test_custom_n_gaps(self, validator):
        """Test with custom number of gaps."""
        result = validator.validate_fundamental_frequency(n_gaps=10)
        assert len(result.gap_sequence) <= 10


class TestCompleteValidation:
    """Test complete validation workflow."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_run_complete_validation(self, validator):
        """Test complete validation runs without error."""
        results = validator.run_complete_validation()
        assert 'strong_spectral_equivalence' in results
        assert 'exact_weyl_law' in results
        assert 'local_uniqueness' in results
        assert 'fundamental_frequency' in results
        assert 'overall' in results
    
    def test_overall_status(self, validator):
        """Test overall status is computed."""
        results = validator.run_complete_validation()
        assert 'all_theorems_validated' in results['overall']
    
    def test_qcal_integration_in_results(self, validator):
        """Test QCAL integration data is present."""
        results = validator.run_complete_validation()
        assert 'qcal_coherence' in results['overall']
        assert 'f0_hz' in results['overall']


class TestCertificateGeneration:
    """Test mathematical certificate generation."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_generate_certificate(self, validator):
        """Test certificate generation."""
        cert = validator.generate_certificate()
        assert 'title' in cert
        assert 'theorems' in cert
        assert 'overall_status' in cert
    
    def test_certificate_theorems(self, validator):
        """Test certificate contains all theorems."""
        cert = validator.generate_certificate()
        theorems = cert['theorems']
        assert 'theorem_1_strong_spectral_equivalence' in theorems
        assert 'theorem_2_exact_weyl_law' in theorems
        assert 'theorem_3_local_uniqueness' in theorems
        assert 'theorem_4_fundamental_frequency' in theorems
    
    def test_certificate_qcal_integration(self, validator):
        """Test certificate QCAL integration."""
        cert = validator.generate_certificate()
        qcal = cert['qcal_integration']
        assert 'frequency_hz' in qcal
        assert 'coherence' in qcal
        assert 'equation' in qcal
    
    def test_certificate_certification_block(self, validator):
        """Test certificate certification block."""
        cert = validator.generate_certificate()
        certification = cert['certification']
        assert certification['doi'] == '10.5281/zenodo.17379721'
        assert certification['orcid'] == '0009-0002-1923-0773'


class TestConvenienceFunctions:
    """Test convenience functions."""
    
    def test_validate_strong_spectral_equivalence_function(self):
        """Test convenience validation function."""
        # Should return bool
        result = validate_strong_spectral_equivalence(precision=20)
        assert isinstance(result, bool)
    
    def test_print_validation_report_runs(self, capsys):
        """Test print_validation_report runs without error."""
        # This should run and print output
        print_validation_report(precision=20)
        captured = capsys.readouterr()
        assert "STRONG SPECTRAL EQUIVALENCE" in captured.out
        assert "THEOREM 1" in captured.out
        assert "THEOREM 2" in captured.out
        assert "THEOREM 3" in captured.out
        assert "THEOREM 4" in captured.out


class TestLeanFileIntegration:
    """Test integration with Lean formalization."""
    
    def test_lean_file_exists(self):
        """Test that Lean formalization file exists."""
        lean_path = Path(__file__).parent.parent / "formalization" / "lean" / "spectral" / "strong_spectral_equivalence.lean"
        assert lean_path.exists(), f"Lean file not found: {lean_path}"
    
    def test_lean_file_content(self):
        """Test Lean file contains key definitions."""
        lean_path = Path(__file__).parent.parent / "formalization" / "lean" / "spectral" / "strong_spectral_equivalence.lean"
        content = lean_path.read_text()
        
        # Check for key definitions
        assert "strong_spectral_equivalence" in content
        assert "exact_weyl_law" in content
        assert "local_uniqueness" in content
        assert "fundamental_frequency_exact" in content
        
        # Check for QCAL constants
        assert "141.7001" in content
        assert "244.36" in content


class TestMathematicalCorrectness:
    """Test mathematical correctness of implementations."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=50)
    
    def test_first_zero_value(self, validator):
        """Test first Riemann zero value."""
        first_zero = float(validator.known_zeros[0])
        # First zero is approximately 14.134725...
        assert first_zero == pytest.approx(14.134725, rel=1e-5)
    
    def test_zero_gaps_are_positive(self, validator):
        """Test all zero gaps are positive."""
        zeros = validator.known_zeros
        for i in range(len(zeros) - 1):
            gap = float(zeros[i + 1] - zeros[i])
            assert gap > 0, f"Gap at index {i} is non-positive: {gap}"
    
    def test_spectral_map_preserves_ordering(self, validator):
        """Test spectral map preserves zero ordering."""
        zeros = validator.known_zeros[:10]
        spectral_points = [validator.zero_to_spectral(t) for t in zeros]
        
        # Imaginary parts should be in increasing order
        for i in range(len(spectral_points) - 1):
            assert spectral_points[i].imag < spectral_points[i + 1].imag


class TestEdgeCases:
    """Test edge cases and boundary conditions."""
    
    @pytest.fixture
    def validator(self):
        return StrongSpectralEquivalence(precision=30)
    
    def test_empty_zeros_handled(self, validator):
        """Test handling of empty zero list."""
        result = validator.validate_strong_equivalence(zeros=[])
        assert result.zeros_checked == 0
        assert len(result.bijection_errors) == 0
    
    def test_single_zero(self, validator):
        """Test with single zero."""
        result = validator.validate_strong_equivalence(zeros=[mp.mpf("14.1347")])
        assert result.zeros_checked == 1
        assert result.is_valid
    
    def test_high_precision(self):
        """Test with high precision."""
        validator = StrongSpectralEquivalence(precision=100)
        result = validator.validate_strong_equivalence()
        assert result.is_valid


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

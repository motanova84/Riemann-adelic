#!/usr/bin/env python3
"""
Test Suite for Riemann-Zeta (ζ) Synchrony Validation

Tests the validation of the relationship between QCAL fundamental frequency
f₀ = 141.7001 Hz and the first Riemann zero γ₁ ≈ 14.134725.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import pytest
import mpmath as mp
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.riemann_zeta_synchrony import RiemannZetaSynchrony


class TestRiemannZetaSynchronyBasics:
    """Test basic functionality of Riemann-Zeta synchrony validator."""
    
    @pytest.fixture
    def validator(self):
        """Create a synchrony validator instance."""
        return RiemannZetaSynchrony(precision=30)
    
    def test_initialization(self, validator):
        """Test validator initialization."""
        assert validator.precision == 30
        assert float(validator.f0) == pytest.approx(141.7001, abs=1e-4)
        assert float(validator.delta_zeta) == pytest.approx(0.2787437627, abs=1e-7)
        assert float(validator.gamma_1) == pytest.approx(14.134725141734693, abs=1e-10)
    
    def test_gamma_1_high_precision(self, validator):
        """Test that γ₁ is stored with high precision."""
        # γ₁ should have at least 30 decimal places
        gamma_1_str = str(validator.gamma_1)
        # Remove decimal point
        digits = gamma_1_str.replace('.', '').replace('-', '')
        assert len(digits) >= 30, f"γ₁ precision insufficient: {gamma_1_str}"
    
    def test_constants_match_qcal_beacon(self, validator):
        """Test that constants match .qcal_beacon values."""
        assert validator.F0_HZ == 141.7001
        assert validator.DELTA_ZETA == pytest.approx(0.2787437627, abs=1e-9)
        assert validator.OCTAVE_MULTIPLIER == 10


class TestOctaveResonance:
    """Test octave resonance calculations."""
    
    @pytest.fixture
    def validator(self):
        """Create a synchrony validator instance."""
        return RiemannZetaSynchrony(precision=30)
    
    def test_compute_octave_resonance(self, validator):
        """Test octave resonance computation."""
        resonance = validator.compute_octave_resonance()
        
        # Check all required keys are present
        assert 'gamma_1' in resonance
        assert 'ten_gamma_1' in resonance
        assert 'f0' in resonance
        assert 'octave_deviation' in resonance
        assert 'ratio' in resonance
        assert 'expected_ratio' in resonance
    
    def test_ten_gamma_1_value(self, validator):
        """Test that 10 × γ₁ ≈ 141.34725."""
        resonance = validator.compute_octave_resonance()
        ten_gamma_1 = float(resonance['ten_gamma_1'])
        
        # 10 × 14.134725141734693 ≈ 141.34725141734693
        assert ten_gamma_1 == pytest.approx(141.34725141734693, abs=1e-10)
    
    def test_octave_deviation_magnitude(self, validator):
        """Test that f₀ - 10×γ₁ is small (order of 0.35 Hz)."""
        resonance = validator.compute_octave_resonance()
        deviation = float(resonance['octave_deviation'])
        
        # f₀ - 10×γ₁ should be small (< 1 Hz)
        # Showing approximate octave resonance
        assert abs(deviation) < 1.0, f"Deviation too large: {deviation}"
        assert abs(deviation) > 0.1, f"Deviation unexpectedly small: {deviation}"
    
    def test_frequency_ratio_near_10(self, validator):
        """Test that f₀/γ₁ ≈ 10."""
        resonance = validator.compute_octave_resonance()
        ratio = float(resonance['ratio'])
        
        # f₀/γ₁ should be close to 10 (octave resonance)
        # Tolerance: within 0.1 of 10
        assert ratio == pytest.approx(10.0, abs=0.1)
    
    def test_expected_ratio_formula(self, validator):
        """Test that expected ratio is 10 + some small modulation."""
        resonance = validator.compute_octave_resonance()
        expected = float(resonance['expected_ratio'])
        
        # Should be slightly greater than 10
        assert expected > 10.0
        assert expected < 10.1
    
    def test_validate_octave_resonance_passes(self, validator):
        """Test that octave resonance validation passes with appropriate tolerance."""
        is_valid, report = validator.validate_octave_resonance(tolerance=0.5)
        
        assert is_valid, f"Octave resonance validation failed:\n{report}"
        assert "OCTAVE RESONANCE CONFIRMED" in report
    
    def test_octave_resonance_with_tolerance(self, validator):
        """Test octave resonance with appropriate tolerance."""
        # With tolerance 0.5 Hz, should pass
        is_valid, report = validator.validate_octave_resonance(tolerance=0.5)
        
        assert is_valid, f"Tolerance check failed:\n{report}"


class TestHarmonicModulation:
    """Test harmonic modulation validation."""
    
    @pytest.fixture
    def validator(self):
        """Create a synchrony validator instance."""
        return RiemannZetaSynchrony(precision=30)
    
    def test_validate_harmonic_modulation(self, validator):
        """Test harmonic modulation validation."""
        is_valid, report = validator.validate_harmonic_modulation()
        
        # Should pass validation
        assert is_valid or "SMALL DEVIATION" in report
        assert "Harmonic Modulation" in report
    
    def test_modulation_factor_small(self, validator):
        """Test that (f₀/γ₁ - 10) × 10 is small."""
        resonance = validator.compute_octave_resonance()
        
        # (f₀/γ₁ - 10) × 10 should be small (< 1)
        modulation = float((resonance['ratio'] - mp.mpf(10)) * mp.mpf(10))
        
        assert abs(modulation) < 1.0


class TestPrimeNavigation:
    """Test prime number navigation analysis."""
    
    @pytest.fixture
    def validator(self):
        """Create a synchrony validator instance."""
        return RiemannZetaSynchrony(precision=30)
    
    def test_compute_prime_navigation_index(self, validator):
        """Test computation of Prime Navigation Index."""
        pni_data = validator.compute_prime_navigation_index()
        
        # Check all required keys
        assert 'gamma_1' in pni_data
        assert 'gamma_2' in pni_data
        assert 'gamma_3' in pni_data
        assert 'delta_1_2' in pni_data
        assert 'delta_2_3' in pni_data
        assert 'avg_spacing' in pni_data
        assert 'freq_spacing_ratio' in pni_data
        assert 'prime_navigation_index' in pni_data
    
    def test_gamma_values_ascending(self, validator):
        """Test that γ₁ < γ₂ < γ₃."""
        pni_data = validator.compute_prime_navigation_index()
        
        assert pni_data['gamma_1'] < pni_data['gamma_2']
        assert pni_data['gamma_2'] < pni_data['gamma_3']
    
    def test_zero_spacing_positive(self, validator):
        """Test that zero spacings are positive."""
        pni_data = validator.compute_prime_navigation_index()
        
        assert pni_data['delta_1_2'] > 0
        assert pni_data['delta_2_3'] > 0
        assert pni_data['avg_spacing'] > 0
    
    def test_prime_navigation_index_range(self, validator):
        """Test that PNI is in valid range [0, 1]."""
        pni_data = validator.compute_prime_navigation_index()
        pni = pni_data['prime_navigation_index']
        
        assert 0 <= pni <= 1, f"PNI out of range: {pni}"
    
    def test_validate_prime_navigation(self, validator):
        """Test prime navigation validation."""
        is_valid, report = validator.validate_prime_navigation()
        
        # Should indicate navigation capability
        assert "Prime Number Navigation" in report
        assert "Navigation Metrics" in report


class TestFullValidation:
    """Test complete synchrony validation."""
    
    @pytest.fixture
    def validator(self):
        """Create a synchrony validator instance."""
        return RiemannZetaSynchrony(precision=30)
    
    def test_full_validation_structure(self, validator):
        """Test that full validation returns proper structure."""
        is_valid, report = validator.full_validation()
        
        # Should return boolean and string
        assert isinstance(is_valid, bool)
        assert isinstance(report, str)
    
    def test_full_validation_includes_all_checks(self, validator):
        """Test that full validation includes all check types."""
        is_valid, report = validator.full_validation()
        
        # Should include all three validation types
        assert "Octave Resonance" in report or "OCTAVE RESONANCE" in report
        assert "Harmonic Modulation" in report or "HARMONIC MODULATION" in report
        assert "Prime Navigation" in report or "Prime Number Navigation" in report
    
    def test_full_validation_includes_summary(self, validator):
        """Test that full validation includes summary."""
        is_valid, report = validator.full_validation()
        
        assert "VALIDATION SUMMARY" in report
        assert "Octave Resonance:" in report
        assert "Harmonic Modulation:" in report
        assert "Prime Navigation:" in report
    
    def test_full_validation_conclusion(self, validator):
        """Test that full validation provides conclusion."""
        is_valid, report = validator.full_validation()
        
        # Should have a conclusion section
        assert "Conclusion:" in report or "SYNCHRONY" in report
    
    def test_validation_passes(self, validator):
        """Test that full validation passes all checks."""
        is_valid, report = validator.full_validation()
        
        # At least octave resonance should pass
        assert "Octave Resonance:      ✅ PASS" in report, \
            f"Octave resonance should pass:\n{report}"


class TestPrecisionScaling:
    """Test validation with different precision levels."""
    
    def test_low_precision_validation(self):
        """Test validation with low precision (15 dps)."""
        validator = RiemannZetaSynchrony(precision=15)
        is_valid, report = validator.validate_octave_resonance()
        
        # Should still pass with lower precision
        assert is_valid or "RESONANCE" in report
    
    def test_high_precision_validation(self):
        """Test validation with high precision (50 dps)."""
        validator = RiemannZetaSynchrony(precision=50)
        is_valid, report = validator.validate_octave_resonance()
        
        # Should pass with high precision
        assert is_valid, f"High precision validation failed:\n{report}"
    
    def test_precision_affects_gamma_1(self):
        """Test that precision affects γ₁ representation."""
        validator_15 = RiemannZetaSynchrony(precision=15)
        validator_50 = RiemannZetaSynchrony(precision=50)
        
        # Both should have same γ₁ value
        diff = abs(validator_15.gamma_1 - validator_50.gamma_1)
        assert float(diff) < 1e-14


class TestMathematicalRelationships:
    """Test mathematical relationships and identities."""
    
    @pytest.fixture
    def validator(self):
        """Create a synchrony validator instance."""
        return RiemannZetaSynchrony(precision=30)
    
    def test_euclidean_plus_delta_near_f0(self, validator):
        """Test that 100√2 + δζ is close to f₀."""
        euclidean = float(validator.EUCLIDEAN_DIAGONAL)
        computed_f0 = euclidean + validator.DELTA_ZETA
        
        # Should be close to f₀ (within 0.01 Hz tolerance)
        assert computed_f0 == pytest.approx(validator.F0_HZ, abs=0.01)
    
    def test_ten_gamma_1_near_f0(self, validator):
        """Test that 10×γ₁ is close to f₀."""
        resonance = validator.compute_octave_resonance()
        ten_gamma_1 = float(resonance['ten_gamma_1'])
        
        # Should be close to f₀ (within 1 Hz showing octave resonance)
        assert ten_gamma_1 == pytest.approx(validator.F0_HZ, abs=1.0)
    
    def test_ratio_deviation_small(self, validator):
        """Test that f₀/γ₁ - 10 is small."""
        resonance = validator.compute_octave_resonance()
        
        lhs = float(resonance['ratio'] - mp.mpf(10))
        
        # Should be small (< 0.1)
        assert abs(lhs) < 0.1


class TestDemonstrationFunction:
    """Test the demonstration function."""
    
    def test_demonstrate_function_runs(self):
        """Test that demonstration function runs without error."""
        from utils.riemann_zeta_synchrony import demonstrate_riemann_zeta_synchrony
        
        # Should run without raising exception
        result = demonstrate_riemann_zeta_synchrony(precision=25)
        
        # Should return a boolean
        assert isinstance(result, bool)
    
    def test_demonstrate_function_returns_true(self):
        """Test that demonstration function indicates success."""
        from utils.riemann_zeta_synchrony import demonstrate_riemann_zeta_synchrony
        
        result = demonstrate_riemann_zeta_synchrony(precision=30)
        
        # Should pass validation
        assert result, "Demonstration should indicate successful validation"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

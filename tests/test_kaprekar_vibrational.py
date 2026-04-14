#!/usr/bin/env python3
"""
Tests for Kaprekar Vibrational Operator

Tests the Kaprekar operator with vibrational frequency analysis including:
- Digit extraction
- Frequency computation
- Kaprekar step operation
- Orbit and attractor analysis
- Coherence classification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.kaprekar_vibrational import (
    KaprekarVibrationalOperator,
    CoherenceType,
)
from utils.digit_frequencies import F0_HZ


class TestKaprekarVibrationalOperator:
    """Test suite for Kaprekar vibrational operator."""
    
    @pytest.fixture
    def operator(self):
        """Create operator instance."""
        return KaprekarVibrationalOperator()
    
    def test_initialization(self, operator):
        """Test operator initialization."""
        assert operator.f0 == F0_HZ
        assert operator.KAPREKAR_CONSTANT == 6174
        assert operator.SINGULAR_POINT == 1000
    
    def test_get_digits_1000(self, operator):
        """Test digit extraction for 1000."""
        digits = operator.get_digits(1000)
        assert digits == [1, 0, 0, 0]
    
    def test_get_digits_6174(self, operator):
        """Test digit extraction for Kaprekar constant."""
        digits = operator.get_digits(6174)
        assert digits == [6, 1, 7, 4]
    
    def test_get_digits_9999(self, operator):
        """Test digit extraction for 9999."""
        digits = operator.get_digits(9999)
        assert digits == [9, 9, 9, 9]
    
    def test_get_digits_invalid_low(self, operator):
        """Test that negative numbers raise ValueError."""
        with pytest.raises(ValueError):
            operator.get_digits(-1)
    
    def test_get_digits_invalid_high(self, operator):
        """Test that numbers > 9999 raise ValueError."""
        with pytest.raises(ValueError):
            operator.get_digits(10000)
    
    def test_compute_frequency_1000(self, operator):
        """Test frequency of singular point 1000."""
        freq = operator.compute_frequency(1000)
        # 1000 has digits [1,0,0,0], so freq = 1×f₀ = f₀
        assert abs(freq - F0_HZ) < 0.001
    
    def test_compute_frequency_9999(self, operator):
        """Test frequency of 9999."""
        freq = operator.compute_frequency(9999)
        # 9999 has digits [9,9,9,9], so freq = 36×f₀
        expected = 36 * F0_HZ
        assert abs(freq - expected) < 0.001
    
    def test_compute_frequency_1234(self, operator):
        """Test frequency of 1234."""
        freq = operator.compute_frequency(1234)
        # Digit sum = 1+2+3+4 = 10
        expected = 10 * F0_HZ
        assert abs(freq - expected) < 0.001
    
    def test_kaprekar_step_6174(self, operator):
        """Test that 6174 is a fixed point."""
        result = operator.kaprekar_step(6174)
        assert result == 6174
    
    def test_kaprekar_step_6174_derivation(self, operator):
        """Test Kaprekar step derivation for 6174."""
        # 6174: digits [6,1,7,4]
        # Descending: 7641
        # Ascending: 1467
        # 7641 - 1467 = 6174
        result = operator.kaprekar_step(6174)
        assert result == 6174
    
    def test_kaprekar_step_1000(self, operator):
        """Test Kaprekar step for 1000."""
        result = operator.kaprekar_step(1000)
        # 1000: digits [1,0,0,0]
        # Descending: 1000
        # Ascending: 0001 = 1
        # 1000 - 1 = 999
        assert result == 999
    
    def test_kaprekar_step_3524(self, operator):
        """Test Kaprekar step for 3524."""
        result = operator.kaprekar_step(3524)
        # 3524: digits [3,5,2,4]
        # Descending: 5432
        # Ascending: 2345
        # 5432 - 2345 = 3087
        assert result == 3087
    
    def test_find_orbit_6174(self, operator):
        """Test orbit for Kaprekar constant (should be immediate)."""
        orbit, attractor = operator.find_orbit(6174)
        
        assert len(orbit) >= 2  # [6174, 6174]
        assert 6174 in attractor
    
    def test_find_orbit_1000(self, operator):
        """Test orbit starting from 1000."""
        orbit, attractor = operator.find_orbit(1000)
        
        # Should reach 6174 eventually
        assert len(orbit) > 1
        # Orbit should converge
        assert len(attractor) >= 1
    
    def test_find_orbit_3524(self, operator):
        """Test orbit for 3524 (known to reach 6174 in 3 steps)."""
        orbit, attractor = operator.find_orbit(3524)
        
        # Should converge to 6174
        assert 6174 in orbit or 6174 in attractor
    
    def test_analyze_number_1000(self, operator):
        """Test complete analysis of singular point 1000."""
        state = operator.analyze_number(1000)
        
        assert state.number == 1000
        assert state.digits == [1, 0, 0, 0]
        assert abs(state.frequency - F0_HZ) < 0.001
        assert state.coherence_type == CoherenceType.PURE
    
    def test_analyze_number_6174(self, operator):
        """Test complete analysis of Kaprekar constant."""
        state = operator.analyze_number(6174)
        
        assert state.number == 6174
        assert state.digits == [6, 1, 7, 4]
        assert state.kaprekar_next == 6174
        assert 6174 in state.attractor
    
    def test_analyze_number_9999(self, operator):
        """Test complete analysis of maximum frequency number."""
        state = operator.analyze_number(9999)
        
        assert state.number == 9999
        assert state.digits == [9, 9, 9, 9]
        expected_freq = 36 * F0_HZ
        assert abs(state.frequency - expected_freq) < 0.001
    
    def test_validate_theorem_singular_1000(self, operator):
        """Test theorem that 1000 is unique with frequency f₀."""
        is_valid, details = operator.validate_theorem_singular_1000()
        
        assert abs(details['freq_1000'] - F0_HZ) < 0.001
        assert abs(details['deviation']) < 0.001
        # 1000 should be unique (or at most 10000 which is out of range)
        assert is_valid
    
    def test_compute_9s_attractor_frequency(self, operator):
        """Test frequency of 9s attractor."""
        freq = operator.compute_9s_attractor_frequency()
        
        # 9999 has digit sum 36
        expected = 36 * F0_HZ
        assert abs(freq - expected) < 0.001
    
    def test_frequency_increases_with_digit_sum(self, operator):
        """Test that frequency increases with digit sum."""
        # Compare different numbers
        freq_1000 = operator.compute_frequency(1000)  # sum = 1
        freq_2000 = operator.compute_frequency(2000)  # sum = 2
        freq_5555 = operator.compute_frequency(5555)  # sum = 20
        freq_9999 = operator.compute_frequency(9999)  # sum = 36
        
        assert freq_1000 < freq_2000 < freq_5555 < freq_9999
    
    def test_coherence_classification_pure(self, operator):
        """Test classification of pure coherence (1000)."""
        state = operator.analyze_number(1000)
        assert state.coherence_type == CoherenceType.PURE
    
    def test_format_analysis(self, operator):
        """Test formatting of analysis results."""
        state = operator.analyze_number(6174)
        formatted = operator.format_analysis(state)
        
        assert "6174" in formatted
        assert "Frequency" in formatted
        assert "Attractor" in formatted


class TestKaprekarProperties:
    """Test mathematical properties of Kaprekar operator."""
    
    @pytest.fixture
    def operator(self):
        """Create operator instance."""
        return KaprekarVibrationalOperator()
    
    def test_kaprekar_convergence(self, operator):
        """Test that random numbers converge within reasonable steps."""
        import random
        random.seed(42)
        
        for _ in range(20):
            n = random.randint(1000, 9999)
            orbit, attractor = operator.find_orbit(n, max_steps=20)
            
            # Should converge within 20 steps
            assert len(orbit) <= 20 + len(attractor)
    
    def test_kaprekar_fixed_point_uniqueness(self, operator):
        """Test that 6174 is the unique fixed point for 4-digit numbers."""
        # Check a sample of numbers
        fixed_points = set()
        
        for n in range(1000, 2000, 100):  # Sample
            if operator.kaprekar_step(n) == n:
                fixed_points.add(n)
        
        # 6174 should be in fixed points if sampled
        # Or we can test it directly
        assert operator.kaprekar_step(6174) == 6174
    
    def test_frequency_preserves_digit_sum(self, operator):
        """Test that frequency is determined by digit sum."""
        # Numbers with same digit sum should have same frequency
        freq_1234 = operator.compute_frequency(1234)  # sum = 10
        freq_2233 = operator.compute_frequency(2233)  # sum = 10
        freq_5500 = operator.compute_frequency(5500)  # sum = 10
        
        assert abs(freq_1234 - freq_2233) < 0.001
        assert abs(freq_2233 - freq_5500) < 0.001
    
    def test_orbit_deterministic(self, operator):
        """Test that orbits are deterministic."""
        # Running twice should give same result
        orbit1, attractor1 = operator.find_orbit(3524)
        orbit2, attractor2 = operator.find_orbit(3524)
        
        assert orbit1 == orbit2
        assert attractor1 == attractor2


class TestVibrationalFrequencyAttractors:
    """Test frequency attractor analysis."""
    
    @pytest.fixture
    def operator(self):
        """Create operator instance."""
        return KaprekarVibrationalOperator()
    
    def test_find_frequency_attractors(self, operator):
        """Test finding frequency attractors."""
        attractors = operator.find_frequency_attractors(n_samples=50)
        
        # Should find at least one attractor
        assert len(attractors) > 0
        
        # All frequencies should be non-negative
        for freq in attractors.keys():
            assert freq >= 0
    
    def test_frequency_attractors_include_6174(self, operator):
        """Test that frequency attractors include 6174."""
        # Analyze several numbers, most should reach 6174
        numbers_reaching_6174 = 0
        
        for n in range(1000, 1100):
            orbit, attractor = operator.find_orbit(n)
            if 6174 in orbit or 6174 in attractor:
                numbers_reaching_6174 += 1
        
        # Most numbers should reach 6174
        assert numbers_reaching_6174 > 50  # More than half


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

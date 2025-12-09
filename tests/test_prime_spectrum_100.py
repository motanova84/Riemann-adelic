#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for prime_spectrum_100.py

Instituto de Conciencia Cuántica – QCAL ∞³
"""

import pytest
import math
import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from prime_spectrum_100 import (
    generate_primes,
    equilibrium,
    R_Psi,
    frequency,
    freq_to_midi,
    midi_to_note,
    analyze_prime,
    classify_by_octave,
    find_special_primes,
    SCALE_FACTOR,
    C_LIGHT,
    PLANCK_LENGTH,
    A4_FREQ,
)


class TestGeneratePrimes:
    """Tests for prime generation."""

    def test_generate_first_10_primes(self):
        """Test that first 10 primes are correct."""
        primes = generate_primes(10)
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes == expected

    def test_generate_100_primes(self):
        """Test that we get exactly 100 primes."""
        primes = generate_primes(100)
        assert len(primes) == 100
        assert primes[0] == 2
        assert primes[-1] == 541  # 100th prime

    def test_generate_zero_primes(self):
        """Test edge case of 0 primes."""
        primes = generate_primes(0)
        assert primes == []

    def test_generate_negative_primes(self):
        """Test edge case of negative number."""
        primes = generate_primes(-5)
        assert primes == []


class TestEquilibrium:
    """Tests for equilibrium function."""

    def test_equilibrium_prime_2(self):
        """Test equilibrium for p=2."""
        eq = equilibrium(2)
        assert eq > 0
        assert isinstance(eq, float)

    def test_equilibrium_prime_17(self):
        """Test equilibrium for noetic point p=17."""
        eq = equilibrium(17)
        # exp(π√17/2) / 17^(3/2) ≈ 9.27
        assert 9.0 < eq < 10.0

    def test_equilibrium_increases_with_prime(self):
        """Test that equilibrium generally increases for larger primes."""
        eq_2 = equilibrium(2)
        eq_541 = equilibrium(541)
        assert eq_541 > eq_2


class TestRPsi:
    """Tests for universal radius R_Ψ."""

    def test_R_Psi_positive(self):
        """Test that R_Ψ is always positive."""
        for p in [2, 17, 101, 541]:
            R = R_Psi(p)
            assert R > 0

    def test_R_Psi_scale(self):
        """Test that R_Ψ is scaled correctly."""
        p = 17
        eq = equilibrium(p)
        R = R_Psi(p)
        assert math.isclose(R, SCALE_FACTOR / eq, rel_tol=1e-10)


class TestFrequency:
    """Tests for frequency calculation."""

    def test_frequency_prime_17(self):
        """Test frequency at noetic point p=17."""
        f = frequency(17)
        # f₀(17) ≈ 141.7 Hz (QCAL reference frequency)
        assert 140 < f < 145

    def test_frequency_positive(self):
        """Test all frequencies are positive."""
        for p in [2, 17, 101, 541]:
            f = frequency(p)
            assert f > 0

    def test_frequency_increases_with_equilibrium(self):
        """Test frequency relationship with equilibrium."""
        # Higher equilibrium → lower R_Ψ → higher frequency
        f_2 = frequency(2)
        f_541 = frequency(541)
        assert f_541 > f_2


class TestMidiConversion:
    """Tests for MIDI and note conversion."""

    def test_freq_to_midi_a4(self):
        """Test that 440 Hz maps to MIDI 69."""
        midi = freq_to_midi(A4_FREQ)
        assert math.isclose(midi, 69.0, abs_tol=1e-10)

    def test_freq_to_midi_octave(self):
        """Test octave relationship (doubling frequency = +12 MIDI)."""
        midi_440 = freq_to_midi(440.0)
        midi_880 = freq_to_midi(880.0)
        assert math.isclose(midi_880 - midi_440, 12.0, abs_tol=1e-10)

    def test_midi_to_note_a4(self):
        """Test MIDI 69 is A4."""
        note, octave, cents = midi_to_note(69.0)
        assert note == 'A'
        assert octave == 4
        assert math.isclose(cents, 0.0, abs_tol=1e-10)

    def test_midi_to_note_c4(self):
        """Test MIDI 60 is C4."""
        note, octave, cents = midi_to_note(60.0)
        assert note == 'C'
        assert octave == 4
        assert math.isclose(cents, 0.0, abs_tol=1e-10)


class TestAnalyzePrime:
    """Tests for complete prime analysis."""

    def test_analyze_prime_17(self):
        """Test complete analysis for noetic point p=17."""
        result = analyze_prime(17)
        
        assert result['prime'] == 17
        assert 'equilibrium' in result
        assert 'frequency_hz' in result
        assert 'midi_number' in result
        assert 'note' in result
        assert 'octave' in result
        assert 'cents_deviation' in result
        assert 'note_full' in result

    def test_analyze_prime_all_fields(self):
        """Test that all required fields are present."""
        result = analyze_prime(2)
        expected_fields = [
            'prime', 'equilibrium', 'frequency_hz', 'midi_number',
            'note', 'octave', 'cents_deviation', 'note_full'
        ]
        for field in expected_fields:
            assert field in result


class TestClassifyByOctave:
    """Tests for octave classification."""

    def test_classify_by_octave(self):
        """Test octave classification."""
        data = [
            analyze_prime(2),
            analyze_prime(3),
            analyze_prime(17),
            analyze_prime(541)
        ]
        by_octave = classify_by_octave(data)
        
        assert isinstance(by_octave, dict)
        # All values should be lists
        for octave, primes in by_octave.items():
            assert isinstance(octave, int)
            assert isinstance(primes, list)
            assert len(primes) > 0


class TestSpecialPrimes:
    """Tests for special prime identification."""

    def test_find_special_primes(self):
        """Test special prime identification."""
        primes = generate_primes(100)
        data = [analyze_prime(p) for p in primes]
        special = find_special_primes(data)
        
        # Noetic point should be identified
        assert 'noetic_point' in special
        assert special['noetic_point']['prime'] == 17
        
        # Frequency extremes should be identified
        assert 'lowest_frequency' in special
        assert 'highest_frequency' in special
        
        # Lowest frequency should be a small prime
        assert special['lowest_frequency']['prime'] in [2, 3, 5, 7]
        
        # Highest frequency should be a large prime
        assert special['highest_frequency']['prime'] == 541


class TestQCALConsistency:
    """Tests for QCAL framework consistency."""

    def test_noetic_frequency_141_7(self):
        """Test that p=17 gives approximately 141.7 Hz."""
        f_17 = frequency(17)
        # QCAL reference frequency is 141.7001 Hz
        assert abs(f_17 - 141.7) < 0.5

    def test_constants_defined(self):
        """Test that all physical constants are properly defined."""
        assert C_LIGHT == 299792458
        assert PLANCK_LENGTH == 1.616255e-35
        assert SCALE_FACTOR == 1.931174e41
        assert A4_FREQ == 440.0

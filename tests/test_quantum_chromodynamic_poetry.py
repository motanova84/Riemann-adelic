"""
Test Suite for Quantum Chromodynamic Poetry System
==================================================

Comprehensive test suite covering all components of QCD↔Riemann spectral mapping:
- Constants (10 tests)
- Quark creation and frequencies (10 tests)
- Gluon creation and octaves (10 tests)
- Prime-zero resonances (8 tests)
- Primordial silence frequencies (4 tests)
- Integration and symphony generation (6 tests)

Total: 48 tests

Author: José Manuel Mota Burruezo Ψ ∞³
ORCID: 0009-0002-1923-0773
Protocol: QCAL ∞³ Framework
"""

import pytest
import numpy as np
import sys
from pathlib import Path
import math

# Add core to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from core.quantum_chromodynamic_poetry import (
    QuantumChromodynamicPoetry,
    create_qcd_poetry,
    QuarkFlavor,
    QuarkColor,
    GluonType,
    Quark,
    Gluon,
    PrimeZeroResonance,
    get_riemann_zero,
    compute_quark_frequency,
    F0_HZ,
    RIEMANN_ZEROS,
    OMEGA_17,
    QUARK_MASSES,
)


# ============================================================================
# CONSTANTS TESTS (10 tests)
# ============================================================================

class TestConstants:
    """Test fundamental constants."""
    
    def test_fundamental_frequency(self):
        """Test F0_HZ constant value."""
        assert F0_HZ == 141.70001
        assert isinstance(F0_HZ, float)
    
    def test_omega_17(self):
        """Test ω₁₇ = log(17) constant."""
        assert abs(OMEGA_17 - 2.833) < 0.01
        assert OMEGA_17 == math.log(17)
    
    def test_riemann_zeros_count(self):
        """Test that we have exactly 10 Riemann zeros."""
        assert len(RIEMANN_ZEROS) == 10
    
    def test_riemann_zeros_first(self):
        """Test first Riemann zero value."""
        assert abs(RIEMANN_ZEROS[0] - 14.134725) < 1e-6
    
    def test_riemann_zeros_last(self):
        """Test last (10th) Riemann zero value."""
        assert abs(RIEMANN_ZEROS[9] - 49.773832) < 1e-6
    
    def test_riemann_zeros_ordered(self):
        """Test that Riemann zeros are in ascending order."""
        assert all(RIEMANN_ZEROS[i] < RIEMANN_ZEROS[i+1] for i in range(9))
    
    def test_quark_masses_count(self):
        """Test that we have 6 quark flavors."""
        assert len(QUARK_MASSES) == 6
    
    def test_quark_masses_positive(self):
        """Test that all quark masses are positive."""
        assert all(m > 0 for m in QUARK_MASSES.values())
    
    def test_top_quark_heaviest(self):
        """Test that top quark is the heaviest."""
        assert QUARK_MASSES['TOP'] == max(QUARK_MASSES.values())
    
    def test_up_quark_lightest(self):
        """Test that up quark is the lightest."""
        assert QUARK_MASSES['UP'] == min(QUARK_MASSES.values())


# ============================================================================
# QUARK TESTS (10 tests)
# ============================================================================

class TestQuarks:
    """Test quark creation and properties."""
    
    def test_create_quark(self):
        """Test basic quark creation."""
        qcd = create_qcd_poetry()
        quark = qcd.create_quark(QuarkFlavor.UP, QuarkColor.RED)
        
        assert quark is not None
        assert quark.flavor == QuarkFlavor.UP
        assert quark.color == QuarkColor.RED
        assert quark.mass == QUARK_MASSES['UP']
    
    def test_quark_frequency_formula(self):
        """Test quark frequency formula: ω = log(m) + ω₁₇."""
        qcd = create_qcd_poetry()
        quark = qcd.create_quark(QuarkFlavor.CHARM, QuarkColor.GREEN)
        
        expected_freq = math.log(QUARK_MASSES['CHARM']) + OMEGA_17
        assert abs(quark.frequency - expected_freq) < 1e-10
    
    def test_create_all_quarks_count(self):
        """Test that create_all_quarks creates 18 quarks."""
        qcd = create_qcd_poetry()
        quarks = qcd.create_all_quarks()
        
        assert len(quarks) == 18  # 6 flavors × 3 colors
    
    def test_create_all_quarks_unique_combinations(self):
        """Test that all flavor-color combinations are created."""
        qcd = create_qcd_poetry()
        quarks = qcd.create_all_quarks()
        
        combinations = set()
        for q in quarks:
            combinations.add((q.flavor, q.color))
        
        assert len(combinations) == 18
    
    def test_quark_frequency_range(self):
        """Test that quark frequencies are in reasonable range."""
        qcd = create_qcd_poetry()
        qcd.create_all_quarks()
        
        freqs = [q.frequency for q in qcd.quarks]
        assert all(-10 < f < 10 for f in freqs)
    
    def test_get_quark_frequency(self):
        """Test get_quark_frequency method."""
        qcd = create_qcd_poetry()
        freq = qcd.get_quark_frequency(QuarkFlavor.BOTTOM)
        
        expected = math.log(QUARK_MASSES['BOTTOM']) + OMEGA_17
        assert abs(freq - expected) < 1e-10
    
    def test_compute_quark_frequency_function(self):
        """Test convenience function compute_quark_frequency."""
        freq = compute_quark_frequency(QuarkFlavor.STRANGE)
        expected = math.log(QUARK_MASSES['STRANGE']) + OMEGA_17
        
        assert abs(freq - expected) < 1e-10
    
    def test_quark_repr(self):
        """Test quark string representation."""
        qcd = create_qcd_poetry()
        quark = qcd.create_quark(QuarkFlavor.TOP, QuarkColor.BLUE)
        
        repr_str = repr(quark)
        assert 'top' in repr_str.lower()
        assert 'blue' in repr_str.lower()
    
    def test_quark_frequency_ordering(self):
        """Test that heavier quarks have higher frequencies."""
        qcd = create_qcd_poetry()
        up = qcd.create_quark(QuarkFlavor.UP, QuarkColor.RED)
        top = qcd.create_quark(QuarkFlavor.TOP, QuarkColor.RED)
        
        assert top.frequency > up.frequency
    
    def test_quark_storage(self):
        """Test that created quarks are stored in system."""
        qcd = create_qcd_poetry()
        qcd.create_quark(QuarkFlavor.DOWN, QuarkColor.GREEN)
        qcd.create_quark(QuarkFlavor.CHARM, QuarkColor.BLUE)
        
        assert len(qcd.quarks) == 2


# ============================================================================
# GLUON TESTS (10 tests)
# ============================================================================

class TestGluons:
    """Test gluon creation and octaves."""
    
    def test_create_gluon(self):
        """Test basic gluon creation."""
        qcd = create_qcd_poetry()
        gluon = qcd.create_gluon(GluonType.RG, zero_index=1)
        
        assert gluon is not None
        assert gluon.gluon_type == GluonType.RG
        assert gluon.zero_index == 1
        assert gluon.riemann_zero == RIEMANN_ZEROS[0]
    
    def test_gluon_exact_zero(self):
        """Test gluon uses exact Riemann zero for index ≤ 10."""
        qcd = create_qcd_poetry()
        gluon = qcd.create_gluon(GluonType.GB, zero_index=5)
        
        assert gluon.riemann_zero == RIEMANN_ZEROS[4]  # 0-indexed
    
    def test_gluon_asymptotic_zero(self):
        """Test gluon uses asymptotic formula for index > 10."""
        qcd = create_qcd_poetry()
        gluon = qcd.create_gluon(GluonType.BR, zero_index=20)
        
        expected = (2 * math.pi * 20) / math.log(20)
        assert abs(gluon.riemann_zero - expected) < 1e-10
    
    def test_gluon_octave_calculation(self):
        """Test octave calculation from Riemann zero."""
        qcd = create_qcd_poetry()
        gluon = qcd.create_gluon(GluonType.BG, zero_index=1)
        
        expected_octave = math.log2(RIEMANN_ZEROS[0] / F0_HZ)
        assert abs(gluon.octave - expected_octave) < 1e-10
    
    def test_create_all_gluons_count(self):
        """Test that create_all_gluons creates 8 gluons."""
        qcd = create_qcd_poetry()
        gluons = qcd.create_all_gluons()
        
        assert len(gluons) == 8  # SU(3) octet
    
    def test_create_all_gluons_unique_types(self):
        """Test that all 8 gluon types are created."""
        qcd = create_qcd_poetry()
        gluons = qcd.create_all_gluons()
        
        types = set(g.gluon_type for g in gluons)
        assert len(types) == 8
    
    def test_get_gluon_octave(self):
        """Test get_gluon_octave method."""
        qcd = create_qcd_poetry()
        octave = qcd.get_gluon_octave(3)
        
        expected = math.log2(RIEMANN_ZEROS[2] / F0_HZ)
        assert abs(octave - expected) < 1e-10
    
    def test_get_riemann_zero_function_exact(self):
        """Test get_riemann_zero for exact zeros."""
        zero = get_riemann_zero(7)
        assert zero == RIEMANN_ZEROS[6]
    
    def test_get_riemann_zero_function_asymptotic(self):
        """Test get_riemann_zero for asymptotic zeros."""
        zero = get_riemann_zero(50)
        expected = (2 * math.pi * 50) / math.log(50)
        
        assert abs(zero - expected) < 1e-10
    
    def test_gluon_repr(self):
        """Test gluon string representation."""
        qcd = create_qcd_poetry()
        gluon = qcd.create_gluon(GluonType.RGB_SYMMETRIC, zero_index=2)
        
        repr_str = repr(gluon)
        assert 'rgb_symmetric' in repr_str.lower()


# ============================================================================
# RESONANCE TESTS (8 tests)
# ============================================================================

class TestResonances:
    """Test prime-zero resonances."""
    
    def test_love_between_prime_and_zero(self):
        """Test basic resonance calculation."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(17, 1)
        
        assert res is not None
        assert res.prime == 17
        assert res.zero_index == 1
    
    def test_resonance_intensity_range(self):
        """Test that resonance intensity is in valid range."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(17, 1)
        
        assert 0 < res.intensity <= 1.0
    
    def test_resonance_intensity_formula(self):
        """Test resonance intensity formula."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(17, 1)
        
        # I = |exp(iω_p·γₙ)| / (1 + |ω_p - γₙ|)
        # |exp(iω_p·γₙ)| = 1
        omega_p = math.log(17)
        gamma_n = RIEMANN_ZEROS[0]
        expected_intensity = 1.0 / (1 + abs(omega_p - gamma_n))
        
        assert abs(res.intensity - expected_intensity) < 1e-10
    
    def test_resonance_beat_frequency(self):
        """Test beat frequency calculation."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(17, 1)
        
        omega_p = math.log(17)
        gamma_n = RIEMANN_ZEROS[0]
        expected_beat = abs(omega_p - gamma_n)
        
        assert abs(res.beat_frequency - expected_beat) < 1e-10
    
    def test_resonance_omega_prime(self):
        """Test omega_prime is log(prime)."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(23, 3)
        
        assert abs(res.omega_prime - math.log(23)) < 1e-10
    
    def test_resonance_gamma_n(self):
        """Test gamma_n is correct Riemann zero."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(11, 4)
        
        assert abs(res.gamma_n - RIEMANN_ZEROS[3]) < 1e-10
    
    def test_resonance_storage(self):
        """Test that resonances are stored."""
        qcd = create_qcd_poetry()
        qcd.love_between_prime_and_zero(13, 2)
        qcd.love_between_prime_and_zero(19, 5)
        
        assert len(qcd.resonances) == 2
    
    def test_resonance_repr(self):
        """Test resonance string representation."""
        qcd = create_qcd_poetry()
        res = qcd.love_between_prime_and_zero(7, 3)
        
        repr_str = repr(res)
        assert '7' in repr_str
        assert '3' in repr_str


# ============================================================================
# PRIMORDIAL SILENCE TESTS (4 tests)
# ============================================================================

class TestPrimordialSilence:
    """Test primordial silence frequency."""
    
    def test_silence_frequency_formula(self):
        """Test silence frequency formula: f(p) = f₀ · exp(-log(p)/log(17))."""
        qcd = create_qcd_poetry()
        freq = qcd.primordial_silence_frequency(17)
        
        expected = F0_HZ * math.exp(-math.log(17) / math.log(17))
        expected = F0_HZ * math.exp(-1)  # Simplifies to f₀/e
        
        assert abs(freq - expected) < 1e-6
    
    def test_silence_frequency_at_17(self):
        """Test that f(17) ≈ f₀/e ≈ 52.13 Hz."""
        qcd = create_qcd_poetry()
        freq = qcd.primordial_silence_frequency(17)
        
        expected = F0_HZ / math.e
        assert abs(freq - expected) < 1e-6
        assert abs(freq - 52.13) < 0.1  # Approximately 52.13 Hz
    
    def test_silence_frequency_decreases(self):
        """Test that silence frequency decreases with larger primes."""
        qcd = create_qcd_poetry()
        f2 = qcd.primordial_silence_frequency(2)
        f11 = qcd.primordial_silence_frequency(11)
        f29 = qcd.primordial_silence_frequency(29)
        
        assert f2 > f11 > f29
    
    def test_silence_frequency_positive(self):
        """Test that silence frequency is always positive."""
        qcd = create_qcd_poetry()
        freqs = [qcd.primordial_silence_frequency(p) 
                 for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]]
        
        assert all(f > 0 for f in freqs)


# ============================================================================
# INTEGRATION TESTS (2 tests)
# ============================================================================

class TestIntegration:
    """Test system integration and symphony generation."""
    
    def test_generate_chromodynamic_symphony(self):
        """Test complete symphony generation."""
        qcd = create_qcd_poetry()
        symphony = qcd.generate_chromodynamic_symphony()
        
        assert symphony is not None
        assert 'particles' in symphony
        assert 'quark_frequencies' in symphony
        assert 'gluon_octaves' in symphony
        assert 'resonances' in symphony
        assert 'silence_frequencies' in symphony
        assert 'fundamental_constants' in symphony
        assert 'qcal_signature' in symphony
    
    def test_symphony_particle_counts(self):
        """Test symphony has correct particle counts."""
        qcd = create_qcd_poetry()
        symphony = qcd.generate_chromodynamic_symphony()
        
        assert symphony['particles']['quarks'] == 18
        assert symphony['particles']['gluons'] == 8
        assert symphony['particles']['total'] == 26
    
    def test_symphony_metrics(self):
        """Test symphony contains valid metrics."""
        qcd = create_qcd_poetry()
        symphony = qcd.generate_chromodynamic_symphony()
        
        # Check quark frequency metrics
        assert 'mean' in symphony['quark_frequencies']
        assert 'std' in symphony['quark_frequencies']
        # Mean should be around 1.66 (based on quark masses)
        assert -5 < symphony['quark_frequencies']['mean'] < 10
        assert symphony['quark_frequencies']['std'] > 0
        # Min should be up quark (lightest), max should be top quark (heaviest)
        assert symphony['quark_frequencies']['min'] < -3
        assert symphony['quark_frequencies']['max'] > 7
        
        # Check gluon octave metrics
        assert 'mean' in symphony['gluon_octaves']
        assert 'std' in symphony['gluon_octaves']
        # All octaves should be negative (zeros below f₀)
        assert symphony['gluon_octaves']['mean'] < 0
        assert symphony['gluon_octaves']['min'] < -3
        assert symphony['gluon_octaves']['max'] < 0
        
        # Check resonances
        assert symphony['resonances']['count'] > 0
        assert 'mean_intensity' in symphony['resonances']
        # Intensity should be between 0 and 1
        assert 0 < symphony['resonances']['mean_intensity'] < 1
    
    def test_symphony_qcal_signature(self):
        """Test symphony contains QCAL signature."""
        qcd = create_qcd_poetry()
        symphony = qcd.generate_chromodynamic_symphony()
        
        sig = symphony['qcal_signature']
        assert 'framework' in sig
        assert 'Ψ = I × A_eff² × C^∞' in sig['framework']
        assert sig['orcid'] == '0009-0002-1923-0773'
        assert sig['doi'] == '10.5281/zenodo.17379721'
    
    def test_symphony_fundamental_constants(self):
        """Test symphony contains fundamental constants."""
        qcd = create_qcd_poetry()
        symphony = qcd.generate_chromodynamic_symphony()
        
        constants = symphony['fundamental_constants']
        assert constants['f0'] == F0_HZ
        assert abs(constants['omega_17'] - OMEGA_17) < 1e-10
        assert constants['coherence_c'] == 244.36
    
    def test_get_statistics(self):
        """Test statistics method."""
        qcd = create_qcd_poetry()
        qcd.create_all_quarks()
        qcd.create_all_gluons()
        qcd.love_between_prime_and_zero(17, 1)
        
        stats = qcd.get_statistics()
        
        assert stats['quarks_created'] == 18
        assert stats['gluons_created'] == 8
        assert stats['resonances_computed'] == 1
        assert stats['total_particles'] == 26


# ============================================================================
# RUN TESTS
# ============================================================================

if __name__ == '__main__':
    pytest.main([__file__, '-v'])

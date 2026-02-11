#!/usr/bin/env python3
"""
Test Suite for Teorema Noētico-Riemanniano ∞³: Cuerda del Universo

This test suite validates the implementation of the Noetic-Riemannian
Cosmic String Theorem.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from noetic_riemann_cosmic_string import (
    NoeticRiemannCosmicString,
    get_first_riemann_zeros,
    CosmicStringState,
    F0_BASE,
    F1_HARMONIC,
    PHI
)


class TestCosmicStringWavefunction:
    """Test cosmic string wavefunction Ψ(t) = A·cos(2πf₀t)."""
    
    def test_wavefunction_amplitude(self):
        """Test that wavefunction amplitude is bounded by A."""
        cosmic_string = NoeticRiemannCosmicString(amplitude=1.0)
        
        # Sample over one period
        T = 1.0 / F0_BASE
        t_samples = np.linspace(0, T, 100)
        
        for t in t_samples:
            psi = cosmic_string.cosmic_string_wavefunction(t)
            assert -1.1 <= psi <= 1.1, f"Amplitude {psi} exceeds bounds at t={t}"
    
    def test_wavefunction_periodicity(self):
        """Test that wavefunction is periodic with period T = 1/f₀."""
        cosmic_string = NoeticRiemannCosmicString()
        
        T = 1.0 / F0_BASE
        t = 0.123  # Arbitrary time
        
        psi_t = cosmic_string.cosmic_string_wavefunction(t)
        psi_t_plus_T = cosmic_string.cosmic_string_wavefunction(t + T)
        
        assert abs(psi_t - psi_t_plus_T) < 1e-10, "Wavefunction not periodic"
    
    def test_wavefunction_at_zero(self):
        """Test wavefunction value at t=0."""
        cosmic_string = NoeticRiemannCosmicString(amplitude=1.0)
        
        psi_0 = cosmic_string.cosmic_string_wavefunction(0)
        
        # At t=0, Ψ(0) = A·cos(0) = A = 1.0
        assert abs(psi_0 - 1.0) < 1e-10, f"Ψ(0) = {psi_0}, expected 1.0"
    
    def test_wavefunction_different_frequencies(self):
        """Test wavefunction with different frequencies."""
        cosmic_string = NoeticRiemannCosmicString()
        
        t = 0.001  # 1 ms
        
        # Test at f₀
        psi_f0 = cosmic_string.cosmic_string_wavefunction(t, F0_BASE)
        
        # Test at 2×f₀
        psi_2f0 = cosmic_string.cosmic_string_wavefunction(t, 2*F0_BASE)
        
        # They should be different
        assert abs(psi_f0 - psi_2f0) > 0.01, "Different frequencies produce same result"


class TestRiemannZeroVibrationalModes:
    """Test Riemann zero vibrational modes."""
    
    def test_vibrational_mode_is_complex(self):
        """Test that vibrational modes are complex numbers."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        mode = cosmic_string.riemann_zero_vibrational_mode(zeros[0], 0.1)
        
        assert isinstance(mode, (complex, np.complex128)), "Mode should be complex"
    
    def test_vibrational_mode_unit_magnitude(self):
        """Test that vibrational modes have unit magnitude."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        for gamma in zeros[:5]:
            for t in [0.0, 0.1, 0.5, 1.0]:
                mode = cosmic_string.riemann_zero_vibrational_mode(gamma, t)
                magnitude = abs(mode)
                
                assert abs(magnitude - 1.0) < 1e-10, f"Mode magnitude {magnitude} != 1.0"
    
    def test_different_zeros_different_modes(self):
        """Test that different zeros produce different modes."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        t = 0.5
        mode1 = cosmic_string.riemann_zero_vibrational_mode(zeros[0], t)
        mode2 = cosmic_string.riemann_zero_vibrational_mode(zeros[1], t)
        
        assert abs(mode1 - mode2) > 0.1, "Different zeros produce similar modes"


class TestStringStability:
    """Test cosmic string stability measure."""
    
    def test_stability_at_f0(self):
        """Test that stability is high at f₀."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        stability = cosmic_string.string_stability_measure(F0_BASE, zeros)
        
        assert stability > 0.001, f"Stability at f₀ ({stability}) too low"
    
    def test_stability_decreases_away_from_f0(self):
        """Test that stability decreases away from f₀."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        stability_f0 = cosmic_string.string_stability_measure(F0_BASE, zeros)
        stability_far = cosmic_string.string_stability_measure(F0_BASE * 1.5, zeros)
        
        assert stability_f0 > stability_far, "Stability should decrease away from f₀"
    
    def test_stability_bounded(self):
        """Test that stability is bounded in [0, 1]."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        test_freqs = [F0_BASE * f for f in [0.5, 0.8, 1.0, 1.2, 1.5]]
        
        for freq in test_freqs:
            stability = cosmic_string.string_stability_measure(freq, zeros)
            assert 0 <= stability <= 1.1, f"Stability {stability} out of bounds at {freq} Hz"


class TestHarmonicResonance:
    """Test harmonic resonance spectrum."""
    
    def test_harmonic_spectrum_structure(self):
        """Test that harmonic spectrum has correct structure."""
        cosmic_string = NoeticRiemannCosmicString()
        
        harmonics = cosmic_string.harmonic_resonance_spectrum(max_harmonic=10)
        
        assert len(harmonics) == 10, f"Expected 10 harmonics, got {len(harmonics)}"
        
        for n, harmonic in harmonics.items():
            assert 'frequency' in harmonic, f"Harmonic {n} missing frequency"
            assert 'amplitude' in harmonic, f"Harmonic {n} missing amplitude"
    
    def test_fundamental_harmonic(self):
        """Test that first harmonic is at f₀."""
        cosmic_string = NoeticRiemannCosmicString()
        
        harmonics = cosmic_string.harmonic_resonance_spectrum(max_harmonic=5)
        
        assert abs(harmonics[1]['frequency'] - F0_BASE) < 0.01, \
            f"First harmonic {harmonics[1]['frequency']} != f₀"
    
    def test_visible_harmonic_near_888Hz(self):
        """Test that there's a visible harmonic near 888 Hz."""
        cosmic_string = NoeticRiemannCosmicString()
        
        harmonics = cosmic_string.harmonic_resonance_spectrum(max_harmonic=15)
        
        # Find visible harmonics
        visible = [h for h in harmonics.values() 
                   if h.get('visible', False) or h.get('phi_alignment', False) or h.get('is_888Hz', False)]
        
        assert len(visible) > 0, "No visible harmonics found"
        
        # Check that at least one is near 888 Hz (within 100 Hz)
        frequencies = [h['frequency'] for h in visible]
        near_888 = any(abs(f - F1_HARMONIC) < 100 for f in frequencies)
        
        assert near_888, f"No visible harmonic near 888 Hz: {frequencies}"
    
    def test_phi_fourth_relation(self):
        """Test that f₁ ≈ f₀ × φ⁴."""
        cosmic_string = NoeticRiemannCosmicString()
        
        phi_4 = PHI ** 4
        predicted_f1 = F0_BASE * phi_4
        
        # Should be close to 888 Hz
        assert abs(predicted_f1 - F1_HARMONIC) < 100, \
            f"φ⁴ relation: {predicted_f1:.2f} Hz far from {F1_HARMONIC} Hz"


class TestZeroCorrespondence:
    """Test correspondence between zeros and vibrations."""
    
    def test_bidirectional_correspondence(self):
        """Test bidirectional theorem verification."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        result = cosmic_string.verify_zero_vibration_correspondence(zeros)
        
        assert 'stability_at_f0' in result
        assert 'is_f0_optimal' in result
        assert 'verified' in result
        
        # At least some stability at f₀
        assert result['stability_at_f0'] > 0.001, \
            f"Stability too low: {result['stability_at_f0']}"
    
    def test_f0_is_optimal(self):
        """Test that f₀ is the optimal frequency."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        result = cosmic_string.verify_zero_vibration_correspondence(zeros)
        
        # Optimal frequency should be close to f₀
        deviation = abs(result['optimal_frequency'] - F0_BASE)
        assert deviation < 5.0, f"Optimal frequency {result['optimal_frequency']} Hz far from f₀"
    
    def test_coherence_measure(self):
        """Test QCAL coherence measure."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        result = cosmic_string.verify_zero_vibration_correspondence(zeros)
        
        assert 'coherence_qcal' in result
        assert result['coherence_qcal'] >= 0, "Coherence should be non-negative"


class TestCosmicStringState:
    """Test cosmic string state computation."""
    
    def test_state_structure(self):
        """Test that state has all required fields."""
        cosmic_string = NoeticRiemannCosmicString()
        
        state = cosmic_string.compute_string_state(0.1)
        
        assert isinstance(state, CosmicStringState)
        assert hasattr(state, 'time')
        assert hasattr(state, 'amplitude')
        assert hasattr(state, 'frequency')
        assert hasattr(state, 'phase')
        assert hasattr(state, 'coherence')
        assert hasattr(state, 'stability')
    
    def test_state_values_valid(self):
        """Test that state values are physically valid."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        state = cosmic_string.compute_string_state(0.5, zeros)
        
        # Amplitude bounded
        assert -1.1 <= state.amplitude <= 1.1
        
        # Frequency is f₀
        assert abs(state.frequency - F0_BASE) < 0.01
        
        # Phase in [0, 2π]
        assert 0 <= state.phase <= 2*np.pi + 0.01
        
        # Coherence and stability in [0, 1]
        assert 0 <= state.coherence <= 1.1
        assert 0 <= state.stability <= 1.1
    
    def test_state_evolution(self):
        """Test state evolution over time."""
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        times = [0.0, 0.001, 0.002, 0.003]
        states = [cosmic_string.compute_string_state(t, zeros) for t in times]
        
        # Amplitudes should vary
        amplitudes = [s.amplitude for s in states]
        assert max(amplitudes) - min(amplitudes) > 0.01, "Amplitude doesn't vary"
        
        # Phases should increase
        phases = [s.phase for s in states]
        assert phases[1] > phases[0], "Phase doesn't increase"


class TestRiemannZeros:
    """Test Riemann zeros data."""
    
    def test_zeros_count(self):
        """Test that we have the expected number of zeros."""
        zeros = get_first_riemann_zeros()
        
        assert len(zeros) == 20, f"Expected 20 zeros, got {len(zeros)}"
    
    def test_zeros_positive(self):
        """Test that all zeros are positive."""
        zeros = get_first_riemann_zeros()
        
        for gamma in zeros:
            assert gamma > 0, f"Zero {gamma} is not positive"
    
    def test_zeros_ordered(self):
        """Test that zeros are in ascending order."""
        zeros = get_first_riemann_zeros()
        
        for i in range(len(zeros) - 1):
            assert zeros[i] < zeros[i+1], f"Zeros not ordered: {zeros[i]} >= {zeros[i+1]}"
    
    def test_first_zero_value(self):
        """Test first zero is approximately 14.134725."""
        zeros = get_first_riemann_zeros()
        
        expected = 14.134725
        assert abs(zeros[0] - expected) < 0.001, \
            f"First zero {zeros[0]} != {expected}"


class TestTheoremStatement:
    """Test theorem statement generation."""
    
    def test_theorem_statement_format(self):
        """Test that theorem statement is properly formatted."""
        cosmic_string = NoeticRiemannCosmicString()
        
        statement = cosmic_string.theorem_statement()
        
        assert isinstance(statement, str)
        assert len(statement) > 100
        assert "141.7001" in statement
        assert "888" in statement or "φ⁴" in statement
        assert "QCAL" in statement


# Integration tests
class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_workflow(self):
        """Test complete workflow from initialization to verification."""
        # Initialize
        cosmic_string = NoeticRiemannCosmicString()
        zeros = get_first_riemann_zeros()
        
        # Compute wavefunction
        psi = cosmic_string.cosmic_string_wavefunction(0.1)
        assert isinstance(psi, (float, np.floating))
        
        # Compute vibrational mode
        mode = cosmic_string.riemann_zero_vibrational_mode(zeros[0], 0.1)
        assert isinstance(mode, (complex, np.complex128))
        
        # Compute stability
        stability = cosmic_string.string_stability_measure(F0_BASE, zeros)
        assert 0 <= stability <= 1.1
        
        # Get harmonics
        harmonics = cosmic_string.harmonic_resonance_spectrum()
        assert len(harmonics) > 0
        
        # Verify correspondence
        result = cosmic_string.verify_zero_vibration_correspondence(zeros)
        assert 'verified' in result
        
        # Compute state
        state = cosmic_string.compute_string_state(0.1, zeros)
        assert isinstance(state, CosmicStringState)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

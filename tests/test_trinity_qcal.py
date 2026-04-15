#!/usr/bin/env python3
"""
Test Suite for Trinity_QCAL Operator
====================================

Tests the Trinity_QCAL formula that interprets the Riemann Hypothesis
as a quantum coherence condition.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
import sys
import importlib.util
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

# Import Trinity_QCAL operator directly to avoid operators/__init__ side effects
trinity_path = repo_root / 'operators' / 'trinity_qcal.py'
spec = importlib.util.spec_from_file_location("trinity_qcal", trinity_path)
trinity_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(trinity_module)

compute_complex_amplitude = trinity_module.compute_complex_amplitude
compute_entropy_gradient = trinity_module.compute_entropy_gradient
compute_trinity_qcal = trinity_module.compute_trinity_qcal
validate_trinity_for_critical_line = trinity_module.validate_trinity_for_critical_line
compute_trinity_with_excited_modes = trinity_module.compute_trinity_with_excited_modes

# Import constants
try:
    from qcal.constants import (
        F0,
        F_MANIFESTATION,
        GAMMA_QCAL_FASE,
        RIEMANN_ZEROS_5,
        RIEMANN_RENORM_SCALE,
        S_OPTIMAL,
    )
    CONSTANTS_AVAILABLE = True
except ImportError:
    CONSTANTS_AVAILABLE = False
    # Fallback values
    F0 = 141.7001
    F_MANIFESTATION = 888.0
    GAMMA_QCAL_FASE = 2.0 * np.pi * F0 / F_MANIFESTATION
    RIEMANN_ZEROS_5 = np.array([14.134725142, 21.022039639, 25.010857580,
                                  30.424876126, 32.935061588])
    RIEMANN_RENORM_SCALE = 36.1236
    S_OPTIMAL = 1.0


class TestComplexAmplitude:
    """Tests for complex amplitude computation ℰ_{s,φ}."""
    
    def test_amplitude_magnitude_above_one(self):
        """Complex amplitude magnitude should be slightly > Ψ due to γ_QCAL."""
        psi = 0.888
        E = compute_complex_amplitude(psi)
        
        # |E| should be slightly larger than Ψ
        assert abs(E) > psi
        # But not too much larger
        assert abs(E) < psi * 1.2
    
    def test_amplitude_phase_matches_gamma_qcal(self):
        """Phase of complex amplitude should equal γ_QCAL."""
        psi = 0.888
        E = compute_complex_amplitude(psi, gamma_qcal=GAMMA_QCAL_FASE)
        
        phase = np.angle(E)
        assert np.isclose(phase, GAMMA_QCAL_FASE, rtol=1e-6)
    
    def test_amplitude_scales_with_psi(self):
        """Complex amplitude should scale linearly with Ψ."""
        psi1 = 0.5
        psi2 = 1.0
        
        E1 = compute_complex_amplitude(psi1)
        E2 = compute_complex_amplitude(psi2)
        
        # Ratio of magnitudes should equal ratio of psi values
        ratio = abs(E2) / abs(E1)
        expected_ratio = psi2 / psi1
        assert np.isclose(ratio, expected_ratio, rtol=1e-6)
    
    def test_amplitude_formula_correctness(self):
        """Verify E = γ_QCAL · exp(i·γ_QCAL) · Ψ."""
        psi = 0.888
        gamma = GAMMA_QCAL_FASE
        
        E_computed = compute_complex_amplitude(psi, gamma)
        E_expected = gamma * np.exp(1j * gamma) * psi
        
        assert np.isclose(E_computed, E_expected)


class TestEntropyGradient:
    """Tests for entropy gradient ∇S(γ_n) computation."""
    
    def test_entropy_gradient_basic(self):
        """Entropy gradient should be computed correctly."""
        gamma_n = RIEMANN_ZEROS_5[:3]  # Use first 3 zeros
        grad_S = compute_entropy_gradient(gamma_n)
        
        # Should be a real number
        assert isinstance(grad_S, (int, float))
        assert not np.isnan(grad_S)
        assert not np.isinf(grad_S)
    
    def test_entropy_with_custom_amplitudes(self):
        """Entropy gradient with custom mode amplitudes."""
        gamma_n = RIEMANN_ZEROS_5[:3]
        amplitudes = np.array([0.5, 0.3, 0.2])
        
        grad_S = compute_entropy_gradient(gamma_n, mode_amplitudes=amplitudes)
        
        assert isinstance(grad_S, (int, float))
    
    def test_entropy_normalization(self):
        """Mode amplitudes should be normalized automatically."""
        gamma_n = RIEMANN_ZEROS_5[:3]
        # Unnormalized amplitudes
        amplitudes = np.array([1.0, 2.0, 3.0])
        
        # Should not raise error, automatically normalized
        grad_S = compute_entropy_gradient(gamma_n, mode_amplitudes=amplitudes)
        assert isinstance(grad_S, (int, float))
    
    def test_entropy_increases_with_more_modes(self):
        """Entropy should change when more modes are included."""
        gamma_n_small = RIEMANN_ZEROS_5[:2]
        gamma_n_large = RIEMANN_ZEROS_5[:5]
        
        grad_S_small = compute_entropy_gradient(gamma_n_small)
        grad_S_large = compute_entropy_gradient(gamma_n_large)
        
        # They should be different
        assert grad_S_small != grad_S_large


class TestTrinityQCAL:
    """Tests for Trinity_QCAL formula computation."""
    
    def test_trinity_basic_computation(self):
        """Trinity_QCAL should compute without errors."""
        psi = 0.888
        result = compute_trinity_qcal(psi)
        
        assert 'trinity_qcal' in result
        assert isinstance(result['trinity_qcal'], (int, float))
        assert not np.isnan(result['trinity_qcal'])
    
    def test_trinity_returns_all_components(self):
        """Result should contain all expected components."""
        psi = 0.888
        result = compute_trinity_qcal(psi)
        
        required_keys = [
            'trinity_qcal',
            'E_amplitude',
            'E_magnitude_sq',
            'E_phase',
            'grad_S',
            'phase_sync_terms',
            'psi',
            'gamma_qcal',
            'rh_condition_satisfied',
            'coherence_level',
        ]
        
        for key in required_keys:
            assert key in result, f"Missing key: {key}"
    
    def test_trinity_with_canonical_psi(self):
        """Test with canonical coherence Ψ = 0.888."""
        result = compute_trinity_qcal(psi=0.888)
        
        # Should have acceptable coherence
        assert result['coherence_level'] in ['ACCEPTABLE', 'GOOD', 'EXCELLENT']
        assert result['psi_above_threshold'] is True
    
    def test_trinity_with_excellent_psi(self):
        """Test with excellent coherence Ψ = 0.999."""
        result = compute_trinity_qcal(psi=0.999)
        
        assert result['coherence_level'] == 'EXCELLENT'
        assert result['psi_above_threshold'] is True
    
    def test_trinity_with_poor_psi(self):
        """Test with poor coherence Ψ = 0.5."""
        result = compute_trinity_qcal(psi=0.5)
        
        assert result['coherence_level'] == 'POOR'
        # Below acceptable threshold
        assert result['psi_above_threshold'] is False
    
    def test_trinity_phase_synchronization(self):
        """Phase synchronization terms should be cosines in [-1, 1]."""
        result = compute_trinity_qcal(psi=0.888)
        
        phase_terms = np.array(result['phase_sync_terms'])
        
        # All cosine values should be in [-1, 1]
        assert np.all(phase_terms >= -1.0)
        assert np.all(phase_terms <= 1.0)
    
    def test_trinity_different_zero_counts(self):
        """Trinity should work with different numbers of zeros."""
        for n_zeros in [1, 2, 3, 5]:
            gamma_n = RIEMANN_ZEROS_5[:n_zeros]
            result = compute_trinity_qcal(psi=0.888, gamma_n=gamma_n)
            
            assert isinstance(result['trinity_qcal'], (int, float))
            assert len(result['phase_sync_terms']) == n_zeros


class TestCriticalLineValidation:
    """Tests for critical line validation."""
    
    def test_validation_basic(self):
        """Critical line validation should run without errors."""
        result = validate_trinity_for_critical_line(num_zeros=3, psi=0.888)
        
        assert 'num_zeros' in result
        assert 'trinity_qcal' in result
        assert 'all_zeros_coherent' in result
    
    def test_validation_with_all_zeros(self):
        """Validation with all available zeros."""
        result = validate_trinity_for_critical_line(num_zeros=5, psi=0.888)
        
        assert result['num_zeros'] == 5
        assert len(result['gamma_n']) == 5
    
    def test_validation_gamma_n_values(self):
        """Validation should use correct gamma_n values."""
        result = validate_trinity_for_critical_line(num_zeros=3, psi=0.888)
        
        gamma_n = np.array(result['gamma_n'])
        expected = RIEMANN_ZEROS_5[:3]
        
        np.testing.assert_array_almost_equal(gamma_n, expected)
    
    def test_validation_coherence_levels(self):
        """Test validation with different coherence levels."""
        for psi, expected_level in [(0.888, 'ACCEPTABLE'), 
                                     (0.95, 'GOOD'),
                                     (0.999, 'EXCELLENT')]:
            result = validate_trinity_for_critical_line(num_zeros=3, psi=psi)
            assert result['coherence_level'] == expected_level
    
    def test_coherence_level_boundaries(self):
        """Test coherence level classification at boundary values."""
        # Test boundary conditions
        test_cases = [
            (0.85, 'ACCEPTABLE'),   # Exactly at ACCEPTABLE threshold
            (0.849, 'POOR'),        # Just below ACCEPTABLE
            (0.95, 'GOOD'),         # Exactly at GOOD threshold
            (0.949, 'ACCEPTABLE'),  # Just below GOOD
            (0.999, 'EXCELLENT'),   # Exactly at EXCELLENT threshold
            (0.998, 'GOOD'),        # Just below EXCELLENT
        ]
        
        for psi, expected_level in test_cases:
            result = validate_trinity_for_critical_line(num_zeros=3, psi=psi)
            assert result['coherence_level'] == expected_level, \
                f"Failed for psi={psi}: expected {expected_level}, got {result['coherence_level']}"


class TestMathematicalProperties:
    """Tests for mathematical properties of Trinity_QCAL."""
    
    def test_amplitude_squared_formula(self):
        """Test |ℰ_{s,φ}|² = (γ_QCAL)² · Ψ²."""
        psi = 0.888
        gamma = GAMMA_QCAL_FASE
        
        E = compute_complex_amplitude(psi, gamma)
        E_mag_sq = abs(E) ** 2
        
        expected = (gamma ** 2) * (psi ** 2)
        assert np.isclose(E_mag_sq, expected, rtol=1e-6)
    
    def test_entropy_gradient_bounds(self):
        """Entropy gradient should be bounded for physical zeros."""
        gamma_n = RIEMANN_ZEROS_5
        grad_S = compute_entropy_gradient(gamma_n)
        
        # Should be a reasonable value (not extremely large)
        assert abs(grad_S) < 100.0
    
    def test_trinity_continuity_in_psi(self):
        """Trinity_QCAL should be continuous in Ψ."""
        psi_values = np.linspace(0.8, 1.0, 10)
        trinity_values = []
        
        for psi in psi_values:
            result = compute_trinity_qcal(psi)
            trinity_values.append(result['trinity_qcal'])
        
        # Check no discontinuous jumps
        diffs = np.diff(trinity_values)
        # Differences should be small and bounded
        assert np.all(np.abs(diffs) < 1.0)


class TestConstants:
    """Tests for QCAL constants used in Trinity_QCAL."""
    
    @pytest.mark.skipif(not CONSTANTS_AVAILABLE, 
                       reason="qcal.constants not available")
    def test_gamma_qcal_value(self):
        """γ_QCAL should equal 2π · f₀ / f₈₈₈."""
        expected = 2.0 * np.pi * F0 / F_MANIFESTATION
        assert np.isclose(GAMMA_QCAL_FASE, expected, rtol=1e-9)
    
    @pytest.mark.skipif(not CONSTANTS_AVAILABLE,
                       reason="qcal.constants not available")
    def test_manifestation_frequency(self):
        """Manifestation frequency should be 888 Hz."""
        assert F_MANIFESTATION == 888.0
    
    @pytest.mark.skipif(not CONSTANTS_AVAILABLE,
                       reason="qcal.constants not available")
    def test_riemann_zeros_count(self):
        """Should have 5 Riemann zeros available."""
        assert len(RIEMANN_ZEROS_5) == 5
    
    @pytest.mark.skipif(not CONSTANTS_AVAILABLE,
                       reason="qcal.constants not available")
    def test_riemann_zeros_ordering(self):
        """Riemann zeros should be in ascending order."""
        zeros = RIEMANN_ZEROS_5
        assert np.all(zeros[:-1] < zeros[1:])


@pytest.mark.slow
class TestNumericalStability:
    """Tests for numerical stability of Trinity_QCAL computations."""
    
    def test_stability_with_small_psi(self):
        """Trinity should be stable for small Ψ values."""
        for psi in [0.01, 0.1, 0.5]:
            result = compute_trinity_qcal(psi)
            assert not np.isnan(result['trinity_qcal'])
            assert not np.isinf(result['trinity_qcal'])
    
    def test_stability_with_large_psi(self):
        """Trinity should be stable for Ψ near 1."""
        for psi in [0.99, 0.999, 0.9999]:
            result = compute_trinity_qcal(psi)
            assert not np.isnan(result['trinity_qcal'])
            assert not np.isinf(result['trinity_qcal'])
    
    def test_stability_with_many_zeros(self):
        """Trinity should be stable with varying numbers of zeros."""
        for n in range(1, 6):
            gamma_n = RIEMANN_ZEROS_5[:n]
            result = compute_trinity_qcal(psi=0.888, gamma_n=gamma_n)
            assert not np.isnan(result['trinity_qcal'])


class TestTrinityWithExcitedModes:
    """Tests for compute_trinity_with_excited_modes()."""

    def _make_excited_modes(self, n: int = 5) -> np.ndarray:
        """Simulate phase-modulated eigenvalues in Hz (as RiemannSpectralHamiltonian produces)."""
        # Simplified γ̃ₙ = γₙ * renorm_scale + f0 * sin(gamma_qcal + theta)
        gamma_n = RIEMANN_ZEROS_5[:n]
        renorm = RIEMANN_RENORM_SCALE if CONSTANTS_AVAILABLE else 36.1236
        f0 = F0 if CONSTANTS_AVAILABLE else 141.7001
        return gamma_n * renorm + f0 * np.sin(GAMMA_QCAL_FASE + 0.1)

    def test_returns_expected_keys(self):
        """Result dict should contain the standard Trinity keys plus excited_modes metadata."""
        gamma_tilde = self._make_excited_modes()
        result = compute_trinity_with_excited_modes(gamma_tilde_n=gamma_tilde, psi=0.888)

        for key in ('trinity_qcal', 'E_magnitude_sq', 'E_phase', 'grad_S',
                    'rh_condition_satisfied', 'coherence_level', 'excited_modes'):
            assert key in result, f"Missing key: {key}"

    def test_excited_modes_metadata(self):
        """Excited modes metadata should reflect the input array."""
        gamma_tilde = self._make_excited_modes(n=3)
        result = compute_trinity_with_excited_modes(gamma_tilde_n=gamma_tilde, psi=0.888)

        assert result['excited_modes']['num_modes'] == 3
        assert result['excited_modes']['mode_type'] == 'phase_modulated'

    def test_no_double_renormalization(self):
        """Entropy gradient should NOT re-renormalize when renorm_scale=1.0 is used."""
        # With renorm_scale=1.0, grad_S uses the Hz values directly divided by F0.
        gamma_tilde = self._make_excited_modes()
        result = compute_trinity_with_excited_modes(gamma_tilde_n=gamma_tilde, psi=0.888)

        # Manually compute expected grad_S (renorm_scale=1.0 → gamma_n_renorm = gamma_tilde)
        f0 = F0 if CONSTANTS_AVAILABLE else 141.7001
        s_opt = S_OPTIMAL if CONSTANTS_AVAILABLE else 1.0
        N = len(gamma_tilde)
        weights = np.ones(N) / N
        expected_grad_S = s_opt - np.sum(weights * (gamma_tilde / f0))
        assert np.isclose(result['grad_S'], expected_grad_S, rtol=1e-6)

    def test_numerical_stability(self):
        """Result should be finite for typical excited mode inputs."""
        gamma_tilde = self._make_excited_modes()
        result = compute_trinity_with_excited_modes(gamma_tilde_n=gamma_tilde, psi=0.888)

        assert not np.isnan(result['trinity_qcal'])
        assert not np.isinf(result['trinity_qcal'])

    def test_with_riemann_spectral_hamiltonian(self):
        """End-to-end test: integrate with RiemannSpectralHamiltonian if available."""
        try:
            ham_path = Path(__file__).parent.parent / 'operators' / 'riemann_spectral_hamiltonian.py'
            spec = importlib.util.spec_from_file_location("riemann_spectral_hamiltonian", ham_path)
            ham_module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(ham_module)
            RiemannSpectralHamiltonian = ham_module.RiemannSpectralHamiltonian
        except Exception:
            pytest.skip("RiemannSpectralHamiltonian not available")

        hamiltonian = RiemannSpectralHamiltonian()
        ham_result = hamiltonian.compute_excited_modes(theta=0.1)
        result = compute_trinity_with_excited_modes(
            gamma_tilde_n=ham_result.eigenvalues_modulated,
            psi=0.888,
        )

        assert 'trinity_qcal' in result
        assert not np.isnan(result['trinity_qcal'])
        assert result['excited_modes']['num_modes'] == len(ham_result.eigenvalues_modulated)


if __name__ == '__main__':
    """Run tests with pytest."""
    pytest.main([__file__, '-v', '--tb=short'])

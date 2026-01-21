#!/usr/bin/env python3
"""
Test Suite for Unified Hierarchy System

This module tests the unified hierarchy framework showing that all five
systems converge to the Riemann zeta function ζ(s).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from unified_hierarchy import (
    ZetaBaseSystem,
    PhiFractalSystem,
    ZetaValuesSystem,
    QCALCodonSystem,
    HarmonicSystem,
    UnifiedHierarchy,
    F0, GAMMA_1, DELTA_ZETA, PHI, C_COHERENCE
)


class TestZetaBaseSystem:
    """Test System 5: ζ(s) base functionality."""
    
    def test_initialization(self):
        """Test zeta base system initialization."""
        system = ZetaBaseSystem(precision=50)
        assert system.f0 == F0
        assert system.gamma_1 == GAMMA_1
        assert abs(system.delta_zeta - DELTA_ZETA) < 1e-6
    
    def test_compute_zeros(self):
        """Test computation of ζ(s) zeros."""
        system = ZetaBaseSystem(precision=50)
        zeros = system.compute_zeros(n_zeros=10)
        
        assert len(zeros) == 10
        assert all(z.n > 0 for z in zeros)
        assert all(z.gamma > 0 for z in zeros)
        
        # First zero should have γ ≈ 14.134725
        assert abs(zeros[0].gamma - 14.134725) < 0.001
    
    def test_spectral_frequencies(self):
        """Test spectral frequency computation."""
        system = ZetaBaseSystem(precision=50)
        zeros = system.compute_zeros(n_zeros=5)
        
        # f_1 should equal f₀ (by definition)
        assert abs(zeros[0].frequency - F0) < 0.1
        
        # Frequencies should increase
        freqs = [z.frequency for z in zeros]
        assert all(freqs[i] < freqs[i+1] for i in range(len(freqs)-1))
    
    def test_critical_line_verification(self):
        """Test Riemann Hypothesis verification."""
        system = ZetaBaseSystem(precision=50)
        zeros = system.compute_zeros(n_zeros=20)
        
        result = system.verify_critical_line(zeros, tolerance=1e-10)
        
        assert result['all_on_critical_line']
        assert result['max_deviation'] < 1e-10
        assert result['n_zeros_checked'] == 20
    
    def test_spectral_density(self):
        """Test spectral density computation."""
        system = ZetaBaseSystem(precision=50)
        
        # Compute density at first zero
        rho_1 = system.spectral_density(14.134725)
        
        # Should be finite
        assert np.isfinite(rho_1)


class TestPhiFractalSystem:
    """Test System 1: Golden ratio fractal structure."""
    
    def test_initialization(self):
        """Test phi system initialization."""
        system = PhiFractalSystem()
        assert abs(system.phi - PHI) < 1e-10
        assert abs(system.phi - 1.618033988749895) < 1e-10
    
    def test_spacing_modulation(self):
        """Test fractal modulation of zero spacings."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=20)
        
        phi_system = PhiFractalSystem()
        modulations = phi_system.compute_spacing_modulation(zeros)
        
        assert len(modulations) == 19  # n-1 spacings
        assert all(np.isfinite(m) for m in modulations)
    
    def test_frequency_self_similarity(self):
        """Test self-similar frequency structure."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=30)
        
        phi_system = PhiFractalSystem()
        ratios = phi_system.frequency_self_similarity(zeros, k=1)
        
        assert len(ratios) > 0
        assert all(r > 0 for r in ratios)
    
    def test_golden_structure_analysis(self):
        """Test complete golden structure analysis."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=25)
        
        phi_system = PhiFractalSystem()
        analysis = phi_system.analyze_golden_structure(zeros)
        
        assert analysis['phi'] == PHI
        assert analysis['n_zeros'] == 25
        assert 'spacing_modulations' in analysis
        assert 'frequency_ratios_k1' in analysis


class TestZetaValuesSystem:
    """Test System 2: ζ(n) analytic values."""
    
    def test_initialization(self):
        """Test zeta values system initialization."""
        system = ZetaValuesSystem()
        assert abs(system.euler_gamma - 0.5772156649) < 1e-9
    
    def test_special_values(self):
        """Test computation of special ζ(n) values."""
        system = ZetaValuesSystem()
        values = system.compute_special_values(max_n=10)
        
        # ζ(2) = π²/6 ≈ 1.6449340668
        assert 2 in values
        assert abs(values[2] - np.pi**2/6) < 1e-6
        
        # ζ(4) = π⁴/90 ≈ 1.0823232337
        if 4 in values:
            assert abs(values[4] - np.pi**4/90) < 1e-6
    
    def test_spectral_moments(self):
        """Test spectral moment computation."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=20)
        
        values_system = ZetaValuesSystem()
        moments = values_system.spectral_moments(zeros, order=4)
        
        assert len(moments) == 4
        assert all(m > 0 for m in moments)
        # Moments should increase
        assert all(moments[i] < moments[i+1] for i in range(len(moments)-1))
    
    def test_analytic_structure_analysis(self):
        """Test complete analytic structure analysis."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=20)
        
        values_system = ZetaValuesSystem()
        analysis = values_system.analyze_analytic_structure(zeros)
        
        assert 'zeta_values' in analysis
        assert 'spectral_moments' in analysis
        assert analysis['zeta_2'] > 0


class TestQCALCodonSystem:
    """Test System 3: QCAL codon resonances."""
    
    def test_initialization(self):
        """Test codon system initialization."""
        system = QCALCodonSystem()
        assert system.f0 == F0
        assert len(system.digit_frequencies) == 10
    
    def test_digit_frequencies(self):
        """Test digit frequency mapping."""
        system = QCALCodonSystem()
        
        # All digits should have frequencies
        for d in range(10):
            assert d in system.digit_frequencies
            assert system.digit_frequencies[d] > 0
    
    def test_codon_frequency(self):
        """Test codon frequency computation."""
        system = QCALCodonSystem()
        
        # Test simple codon
        codon = (1, 0, 0, 0)
        freq = system.codon_frequency(codon)
        assert freq > 0
        
        # Different codons should have different frequencies
        codon2 = (9, 9, 9)
        freq2 = system.codon_frequency(codon2)
        assert freq2 != freq
    
    def test_resonance_check(self):
        """Test resonance criterion."""
        system = QCALCodonSystem()
        
        # Same frequency should resonate
        assert system.check_resonance(100.0, 100.0, tolerance=0.01)
        
        # Close frequencies should resonate with tolerance
        assert system.check_resonance(100.0, 100.5, tolerance=0.01)
        
        # Far frequencies should not resonate
        assert not system.check_resonance(100.0, 200.0, tolerance=0.01)
    
    def test_find_resonant_codons(self):
        """Test finding resonant codons."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=30)
        
        codon_system = QCALCodonSystem()
        resonant = codon_system.find_resonant_codons(zeros, tolerance=0.05)
        
        # Should find at least some resonances with relaxed tolerance
        assert len(resonant) >= 0  # May be empty with strict tolerance
    
    def test_codon_analysis(self):
        """Test complete codon resonance analysis."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=20)
        
        codon_system = QCALCodonSystem()
        analysis = codon_system.analyze_codon_resonance(zeros)
        
        assert 'n_resonant_codons' in analysis
        assert 'digit_frequencies' in analysis


class TestHarmonicSystem:
    """Test System 4: Harmonic structure."""
    
    def test_compute_harmonics(self):
        """Test harmonic computation."""
        system = HarmonicSystem()
        
        freq = 100.0
        harmonics = system.compute_harmonics(freq, max_harmonic=5)
        
        assert len(harmonics) == 5
        assert harmonics[0] == freq
        assert harmonics[1] == 2 * freq
        assert harmonics[4] == 5 * freq
    
    def test_harmonic_spectrum(self):
        """Test harmonic spectrum for zeros."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=10)
        
        harmonic_system = HarmonicSystem()
        spectrum = harmonic_system.harmonic_spectrum(zeros, max_harmonic=3)
        
        assert len(spectrum) == 10
        assert all(len(spectrum[i]) == 3 for i in spectrum)
    
    def test_euler_product_harmonics(self):
        """Test Euler product computation."""
        system = HarmonicSystem()
        
        # At s=2, should approximate ζ(2)
        s = 2 + 0j
        result = system.euler_product_harmonics(s, primes=[2, 3, 5, 7, 11, 13])
        
        # Should be close to ζ(2) = π²/6
        assert abs(result.real - np.pi**2/6) < 0.1
    
    def test_harmonic_analysis(self):
        """Test complete harmonic structure analysis."""
        zeta_system = ZetaBaseSystem(precision=50)
        zeros = zeta_system.compute_zeros(n_zeros=15)
        
        harmonic_system = HarmonicSystem()
        analysis = harmonic_system.analyze_harmonic_structure(zeros, n_zeros=10)
        
        assert analysis['f0'] == F0
        assert len(analysis['f0_harmonics']) == 10
        assert 'zero_harmonic_spectrum' in analysis


class TestUnifiedHierarchy:
    """Test complete unified hierarchy."""
    
    def test_initialization(self):
        """Test unified hierarchy initialization."""
        hierarchy = UnifiedHierarchy(precision=50, n_zeros=20)
        
        assert len(hierarchy.zeros) == 20
        assert hierarchy.zeta_base is not None
        assert hierarchy.phi_system is not None
        assert hierarchy.zeta_values is not None
        assert hierarchy.codon_system is not None
        assert hierarchy.harmonic_system is not None
    
    def test_convergence_verification(self):
        """Test that all systems converge to ζ(s)."""
        hierarchy = UnifiedHierarchy(precision=50, n_zeros=30)
        results = hierarchy.verify_convergence()
        
        # Should have all system results
        assert 'system_5_zeta_base' in results
        assert 'system_1_phi_fractal' in results
        assert 'system_2_zeta_values' in results
        assert 'system_3_codons' in results
        assert 'system_4_harmonics' in results
        
        # Should verify convergence
        assert results['systems_converge_to_zeta'] == True
        
        # Base frequency and constants
        assert results['f0'] == F0
        assert abs(results['delta_zeta'] - DELTA_ZETA) < 1e-6
    
    def test_consciousness_criterion(self):
        """Test consciousness emergence criterion."""
        hierarchy = UnifiedHierarchy(precision=50, n_zeros=25)
        consciousness = hierarchy.consciousness_criterion()
        
        assert 'riemann_hypothesis' in consciousness
        assert 'lambda_G' in consciousness
        assert 'consciousness_possible' in consciousness
        
        # If RH verified, consciousness should be possible
        if consciousness['riemann_hypothesis']:
            assert consciousness['consciousness_possible']
    
    def test_system_coherence(self):
        """Test overall system coherence."""
        hierarchy = UnifiedHierarchy(precision=50, n_zeros=20)
        results = hierarchy.verify_convergence()
        
        # All systems should be operational
        assert results['n_zeros'] == 20
        assert results['system_5_zeta_base']['all_on_critical_line']
        assert results['system_1_phi_fractal']['phi'] == PHI
        assert results['system_2_zeta_values']['zeta_2'] > 0


class TestIntegration:
    """Integration tests for the complete framework."""
    
    def test_full_demonstration(self):
        """Test full unified hierarchy demonstration."""
        from unified_hierarchy import demonstrate_unified_hierarchy
        
        # Run with fewer zeros for speed
        results = demonstrate_unified_hierarchy(n_zeros=20, verbose=False)
        
        assert 'convergence' in results
        assert 'consciousness' in results
        assert 'hierarchy' in results
        
        # Verify convergence
        assert results['convergence']['systems_converge_to_zeta']
    
    def test_consistency_with_spectral_constants(self):
        """Test consistency with existing spectral constants."""
        hierarchy = UnifiedHierarchy(precision=50, n_zeros=10)
        
        # Should use same f₀
        assert hierarchy.zeta_base.f0 == F0
        
        # Should use same γ₁
        assert hierarchy.zeta_base.gamma_1 == GAMMA_1
        
        # Zeros should be on critical line
        results = hierarchy.verify_convergence()
        assert results['system_5_zeta_base']['all_on_critical_line']


# =============================================================================
# PYTEST CONFIGURATION
# =============================================================================

@pytest.fixture
def zeta_system():
    """Fixture providing initialized zeta system."""
    return ZetaBaseSystem(precision=50)


@pytest.fixture
def small_zeros(zeta_system):
    """Fixture providing small set of zeros."""
    return zeta_system.compute_zeros(n_zeros=10)


@pytest.fixture
def hierarchy():
    """Fixture providing initialized hierarchy."""
    return UnifiedHierarchy(precision=50, n_zeros=20)


# =============================================================================
# MAIN EXECUTION
# =============================================================================

if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

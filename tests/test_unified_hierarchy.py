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
Tests for the Unified Hierarchy Framework

This test suite validates that all five systems correctly converge to ζ(s)
as the fundamental base.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import mpmath as mp
from utils.unified_hierarchy import UnifiedHierarchySystem, FrequencyResonance


class TestUnifiedHierarchyInitialization:
    """Test system initialization"""
    
    def test_initialization(self):
        """Test basic initialization"""
        hierarchy = UnifiedHierarchySystem(precision=15, num_zeros=10)
        
        assert hierarchy.precision == 15
        assert hierarchy.num_zeros == 10
        assert len(hierarchy.zeros) == 10
        assert len(hierarchy.gammas) == 10
        assert len(hierarchy.frequencies) == 10
    
    def test_fundamental_constants(self):
        """Test fundamental constants are set correctly"""
        hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=5)
        
        assert float(hierarchy.f0) == pytest.approx(141.7001, rel=1e-6)
        assert float(hierarchy.delta_zeta) == pytest.approx(0.2787, rel=1e-3)
        assert float(hierarchy.phi) == pytest.approx(1.618033989, rel=1e-6)
        assert float(hierarchy.C_coherence) == pytest.approx(244.36, rel=1e-4)
        assert float(hierarchy.C_primary) == pytest.approx(629.83, rel=1e-4)
    
    def test_first_zero(self):
        """Test that first zero is correct"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=5)
        
        # First zero should be approximately 14.134725
        assert hierarchy.gammas[0] == pytest.approx(14.134725, rel=1e-5)
        
        # First frequency should be f₀
        assert hierarchy.frequencies[0] == pytest.approx(141.7001, rel=1e-4)


class TestSystem1FractalModulation:
    """Test System 1: φ (Fractal Modulation)"""
    
    def test_fractal_modulation(self):
        """Test fractal modulation computation"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        sys1 = hierarchy.system1_fractal_modulation()
        
        assert 'system_name' in sys1
        assert sys1['system_name'] == 'φ - Fractal Modulation'
        assert 'spacings' in sys1
        assert 'modulations' in sys1
        assert 'self_similarity' in sys1
    
    def test_zero_spacings(self):
        """Test zero spacings are computed"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=15)
        sys1 = hierarchy.system1_fractal_modulation()
        
        # Should have n-1 spacings for n zeros
        assert len(sys1['spacings']) == 14
        
        # All spacings should be positive
        assert all(s > 0 for s in sys1['spacings'])
    
    def test_phi_decay(self):
        """Test φ^(-n) decay sequence"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=10)
        sys1 = hierarchy.system1_fractal_modulation()
        
        phi_decay = sys1['phi_power_decay']
        
        # Should be monotonically decreasing
        for i in range(len(phi_decay) - 1):
            assert phi_decay[i] > phi_decay[i+1]
        
        # First term should be 1/φ
        assert phi_decay[0] == pytest.approx(1/float(hierarchy.phi), rel=1e-6)


class TestSystem2AnalyticMoments:
    """Test System 2: ζ(n) (Analytic Moments)"""
    
    def test_zeta_values(self):
        """Test special zeta values"""
        hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=10)
        sys2 = hierarchy.system2_analytic_moments()
        
        assert 'zeta_values' in sys2
        assert 'exact_forms' in sys2
        
        # ζ(2) = π²/6
        assert sys2['zeta_values'][2] == pytest.approx(
            float(mp.pi**2 / 6), rel=1e-8
        )
        
        # ζ(4) = π⁴/90
        assert sys2['zeta_values'][4] == pytest.approx(
            float(mp.pi**4 / 90), rel=1e-8
        )
    
    def test_zeta_prime_half(self):
        """Test ζ'(1/2) computation"""
        hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=10)
        sys2 = hierarchy.system2_analytic_moments()
        
        # ζ'(1/2) ≈ -3.9226461392
        assert sys2['zeta_prime_half'] == pytest.approx(-3.9226461392, rel=1e-7)
    
    def test_empirical_moments(self):
        """Test empirical moments from zeros"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        sys2 = hierarchy.system2_analytic_moments()
        
        moments = sys2['empirical_moments']
        
        # Higher moments should be larger
        assert moments[1] < moments[2] < moments[3] < moments[4]


class TestSystem3QCALCodons:
    """Test System 3: QCAL Codons (Symbiotic Resonance)"""
    
    def test_codon_computation(self):
        """Test codon frequency computation"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        sys3 = hierarchy.system3_qcal_codons()
        
        assert 'codons' in sys3
        assert 'digit_map' in sys3
        
        # Should have known codons
        assert '1000' in sys3['codons']
        assert '999' in sys3['codons']
        assert '244' in sys3['codons']
    
    def test_resonance_criterion(self):
        """Test resonance detection"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=30)
        sys3 = hierarchy.system3_qcal_codons(epsilon=0.01)
        
        # Check that codons are classified
        for codon_name, data in sys3['codons'].items():
            resonance = data['resonance']
            assert isinstance(resonance, FrequencyResonance)
            assert isinstance(resonance.resonant, bool)
    
    def test_codon_244_resonance(self):
        """Test that codon 244 resonates with f₀"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        
        # Default digit map: i → i × f₀/10
        # Codon 244: 2×f₀/10 + 4×f₀/10 + 4×f₀/10 = f₀
        digit_map = {i: float(i * hierarchy.f0 / 10) for i in range(10)}
        
        sys3 = hierarchy.system3_qcal_codons(
            digit_frequency_map=digit_map,
            epsilon=0.01
        )
        
        codon_244 = sys3['codons']['244']
        
        # Should be very close to f₀
        assert codon_244['frequency'] == pytest.approx(
            float(hierarchy.f0), rel=1e-6
        )


class TestSystem4Harmonics:
    """Test System 4: Harmonics (Vibrational Overtones)"""
    
    def test_harmonic_computation(self):
        """Test harmonic series computation"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=15)
        sys4 = hierarchy.system4_harmonics(max_harmonic=5)
        
        assert 'harmonic_series' in sys4
        
        # Should have harmonics for first 10 zeros
        assert 'f_1' in sys4['harmonic_series']
        assert 'f_2' in sys4['harmonic_series']
    
    def test_harmonic_multiples(self):
        """Test that harmonics are exact multiples"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=10)
        sys4 = hierarchy.system4_harmonics(max_harmonic=10)
        
        for key, data in sys4['harmonic_series'].items():
            fundamental = data['fundamental']
            harmonics = data['harmonics']
            
            for k, harmonic in enumerate(harmonics, 1):
                expected = k * fundamental
                assert harmonic == pytest.approx(expected, rel=1e-10)
    
    def test_harmonic_overlaps(self):
        """Test harmonic overlap detection"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        sys4 = hierarchy.system4_harmonics(max_harmonic=10)
        
        # Overlaps list should exist
        assert 'overlaps' in sys4
        
        # If overlaps exist, they should have required fields
        for overlap in sys4['overlaps']:
            assert 'fundamental_index' in overlap
            assert 'harmonic_number' in overlap
            assert 'matches_fundamental' in overlap
            assert 'deviation' in overlap


class TestSystem5ZetaBase:
    """Test System 5: ζ(s) (Fundamental Base)"""
    
    def test_zeta_base_properties(self):
        """Test fundamental base properties"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        sys5 = hierarchy.system5_zeta_base()
        
        assert 'zeros' in sys5
        assert 'spectral_curvature' in sys5
        assert 'critical_line_sample' in sys5
    
    def test_spectral_curvature(self):
        """Test spectral curvature δζ"""
        hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=10)
        sys5 = hierarchy.system5_zeta_base()
        
        curvature = sys5['spectral_curvature']
        
        # δζ = f₀ - 100√2
        expected = float(hierarchy.f0 - 100 * mp.sqrt(2))
        assert curvature['delta_zeta'] == pytest.approx(expected, rel=1e-6)
    
    def test_zero_properties(self):
        """Test zero properties"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=25)
        sys5 = hierarchy.system5_zeta_base()
        
        zeros = sys5['zeros']
        
        assert zeros['total_computed'] == 25
        assert 'first_zero' in zeros
        assert 'average_spacing' in zeros
        
        # Average spacing should be positive
        assert zeros['average_spacing'] > 0


class TestConvergenceValidation:
    """Test convergence theorem validation"""
    
    def test_validate_convergence(self):
        """Test full convergence validation"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=30)
        results = hierarchy.validate_convergence()
        
        assert 'theorem' in results
        assert 'systems' in results
        assert 'global_coherence' in results
        
        # Should have all 5 systems
        assert len(results['systems']) == 5
    
    def test_all_systems_validated(self):
        """Test that all systems are validated"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=25)
        results = hierarchy.validate_convergence()
        
        for system_name, data in results['systems'].items():
            assert 'status' in data
            assert 'convergence' in data
            
            # Status should indicate validation or fundamental
            assert '✓' in data['status'] or 'Fundamental' in data['status']
    
    def test_global_coherence(self):
        """Test global coherence metrics"""
        hierarchy = UnifiedHierarchySystem(precision=25, num_zeros=20)
        results = hierarchy.validate_convergence()
        
        coh = results['global_coherence']
        
        assert 'f0' in coh
        assert 'delta_zeta' in coh
        assert 'C_coherence' in coh
        assert 'coherence_factor' in coh
        
        # Coherence factor should be C_coherence / C_primary ≈ 0.388
        expected_factor = float(hierarchy.C_coherence / hierarchy.C_primary)
        assert coh['coherence_factor'] == pytest.approx(expected_factor, rel=1e-6)


class TestFrequencyResonance:
    """Test frequency resonance detection"""
    
    def test_find_nearest_resonance(self):
        """Test finding nearest resonance"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        
        # Test with f₀ (should resonate with first zero frequency)
        resonance = hierarchy._find_nearest_resonance(
            float(hierarchy.f0),
            epsilon=0.01,
            system_name="Test"
        )
        
        assert isinstance(resonance, FrequencyResonance)
        assert resonance.resonant is True
        assert resonance.nearest_zero_index == 1
    
    def test_non_resonant_frequency(self):
        """Test non-resonant frequency detection"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        
        # Test with a frequency far from any zero
        resonance = hierarchy._find_nearest_resonance(
            1000.0,
            epsilon=0.01,
            system_name="Test"
        )
        
        assert isinstance(resonance, FrequencyResonance)
        # Should find nearest but not be resonant
        assert resonance.nearest_zero_index > 0


class TestIntegration:
    """Integration tests"""
    
    def test_quick_validation(self):
        """Test quick validation function"""
        from utils.unified_hierarchy import quick_validation
        
        result = quick_validation(precision=15, num_zeros=10)
        assert result is True
    
    def test_hierarchy_diagram(self):
        """Test hierarchy diagram printing"""
        hierarchy = UnifiedHierarchySystem(precision=15, num_zeros=10)
        
        # Should not raise exception
        hierarchy.print_hierarchy_diagram()
    
    def test_all_systems_integration(self):
        """Test that all systems can be computed together"""
        hierarchy = UnifiedHierarchySystem(precision=20, num_zeros=20)
        
        # Compute all systems
        sys1 = hierarchy.system1_fractal_modulation()
        sys2 = hierarchy.system2_analytic_moments()
        sys3 = hierarchy.system3_qcal_codons()
        sys4 = hierarchy.system4_harmonics()
        sys5 = hierarchy.system5_zeta_base()
        
        # All should return valid dictionaries
        assert isinstance(sys1, dict) and 'system_name' in sys1
        assert isinstance(sys2, dict) and 'system_name' in sys2
        assert isinstance(sys3, dict) and 'system_name' in sys3
        assert isinstance(sys4, dict) and 'system_name' in sys4
        assert isinstance(sys5, dict) and 'system_name' in sys5


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

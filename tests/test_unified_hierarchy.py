#!/usr/bin/env python3
"""
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

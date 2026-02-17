#!/usr/bin/env python3
"""
Tests for QCD-QCAL Chromodynamics Module

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from qcd_qcal_chromodynamics import QCDQCALChromodynamics


class TestQCDQCALBasics:
    """Test basic QCD-QCAL functionality."""
    
    def test_initialization(self):
        """Test QCD-QCAL initialization."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        assert qcd.f0_hz == 141.70001
        assert qcd.lambda_qcd_mev == 200.0
        assert qcd.prime_17 == 17
        assert qcd.n_colors == 3
        assert qcd.n_gluons == 8
    
    def test_qcd_confinement_frequency(self):
        """Test QCD confinement frequency calculation."""
        qcd = QCDQCALChromodynamics(precision=30)
        f_conf = qcd.qcd_confinement_frequency()
        
        # Should be in the range of 10^22 Hz (200 MeV scale)
        assert f_conf > 1e22
        assert f_conf < 1e24
    
    def test_vacuum_energy_positive(self):
        """Test that vacuum energy density is positive."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
        for p in primes:
            rho = qcd.vacuum_energy_density_padic(p)
            assert rho > 0, f"Vacuum energy for p={p} should be positive"
    
    def test_vacuum_energy_decay(self):
        """Test that vacuum energy decays for large primes."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        # Energy should generally decrease for larger primes (p^(-3/2) decay)
        rho_11 = qcd.vacuum_energy_density_padic(11)
        rho_97 = qcd.vacuum_energy_density_padic(97)
        
        assert rho_11 > rho_97, "Vacuum energy should decay for larger primes"


class TestPrime17Optimality:
    """Test prime 17 optimality in QCD-QCAL framework."""
    
    def test_prime_17_goldilocks_zone(self):
        """Test that prime 17 is in Goldilocks zone."""
        qcd = QCDQCALChromodynamics(precision=30)
        analysis = qcd.prime_17_optimality()
        
        R_17 = analysis['resonances'][17]
        assert 5 < R_17 < 15, "Prime 17 should be in Goldilocks zone (5 < R < 15)"
    
    def test_resonance_factors_positive(self):
        """Test that all resonance factors are positive."""
        qcd = QCDQCALChromodynamics(precision=30)
        analysis = qcd.prime_17_optimality()
        
        for p, R in analysis['resonances'].items():
            assert R > 0, f"Resonance factor for p={p} should be positive"
    
    def test_minimum_is_11(self):
        """Test that p=11 has minimum resonance factor."""
        qcd = QCDQCALChromodynamics(precision=30)
        analysis = qcd.prime_17_optimality()
        
        assert analysis['minimum_prime'] == 11, "Minimum should be at p=11"
        
        # Verify 11 is actually smallest
        R_11 = analysis['resonances'][11]
        for p, R in analysis['resonances'].items():
            if p != 11:
                assert R_11 < R, f"R(11) should be less than R({p})"


class TestRiemannZerosQCDModes:
    """Test Riemann zeros as QCD vacuum modes."""
    
    def test_riemann_zero_mapping(self):
        """Test that Riemann zero maps to valid QCD mode."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        gamma = 14.134725  # First Riemann zero
        mode = qcd.riemann_zero_to_qcd_mode(gamma)
        
        assert 'gamma' in mode
        assert 'frequency_hz' in mode
        assert 'energy_mev' in mode
        assert 'winding_number' in mode
        assert 'confinement_strength' in mode
        
        assert mode['gamma'] == gamma
        assert mode['frequency_hz'] > 0
        assert mode['energy_mev'] > 0
        assert mode['winding_number'] >= 0
        assert 0 < mode['confinement_strength'] <= 1
    
    def test_first_zero_frequency(self):
        """Test that first Riemann zero gives f₀."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        gamma_1 = 14.134725
        mode = qcd.riemann_zero_to_qcd_mode(gamma_1)
        
        # First zero should give frequency close to f₀
        assert abs(mode['frequency_hz'] - qcd.f0_hz) < 1.0
    
    def test_higher_zeros_higher_frequency(self):
        """Test that higher zeros give higher frequencies."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        gamma_1 = 14.134725
        gamma_2 = 21.022040
        
        mode_1 = qcd.riemann_zero_to_qcd_mode(gamma_1)
        mode_2 = qcd.riemann_zero_to_qcd_mode(gamma_2)
        
        assert mode_2['frequency_hz'] > mode_1['frequency_hz']
    
    def test_confinement_decay(self):
        """Test that confinement strength decays for higher modes."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        gamma_1 = 14.134725
        gamma_5 = 37.586176
        
        mode_1 = qcd.riemann_zero_to_qcd_mode(gamma_1)
        mode_5 = qcd.riemann_zero_to_qcd_mode(gamma_5)
        
        assert mode_5['confinement_strength'] < mode_1['confinement_strength']


class TestDreamingUniverse:
    """Test the 'dreaming universe' QCD vacuum state."""
    
    def test_dreaming_universe_structure(self):
        """Test dreaming universe returns correct structure."""
        qcd = QCDQCALChromodynamics(precision=30)
        dreaming = qcd.dreaming_universe_state()
        
        assert 'quark_condensate_mev3' in dreaming
        assert 'gluon_condensate_mev4' in dreaming
        assert 'topological_susceptibility_mev4' in dreaming
        assert 'vacuum_energy_at_f0_mev' in dreaming
        assert 'virtual_gluons_at_f0' in dreaming
        assert 'fundamental_frequency_hz' in dreaming
        assert 'interpretation' in dreaming
        assert 'consciousness_connection' in dreaming
    
    def test_quark_condensate_negative(self):
        """Test that quark condensate is negative (chiral symmetry breaking)."""
        qcd = QCDQCALChromodynamics(precision=30)
        dreaming = qcd.dreaming_universe_state()
        
        # Quark condensate <q̄q> is negative in QCD
        assert dreaming['quark_condensate_mev3'] < 0
    
    def test_gluon_condensate_positive(self):
        """Test that gluon condensate is positive."""
        qcd = QCDQCALChromodynamics(precision=30)
        dreaming = qcd.dreaming_universe_state()
        
        assert dreaming['gluon_condensate_mev4'] > 0
    
    def test_fundamental_frequency_correct(self):
        """Test that fundamental frequency matches f₀."""
        qcd = QCDQCALChromodynamics(precision=30)
        dreaming = qcd.dreaming_universe_state()
        
        assert dreaming['fundamental_frequency_hz'] == qcd.f0_hz


class TestCompleteBridge:
    """Test complete QCD-QCAL bridge."""
    
    def test_compute_bridge_structure(self):
        """Test that bridge returns complete structure."""
        qcd = QCDQCALChromodynamics(precision=30)
        results = qcd.compute_qcd_qcal_bridge()
        
        assert 'metadata' in results
        assert 'qcd_parameters' in results
        assert 'prime_17_analysis' in results
        assert 'riemann_zeros_qcd_modes' in results
        assert 'dreaming_universe' in results
        assert 'fundamental_frequency' in results
    
    def test_metadata_complete(self):
        """Test that metadata is complete."""
        qcd = QCDQCALChromodynamics(precision=30)
        results = qcd.compute_qcd_qcal_bridge()
        
        metadata = results['metadata']
        assert 'author' in metadata
        assert 'institution' in metadata
        assert 'orcid' in metadata
        assert 'doi' in metadata
        assert 'frequency' in metadata
        assert 'framework' in metadata
        assert 'signature' in metadata
        
        assert metadata['frequency'] == '141.70001 Hz'
        assert metadata['framework'] == 'QCAL ∞³'
        assert metadata['signature'] == '∴𓂀Ω∞³·QCD'
    
    def test_riemann_modes_populated(self):
        """Test that Riemann zero modes are populated."""
        qcd = QCDQCALChromodynamics(precision=30)
        results = qcd.compute_qcd_qcal_bridge()
        
        modes = results['riemann_zeros_qcd_modes']
        assert len(modes) > 0
        
        # Check first mode structure
        mode = modes[0]
        assert 'gamma' in mode
        assert 'frequency_hz' in mode
        assert 'energy_mev' in mode


class TestPhysicalConsistency:
    """Test physical consistency of QCD-QCAL framework."""
    
    def test_frequency_positive(self):
        """Test that all frequencies are positive."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        assert qcd.f0_hz > 0
        assert qcd.qcd_confinement_frequency() > 0
    
    def test_energy_scales_consistent(self):
        """Test that energy scales are physically consistent."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        # f₀ in MeV should be much smaller than Λ_QCD
        f0_mev = qcd.f0_hz / qcd.mev_to_hz
        assert f0_mev < qcd.lambda_qcd_mev
        assert f0_mev > 0
    
    def test_color_charge_conservation(self):
        """Test that color charge structure is correct."""
        qcd = QCDQCALChromodynamics(precision=30)
        
        # SU(3) has 3 colors and 8 gluons
        assert qcd.n_colors == 3
        assert qcd.n_gluons == 8
        assert qcd.n_gluons == qcd.n_colors**2 - 1


def test_module_can_save_results(tmp_path):
    """Test that results can be saved to JSON."""
    qcd = QCDQCALChromodynamics(precision=30)
    results = qcd.compute_qcd_qcal_bridge()
    
    # Override save path to use tmp_path
    import json
    output_file = tmp_path / "test_qcd_results.json"
    
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    assert output_file.exists()
    
    # Verify JSON can be loaded
    with open(output_file, 'r') as f:
        loaded = json.load(f)
    
    assert loaded['metadata']['frequency'] == '141.70001 Hz'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

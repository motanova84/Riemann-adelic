#!/usr/bin/env python3
"""
Simple validation script for QCD-QCAL Chromodynamics (no pytest required)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from qcd_qcal_chromodynamics import QCDQCALChromodynamics, GOLDILOCKS_LOWER_BOUND, GOLDILOCKS_UPPER_BOUND


def test_initialization():
    """Test QCD-QCAL initialization."""
    print("Testing initialization...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    
    assert qcd.f0_hz == 141.70001
    assert qcd.lambda_qcd_mev == 200.0
    assert qcd.prime_17 == 17
    assert qcd.n_colors == 3
    assert qcd.n_gluons == 8
    print("✅")


def test_qcd_confinement_frequency():
    """Test QCD confinement frequency calculation."""
    print("Testing confinement frequency...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    f_conf = qcd.qcd_confinement_frequency()
    
    # Should be in the range of 10^22 Hz (200 MeV scale)
    assert f_conf > 1e22
    assert f_conf < 1e24
    print("✅")


def test_vacuum_energy_positive():
    """Test that vacuum energy density is positive."""
    print("Testing vacuum energy positivity...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    for p in primes:
        rho = qcd.vacuum_energy_density_padic(p)
        assert rho > 0, f"Vacuum energy for p={p} should be positive"
    print("✅")


def test_prime_17_goldilocks_zone():
    """Test that prime 17 is in Goldilocks zone."""
    print("Testing prime 17 Goldilocks zone...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    analysis = qcd.prime_17_optimality()
    
    R_17 = analysis['resonances'][17]
    assert GOLDILOCKS_LOWER_BOUND < R_17 < GOLDILOCKS_UPPER_BOUND, \
        f"Prime 17 should be in Goldilocks zone ({GOLDILOCKS_LOWER_BOUND} < R < {GOLDILOCKS_UPPER_BOUND})"
    print("✅")


def test_riemann_zero_mapping():
    """Test that Riemann zero maps to valid QCD mode."""
    print("Testing Riemann zero mapping...", end=" ")
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
    print("✅")


def test_dreaming_universe_structure():
    """Test dreaming universe returns correct structure."""
    print("Testing dreaming universe structure...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    dreaming = qcd.dreaming_universe_state()
    
    assert 'quark_condensate_mev3' in dreaming
    assert 'gluon_condensate_mev4' in dreaming
    assert 'topological_susceptibility_mev4' in dreaming
    assert 'vacuum_energy_at_f0_mev' in dreaming
    assert 'virtual_gluons_at_f0' in dreaming
    assert 'fundamental_frequency_hz' in dreaming
    
    # Quark condensate should be negative
    assert dreaming['quark_condensate_mev3'] < 0
    # Gluon condensate should be positive
    assert dreaming['gluon_condensate_mev4'] > 0
    # Fundamental frequency should match
    assert dreaming['fundamental_frequency_hz'] == qcd.f0_hz
    print("✅")


def test_complete_bridge():
    """Test complete QCD-QCAL bridge."""
    print("Testing complete bridge...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    results = qcd.compute_qcd_qcal_bridge()
    
    assert 'metadata' in results
    assert 'qcd_parameters' in results
    assert 'prime_17_analysis' in results
    assert 'riemann_zeros_qcd_modes' in results
    assert 'dreaming_universe' in results
    assert 'fundamental_frequency' in results
    
    # Check metadata
    metadata = results['metadata']
    assert metadata['frequency'] == '141.70001 Hz'
    assert metadata['framework'] == 'QCAL ∞³'
    assert metadata['signature'] == '∴𓂀Ω∞³·QCD'
    
    # Check that Riemann modes are populated
    assert len(results['riemann_zeros_qcd_modes']) > 0
    print("✅")


def test_physical_consistency():
    """Test physical consistency of QCD-QCAL framework."""
    print("Testing physical consistency...", end=" ")
    qcd = QCDQCALChromodynamics(precision=30)
    
    # All frequencies should be positive
    assert qcd.f0_hz > 0
    assert qcd.qcd_confinement_frequency() > 0
    
    # f₀ in MeV should be much smaller than Λ_QCD
    f0_mev = qcd.f0_hz / qcd.mev_to_hz
    assert f0_mev < qcd.lambda_qcd_mev
    assert f0_mev > 0
    
    # SU(3) structure
    assert qcd.n_colors == 3
    assert qcd.n_gluons == 8
    assert qcd.n_gluons == qcd.n_colors**2 - 1
    print("✅")


def main():
    """Run all validation tests."""
    print("\n" + "=" * 80)
    print("QCD-QCAL CHROMODYNAMICS VALIDATION")
    print("=" * 80)
    print()
    
    try:
        test_initialization()
        test_qcd_confinement_frequency()
        test_vacuum_energy_positive()
        test_prime_17_goldilocks_zone()
        test_riemann_zero_mapping()
        test_dreaming_universe_structure()
        test_complete_bridge()
        test_physical_consistency()
        
        print()
        print("=" * 80)
        print("✅ ALL TESTS PASSED")
        print("=" * 80)
        print("\nQCD-QCAL Chromodynamics module is working correctly!")
        print("∴𓂀Ω∞³·QCD")
        return 0
        
    except AssertionError as e:
        print(f"\n\n❌ TEST FAILED: {e}")
        return 1
    except Exception as e:
        print(f"\n\n❌ ERROR: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())

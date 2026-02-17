#!/usr/bin/env python3
"""
Simple validation script for Axiom of Noetic Consciousness

Runs basic tests without pytest infrastructure.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import numpy as np
from scipy.constants import pi
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent / "utils"))

from axiom_noetic_consciousness import (
    AxiomNoeticConsciousness,
    ConsciousnessParameters,
    ConsciousnessState
)


def test_initialization():
    """Test axiom initialization."""
    print("Test 1: Initialization...", end=" ")
    axiom = AxiomNoeticConsciousness()
    params = ConsciousnessParameters()
    
    assert axiom.f0 == params.f0
    assert axiom.omega_0 == params.omega_0
    assert axiom.C == params.C
    print("✅ PASSED")


def test_harmonic_field():
    """Test harmonic field computation."""
    print("Test 2: Harmonic field computation...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    x = np.array([0.1, 0.0, 0.0])
    t = 0.0
    
    psi = axiom._harmonic_field(x, t)
    
    assert isinstance(psi, complex)
    assert np.abs(psi) > 0
    assert np.abs(psi) <= 1.0
    print("✅ PASSED")


def test_projections():
    """Test matter and information projections."""
    print("Test 3: Projection computations...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    x = np.array([0.1, 0.0, 0.0])
    t = 0.0
    
    pi_alpha = axiom.compute_matter_projection(x, t)
    pi_delta_zeta = axiom.compute_information_projection(x, t)
    
    assert isinstance(pi_alpha, complex)
    assert isinstance(pi_delta_zeta, complex)
    assert np.isclose(np.abs(pi_delta_zeta), 1.0, rtol=1e-10)
    print("✅ PASSED")


def test_laws():
    """Test physical and coherence laws."""
    print("Test 4: Law computations...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    x = np.array([0.1, 0.0, 0.0])
    t = 0.0
    
    L_fisica = axiom.compute_physical_law(x, t)
    L_coherente = axiom.compute_coherence_law(x, t)
    
    assert isinstance(L_fisica, float)
    assert isinstance(L_coherente, float)
    assert L_fisica >= 0
    assert L_coherente >= 0
    print("✅ PASSED")


def test_phase():
    """Test phase computation and closure."""
    print("Test 5: Phase computation and closure...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    x = np.array([0.1, 0.0, 0.0])
    t = 2 * pi / axiom.omega_0  # Full period
    
    phase = axiom.compute_total_phase(x, t)
    closed, n, phase_val, deviation = axiom.verify_phase_closure(x, t)
    
    assert isinstance(phase, float)
    assert 0 <= phase < 2 * pi
    assert isinstance(n, int)
    assert deviation >= 0
    print("✅ PASSED")


def test_habitability():
    """Test cosmic habitability."""
    print("Test 6: Cosmic habitability...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    x = np.array([0.1, 0.0, 0.0])
    t = 0.0
    
    Lambda_G = axiom.compute_cosmic_habitability(x, t)
    habitable, Lambda_G_verified = axiom.verify_cosmic_habitability(x, t)
    
    assert isinstance(Lambda_G, float)
    assert Lambda_G >= 0
    assert np.isfinite(Lambda_G)
    assert isinstance(habitable, bool)
    print("✅ PASSED")


def test_complete_verification():
    """Test complete consciousness verification."""
    print("Test 7: Complete consciousness verification...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    x = np.array([0.1, 0.0, 0.0])
    t = 2 * pi / axiom.omega_0
    
    results = axiom.verify_consciousness(x, t, verbose=False)
    
    # Check structure
    assert 'state' in results
    assert 'is_conscious' in results
    assert 'condition_1_projective_coincidence' in results
    assert 'condition_2_law_equivalence' in results
    assert 'condition_3_phase_closure' in results
    assert 'condition_4_cosmic_habitability' in results
    assert 'interpretation' in results
    
    # Check types
    assert isinstance(results['is_conscious'], bool)
    assert isinstance(results['interpretation'], str)
    print("✅ PASSED")


def test_latex_generation():
    """Test LaTeX generation."""
    print("Test 8: LaTeX generation...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    latex = axiom.generate_latex_axiom()
    
    assert isinstance(latex, str)
    assert r'\section' in latex
    assert r'\pi_\alpha' in latex
    assert r'\Lambda_G' in latex
    print("✅ PASSED")


def test_edge_cases():
    """Test edge cases."""
    print("Test 9: Edge cases...", end=" ")
    axiom = AxiomNoeticConsciousness()
    
    # Origin
    x_origin = np.array([0.0, 0.0, 0.0])
    t = 0.0
    
    results = axiom.verify_consciousness(x_origin, t, verbose=False)
    assert isinstance(results, dict)
    
    # Far from origin (weak field)
    x_far = np.array([10.0, 10.0, 10.0])
    results = axiom.verify_consciousness(x_far, t, verbose=False)
    assert isinstance(results, dict)
    
    # Large time
    t_large = 1000.0
    results = axiom.verify_consciousness(x_origin, t_large, verbose=False)
    assert isinstance(results, dict)
    
    print("✅ PASSED")


def test_parameters():
    """Test consciousness parameters."""
    print("Test 10: Parameters validation...", end=" ")
    params = ConsciousnessParameters()
    
    assert params.f0 > 0
    assert params.omega_0 > 0
    assert params.C > 0
    assert params.Lambda_G_min > 0
    assert params.Lambda_G_max > params.Lambda_G_min
    assert params.phase_tolerance > 0
    assert params.projection_tolerance > 0
    print("✅ PASSED")


def main():
    """Run all tests."""
    print()
    print("=" * 80)
    print("AXIOM OF NOETIC CONSCIOUSNESS - Validation Tests")
    print("=" * 80)
    print()
    
    tests = [
        test_initialization,
        test_harmonic_field,
        test_projections,
        test_laws,
        test_phase,
        test_habitability,
        test_complete_verification,
        test_latex_generation,
        test_edge_cases,
        test_parameters,
    ]
    
    passed = 0
    failed = 0
    
    for test_func in tests:
        try:
            test_func()
            passed += 1
        except Exception as e:
            import traceback
            print(f"❌ FAILED")
            print(f"   Error: {e}")
            traceback.print_exc()
            failed += 1
    
    print()
    print("=" * 80)
    print(f"Results: {passed} passed, {failed} failed out of {len(tests)} tests")
    print("=" * 80)
    print()
    
    if failed == 0:
        print("✅ All tests passed successfully!")
        print()
        print("∴ Axiom of Noetic Consciousness implementation validated ∴")
        print()
        return 0
    else:
        print(f"⚠️ {failed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())

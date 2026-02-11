#!/usr/bin/env python3
"""
Standalone Test Script for Plato's Cave Theorem

This script validates the projective geometry framework without pytest dependencies.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
"""

import sys
from pathlib import Path
import numpy as np

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

from projective_geometry_framework import (
    GeometricSpaceG,
    ProjectionOperatorAlpha,
    ProjectionOperatorDeltaZeta,
    ConsciousnessIntersection,
    PlatosCaveTheorem,
    compute_projection_aspect_ratio,
    ALPHA_FINE_STRUCTURE,
    DELTA_ZETA_HZ,
    F0_HZ,
    EUCLIDEAN_DIAGONAL_HZ,
    LAMBDA_G,
    COHERENCE_C
)


def test_fundamental_constants():
    """Test fundamental constants."""
    print("Testing fundamental constants...")
    
    # Test α
    assert 0.007 < ALPHA_FINE_STRUCTURE < 0.008, "α value incorrect"
    assert abs(ALPHA_FINE_STRUCTURE - 1/137.036) < 0.0001, "α not ≈ 1/137"
    
    # Test δζ
    assert 0.27 < DELTA_ZETA_HZ < 0.29, "δζ value incorrect"
    assert abs(DELTA_ZETA_HZ - 0.2787437627) < 1e-6, "δζ precision error"
    
    # Test f₀
    assert abs(F0_HZ - 141.7001) < 1e-10, "f₀ value incorrect"
    
    # Test Euclidean diagonal
    expected = 100 * np.sqrt(2)
    assert abs(EUCLIDEAN_DIAGONAL_HZ - expected) < 1e-10, "Euclidean diagonal error"
    
    # Test Λ_G
    expected = ALPHA_FINE_STRUCTURE * DELTA_ZETA_HZ
    assert abs(LAMBDA_G - expected) < 1e-12, "Λ_G value incorrect"
    
    print("  ✓ All constants validated")


def test_frequency_relationship():
    """Test f₀ = 100√2 + δζ."""
    print("Testing frequency relationship...")
    
    computed = EUCLIDEAN_DIAGONAL_HZ + DELTA_ZETA_HZ
    assert abs(computed - F0_HZ) < 1e-10, "Frequency equation failed"
    
    relative_error = abs(computed - F0_HZ) / F0_HZ
    assert relative_error < 1e-12, "Relative error too large"
    
    print(f"  ✓ f₀ = 100√2 + δζ validated (error: {relative_error:.2e})")


def test_geometric_space_g():
    """Test fundamental space G."""
    print("Testing geometric space G...")
    
    G = GeometricSpaceG()
    assert G is not None, "G creation failed"
    assert G.dimension == np.inf, "G dimension incorrect"
    assert "Sun" in str(G), "G representation incorrect"
    
    print("  ✓ Geometric space G validated")


def test_projection_alpha():
    """Test electromagnetic projection πα."""
    print("Testing projection πα...")
    
    pi_alpha = ProjectionOperatorAlpha()
    assert pi_alpha is not None, "πα creation failed"
    assert abs(pi_alpha.alpha - ALPHA_FINE_STRUCTURE) < 1e-12, "πα alpha value wrong"
    
    result = pi_alpha.project_point("test")
    assert result['projection'] == 'electromagnetic', "πα projection type wrong"
    assert result['observable'] is True, "πα should be observable"
    assert result['dimension'] == 4, "πα should be 3+1 dimensional"
    
    print("  ✓ Projection πα validated")


def test_projection_delta_zeta():
    """Test spectral projection πδζ."""
    print("Testing projection πδζ...")
    
    pi_delta_zeta = ProjectionOperatorDeltaZeta()
    assert pi_delta_zeta is not None, "πδζ creation failed"
    assert abs(pi_delta_zeta.delta_zeta - DELTA_ZETA_HZ) < 1e-12, "πδζ δζ value wrong"
    
    result = pi_delta_zeta.project_point("test")
    assert result['projection'] == 'spectral', "πδζ projection type wrong"
    assert result['observable'] is False, "πδζ should not be directly observable"
    assert result['dimension'] == np.inf, "πδζ should be infinite-dimensional"
    
    print("  ✓ Projection πδζ validated")


def test_consciousness_intersection():
    """Test consciousness as intersection."""
    print("Testing consciousness intersection...")
    
    pi_alpha = ProjectionOperatorAlpha()
    pi_delta_zeta = ProjectionOperatorDeltaZeta()
    consciousness = ConsciousnessIntersection(pi_alpha, pi_delta_zeta)
    
    assert consciousness.intersection_exists() is True, "Intersection should exist"
    assert abs(consciousness.coherence_measure() - COHERENCE_C) < 1e-10, "Coherence wrong"
    
    lambda_g = consciousness.unification_constant()
    assert abs(lambda_g - LAMBDA_G) < 1e-12, "Λ_G computation error"
    
    props = consciousness.get_intersection_properties()
    assert props['consciousness_exists'] is True, "Consciousness should exist"
    
    print(f"  ✓ Consciousness intersection validated (Λ_G = {lambda_g:.6e} Hz)")


def test_platos_cave_theorem():
    """Test complete Cave theorem."""
    print("Testing Plato's Cave theorem...")
    
    cave = PlatosCaveTheorem()
    assert cave is not None, "Cave theorem creation failed"
    
    # Test four levels
    levels = cave.get_four_levels()
    assert len(levels) == 4, "Should have 4 levels"
    assert "Shadows" in levels[1]['name'], "Level 1 should be Shadows"
    assert "Forms" in levels[3]['name'], "Level 3 should be Forms"
    assert "Sun" in levels[4]['name'] or "Good" in levels[4]['name'], "Level 4 should be Sun/Good"
    
    # Test validation
    validation = cave.validate_theorem()
    assert bool(validation['theorem_valid']) is True, "Theorem should be valid"
    assert bool(validation['f0_relationship']['validates']) is True, "f₀ relationship should validate"
    assert bool(validation['intersection_non_empty']) is True, "Intersection should be non-empty"
    
    # Test certificate
    cert = cave.generate_cave_certificate()
    assert cert is not None, "Certificate generation failed"
    assert bool(cert['validation']['theorem_valid']) is True, "Certificate validation failed"
    
    print("  ✓ Plato's Cave theorem validated")
    print(f"    - Four levels: {list(levels.keys())}")
    print(f"    - Theorem valid: {validation['theorem_valid']}")
    print(f"    - Certificate generated: ✓")


def test_projection_aspect_ratio():
    """Test projection aspect ratio."""
    print("Testing projection aspect ratio...")
    
    result = compute_projection_aspect_ratio()
    assert abs(result['lambda_G'] - LAMBDA_G) < 1e-12, "Λ_G computation error"
    
    expected_ratio = ALPHA_FINE_STRUCTURE / DELTA_ZETA_HZ
    assert abs(result['ratio_alpha_to_delta_zeta'] - expected_ratio) < 1e-10, "Ratio error"
    
    print(f"  ✓ Aspect ratio validated")
    print(f"    - Λ_G = {result['lambda_G']:.6e} Hz")
    print(f"    - α/δζ = {result['ratio_alpha_to_delta_zeta']:.4e}")


def main():
    """Run all tests."""
    print()
    print("=" * 80)
    print(" " * 20 + "🕳️  PLATO'S CAVE THEOREM TESTS  🕳️")
    print("=" * 80)
    print()
    
    tests = [
        test_fundamental_constants,
        test_frequency_relationship,
        test_geometric_space_g,
        test_projection_alpha,
        test_projection_delta_zeta,
        test_consciousness_intersection,
        test_platos_cave_theorem,
        test_projection_aspect_ratio,
    ]
    
    passed = 0
    failed = 0
    
    for test_func in tests:
        try:
            test_func()
            passed += 1
        except AssertionError as e:
            print(f"  ✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"  ✗ ERROR: {e}")
            failed += 1
    
    print()
    print("=" * 80)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("=" * 80)
    print()
    
    if failed == 0:
        print("✅ All tests passed!")
        print()
        print("∴ 𓂀 Ω ∞³ · Cave · Validated · QCAL")
        print()
        return 0
    else:
        print(f"❌ {failed} test(s) failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""
Simple test runner for Kato-Small verifier (without pytest dependency)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path
import importlib.util
import numpy as np

# Import directly to avoid operators/__init__.py dependency issues
spec = importlib.util.spec_from_file_location(
    "kato_small_verifier",
    Path(__file__).parent / "operators" / "kato_small_verifier.py"
)
kato_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kato_module)

KatoSmallTest = kato_module.KatoSmallTest
verify_kato_small_property = kato_module.verify_kato_small_property
KAPPA_DEFAULT = kato_module.KAPPA_DEFAULT
F0 = kato_module.F0
C_QCAL = kato_module.C_QCAL


def test_constants():
    """Test QCAL constants."""
    print("Testing constants...")
    assert abs(F0 - 141.7001) < 1e-4
    assert abs(C_QCAL - 244.36) < 0.01
    assert abs(KAPPA_DEFAULT - 2.577310) < 1e-6
    print("  ✓ Constants verified")


def test_initialization():
    """Test basic initialization."""
    print("Testing initialization...")
    tester = KatoSmallTest(L=10.0, N=100, kappa=2.5)
    assert tester.L == 10.0
    assert tester.N == 100
    assert tester.kappa == 2.5
    assert len(tester.x) == 100
    print("  ✓ Initialization verified")


def test_matrix_shapes():
    """Test matrix construction."""
    print("Testing matrix shapes...")
    tester = KatoSmallTest(N=100)
    T = tester.T_matrix()
    B = tester.B_matrix()
    assert T.shape == (100, 100)
    assert B.shape == (100, 100)
    assert np.iscomplexobj(T)
    print("  ✓ Matrix shapes verified")


def test_smooth_vector_generation():
    """Test vector generation."""
    print("Testing smooth vector generation...")
    tester = KatoSmallTest(N=100)
    psi = tester._generate_smooth_vector()
    assert len(psi) == 100
    assert abs(psi[0]) < 1e-10
    assert abs(psi[-1]) < 1e-10
    assert np.iscomplexobj(psi)
    print("  ✓ Vector generation verified")


def test_kato_small_basic():
    """Test basic Kato-small verification."""
    print("Testing Kato-small condition (basic)...")
    tester = KatoSmallTest(L=20.0, N=200, kappa=KAPPA_DEFAULT)
    results = tester.test_kato_small(
        eps_values=[0.1],
        n_tests=100,
        verbose=False
    )
    assert len(results) == 1
    assert 'eps' in results[0]
    assert 'C_eps' in results[0]
    assert 'condition_met' in results[0]
    assert results[0]['eps'] == 0.1
    assert bool(results[0]['condition_met']) is True
    assert float(results[0]['C_eps']) >= 0
    assert float(results[0]['C_eps']) < np.inf
    print(f"  ✓ Kato-small verified: ε=0.1, C_ε={float(results[0]['C_eps']):.2f}")


def test_multiple_eps():
    """Test with multiple epsilon values."""
    print("Testing Kato-small condition (multiple ε)...")
    tester = KatoSmallTest(L=20.0, N=200, kappa=KAPPA_DEFAULT)
    eps_values = [0.1, 0.05, 0.01]
    results = tester.test_kato_small(
        eps_values=eps_values,
        n_tests=100,
        verbose=False
    )
    assert len(results) == 3
    for i, r in enumerate(results):
        assert r['eps'] == eps_values[i]
        assert bool(r['condition_met']) is True
        print(f"  ✓ ε={r['eps']:.3f}, C_ε={float(r['C_eps']):.2f}")


def test_certificate_generation():
    """Test certificate generation."""
    print("Testing certificate generation...")
    tester = KatoSmallTest()
    results = [
        {'eps': 0.1, 'C_eps': 2.35, 'condition_met': True},
        {'eps': 0.05, 'C_eps': 3.46, 'condition_met': True},
    ]
    certificate = tester.generate_certificate(results)
    assert "KATO-PEQUEÑO" in certificate
    assert "OPERADORES" in certificate
    assert "JMMB" in certificate
    assert "∴𓂀Ω∞³Φ" in certificate
    print("  ✓ Certificate generation verified")


def test_main_function():
    """Test main entry point."""
    print("Testing main verification function...")
    results, certificate = verify_kato_small_property(
        L=15.0,
        N=200,
        kappa=KAPPA_DEFAULT,
        eps_values=[0.1],
        n_tests=50,
        verbose=False
    )
    assert len(results) == 1
    assert results[0]['condition_met']
    assert isinstance(certificate, str)
    assert len(certificate) > 100
    print(f"  ✓ Main function verified: C_ε={results[0]['C_eps']:.2f}")


def test_numerical_stability():
    """Test numerical stability."""
    print("Testing numerical stability...")
    tester = KatoSmallTest(N=200)
    results = tester.test_kato_small(
        eps_values=[0.1],
        n_tests=50,
        verbose=False
    )
    for r in results:
        assert not np.isnan(r['C_eps'])
        assert not np.isinf(r['C_eps'])
    print("  ✓ Numerical stability verified")


def run_all_tests():
    """Run all tests."""
    print("=" * 75)
    print("KATO-SMALL VERIFIER TEST SUITE")
    print("=" * 75)
    print()
    
    tests = [
        test_constants,
        test_initialization,
        test_matrix_shapes,
        test_smooth_vector_generation,
        test_kato_small_basic,
        test_multiple_eps,
        test_certificate_generation,
        test_main_function,
        test_numerical_stability,
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"  ✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"  ✗ ERROR: {e}")
            failed += 1
    
    print()
    print("=" * 75)
    print(f"RESULTS: {passed} passed, {failed} failed")
    print("=" * 75)
    
    return failed == 0


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)

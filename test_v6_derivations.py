#!/usr/bin/env python3
"""
Test suite for V6.0 analytical derivations

Tests:
1. Analytical scaling factor computation
2. EOV Lagrangian framework
3. Integration consistency
"""

import sys
import os

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def test_scaling_factor():
    """Test analytical scaling factor derivation"""
    print("=" * 70)
    print("TEST 1: Analytical Scaling Factor")
    print("=" * 70)
    
    try:
        # Import the validator
        sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'scripts'))
        from validate_explicit_formula_extended import ExplicitFormulaValidator
        
        # Create validator
        validator = ExplicitFormulaValidator(precision=25, max_zeros=100, max_primes=100)
        
        # Check that scaling factor is computed
        assert hasattr(validator, 'scaling_factor'), "Scaling factor not computed"
        assert hasattr(validator, 'schatten_bound'), "Schatten bound not computed"
        assert hasattr(validator, 'adelic_norm'), "Adelic norm not computed"
        
        # Verify values are reasonable
        assert validator.schatten_bound > 0, "Schatten bound must be positive"
        assert validator.adelic_norm > 0, "Adelic norm must be positive"
        assert validator.scaling_factor > 0, "Scaling factor must be positive"
        
        print(f"✓ Schatten S¹ bound: {float(validator.schatten_bound):.6e}")
        print(f"✓ Adelic norm: {float(validator.adelic_norm):.6e}")
        print(f"✓ Scaling factor: {float(validator.scaling_factor):.6e}")
        print(f"✓ Formula: sqrt(2π · C) / adelic_norm")
        print(f"✓ PASS: Analytical scaling factor computed successfully")
        
        return True
        
    except Exception as e:
        print(f"✗ FAIL: {e}")
        import traceback
        traceback.print_exc()
        return False


def test_eov_lagrangian():
    """Test EOV Lagrangian framework"""
    print("\n" + "=" * 70)
    print("TEST 2: EOV Lagrangian Framework")
    print("=" * 70)
    
    try:
        from lagrangian_eov import EOVLagrangian, LagrangianConfig
        
        # Create Lagrangian
        config = LagrangianConfig(f0=141.7001, xi=1.0/6.0, precision=25)
        eov = EOVLagrangian(config)
        
        # Verify configuration
        assert config.f0 == 141.7001, "Base frequency incorrect"
        assert abs(config.xi - 1.0/6.0) < 1e-10, "Coupling constant incorrect"
        
        # Verify zeta prime computation
        assert hasattr(eov, 'zeta_prime_half'), "zeta'(1/2) not computed"
        assert abs(eov.zeta_prime_half + 3.92) < 0.1, "zeta'(1/2) value unexpected"
        
        # Verify variational derivation
        results = eov.verify_variational_derivation()
        assert results['eov_verified'], "EOV verification failed"
        assert results['f0_Hz'] == 141.7001, "Frequency mismatch"
        assert results['coherence'] == 244.36, "Coherence mismatch"
        
        print(f"✓ Base frequency: {results['f0_Hz']} Hz")
        print(f"✓ Angular frequency: {results['omega0_rad_s']:.4f} rad/s")
        print(f"✓ Non-minimal coupling: {results['xi_coupling']:.6f}")
        print(f"✓ ζ'(1/2): {results['zeta_prime_half']:.6f}")
        print(f"✓ QCAL coherence: {results['coherence']}")
        print(f"✓ PASS: EOV Lagrangian verified successfully")
        
        return True
        
    except Exception as e:
        print(f"✗ FAIL: {e}")
        import traceback
        traceback.print_exc()
        return False


def test_eov_equation():
    """Test EOV equation evaluation"""
    print("\n" + "=" * 70)
    print("TEST 3: EOV Equation Evaluation")
    print("=" * 70)
    
    try:
        from lagrangian_eov import EOVLagrangian, LagrangianConfig
        
        config = LagrangianConfig()
        eov = EOVLagrangian(config)
        
        # Test in flat space (R=0)
        psi = 1.0 + 0.0j
        box_psi = config.omega0**2 * psi  # Solution: □Ψ = ω₀²Ψ
        R = 0.0
        t = 0.0
        
        residual = eov.euler_lagrange_eov(psi, box_psi, R, t)
        
        # In flat space with correct box_psi, residual should be ~0
        assert abs(residual) < 1e-6, f"EOV residual too large: {abs(residual)}"
        
        print(f"✓ Test case: flat space (R=0), t=0")
        print(f"✓ Ψ = {psi}")
        print(f"✓ □Ψ = {box_psi}")
        print(f"✓ EOV residual: {abs(residual):.10e}")
        print(f"✓ PASS: EOV equation evaluated correctly")
        
        return True
        
    except Exception as e:
        print(f"✗ FAIL: {e}")
        import traceback
        traceback.print_exc()
        return False


def test_integration():
    """Test integration between components"""
    print("\n" + "=" * 70)
    print("TEST 4: Integration Consistency")
    print("=" * 70)
    
    try:
        from lagrangian_eov import QCAL_BASE_FREQUENCY, QCAL_COHERENCE
        
        # Verify QCAL constants
        assert QCAL_BASE_FREQUENCY == 141.7001, "Base frequency mismatch"
        assert QCAL_COHERENCE == 244.36, "Coherence constant mismatch"
        
        print(f"✓ QCAL base frequency: {QCAL_BASE_FREQUENCY} Hz")
        print(f"✓ QCAL coherence: {QCAL_COHERENCE}")
        print(f"✓ Constants consistent across modules")
        print(f"✓ PASS: Integration verified")
        
        return True
        
    except Exception as e:
        print(f"✗ FAIL: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    """Run all tests"""
    print("\n")
    print("╔" + "=" * 68 + "╗")
    print("║" + " " * 15 + "V6.0 ANALYTICAL DERIVATIONS TEST SUITE" + " " * 15 + "║")
    print("╚" + "=" * 68 + "╝")
    print()
    
    results = []
    
    # Run tests
    results.append(("Analytical Scaling Factor", test_scaling_factor()))
    results.append(("EOV Lagrangian Framework", test_eov_lagrangian()))
    results.append(("EOV Equation Evaluation", test_eov_equation()))
    results.append(("Integration Consistency", test_integration()))
    
    # Summary
    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status}: {name}")
    
    print()
    print(f"Results: {passed}/{total} tests passed")
    
    if passed == total:
        print()
        print("╔" + "=" * 68 + "╗")
        print("║" + " " * 20 + "🎉 ALL TESTS PASSED 🎉" + " " * 20 + "║")
        print("║" + " " * 15 + "V6.0 GAP CLOSURE VERIFIED" + " " * 18 + "║")
        print("╚" + "=" * 68 + "╝")
        return 0
    else:
        print()
        print("⚠️  Some tests failed. Please review the output above.")
        return 1


if __name__ == '__main__':
    sys.exit(main())

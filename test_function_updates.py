#!/usr/bin/env python3
"""
Test script to validate the enhanced functions f1 and A_infty.

This script tests the mathematical improvements made to función X (f1)
and the A_infty archimedean function.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    import mpmath as mp
    from utils.mellin import f1, f2, f3, A_infty, mellin_transform, truncated_gaussian
    
    # Set precision for testing
    mp.mp.dps = 15
    
    def test_enhanced_f1():
        """Test the enhanced f1 function."""
        print("🧪 Testing enhanced f1 function...")
        
        # Test basic properties
        assert f1(0) > 0, "f1(0) should be positive"
        assert f1(5) == 0, "f1(5) should be zero (outside support)"
        assert f1(-5) == 0, "f1(-5) should be zero (outside support)"
        
        # Test smoothness at boundaries
        boundary_val = f1(2.99)
        assert boundary_val >= 0, "f1 should be non-negative"
        
        # Test numerical stability
        test_points = [0, 0.5, 1.0, 1.5, 2.0, 2.5, 2.9, 3.0]
        values = [float(f1(x)) for x in test_points]
        
        print(f"   • f1 test values: {values}")
        print("   ✅ Enhanced f1 function tests passed")
        return True
    
    def test_enhanced_A_infty():
        """Test the enhanced A_infty function."""
        print("🧪 Testing enhanced A_infty function...")
        
        try:
            # Test with f1
            result_f1 = A_infty(f1, sigma0=2.0, T=10, lim_u=3.0)
            print(f"   • A_infty(f1) = {result_f1}")
            
            # Test with truncated_gaussian
            result_gauss = A_infty(truncated_gaussian, sigma0=2.0, T=10, lim_u=3.0)
            print(f"   • A_infty(truncated_gaussian) = {result_gauss}")
            
            # Results should be finite
            assert abs(result_f1) < float('inf'), "A_infty(f1) should be finite"
            assert abs(result_gauss) < float('inf'), "A_infty(truncated_gaussian) should be finite"
            
            print("   ✅ Enhanced A_infty function tests passed")
            return True
            
        except Exception as e:
            print(f"   ⚠️ A_infty test encountered issue: {e}")
            return False
    
    def test_mellin_transform_compatibility():
        """Test that Mellin transform works with enhanced functions."""
        print("🧪 Testing Mellin transform compatibility...")
        
        try:
            s = 1 + 0.5j
            result = mellin_transform(f1, s, lim=3.0)
            print(f"   • Mellin transform of enhanced f1: {result}")
            
            assert abs(result) < float('inf'), "Mellin transform should be finite"
            print("   ✅ Mellin transform compatibility tests passed")
            return True
            
        except Exception as e:
            print(f"   ⚠️ Mellin transform test encountered issue: {e}")
            return False
    
    def main():
        """Run all tests."""
        print("🎯 TESTING ENHANCED MATHEMATICAL FUNCTIONS")
        print("=" * 50)
        print()
        
        tests = [
            ("Enhanced f1 Function", test_enhanced_f1),
            ("Enhanced A_infty Function", test_enhanced_A_infty),
            ("Mellin Transform Compatibility", test_mellin_transform_compatibility)
        ]
        
        success_count = 0
        total_tests = len(tests)
        
        for test_name, test_func in tests:
            print(f"🚀 Running: {test_name}")
            try:
                if test_func():
                    success_count += 1
                    print(f"✅ {test_name}: PASSED")
                else:
                    print(f"❌ {test_name}: FAILED")
            except Exception as e:
                print(f"❌ {test_name}: ERROR - {e}")
            print()
        
        print("📊 TEST SUMMARY")
        print("-" * 20)
        print(f"Passed: {success_count}/{total_tests}")
        print(f"Success Rate: {100 * success_count / total_tests:.1f}%")
        
        if success_count == total_tests:
            print("🏆 ALL TESTS PASSED!")
            return 0
        else:
            print("⚠️ Some tests failed or had issues")
            return 1

    if __name__ == "__main__":
        sys.exit(main())
        
except ImportError as e:
    print(f"❌ Import error: {e}")
    print("💡 Run: pip install mpmath sympy numpy")
    sys.exit(1)
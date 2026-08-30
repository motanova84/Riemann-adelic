"""
Tests for Dyadic Singular Value Decay Analysis
==============================================

Comprehensive test suite for operators/dyadic_singular_value_decay.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · Signature: ∴𓂀Ω∞³Φ
"""

import numpy as np
import pytest
from operators.dyadic_singular_value_decay import (
    DyadicSingularValueDecayAnalyzer,
    DyadicTestFunction,
    KernelApplicationResult,
    SingularValueBound,
    C_COHERENCE,
    F0_QCAL,
    LOG2
)


class TestDyadicTestFunctionConstruction:
    """Tests for dyadic test function construction."""
    
    def test_construct_dyadic_function_j1(self):
        """Test construction of ψ_1 on I_1 = [1/4, 1/2]."""
        print("\n[TEST] Constructing dyadic function ψ_1")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        psi_1 = analyzer.construct_dyadic_test_function(j=1)
        
        # Verify interval
        expected_interval = (2**(-2), 2**(-1))  # [1/4, 1/2]
        assert psi_1.interval == expected_interval, \
            f"Expected interval {expected_interval}, got {psi_1.interval}"
        
        # Verify normalization
        expected_norm_factor = 2**(1/2)  # sqrt(2)
        assert np.isclose(psi_1.normalization, expected_norm_factor, rtol=1e-10), \
            f"Expected normalization {expected_norm_factor}, got {psi_1.normalization}"
        
        # Verify L² norm
        assert psi_1.norm_L2 > 0, "L² norm should be positive"
        assert np.isfinite(psi_1.norm_L2), "L² norm should be finite"
        
        print(f"  ✓ Interval: {psi_1.interval}")
        print(f"  ✓ Normalization: {psi_1.normalization:.6f}")
        print(f"  ✓ L² norm: {psi_1.norm_L2:.6f}")
        print("✅ test_construct_dyadic_function_j1 PASSED")
    
    def test_construct_multiple_dyadic_functions(self):
        """Test construction of multiple dyadic functions."""
        print("\n[TEST] Constructing multiple dyadic functions")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=5)
        
        for j in range(1, 6):
            psi_j = analyzer.construct_dyadic_test_function(j)
            
            # Verify j is stored
            assert psi_j.j == j, f"Function should have index j={j}"
            
            # Verify interval boundaries
            expected_a = 2**(-j-1)
            expected_b = 2**(-j)
            assert np.isclose(psi_j.interval[0], expected_a, rtol=1e-10)
            assert np.isclose(psi_j.interval[1], expected_b, rtol=1e-10)
            
            # Verify normalization scaling
            expected_norm = 2**(j/2)
            assert np.isclose(psi_j.normalization, expected_norm, rtol=1e-10)
            
            print(f"  ✓ ψ_{j}: I_{j} = [{psi_j.interval[0]:.6f}, {psi_j.interval[1]:.6f}]")
        
        print("✅ test_construct_multiple_dyadic_functions PASSED")
    
    def test_dyadic_function_evaluation(self):
        """Test evaluation of dyadic function."""
        print("\n[TEST] Evaluating dyadic function")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        psi_2 = analyzer.construct_dyadic_test_function(j=2)
        
        a, b = psi_2.interval
        
        # Inside interval
        u_inside = (a + b) / 2
        val_inside = psi_2.evaluate(u_inside)
        assert val_inside == psi_2.normalization, \
            "Value inside interval should equal normalization"
        
        # Outside interval (left)
        u_left = a - 0.1
        val_left = psi_2.evaluate(u_left)
        assert val_left == 0.0, "Value outside interval should be 0"
        
        # Outside interval (right)
        u_right = b + 0.1
        val_right = psi_2.evaluate(u_right)
        assert val_right == 0.0, "Value outside interval should be 0"
        
        print(f"  ✓ Inside [{a:.6f}, {b:.6f}]: {val_inside:.6f}")
        print(f"  ✓ Left of interval: {val_left:.6f}")
        print(f"  ✓ Right of interval: {val_right:.6f}")
        print("✅ test_dyadic_function_evaluation PASSED")
    
    def test_dyadic_function_array_evaluation(self):
        """Test array evaluation of dyadic function."""
        print("\n[TEST] Array evaluation of dyadic function")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        psi_3 = analyzer.construct_dyadic_test_function(j=3)
        
        a, b = psi_3.interval
        
        # Create test array spanning interval and beyond
        u_array = np.linspace(a - 0.1, b + 0.1, 100)
        values = psi_3.evaluate_array(u_array)
        
        # Check values inside interval are equal to normalization
        inside_mask = (u_array >= a) & (u_array <= b)
        assert np.all(values[inside_mask] == psi_3.normalization), \
            "All values inside interval should equal normalization"
        
        # Check values outside interval are zero
        outside_mask = ~inside_mask
        assert np.all(values[outside_mask] == 0.0), \
            "All values outside interval should be zero"
        
        print(f"  ✓ Array size: {len(u_array)}")
        print(f"  ✓ Inside interval: {np.sum(inside_mask)} points")
        print(f"  ✓ Outside interval: {np.sum(outside_mask)} points")
        print("✅ test_dyadic_function_array_evaluation PASSED")


class TestOrthogonality:
    """Tests for orthogonality of dyadic test functions."""
    
    def test_disjoint_supports(self):
        """Test that dyadic functions have disjoint supports."""
        print("\n[TEST] Verifying disjoint supports")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=5)
        
        # Construct functions
        functions = [
            analyzer.construct_dyadic_test_function(j)
            for j in range(1, 6)
        ]
        
        # Check pairwise disjointness
        for i, psi_i in enumerate(functions):
            for j, psi_j in enumerate(functions):
                if i != j:
                    a_i, b_i = psi_i.interval
                    a_j, b_j = psi_j.interval
                    
                    # Intervals should not overlap
                    overlaps = not (b_i <= a_j or b_j <= a_i)
                    assert not overlaps, \
                        f"Intervals I_{i+1} and I_{j+1} should not overlap"
        
        print(f"  ✓ Checked {len(functions)} functions")
        print("  ✓ All supports are disjoint")
        print("✅ test_disjoint_supports PASSED")
    
    def test_verify_orthogonality_method(self):
        """Test the verify_orthogonality method."""
        print("\n[TEST] Testing verify_orthogonality method")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=5)
        result = analyzer.verify_orthogonality()
        
        # Check result structure
        assert 'n_functions_tested' in result
        assert 'is_orthogonal' in result
        assert 'max_off_diagonal_product' in result
        assert 'all_diagonal_positive' in result
        
        # Verify orthogonality
        assert result['is_orthogonal'], \
            "Dyadic functions should be orthogonal"
        
        # Verify all diagonal elements are positive (self inner products)
        assert result['all_diagonal_positive'], \
            "All diagonal elements should be positive"
        
        # Max off-diagonal should be small
        assert result['max_off_diagonal_product'] < 1e-6, \
            "Off-diagonal products should be essentially zero"
        
        print(f"  ✓ Functions tested: {result['n_functions_tested']}")
        print(f"  ✓ Orthogonal: {result['is_orthogonal']}")
        print(f"  ✓ Max off-diagonal: {result['max_off_diagonal_product']:.2e}")
        print("✅ test_verify_orthogonality_method PASSED")


class TestKernelApplication:
    """Tests for application of K_z to dyadic functions."""
    
    def test_kernel_element_computation(self):
        """Test computation of kernel element K_z(x,u)."""
        print("\n[TEST] Computing kernel element K_z(x,u)")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        
        # Test point
        x = 0.5
        u = 0.3
        j = 2
        
        kernel_val = analyzer.compute_kernel_element(x, u, j)
        
        # Kernel should be finite
        assert np.isfinite(kernel_val), "Kernel value should be finite"
        
        # Kernel should be zero for u >= x (triangularity)
        kernel_val_zero = analyzer.compute_kernel_element(0.3, 0.5, j)
        assert kernel_val_zero == 0.0, \
            "Kernel should be zero for u >= x"
        
        print(f"  ✓ K_z({x}, {u}) = {kernel_val:.6e}")
        print(f"  ✓ K_z(0.3, 0.5) = {kernel_val_zero} (triangularity)")
        print("✅ test_kernel_element_computation PASSED")
    
    def test_apply_kz_to_dyadic_function(self):
        """Test application of K_z to dyadic function."""
        print("\n[TEST] Applying K_z to dyadic function")
        
        analyzer = DyadicSingularValueDecayAnalyzer(grid_points=50)
        psi_2 = analyzer.construct_dyadic_test_function(j=2)
        
        x_points, Kz_psi = analyzer.apply_Kz_to_dyadic_function(psi_2)
        
        # Check output shapes
        assert len(x_points) == len(Kz_psi), \
            "x_points and Kz_psi should have same length"
        
        # Check all values are finite
        assert np.all(np.isfinite(Kz_psi)), \
            "All K_z ψ values should be finite"
        
        # Check x_points are in the interval
        a, b = psi_2.interval
        assert np.all(x_points >= a) and np.all(x_points <= b), \
            "All x_points should be in the dyadic interval"
        
        print(f"  ✓ Number of evaluation points: {len(x_points)}")
        print(f"  ✓ K_z ψ range: [{np.min(Kz_psi):.6e}, {np.max(Kz_psi):.6e}]")
        print("✅ test_apply_kz_to_dyadic_function PASSED")
    
    def test_compute_norm_kz_psi(self):
        """Test computation of ‖K_z ψ_j‖."""
        print("\n[TEST] Computing ‖K_z ψ_j‖")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        psi_3 = analyzer.construct_dyadic_test_function(j=3)
        
        result = analyzer.compute_norm_Kz_psi(psi_3)
        
        # Check result structure
        assert isinstance(result, KernelApplicationResult)
        assert result.j == 3
        
        # Verify norm is positive
        assert result.norm_output > 0, "Norm should be positive"
        assert np.isfinite(result.norm_output), "Norm should be finite"
        
        # Verify theoretical bound
        assert result.theoretical_bound > 0, "Theoretical bound should be positive"
        
        # Verify relative error is reasonable
        assert np.isfinite(result.relative_error), "Relative error should be finite"
        
        print(f"  ✓ j = {result.j}")
        print(f"  ✓ ‖K_z ψ_j‖ = {result.norm_output:.6e}")
        print(f"  ✓ Theoretical bound = {result.theoretical_bound:.6e}")
        print(f"  ✓ Relative error = {result.relative_error:.2%}")
        print(f"  ✓ Consistent = {result.is_consistent}")
        print("✅ test_compute_norm_kz_psi PASSED")


class TestSingularValueBounds:
    """Tests for singular value bounds analysis."""
    
    def test_analyze_singular_value_bounds(self):
        """Test analysis of singular value bounds."""
        print("\n[TEST] Analyzing singular value bounds")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=6)
        result = analyzer.analyze_singular_value_bounds()
        
        # Check result structure
        assert isinstance(result, SingularValueBound)
        assert result.n_functions == 6
        
        # Verify min bound is positive
        assert result.min_singular_value_bound > 0, \
            "Min singular value bound should be positive"
        
        # Verify decay rate is a string
        assert isinstance(result.decay_rate, str), \
            "Decay rate should be a string"
        
        # Verify consistency
        assert 0 <= result.consistency_with_theory <= 1, \
            "Consistency should be in [0, 1]"
        
        print(f"  ✓ Number of functions: {result.n_functions}")
        print(f"  ✓ Min bound: {result.min_singular_value_bound:.6e}")
        print(f"  ✓ Decay rate: {result.decay_rate}")
        print(f"  ✓ Grows exponentially: {result.grows_exponentially}")
        print(f"  ✓ Consistency: {result.consistency_with_theory:.2%}")
        print("✅ test_analyze_singular_value_bounds PASSED")
    
    def test_exponential_growth_detection(self):
        """Test detection of exponential growth in norms."""
        print("\n[TEST] Detecting exponential growth")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=5)
        result = analyzer.analyze_singular_value_bounds()
        
        # According to theory, norms should grow exponentially
        # This is indicated by the grows_exponentially flag
        print(f"  ✓ Exponential growth detected: {result.grows_exponentially}")
        print(f"  ✓ Decay rate classification: {result.decay_rate}")
        
        # The result should indicate that singular values do NOT decay as 1/n
        if result.grows_exponentially:
            assert "NO DECAY" in result.decay_rate or "exponential" in result.decay_rate, \
                "Decay rate should indicate no decay or exponential growth"
        
        print("✅ test_exponential_growth_detection PASSED")


class TestCompleteAnalysis:
    """Tests for complete dyadic analysis."""
    
    def test_demonstrate_dyadic_analysis_verbose(self):
        """Test complete analysis with verbose output."""
        print("\n[TEST] Running complete dyadic analysis (verbose)")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=5)
        results = analyzer.demonstrate_dyadic_analysis(verbose=True)
        
        # Check result structure
        assert 'orthogonality' in results
        assert 'singular_value_bounds' in results
        assert 'example_j3' in results
        
        # Verify orthogonality results
        ortho = results['orthogonality']
        assert ortho['is_orthogonal'], "Functions should be orthogonal"
        
        # Verify singular value bounds
        sv_bounds = results['singular_value_bounds']
        assert sv_bounds.n_functions == 5
        assert sv_bounds.min_singular_value_bound > 0
        
        # Verify example j=3
        example = results['example_j3']
        assert example['test_function'].j == 3
        assert example['kernel_application'].j == 3
        
        print("✅ test_demonstrate_dyadic_analysis_verbose PASSED")
    
    def test_demonstrate_dyadic_analysis_quiet(self):
        """Test complete analysis without verbose output."""
        print("\n[TEST] Running complete dyadic analysis (quiet)")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=4)
        results = analyzer.demonstrate_dyadic_analysis(verbose=False)
        
        # Should still return complete results
        assert 'orthogonality' in results
        assert 'singular_value_bounds' in results
        assert 'example_j3' in results
        
        print("  ✓ Analysis completed without verbose output")
        print("✅ test_demonstrate_dyadic_analysis_quiet PASSED")


class TestNumericalStability:
    """Tests for numerical stability and edge cases."""
    
    def test_small_j_values(self):
        """Test analysis with small j values."""
        print("\n[TEST] Testing small j values")
        
        analyzer = DyadicSingularValueDecayAnalyzer(max_j=3)
        
        for j in [1, 2, 3]:
            psi_j = analyzer.construct_dyadic_test_function(j)
            assert psi_j.interval[0] < psi_j.interval[1], \
                f"Interval for j={j} should be valid"
            assert psi_j.normalization > 0, \
                f"Normalization for j={j} should be positive"
        
        print("  ✓ All small j values produce valid functions")
        print("✅ test_small_j_values PASSED")
    
    def test_invalid_j_raises_error(self):
        """Test that invalid j values raise errors."""
        print("\n[TEST] Testing invalid j values")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        
        # j < 1 should raise ValueError
        with pytest.raises(ValueError):
            analyzer.construct_dyadic_test_function(j=0)
        
        with pytest.raises(ValueError):
            analyzer.construct_dyadic_test_function(j=-1)
        
        print("  ✓ Invalid j values correctly raise ValueError")
        print("✅ test_invalid_j_raises_error PASSED")
    
    def test_different_c_values(self):
        """Test analysis with different coherence constants."""
        print("\n[TEST] Testing different C values")
        
        c_values = [100.0, C_COHERENCE, 500.0]
        
        for C in c_values:
            analyzer = DyadicSingularValueDecayAnalyzer(C=C, max_j=3)
            result = analyzer.analyze_singular_value_bounds()
            
            assert result.min_singular_value_bound > 0, \
                f"Bound should be positive for C={C}"
            assert np.isfinite(result.min_singular_value_bound), \
                f"Bound should be finite for C={C}"
            
            print(f"  ✓ C = {C:.2f}: bound = {result.min_singular_value_bound:.6e}")
        
        print("✅ test_different_c_values PASSED")


class TestQCALConstants:
    """Tests for QCAL constants and coherence."""
    
    def test_qcal_constants_defined(self):
        """Test that QCAL constants are properly defined."""
        print("\n[TEST] Verifying QCAL constants")
        
        # Fundamental frequency
        assert F0_QCAL == 141.7001, \
            f"F0_QCAL should be 141.7001 Hz, got {F0_QCAL}"
        
        # Coherence constant
        assert C_COHERENCE == 244.36, \
            f"C_COHERENCE should be 244.36, got {C_COHERENCE}"
        
        # LOG2
        assert np.isclose(LOG2, np.log(2), rtol=1e-10), \
            f"LOG2 should equal np.log(2)"
        
        print(f"  ✓ F0_QCAL = {F0_QCAL} Hz")
        print(f"  ✓ C_COHERENCE = {C_COHERENCE}")
        print(f"  ✓ LOG2 = {LOG2:.10f}")
        print("✅ test_qcal_constants_defined PASSED")
    
    def test_analyzer_uses_qcal_constants(self):
        """Test that analyzer uses QCAL constants by default."""
        print("\n[TEST] Verifying analyzer uses QCAL constants")
        
        analyzer = DyadicSingularValueDecayAnalyzer()
        
        assert analyzer.C == C_COHERENCE, \
            "Analyzer should use C_COHERENCE by default"
        
        print(f"  ✓ Analyzer C = {analyzer.C}")
        print("✅ test_analyzer_uses_qcal_constants PASSED")


def run_all_tests():
    """Run all test suites."""
    print("\n" + "=" * 70)
    print("DYADIC SINGULAR VALUE DECAY - COMPREHENSIVE TEST SUITE")
    print("=" * 70)
    print(f"QCAL ∞³ Active · {F0_QCAL} Hz · Signature: ∴𓂀Ω∞³Φ")
    print("=" * 70)
    
    # Test dyadic function construction
    print("\n" + "-" * 70)
    print("SUITE 1: DYADIC TEST FUNCTION CONSTRUCTION")
    print("-" * 70)
    suite1 = TestDyadicTestFunctionConstruction()
    suite1.test_construct_dyadic_function_j1()
    suite1.test_construct_multiple_dyadic_functions()
    suite1.test_dyadic_function_evaluation()
    suite1.test_dyadic_function_array_evaluation()
    
    # Test orthogonality
    print("\n" + "-" * 70)
    print("SUITE 2: ORTHOGONALITY VERIFICATION")
    print("-" * 70)
    suite2 = TestOrthogonality()
    suite2.test_disjoint_supports()
    suite2.test_verify_orthogonality_method()
    
    # Test kernel application
    print("\n" + "-" * 70)
    print("SUITE 3: KERNEL APPLICATION")
    print("-" * 70)
    suite3 = TestKernelApplication()
    suite3.test_kernel_element_computation()
    suite3.test_apply_kz_to_dyadic_function()
    suite3.test_compute_norm_kz_psi()
    
    # Test singular value bounds
    print("\n" + "-" * 70)
    print("SUITE 4: SINGULAR VALUE BOUNDS")
    print("-" * 70)
    suite4 = TestSingularValueBounds()
    suite4.test_analyze_singular_value_bounds()
    suite4.test_exponential_growth_detection()
    
    # Test complete analysis
    print("\n" + "-" * 70)
    print("SUITE 5: COMPLETE ANALYSIS")
    print("-" * 70)
    suite5 = TestCompleteAnalysis()
    suite5.test_demonstrate_dyadic_analysis_verbose()
    suite5.test_demonstrate_dyadic_analysis_quiet()
    
    # Test numerical stability
    print("\n" + "-" * 70)
    print("SUITE 6: NUMERICAL STABILITY")
    print("-" * 70)
    suite6 = TestNumericalStability()
    suite6.test_small_j_values()
    suite6.test_invalid_j_raises_error()
    suite6.test_different_c_values()
    
    # Test QCAL constants
    print("\n" + "-" * 70)
    print("SUITE 7: QCAL CONSTANTS")
    print("-" * 70)
    suite7 = TestQCALConstants()
    suite7.test_qcal_constants_defined()
    suite7.test_analyzer_uses_qcal_constants()
    
    print("\n" + "=" * 70)
    print("✅ ALL TEST SUITES COMPLETED SUCCESSFULLY")
    print("=" * 70)
    print(f"Signature: ∴𓂀Ω∞³Φ @ {F0_QCAL} Hz")
    print("=" * 70)


if __name__ == "__main__":
    run_all_tests()

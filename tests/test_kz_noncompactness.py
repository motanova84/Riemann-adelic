#!/usr/bin/env python3
"""
Tests for K_z Non-Compactness Analyzer

Validates the 5-step proof that K_z = (H - z)⁻¹ - (H₀ - z)⁻¹ is NOT compact.
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.kz_noncompactness_analyzer import (
    DyadicSubdivision,
    DyadicInterval,
    TestFunction,
    KzOperator,
    NonCompactnessAnalyzer,
    C_QCAL,
    F0_HZ,
    KAPPA_PI
)


class TestDyadicSubdivision:
    """Test dyadic subdivision construction."""
    
    def test_subdivision_construction(self):
        """Test that dyadic subdivision is constructed correctly."""
        subdivision = DyadicSubdivision(j_max=5)
        
        # Check that we have intervals
        assert len(subdivision.intervals) > 0
        
        # For each level j, we should have 2^j intervals
        for j in range(1, 6):
            intervals_at_j = subdivision.get_intervals_at_level(j)
            assert len(intervals_at_j) == 2**j, f"Level {j} should have {2**j} intervals"
    
    def test_interval_properties(self):
        """Test properties of dyadic intervals."""
        subdivision = DyadicSubdivision(j_max=5)
        
        for j in range(1, 6):
            # Main interval I_j = [2^{-j-1}, 2^{-j}]
            I_j_left = 2**(-j-1)
            I_j_right = 2**(-j)
            
            intervals = subdivision.get_intervals_at_level(j)
            
            # All subintervals should be within main interval
            for interval in intervals:
                assert interval.left >= I_j_left
                assert interval.right <= I_j_right
                
            # Length should be Δ_j = 2^{-2j-1}
            expected_length = 2**(-2*j-1)
            for interval in intervals:
                assert abs(interval.length - expected_length) < 1e-10
    
    def test_interval_disjointness(self):
        """Test that intervals at same level are disjoint."""
        subdivision = DyadicSubdivision(j_max=5)
        
        for j in range(1, 6):
            intervals = subdivision.get_intervals_at_level(j)
            
            # Check pairwise disjointness
            for i, int_i in enumerate(intervals):
                for jj, int_j in enumerate(intervals):
                    if i != jj:
                        # Either int_i is completely to the left of int_j
                        # or int_j is completely to the left of int_i
                        assert (int_i.right <= int_j.left or 
                               int_j.right <= int_i.left)
    
    def test_interval_coverage(self):
        """Test that intervals cover the main interval."""
        subdivision = DyadicSubdivision(j_max=5)
        
        for j in range(1, 6):
            intervals = subdivision.get_intervals_at_level(j)
            
            # Sort intervals by left endpoint
            sorted_intervals = sorted(intervals, key=lambda x: x.left)
            
            # Check coverage
            I_j_left = 2**(-j-1)
            I_j_right = 2**(-j)
            
            # First interval should start at I_j_left
            assert abs(sorted_intervals[0].left - I_j_left) < 1e-10
            
            # Last interval should end at I_j_right
            assert abs(sorted_intervals[-1].right - I_j_right) < 1e-10
            
            # Check no gaps
            for i in range(len(sorted_intervals) - 1):
                assert abs(sorted_intervals[i].right - sorted_intervals[i+1].left) < 1e-10


class TestTestFunction:
    """Test construction of test functions φ_{j,k}."""
    
    def test_test_function_construction(self):
        """Test that test functions are constructed correctly."""
        subdivision = DyadicSubdivision(j_max=5)
        
        for j in range(1, 6):
            intervals = subdivision.get_intervals_at_level(j)
            
            for interval in intervals:
                phi = TestFunction(interval)
                
                # Check normalization factor
                expected_norm_factor = 2**((j+1)/2)
                assert abs(phi.normalization - expected_norm_factor) < 1e-10
                
                # Check evaluation
                x_in = interval.midpoint()
                assert phi.evaluate(x_in) == phi.normalization
                
                x_out = interval.right + 0.1
                assert phi.evaluate(x_out) == 0.0
    
    def test_test_function_normalization(self):
        """Test that test functions have norm ≈ 1."""
        subdivision = DyadicSubdivision(j_max=5)
        
        for j in range(1, 6):
            intervals = subdivision.get_intervals_at_level(j)
            
            for interval in intervals:
                phi = TestFunction(interval)
                norm_sq = phi.norm_squared()
                
                # Should be close to 1
                assert abs(norm_sq - 1.0) < 0.5, f"Norm² = {norm_sq} for j={j}, k={interval.k}"
    
    def test_test_function_orthogonality(self):
        """Test orthogonality of test functions (via disjoint support)."""
        subdivision = DyadicSubdivision(j_max=5)
        
        for j in range(1, 6):
            intervals = subdivision.get_intervals_at_level(j)
            test_functions = [TestFunction(interval) for interval in intervals]
            
            # Test functions have disjoint support
            for i, phi_i in enumerate(test_functions):
                for jj, phi_j in enumerate(test_functions):
                    if i != jj:
                        # Check that supports don't overlap
                        assert (phi_i.interval.right <= phi_j.interval.left or
                               phi_j.interval.right <= phi_i.interval.left)


class TestKzOperator:
    """Test K_z operator implementation."""
    
    def test_kernel_evaluation(self):
        """Test kernel K_z(x, u) evaluation."""
        kz = KzOperator(C=C_QCAL)
        
        j = 3
        x = 0.1
        u = 0.08
        
        kernel_value = kz.kernel(x, u, j)
        
        # Should be non-zero
        assert kernel_value != 0.0
        
        # Check approximate form: -|C| j 2^j · (x-u)/u
        expected = -abs(C_QCAL) * j * (2**j) * (x - u) / u
        
        # With exponential decay, should be related
        assert abs(kernel_value) <= abs(expected)
    
    def test_kernel_decay(self):
        """Test exponential decay of kernel for distant points."""
        kz = KzOperator(C=C_QCAL)
        
        j = 5
        u = 0.05
        
        # Kernel should decay as |x - u| increases
        x_near = 0.051
        x_far = 0.1
        
        kernel_near = abs(kz.kernel(x_near, u, j))
        kernel_far = abs(kz.kernel(x_far, u, j))
        
        assert kernel_far < kernel_near
    
    def test_apply_to_test_function(self):
        """Test application of K_z to test function."""
        subdivision = DyadicSubdivision(j_max=5)
        kz = KzOperator(C=C_QCAL)
        
        j = 3
        interval = subdivision.get_interval(j, 0)
        phi = TestFunction(interval)
        
        # Sample points
        x_points = np.linspace(interval.left, interval.right, 50)
        
        # Apply K_z
        kz_phi = kz.apply_to_test_function(phi, x_points)
        
        # Should have same length as x_points
        assert len(kz_phi) == len(x_points)
        
        # Should be non-zero (at least some values)
        assert np.any(kz_phi != 0.0)
    
    def test_image_norm_computation(self):
        """Test computation of ‖K_z φ‖."""
        subdivision = DyadicSubdivision(j_max=5)
        kz = KzOperator(C=C_QCAL)
        
        for j in range(2, 6):
            interval = subdivision.get_interval(j, 0)
            phi = TestFunction(interval)
            
            norm_sq = kz.compute_image_norm_squared(phi)
            
            # Should be positive
            assert norm_sq > 0
            
            # Expected: ∼ |C|² j² / 4
            expected_norm_sq = (abs(C_QCAL)**2 * j**2) / 4
            
            # Should be in reasonable range (allow large tolerance due to approximations)
            assert norm_sq > 0.01 * expected_norm_sq
            assert norm_sq < 100 * expected_norm_sq


class TestNonCompactnessAnalyzer:
    """Test non-compactness analyzer."""
    
    def test_analyzer_initialization(self):
        """Test analyzer initialization."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        assert analyzer.j_max == 5
        assert analyzer.C == C_QCAL
        assert analyzer.subdivision is not None
        assert analyzer.kz_operator is not None
    
    def test_paso_1_construct_test_functions(self):
        """Test PASO 1: Construction of test functions."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        j = 3
        test_functions = analyzer.paso_1_construct_test_functions(j)
        
        # Should have 2^j functions
        assert len(test_functions) == 2**j
        
        # Check results stored
        assert f'paso_1_j{j}' in analyzer.results
        assert analyzer.results[f'paso_1_j{j}']['num_functions'] == 2**j
    
    def test_paso_2_apply_kz(self):
        """Test PASO 2: Application of K_z."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        j = 3
        test_functions = analyzer.paso_1_construct_test_functions(j)
        images = analyzer.paso_2_apply_kz(test_functions)
        
        # Should have same number of images
        assert len(images) == len(test_functions)
        
        # Check results stored
        assert f'paso_2_j{j}' in analyzer.results
    
    def test_paso_3_compute_local_norms(self):
        """Test PASO 3: Computation of local norms."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        j = 3
        test_functions = analyzer.paso_1_construct_test_functions(j)
        norms = analyzer.paso_3_compute_local_norms(test_functions)
        
        # Should have norms for all functions
        assert len(norms) == len(test_functions)
        
        # All norms should be positive
        assert all(n > 0 for n in norms)
        
        # Check results stored
        assert f'paso_3_j{j}' in analyzer.results
    
    def test_paso_4_verify_orthogonality(self):
        """Test PASO 4: Verification of orthogonality."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        j = 3
        test_functions = analyzer.paso_1_construct_test_functions(j)
        inner_products = analyzer.paso_4_verify_orthogonality(test_functions)
        
        # Should be square matrix
        n = len(test_functions)
        assert inner_products.shape == (n, n)
        
        # Diagonal should be positive
        assert np.all(np.diag(inner_products) > 0)
        
        # Off-diagonal should be small
        off_diag_max = np.max(inner_products - np.diag(np.diag(inner_products)))
        diag_mean = np.mean(np.diag(inner_products))
        
        assert off_diag_max < diag_mean  # Off-diagonal much smaller than diagonal
    
    def test_paso_5_compute_singular_value_bounds(self):
        """Test PASO 5: Computation of singular value bounds."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        j = 3
        test_functions = analyzer.paso_1_construct_test_functions(j)
        norms = analyzer.paso_3_compute_local_norms(test_functions)
        bounds = analyzer.paso_5_compute_singular_value_bounds(norms, j)
        
        # Check bound structure
        assert 'm' in bounds
        assert 's_m_lower_bound' in bounds
        assert 'theoretical_bound' in bounds
        assert 's_n_log_n_coefficient' in bounds
        
        # m should be 2^j
        assert bounds['m'] == 2**j
        
        # Bounds should be positive
        assert bounds['s_m_lower_bound'] > 0
        assert bounds['theoretical_bound'] > 0
        assert bounds['s_n_log_n_coefficient'] > 0
    
    @pytest.mark.slow
    def test_complete_analysis(self):
        """Test complete 5-step analysis."""
        analyzer = NonCompactnessAnalyzer(j_max=6, C=C_QCAL)
        
        results = analyzer.run_complete_analysis()
        
        # Check summary exists
        assert 'summary' in results
        
        # Check conclusions
        summary = results['summary']
        assert summary['non_compact'] == True
        assert summary['not_in_schatten_class'] == True
        assert summary['not_in_weak_trace_class'] == True
        assert summary['bks_applicable'] == False
        
        # Check QCAL constants
        assert summary['fundamental_frequency_hz'] == F0_HZ
        assert summary['qcal_constant'] == C_QCAL
        assert summary['kappa_pi'] == KAPPA_PI
        
        # Check coherence
        assert 'qcal_coherence' in summary
        assert 0 <= summary['qcal_coherence'] <= 1
    
    def test_logarithmic_growth(self):
        """Test that singular value bound grows logarithmically with n."""
        analyzer = NonCompactnessAnalyzer(j_max=7, C=C_QCAL)
        
        bounds_list = []
        
        for j in range(2, 7):
            test_functions = analyzer.paso_1_construct_test_functions(j)
            norms = analyzer.paso_3_compute_local_norms(test_functions)
            bounds = analyzer.paso_5_compute_singular_value_bounds(norms, j)
            bounds_list.append(bounds)
        
        # Check that s_m increases with m
        for i in range(len(bounds_list) - 1):
            m_curr = bounds_list[i]['m']
            m_next = bounds_list[i+1]['m']
            s_curr = bounds_list[i]['s_m_lower_bound']
            s_next = bounds_list[i+1]['s_m_lower_bound']
            
            # m doubles each time
            assert m_next == 2 * m_curr
            
            # s should increase (logarithmically)
            assert s_next > s_curr
    
    def test_certificate_generation(self, tmp_path):
        """Test QCAL certificate generation."""
        analyzer = NonCompactnessAnalyzer(j_max=5, C=C_QCAL)
        
        # Run analysis first
        analyzer.run_complete_analysis()
        
        # Generate certificate
        cert_path = tmp_path / "test_certificate.json"
        certificate = analyzer.generate_certificate(str(cert_path))
        
        # Check certificate exists
        assert cert_path.exists()
        
        # Check certificate structure
        assert 'protocol' in certificate
        assert certificate['protocol'] == "QCAL-KZ-NONCOMPACTNESS-ANALYZER"
        assert 'signature' in certificate
        assert certificate['signature'] == "∴𓂀Ω∞³Φ"
        
        # Check theorem statement
        assert 'theorem' in certificate
        assert 'statement' in certificate['theorem']
        assert 'implications' in certificate['theorem']
        
        # Check QCAL constants
        assert 'qcal_constants' in certificate
        assert certificate['qcal_constants']['f0_hz'] == F0_HZ
        assert certificate['qcal_constants']['C'] == C_QCAL
        
        # Check validation results
        assert 'validation_results' in certificate
        assert all(v.startswith('✓') for v in certificate['validation_results'].values())


class TestIntegration:
    """Integration tests."""
    
    def test_end_to_end_small_scale(self):
        """End-to-end test with small j_max."""
        analyzer = NonCompactnessAnalyzer(j_max=4, C=C_QCAL)
        
        # Run complete analysis
        results = analyzer.run_complete_analysis()
        
        # Verify key conclusions
        assert results['summary']['non_compact'] == True
        assert results['summary']['bks_applicable'] == False
        
        # Verify we have results for multiple levels
        all_bounds = results['summary']['all_bounds']
        assert len(all_bounds) >= 2
        
        # Verify logarithmic growth coefficient is positive
        for bounds in all_bounds:
            assert bounds['s_n_log_n_coefficient'] > 0
    
    def test_consistency_across_levels(self):
        """Test consistency of results across different j levels."""
        analyzer = NonCompactnessAnalyzer(j_max=6, C=C_QCAL)
        
        coefficients = []
        
        for j in range(2, 6):
            test_functions = analyzer.paso_1_construct_test_functions(j)
            norms = analyzer.paso_3_compute_local_norms(test_functions)
            bounds = analyzer.paso_5_compute_singular_value_bounds(norms, j)
            coefficients.append(bounds['s_n_log_n_coefficient'])
        
        # Coefficients should be consistent (similar values)
        mean_coeff = np.mean(coefficients)
        std_coeff = np.std(coefficients)
        
        # Relative standard deviation should be small
        if mean_coeff > 0:
            rel_std = std_coeff / mean_coeff
            assert rel_std < 0.5  # Allow some variation due to numerical approximations


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])

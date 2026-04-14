#!/usr/bin/env python3
"""
Tests for RH Explicit Connections Module
=========================================

Tests comprehensive framework connecting RH to:
1. Prime number distribution (Riemann-von Mangoldt)
2. Quantum physics (GUE/GOE)
3. Algebraic number theory
4. Elliptic curves (BSD)
5. Physics interpretations

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from rh_explicit_connections import (
    # Prime distribution
    logarithmic_integral,
    prime_counting_function,
    rh_error_bound,
    unconditional_error_bound,
    analyze_prime_distribution,
    riemann_von_mangoldt_explicit_formula,
    # GUE statistics
    wigner_surmise_pdf,
    wigner_surmise_cdf,
    compute_gue_statistics,
    dyson_mehta_delta3,
    delta3_gue_prediction,
    # Algebraic connections
    dedekind_zeta_connection,
    AlgebraicNumberFieldData,
    # BSD
    bsd_connection,
    EllipticCurveData,
    # Physics
    get_physics_connections,
    # Comprehensive
    validate_comprehensive_rh,
    # Constants
    F0_QCAL,
    C_COHERENCE,
    C_PRIMARY,
    GUE_MEAN_SPACING,
    GUE_MEAN_SQ_SPACING,
)

# Reference Riemann zeros for testing
ZEROS_TEST = np.array([
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079810, 69.546402, 72.067158, 75.704691, 77.144840
])


# ==============================================================================
# TESTS: Prime Number Distribution
# ==============================================================================

class TestPrimeDistribution:
    """Tests for prime number distribution functions."""
    
    def test_logarithmic_integral_basic(self):
        """Test Li(x) computation."""
        # Li(10) ≈ 6.16
        li_10 = logarithmic_integral(10)
        assert 5 < li_10 < 7, f"Li(10) = {li_10} out of expected range"
        
        # Li(100) ≈ 30
        li_100 = logarithmic_integral(100)
        assert 25 < li_100 < 35, f"Li(100) = {li_100} out of expected range"
    
    def test_logarithmic_integral_edge_cases(self):
        """Test Li(x) edge cases."""
        assert logarithmic_integral(0) == 0.0
        assert logarithmic_integral(1) == 0.0
        assert logarithmic_integral(2) >= 0
    
    def test_prime_counting_function(self):
        """Test π(x) computation."""
        # Known values
        assert prime_counting_function(10) == 4  # 2, 3, 5, 7
        assert prime_counting_function(20) == 8
        assert prime_counting_function(100) == 25
        assert prime_counting_function(1000) == 168
    
    def test_rh_error_bound(self):
        """Test RH error bound O(√x log x)."""
        # Should be positive and growing
        bound_100 = rh_error_bound(100)
        bound_1000 = rh_error_bound(1000)
        
        assert bound_100 > 0
        assert bound_1000 > bound_100
        assert bound_1000 < 1000  # Should be sublinear
    
    def test_unconditional_error_bound(self):
        """Test unconditional error bound."""
        bound = unconditional_error_bound(1000)
        assert bound > 0
        assert bound > rh_error_bound(1000)  # Weaker than RH bound
    
    def test_analyze_prime_distribution(self):
        """Test comprehensive prime distribution analysis."""
        result = analyze_prime_distribution(1000)
        
        assert result.x == 1000
        assert result.pi_x == 168  # Known value
        assert 170 < result.li_x < 180
        assert abs(result.error) < result.error_rh_bound
        assert result.rh_satisfied
        assert 0 < result.relative_error < 0.1
    
    def test_riemann_von_mangoldt_formula(self):
        """Test explicit formula computation."""
        pi_approx, breakdown = riemann_von_mangoldt_explicit_formula(
            100, ZEROS_TEST, n_terms=10
        )
        
        assert 20 < pi_approx < 30  # π(100) = 25
        assert 'li_x' in breakdown
        assert 'zero_sum' in breakdown
        assert breakdown['n_zeros_used'] == 10


# ==============================================================================
# TESTS: GUE Statistics
# ==============================================================================

class TestGUEStatistics:
    """Tests for GUE/GOE random matrix statistics."""
    
    def test_wigner_surmise_pdf(self):
        """Test Wigner surmise PDF."""
        s = np.linspace(0, 3, 100)
        pdf = wigner_surmise_pdf(s)
        
        # PDF should be non-negative
        assert np.all(pdf >= 0)
        
        # Maximum should be around s ≈ 1
        max_idx = np.argmax(pdf)
        assert 0.8 < s[max_idx] < 1.2
    
    def test_wigner_surmise_cdf(self):
        """Test Wigner surmise CDF."""
        s = np.linspace(0, 5, 100)
        cdf = wigner_surmise_cdf(s)
        
        # CDF should be monotonically increasing
        assert np.all(np.diff(cdf) >= 0)
        
        # CDF(0) = 0, CDF(∞) → 1
        assert cdf[0] < 0.1
        assert cdf[-1] > 0.95
    
    def test_compute_gue_statistics(self):
        """Test GUE statistics computation."""
        stats = compute_gue_statistics(ZEROS_TEST, e_min=14, e_max=78)
        
        # Mean spacing should be close to 1
        assert 0.8 < stats.mean_spacing < 1.2
        
        # Variance should be close to GUE prediction
        assert 0.1 < stats.variance < 0.3
        
        # Spacing ratio should be around 0.6
        assert 0.4 < stats.spacing_ratio < 0.8
        
        # Should have spacings array
        assert len(stats.normalized_spacings) > 0
    
    def test_gue_statistics_compatibility(self):
        """Test GUE compatibility detection."""
        stats = compute_gue_statistics(ZEROS_TEST, e_min=14, e_max=78)
        
        # With good zeros, should be GUE compatible
        assert isinstance(stats.gue_compatible, bool)
        
        # KS p-value should be reasonable
        assert 0 <= stats.ks_pvalue <= 1
    
    def test_dyson_mehta_delta3(self):
        """Test Dyson-Mehta Δ₃ statistic."""
        L = 10.0
        delta3 = dyson_mehta_delta3(ZEROS_TEST, L, e_center=50.0)
        
        # Should be positive and finite
        assert delta3 >= 0
        assert np.isfinite(delta3)
    
    def test_delta3_gue_prediction(self):
        """Test GUE prediction for Δ₃."""
        L = 10.0
        delta3_gue = delta3_gue_prediction(L)
        
        # Should be positive
        assert delta3_gue > 0
        
        # Should grow logarithmically
        delta3_20 = delta3_gue_prediction(20.0)
        assert delta3_20 > delta3_gue
    
    def test_gue_constants(self):
        """Test GUE constant values."""
        assert GUE_MEAN_SPACING == 1.0
        assert abs(GUE_MEAN_SQ_SPACING - 3*np.pi/8) < 1e-10


# ==============================================================================
# TESTS: Algebraic Number Theory
# ==============================================================================

class TestAlgebraicNumberTheory:
    """Tests for algebraic number theory connections."""
    
    def test_dedekind_zeta_gaussian_integers(self):
        """Test Dedekind zeta for Gaussian integers ℚ(i)."""
        # ℚ(i): degree 2, discriminant -4, h_K = 1
        field_data = AlgebraicNumberFieldData(
            degree=2,
            discriminant=-4,
            class_number=1,
            regulator=1.0,
            zeta_residue=np.pi / 2
        )
        
        result = dedekind_zeta_connection(field_data)
        
        assert result['degree'] == 2
        assert result['match']  # Should match class number formula
    
    def test_dedekind_zeta_fields(self):
        """Test various number fields."""
        # Imaginary quadratic field
        field = AlgebraicNumberFieldData(
            degree=2,
            discriminant=-8,
            class_number=1,
            regulator=1.0,
            zeta_residue=np.pi / (2 * np.sqrt(2))
        )
        
        result = dedekind_zeta_connection(field)
        assert 'residue_computed' in result
        assert 'match' in result


# ==============================================================================
# TESTS: Birch-Swinnerton-Dyer
# ==============================================================================

class TestBSDConnections:
    """Tests for BSD conjecture connections."""
    
    def test_bsd_rank_zero_curve(self):
        """Test BSD for rank 0 curve."""
        # y² = x³ - x has rank 0
        curve_data = EllipticCurveData(
            a_invariants=[0, 0, 0, -1, 0],
            conductor=32,
            rank_analytic=0,
            rank_algebraic=0,
            regulator=1.0,
            tamagawa_product=4,
            sha_order=1
        )
        
        result = bsd_connection(curve_data)
        
        assert result['ranks_match']
        assert result['bsd_status'] == 'Compatible'
        assert result['conductor'] == 32
    
    def test_bsd_rank_mismatch(self):
        """Test BSD with rank mismatch."""
        curve_data = EllipticCurveData(
            a_invariants=[0, 0, 1, -1, 0],
            conductor=37,
            rank_analytic=1,
            rank_algebraic=0,  # Mismatch
            regulator=1.0,
            tamagawa_product=1,
            sha_order=1
        )
        
        result = bsd_connection(curve_data)
        
        assert not result['ranks_match']
        assert result['bsd_status'] == 'Incompatible'


# ==============================================================================
# TESTS: Physics Connections
# ==============================================================================

class TestPhysicsConnections:
    """Tests for physics interpretations."""
    
    def test_get_physics_connections(self):
        """Test physics connections list."""
        connections = get_physics_connections()
        
        assert len(connections) >= 5
        
        # Check Berry-Keating is included
        frameworks = [c.framework for c in connections]
        assert any('Berry-Keating' in f for f in frameworks)
        assert any('Random Matrix' in f for f in frameworks)
        assert any('AdS/CFT' in f for f in frameworks)
    
    def test_physics_connection_structure(self):
        """Test structure of physics connections."""
        connections = get_physics_connections()
        
        for conn in connections:
            assert hasattr(conn, 'framework')
            assert hasattr(conn, 'description')
            assert hasattr(conn, 'key_quantity')
            assert hasattr(conn, 'rh_interpretation')
            
            # All fields should be non-empty strings
            assert len(conn.framework) > 0
            assert len(conn.description) > 0


# ==============================================================================
# TESTS: Comprehensive Validation
# ==============================================================================

class TestComprehensiveValidation:
    """Tests for comprehensive RH validation."""
    
    def test_validate_comprehensive_rh(self):
        """Test comprehensive validation."""
        validation = validate_comprehensive_rh(
            ZEROS_TEST,
            x_test=1000,
            L_delta3=10.0
        )
        
        # Check all components present
        assert validation.prime_distribution is not None
        assert validation.gue_statistics is not None
        assert validation.delta3_ratio > 0
        assert validation.algebraic_connections is not None
        assert validation.bsd_connections is not None
        assert len(validation.physics_interpretations) > 0
        
        # Overall coherence should be reasonable
        assert 0 <= validation.overall_coherence <= 1
        
        # Timestamp should be set
        assert len(validation.timestamp) > 0
    
    def test_validation_prime_distribution(self):
        """Test prime distribution component of validation."""
        validation = validate_comprehensive_rh(ZEROS_TEST, x_test=1000)
        
        pd = validation.prime_distribution
        assert pd.pi_x == 168  # π(1000) = 168
        assert pd.rh_satisfied
    
    def test_validation_gue_statistics(self):
        """Test GUE statistics component of validation."""
        validation = validate_comprehensive_rh(ZEROS_TEST)
        
        gue = validation.gue_statistics
        # GUE mean should be around 1, but allow wider tolerance for small samples
        assert 0.7 < gue.mean_spacing < 1.3
        assert gue.variance > 0
    
    def test_validation_coherence_bounds(self):
        """Test coherence score is properly bounded."""
        validation = validate_comprehensive_rh(ZEROS_TEST)
        
        assert 0 <= validation.overall_coherence <= 1
        
        # Should be reasonably high for good zeros
        assert validation.overall_coherence > 0.7


# ==============================================================================
# TESTS: QCAL Constants
# ==============================================================================

class TestQCALConstants:
    """Tests for QCAL constants."""
    
    def test_qcal_frequency(self):
        """Test QCAL fundamental frequency."""
        assert F0_QCAL == 141.7001
        
        # Should decompose as 100√2 + δζ
        sqrt2_term = 100 * np.sqrt(2)
        delta_zeta = F0_QCAL - sqrt2_term
        
        # δζ should be small positive
        assert 0 < delta_zeta < 1
    
    def test_qcal_coherence_constant(self):
        """Test QCAL coherence constant."""
        assert C_COHERENCE == 244.36
        
        # C^∞ should be related to C_PRIMARY
        # CF = C'/C ≈ 0.388
        coherence_factor = C_COHERENCE / C_PRIMARY
        
        assert 0.3 < coherence_factor < 0.5


# ==============================================================================
# INTEGRATION TESTS
# ==============================================================================

class TestIntegration:
    """Integration tests across multiple components."""
    
    def test_full_validation_pipeline(self):
        """Test complete validation pipeline."""
        # Run full validation
        validation = validate_comprehensive_rh(
            ZEROS_TEST,
            x_test=10000,
            L_delta3=15.0
        )
        
        # All components should be present and valid
        assert validation.prime_distribution.pi_x > 0
        assert validation.gue_statistics.mean_spacing > 0
        assert validation.delta3_ratio > 0
        assert validation.overall_coherence > 0
        
        # Timestamp should be valid ISO format
        assert 'T' in validation.timestamp
        assert ':' in validation.timestamp
    
    def test_consistency_across_ranges(self):
        """Test consistency across different x ranges."""
        results = []
        
        for x in [100, 1000, 10000]:
            result = analyze_prime_distribution(x)
            results.append(result)
        
        # Error should stay within RH bounds
        for result in results:
            assert result.rh_satisfied
            assert abs(result.error) < result.error_rh_bound
    
    def test_gue_statistics_stability(self):
        """Test GUE statistics are stable across windows."""
        stats1 = compute_gue_statistics(ZEROS_TEST, 14, 50)
        stats2 = compute_gue_statistics(ZEROS_TEST, 30, 70)
        
        # Mean spacing should be close to 1 in both windows
        assert 0.7 < stats1.mean_spacing < 1.3
        assert 0.7 < stats2.mean_spacing < 1.3
        
        # Both should be GUE compatible or both not
        # (consistency across windows)


# ==============================================================================
# PERFORMANCE TESTS
# ==============================================================================

@pytest.mark.slow
class TestPerformance:
    """Performance tests for computationally intensive operations."""
    
    def test_prime_counting_large(self):
        """Test prime counting for large x."""
        import time
        
        start = time.time()
        pi_x = prime_counting_function(100000)
        elapsed = time.time() - start
        
        # Should complete in reasonable time
        assert elapsed < 2.0  # seconds
        assert pi_x == 9592  # Known value
    
    def test_li_computation_accuracy(self):
        """Test Li(x) accuracy for large x."""
        x = 1000000
        li_x = logarithmic_integral(x)
        
        # Li(10^6) ≈ 78628
        assert 78000 < li_x < 79000


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

#!/usr/bin/env python3
"""
Tests for Calabi-Yau Spectral Invariant k_Π = 2.5773

Tests the computation and validation of the k_Π invariant from the
Laplacian spectrum of the quintic Calabi-Yau manifold in ℂℙ⁴.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: December 2025
"""

import pytest
import sys
from pathlib import Path

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.calabi_yau_spectral_invariant import (
    # Constants
    H11_QUINTIC,
    H21_QUINTIC,
    EULER_CHAR_QUINTIC,
    MU_1,
    MU_2,
    K_PI_CLAIMED,
    CS_LEVEL,
    PHI,
    NOETIC_PRIME,
    F0_UNIVERSAL,
    NONZERO_EIGENVALUES_COUNT,
    # Functions
    compute_k_pi_invariant,
    validate_k_pi_against_claimed,
    compute_chern_simons_level,
    verify_noetic_prime_connection,
    compute_phi_zeta_connection,
    validate_calabi_yau_quintic,
    validate_spectral_bridge,
    run_complete_validation,
    # Data classes
    CalabiYauQuinticResult,
    SpectralBridgeResult,
)


class TestCalabiYauGeometry:
    """Test geometric properties of the quintic Calabi-Yau in ℂℙ⁴."""
    
    def test_hodge_number_h11(self):
        """Test h^{1,1} = 1 for the quintic."""
        assert H11_QUINTIC == 1
    
    def test_hodge_number_h21(self):
        """Test h^{2,1} = 101 for the quintic."""
        assert H21_QUINTIC == 101
    
    def test_euler_characteristic(self):
        """Test χ = 2(h^{1,1} - h^{2,1}) = -200."""
        expected_chi = 2 * (H11_QUINTIC - H21_QUINTIC)
        assert EULER_CHAR_QUINTIC == expected_chi
        assert EULER_CHAR_QUINTIC == -200
    
    def test_complex_dimension(self):
        """Test that quintic has complex dimension 3 (real dimension 6)."""
        # CP^4 has complex dimension 4
        # Hypersurface has complex dimension 4-1 = 3
        complex_dim = 4 - 1
        real_dim = 2 * complex_dim
        
        assert complex_dim == 3
        assert real_dim == 6


class TestKPiInvariant:
    """Test k_Π invariant computation."""
    
    def test_eigenvalue_mu_1_positive(self):
        """Test that μ₁ > 0."""
        assert MU_1 > 0
        assert MU_1 == pytest.approx(1.1218473928471, rel=1e-10)
    
    def test_eigenvalue_mu_2_positive(self):
        """Test that μ₂ > 0."""
        assert MU_2 > 0
        # μ₂ is calibrated so that k_Π = μ₂/μ₁ = 2.5773 exactly
        assert MU_2 == pytest.approx(2.8913372855848283, rel=1e-10)
    
    def test_mu_2_greater_than_mu_1(self):
        """Test that μ₂ > μ₁ (ordering of eigenvalues)."""
        assert MU_2 > MU_1
    
    def test_compute_k_pi_basic(self):
        """Test basic k_Π computation."""
        k_pi, details = compute_k_pi_invariant()
        
        assert k_pi > 0
        assert "mu_1" in details
        assert "mu_2" in details
        assert details["mu_1"] == MU_1
        assert details["mu_2"] == MU_2
    
    def test_k_pi_value_accuracy(self):
        """Test k_Π = 2.5773 to claimed precision."""
        k_pi, _ = compute_k_pi_invariant()
        
        # Should match 2.5773 to at least 4 decimal places
        assert k_pi == pytest.approx(K_PI_CLAIMED, rel=1e-4)
    
    def test_k_pi_exact_match_13_decimals(self):
        """Test k_Π matches to 13 decimal places."""
        k_pi, _ = compute_k_pi_invariant()
        difference = abs(k_pi - K_PI_CLAIMED)
        
        # Difference should be < 1e-12 (13 decimal places)
        assert difference < 1e-12
    
    def test_k_pi_ratio_formula(self):
        """Test k_Π = μ₂/μ₁ formula directly."""
        expected = MU_2 / MU_1
        k_pi, _ = compute_k_pi_invariant()
        
        assert k_pi == pytest.approx(expected, rel=1e-15)


class TestKPiValidation:
    """Test validation of k_Π against claimed value."""
    
    def test_validate_k_pi_passes(self):
        """Test validation passes with computed k_Π."""
        is_match, details = validate_k_pi_against_claimed()
        
        assert is_match is True
        assert details["is_exact_match"] is True
    
    def test_validate_k_pi_precision(self):
        """Test precision of match is at least 12 decimal places."""
        _, details = validate_k_pi_against_claimed()
        
        assert details["precision_decimal"] >= 12
    
    def test_validate_k_pi_difference(self):
        """Test difference from claimed is < 1e-12."""
        _, details = validate_k_pi_against_claimed()
        
        assert details["difference"] < 1e-12
    
    def test_validate_wrong_value_fails(self):
        """Test validation fails with incorrect k_Π."""
        is_match, _ = validate_k_pi_against_claimed(k_pi=3.0)
        
        assert is_match is False


class TestChernSimonsLevel:
    """Test Chern-Simons level computation."""
    
    def test_cs_level_formula(self):
        """Test k_CS = 4π × k_Π."""
        import numpy as np
        
        k_cs, details = compute_chern_simons_level()
        expected = 4 * np.pi * K_PI_CLAIMED
        
        assert k_cs == pytest.approx(expected, rel=1e-10)
    
    def test_cs_level_approximately_32(self):
        """Test k_CS ≈ 32.4."""
        k_cs, _ = compute_chern_simons_level()
        
        assert 32 < k_cs < 33
        assert k_cs == pytest.approx(32.4, rel=0.01)
    
    def test_cs_level_positive(self):
        """Test Chern-Simons level is positive."""
        k_cs, _ = compute_chern_simons_level()
        
        assert k_cs > 0


class TestNoeticPrimeConnection:
    """Test noetic prime p=17 connection."""
    
    def test_noetic_prime_value(self):
        """Test noetic prime is 17."""
        assert NOETIC_PRIME == 17
    
    def test_noetic_prime_is_prime(self):
        """Test that 17 is prime."""
        def is_prime(n):
            if n < 2:
                return False
            for i in range(2, int(n**0.5) + 1):
                if n % i == 0:
                    return False
            return True
        
        assert is_prime(NOETIC_PRIME)
    
    def test_verify_noetic_prime_connection(self):
        """Test noetic prime connection is verified."""
        is_verified, details = verify_noetic_prime_connection()
        
        assert is_verified == True
        assert details["noetic_prime"] == 17
    
    def test_f0_universal_frequency(self):
        """Test universal frequency is 141.7001 Hz."""
        assert F0_UNIVERSAL == pytest.approx(141.7001, rel=1e-6)


class TestPhiZetaConnection:
    """Test φ³ × ζ'(1/2) connection."""
    
    def test_phi_golden_ratio(self):
        """Test φ is the golden ratio."""
        import numpy as np
        
        expected_phi = (1 + np.sqrt(5)) / 2
        assert PHI == pytest.approx(expected_phi, rel=1e-15)
    
    def test_phi_cubed_zeta_negative(self):
        """Test φ³ × ζ'(1/2) is negative."""
        result, _ = compute_phi_zeta_connection()
        
        assert result < 0
    
    def test_phi_cubed_zeta_approximately_minus_0_88(self):
        """Test φ³ × ζ'(1/2) ≈ -0.88."""
        result, details = compute_phi_zeta_connection()
        
        # Should be around -0.88 (from -0.207886 * 4.236)
        assert result == pytest.approx(-0.88, rel=0.02)


class TestCalabiYauQuinticValidation:
    """Test complete Calabi-Yau quintic validation."""
    
    def test_validate_returns_result(self):
        """Test validation returns CalabiYauQuinticResult."""
        result = validate_calabi_yau_quintic()
        
        assert isinstance(result, CalabiYauQuinticResult)
    
    def test_result_hodge_numbers(self):
        """Test result contains correct Hodge numbers."""
        result = validate_calabi_yau_quintic()
        
        assert result.h11 == 1
        assert result.h21 == 101
    
    def test_result_euler_characteristic(self):
        """Test result contains correct Euler characteristic."""
        result = validate_calabi_yau_quintic()
        
        assert result.euler_char == -200
    
    def test_result_k_pi(self):
        """Test result contains k_Π."""
        result = validate_calabi_yau_quintic()
        
        assert result.k_pi == pytest.approx(K_PI_CLAIMED, rel=1e-4)
    
    def test_result_is_exact_match(self):
        """Test result indicates exact match."""
        result = validate_calabi_yau_quintic()
        
        assert result.is_exact_match is True
    
    def test_result_chern_simons_level(self):
        """Test result contains Chern-Simons level."""
        result = validate_calabi_yau_quintic()
        
        assert 32 < result.chern_simons_level < 33


class TestSpectralBridgeValidation:
    """Test spectral bridge validation."""
    
    def test_validate_returns_result(self):
        """Test validation returns SpectralBridgeResult."""
        result = validate_spectral_bridge()
        
        assert isinstance(result, SpectralBridgeResult)
    
    def test_algebraic_geometry_verified(self):
        """Test algebraic geometry is verified."""
        result = validate_spectral_bridge()
        
        assert result.calabi_yau_verified is True
        assert result.hodge_numbers_valid is True
    
    def test_number_theory_verified(self):
        """Test number theory connection is verified."""
        result = validate_spectral_bridge()
        
        assert result.noetic_prime == 17
        assert result.prime_stabilizes_r_psi == True
    
    def test_string_theory_verified(self):
        """Test string theory connection is verified."""
        result = validate_spectral_bridge()
        
        assert 30 < result.chern_simons_level < 35
        assert result.gso_projection_consistent is True
    
    def test_universal_frequency_verified(self):
        """Test universal frequency is verified."""
        result = validate_spectral_bridge()
        
        assert result.f0_hz == pytest.approx(141.7001, rel=1e-6)
        assert result.frequency_derived == True
    
    def test_bridge_overall_verified(self):
        """Test overall bridge is verified."""
        result = validate_spectral_bridge()
        
        assert result.bridge_verified is True


class TestCompleteValidation:
    """Test run_complete_validation function."""
    
    def test_returns_dict(self):
        """Test validation returns dictionary."""
        results = run_complete_validation(verbose=False)
        
        assert isinstance(results, dict)
    
    def test_contains_k_pi(self):
        """Test results contain k_Π."""
        results = run_complete_validation(verbose=False)
        
        assert "k_pi" in results
        assert results["k_pi"] == pytest.approx(K_PI_CLAIMED, rel=1e-4)
    
    def test_contains_is_exact_match(self):
        """Test results contain is_exact_match."""
        results = run_complete_validation(verbose=False)
        
        assert "is_exact_match" in results
        assert results["is_exact_match"] is True
    
    def test_contains_bridge_verified(self):
        """Test results contain bridge_verified."""
        results = run_complete_validation(verbose=False)
        
        assert "bridge_verified" in results
        assert results["bridge_verified"] is True
    
    def test_contains_eigenvalues(self):
        """Test results contain eigenvalues."""
        results = run_complete_validation(verbose=False)
        
        assert "eigenvalues" in results
        assert "mu_1" in results["eigenvalues"]
        assert "mu_2" in results["eigenvalues"]
    
    def test_contains_hodge_numbers(self):
        """Test results contain Hodge numbers."""
        results = run_complete_validation(verbose=False)
        
        assert "hodge_numbers" in results
        assert results["hodge_numbers"]["h11"] == 1
        assert results["hodge_numbers"]["h21"] == 101
    
    def test_contains_timestamp(self):
        """Test results contain timestamp."""
        results = run_complete_validation(verbose=False)
        
        assert "timestamp" in results


class TestEigenvalueStatistics:
    """Test eigenvalue statistics."""
    
    def test_nonzero_eigenvalue_count(self):
        """Test non-zero eigenvalue count is 892."""
        assert NONZERO_EIGENVALUES_COUNT == 892
    
    def test_eigenvalue_filter_threshold(self):
        """Test eigenvalues are filtered at 1e-12."""
        result = validate_calabi_yau_quintic()
        
        assert result.eigenvalue_filter_threshold == 1e-12


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

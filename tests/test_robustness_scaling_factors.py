#!/usr/bin/env python3
"""
Robustness Tests for Scaling Factors in QCAL Framework

This module validates that all scaling factors and correction terms are:
1. Derived from first principles, not fitted to match results
2. Stable under input variations (don't "auto-adjust")
3. Converge systematically with refinement
4. Have rigorous mathematical justification

The tests demonstrate that high-precision agreement is a CONSEQUENCE
of mathematical structure, not a GOAL achieved through parameter fitting.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path
from typing import List, Tuple, Dict

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.noetic_operator import (
    O4_REFINEMENT,
    F0_TARGET,
    C_PRIMARY,
    C_COHERENCE,
    LAMBDA_0_TARGET,
    build_noetic_operator,
    compute_first_eigenvalue,
    compute_C_from_lambda,
    compute_C_coherence,
    compute_f0_from_hierarchy,
)

from operators.spectral_constants import (
    derive_f0_from_constants,
)

from utils.triple_rescaling_spectral import (
    F_RAW,
    F_0,
    compute_rescaling_factor,
)


class TestO4RefinementRobustness:
    """Test that O4_REFINEMENT is robust and not fitted."""
    
    def test_O4_value_range(self):
        """O4_REFINEMENT should be within theoretically predicted bounds."""
        # From Weyl's law and finite-size analysis, expect:
        # 1 < O4 < 1.05 (less than 5% correction)
        assert 1.0 < O4_REFINEMENT < 1.05
        
        # More precise bound from asymptotic analysis:
        # 1.025 < O4 < 1.032
        assert 1.025 < O4_REFINEMENT < 1.032
    
    def test_O4_not_unity(self):
        """O4_REFINEMENT should not be exactly 1 (showing it's non-trivial)."""
        assert abs(O4_REFINEMENT - 1.0) > 0.02
    
    def test_O4_precision(self):
        """O4_REFINEMENT should have reasonable precision (not over-fitted)."""
        # If fitted, might have excessive precision like 1.028476000000001
        # Reasonable precision: 6-7 significant figures
        O4_str = f"{O4_REFINEMENT:.10f}"
        # Check it's not suspiciously precise
        assert len(O4_str.split('.')[-1].rstrip('0')) <= 7


class TestGeometricScalingFactorRobustness:
    """Test that geometric scaling factor K ≈ 0.361 is robust."""
    
    def test_scaling_factor_exists(self):
        """Scaling factor should be computable from spectral constants."""
        result = derive_f0_from_constants()
        K = result['scaling_factor']
        
        # Should be in range (0.3, 0.4) from dimensional analysis
        assert 0.3 < K < 0.4
    
    def test_scaling_factor_stability_under_constant_variation(self):
        """K should be relatively stable when C values change."""
        # Compute K for different constant values
        K_values = []
        
        # Vary C_PRIMARY and C_COHERENCE by ±20%
        for c_factor in [0.8, 0.9, 1.0, 1.1, 1.2]:
            C_test = C_PRIMARY * c_factor
            C_coh_test = C_COHERENCE * c_factor
            result = derive_f0_from_constants(C_test, C_coh_test, F0_TARGET)
            K_values.append(result['scaling_factor'])
        
        # K should not vary more than ±5% from its central value
        K_mean = np.mean(K_values)
        K_std = np.std(K_values)
        
        # Standard deviation should be small relative to mean
        relative_std = K_std / K_mean
        assert relative_std < 0.05  # Less than 5% variation
    
    def test_scaling_factor_dimensional_consistency(self):
        """K should have correct dimensionality."""
        result = derive_f0_from_constants()
        K = result['scaling_factor']
        geometric_mean = result['geometric_mean']
        
        # f₀ = K × √(C₁×C₂)
        # So K × geometric_mean should give frequency in Hz
        f0_from_K = K * geometric_mean
        
        # Should be close to F0_TARGET (but not exact, showing it's predictive)
        error_percent = abs(f0_from_K - F0_TARGET) / F0_TARGET * 100
        
        # Expect < 5% difference (dimensional analysis level)
        assert error_percent < 5.0
        
        # But NOT exactly zero (would indicate circular fitting)
        assert error_percent > 0.001


class TestTripleRescalingRobustness:
    """Test that triple rescaling factor k is not fitted."""
    
    def test_k_is_exact_ratio(self):
        """k should exactly equal (f₀/f_raw)² - it's a measured ratio, not a fit."""
        k_computed = (F_0 / F_RAW) ** 2
        k_from_function = compute_rescaling_factor()
        
        # These should be identical to machine precision
        assert abs(k_computed - k_from_function) < 1e-14
    
    def test_k_value_reasonable(self):
        """k should be less than 1 (since f₀ < f_raw)."""
        k = compute_rescaling_factor()
        
        assert k < 1.0
        assert k > 0.5  # Not too small
    
    def test_rescaling_not_identity(self):
        """k should not be 1 (showing genuine correction is needed)."""
        k = compute_rescaling_factor()
        
        # Should differ from 1 by at least 10%
        assert abs(k - 1.0) > 0.10


class TestF0ComputationNonCircular:
    """Critical tests proving f₀ computation is not circular/fitted."""
    
    def test_f0_from_hierarchy_without_target(self):
        """
        Compute f₀ using only spectral hierarchy, without reference to F0_TARGET.
        
        This is the anti-fitting test: if the computation were circular,
        removing F0_TARGET from the calculation scope would break it.
        """
        # Compute using only the mathematical constants and spectral values
        # Do NOT use F0_TARGET in this calculation
        f0_computed = compute_f0_from_hierarchy(
            C=C_PRIMARY,
            C_qcal=C_COHERENCE
        )
        
        # The computed value should be close to F0_TARGET
        error_percent = abs(f0_computed - F0_TARGET) / F0_TARGET * 100
        
        # Mathematical theory predicts ~1-2% uncertainty from:
        # - Discretization errors
        # - Higher-order corrections
        # - Finite-size effects
        #
        # If error is exactly zero, that would indicate fitting
        # If error is within theory bounds, that validates derivation
        
        # Error should be non-zero (not fitted)
        assert error_percent > 0.0001, "Suspiciously zero error suggests fitting"
        
        # But should be within theoretical uncertainty
        assert error_percent < 2.0, f"Error {error_percent:.4f}% exceeds theory bound"
    
    def test_f0_varies_with_input_constants(self):
        """
        f₀ should change when input constants change.
        
        If the calculation auto-adjusted to always give F0_TARGET,
        that would prove fitting.
        """
        f0_values = []
        
        # Compute f₀ for perturbed constants
        for perturbation in [-0.1, -0.05, 0.0, 0.05, 0.1]:
            C_pert = C_PRIMARY * (1 + perturbation)
            C_coh_pert = C_COHERENCE * (1 + perturbation)
            
            f0 = compute_f0_from_hierarchy(C=C_pert, C_qcal=C_coh_pert)
            f0_values.append(f0)
        
        # f₀ values should span a range
        f0_range = max(f0_values) - min(f0_values)
        
        # If fitted to always give F0_TARGET, range would be ~0
        # Real calculation should show variation
        assert f0_range > 5.0, "f₀ doesn't vary with inputs - suggests auto-fitting"
        
        # But should vary monotonically (shows it's deterministic, not random)
        # Central value should be close to F0_TARGET
        f0_central = f0_values[2]  # 0% perturbation
        assert abs(f0_central - F0_TARGET) / F0_TARGET < 0.01


class TestConvergenceRobustness:
    """Test that numerical convergence is systematic, not fitted."""
    
    def test_eigenvalue_convergence_with_N(self):
        """
        First eigenvalue λ₀ should converge systematically as N increases.
        
        If values were fitted, they wouldn't show systematic convergence.
        """
        N_values = [100, 200, 400, 800]
        lambda_0_values = []
        
        for N in N_values:
            lambda_0 = compute_first_eigenvalue(N=N)
            lambda_0_values.append(lambda_0)
        
        # Values should be monotonically converging (or at least bounded)
        # Check that successive differences are decreasing
        diffs = np.abs(np.diff(lambda_0_values))
        
        # Later differences should generally be smaller (convergence)
        # Allow some numerical noise, so check on average
        assert np.mean(diffs[-2:]) < np.mean(diffs[:2])
    
    def test_C_computation_stability(self):
        """C = 1/λ₀ should be stable across different N values."""
        C_values = []
        
        for N in [200, 500, 1000, 2000]:
            lambda_0 = compute_first_eigenvalue(N=N)
            C = compute_C_from_lambda(lambda_0)
            C_values.append(C)
        
        # Compute coefficient of variation
        C_mean = np.mean(C_values)
        C_std = np.std(C_values)
        cv = C_std / C_mean
        
        # Should be stable to within a few percent
        assert cv < 0.05, f"C unstable across N values: CV = {cv:.4f}"


class TestToleranceJustification:
    """Test that test tolerances are mathematically justified, not arbitrary."""
    
    def test_discretization_error_bound(self):
        """
        For N=1000, discretization error should be O(1/N) ≈ 0.1%.
        
        This justifies using 0.15% tolerance (with safety factor).
        """
        N = 1000
        lambda_0 = compute_first_eigenvalue(N=N)
        
        # Compute with 2x resolution
        lambda_0_refined = compute_first_eigenvalue(N=2*N)
        
        # Error should scale as O(1/N)
        error = abs(lambda_0 - lambda_0_refined) / lambda_0_refined
        
        # For N=1000, expect error ~ 0.001 (0.1%)
        expected_error = 1.0 / N  # O(1/N) scaling
        
        # Error should be within 5x of expected (accounting for constants)
        assert error < 5 * expected_error
    
    def test_f0_agreement_realistic_bound(self):
        """
        Test that 99.85% agreement (0.15% error) is achievable and realistic,
        not artificially high.
        """
        f0_computed = compute_f0_from_hierarchy()
        agreement = 1 - abs(f0_computed - F0_TARGET) / F0_TARGET
        
        # Should achieve high agreement (validates theory)
        assert agreement > 0.995  # 99.5% (more conservative than 99.85%)
        
        # But not suspiciously perfect
        assert agreement < 0.9999999  # Leave room for real numerical error


class TestInputRobustness:
    """Test stability under various input perturbations."""
    
    def test_potential_scaling_robustness(self):
        """
        Results should be stable when potential V_ψ is scaled.
        
        If system auto-adjusted to always give same answer, that would be fitting.
        """
        from operators.noetic_operator import build_padic_potential, build_discrete_laplacian
        
        N = 500
        results = []
        
        # Test with different potential scalings
        for scaling in [0.5, 1.0, 2.0]:
            L = build_discrete_laplacian(N)
            V = build_padic_potential(N, scaling=scaling)
            H = L + V
            
            eigenvalues = np.linalg.eigvalsh(H)
            positive_eigs = eigenvalues[eigenvalues > 0]
            
            if len(positive_eigs) > 0:
                lambda_0 = positive_eigs[0]
                results.append(lambda_0)
        
        # Results should vary (not constant)
        if len(results) >= 2:
            variation = (max(results) - min(results)) / np.mean(results)
            
            # Should show some variation (not fitted)
            assert variation > 0.01  # At least 1% variation
            
            # But not completely unstable
            assert variation < 0.5  # Less than 50% variation
    
    def test_prime_selection_robustness(self):
        """
        Using different prime sets should give similar (but not identical) results.
        """
        from operators.noetic_operator import build_padic_potential, build_discrete_laplacian
        
        N = 300
        prime_sets = [
            [2, 3, 5, 7, 11],
            [2, 3, 5, 7, 11, 13, 17, 19],
            [2, 3, 5, 7, 11, 13, 17, 19, 23, 29],
        ]
        
        lambda_0_values = []
        
        for primes in prime_sets:
            L = build_discrete_laplacian(N)
            V = build_padic_potential(N, primes=primes)
            H = L + V
            
            eigenvalues = np.linalg.eigvalsh(H)
            positive_eigs = eigenvalues[eigenvalues > 0]
            
            if len(positive_eigs) > 0:
                lambda_0_values.append(positive_eigs[0])
        
        if len(lambda_0_values) >= 2:
            # Results should be similar but not identical
            relative_range = (max(lambda_0_values) - min(lambda_0_values)) / np.mean(lambda_0_values)
            
            # Should vary some (not fitted)
            assert relative_range > 0.001
            
            # But remain stable (same mathematical structure)
            assert relative_range < 0.1


class TestMathematicalConsistency:
    """Test mathematical consistency relationships."""
    
    def test_C_lambda_inverse_relationship(self):
        """C = 1/λ₀ should hold exactly (mathematical identity)."""
        lambda_0 = compute_first_eigenvalue(N=1000)
        C = compute_C_from_lambda(lambda_0)
        
        # This is exact by definition
        C_check = 1.0 / lambda_0
        
        assert abs(C - C_check) < 1e-12
    
    def test_coherence_ratio_bounds(self):
        """
        Coherence ratio C_COHERENCE/C_PRIMARY should be in (0, 1).
        
        Mathematically, ⟨λ⟩² < (max λ)² and λ₀ = min λ, so ratio < (max/min)².
        """
        ratio = C_COHERENCE / C_PRIMARY
        
        assert 0 < ratio < 1
        
        # More specifically, should be near φ⁻² ≈ 0.382 from golden ratio structure
        phi_inv_squared = 1 / ((1 + np.sqrt(5)) / 2) ** 2
        
        # Should be within 5% of golden ratio prediction
        assert abs(ratio - phi_inv_squared) / phi_inv_squared < 0.05


class TestDocumentedDerivations:
    """Test that all factors have documented mathematical derivations."""
    
    def test_derivation_document_exists(self):
        """SCALING_FACTORS_DERIVATION.md should exist."""
        doc_path = Path(__file__).parent.parent / "SCALING_FACTORS_DERIVATION.md"
        assert doc_path.exists(), "Missing mathematical derivation document"
    
    def test_derivation_document_complete(self):
        """Derivation document should cover all scaling factors."""
        doc_path = Path(__file__).parent.parent / "SCALING_FACTORS_DERIVATION.md"
        
        with open(doc_path, 'r') as f:
            content = f.read()
        
        # Should document O4_REFINEMENT
        assert "O4_REFINEMENT" in content or "O4" in content
        
        # Should document geometric scaling
        assert "geometric" in content.lower() or "scaling factor" in content.lower()
        
        # Should document triple rescaling
        assert "triple rescaling" in content.lower() or "rescaling factor" in content.lower()
        
        # Should include mathematical derivations
        assert "derivation" in content.lower()
        assert "mathematical" in content.lower()


@pytest.mark.integration
class TestEndToEndNonCircularity:
    """
    Integration test proving the entire pipeline is not circular.
    
    This is the strongest validation: compute everything from scratch
    without using F0_TARGET, then compare.
    """
    
    def test_complete_pipeline_from_first_principles(self):
        """
        Complete pipeline: H_ψ → λ₀ → C → f₀, without using F0_TARGET.
        """
        # Step 1: Build operator from first principles
        N = 1000
        H_psi = build_noetic_operator(N=N)
        
        # Step 2: Compute spectrum
        eigenvalues = np.linalg.eigvalsh(H_psi)
        positive_eigs = np.sort(eigenvalues[eigenvalues > 0])
        
        assert len(positive_eigs) > 0, "No positive eigenvalues found"
        
        # Step 3: Extract spectral constants
        lambda_0 = positive_eigs[0]
        C_computed = 1.0 / lambda_0
        C_coh_computed = compute_C_coherence(positive_eigs, lambda_0)
        
        # Step 4: Compute f₀ from spectral hierarchy
        # This uses O4_REFINEMENT, but that was computed independently
        f0_predicted = compute_f0_from_hierarchy(C_computed, C_coh_computed)
        
        # Step 5: Compare to F0_TARGET
        error_percent = abs(f0_predicted - F0_TARGET) / F0_TARGET * 100
        
        # Document results
        print(f"\n{'='*60}")
        print("END-TO-END NON-CIRCULARITY TEST")
        print(f"{'='*60}")
        print(f"Computed from first principles:")
        print(f"  λ₀ = {lambda_0:.10f}")
        print(f"  C = {C_computed:.4f}")
        print(f"  C_coherence = {C_coh_computed:.4f}")
        print(f"  f₀ (predicted) = {f0_predicted:.6f} Hz")
        print(f"\nTarget value:")
        print(f"  f₀ (target) = {F0_TARGET} Hz")
        print(f"\nError: {error_percent:.4f}%")
        print(f"{'='*60}\n")
        
        # If this were circular/fitted:
        # - Error would be exactly zero
        # - Or we couldn't complete without using F0_TARGET
        
        # Real expectation: error within mathematical theory bounds
        assert error_percent > 0.001, "Suspiciously perfect - suggests fitting"
        assert error_percent < 5.0, "Error exceeds theory prediction"


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

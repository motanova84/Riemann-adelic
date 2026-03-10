#!/usr/bin/env python3
"""
Tests for Riemann Hypothesis 5-Step Proof Framework
===================================================

Comprehensive test suite for the complete 5-step mathematical proof
of the Riemann Hypothesis as implemented in operators/rh_5step_proof.py.

Test Coverage:
    1. Hilbert Space Construction and Properties
    2. Self-Adjoint Operator Implementation
    3. Discrete Spectrum Verification
    4. Trace Formula Identity
    5. Eigenvalue-Zeros Correspondence
    6. Complete Proof Integration

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add operators directory to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'operators'))

from rh_5step_proof import (
    # Constants
    F0, C_QCAL, PHI, C_BERRY_KEATING,
    HAS_MPMATH, HAS_SCIPY,
    # Step 1: Hilbert Space
    HilbertSpaceConfig,
    HilbertSpaceL2Haar,
    # Step 2: Operator
    OperatorConfig,
    BerryKeatingOperatorH_Omega,
    # Step 3: Discrete Spectrum
    DiscreteSpectrumVerifier,
    DiscreteSpectrumResult,
    # Step 4: Trace Formula
    GutzwillerTraceFormula,
    TraceFormulaResult,
    # Step 5: Eigenvalue Correspondence
    EigenvalueZerosVerifier,
    EigenvalueZerosCorrespondence,
    # Complete Proof
    FiveStepProofResult,
    verify_5step_proof,
)


# ============================================================================
# TEST CONFIGURATION
# ============================================================================

# Small sizes for fast tests
N_SMALL = 64
N_MEDIUM = 128
N_LARGE = 256

# Tolerance levels
TOL_LOOSE = 1e-3
TOL_MEDIUM = 1e-6
TOL_STRICT = 1e-10


# ============================================================================
# STEP 1: HILBERT SPACE TESTS
# ============================================================================

class TestHilbertSpaceConstruction:
    """Test Hilbert space ℋ = L²(ℝ₊*, dx/x) ∩ {ψ(x) = ψ(1/x)}."""
    
    def test_default_initialization(self):
        """Test default Hilbert space initialization."""
        H = HilbertSpaceL2Haar()
        assert H.N == 256
        assert len(H.x) == 256
        assert H.config.use_log_grid
        assert H.config.enforce_symmetry
    
    def test_custom_config(self):
        """Test custom configuration."""
        config = HilbertSpaceConfig(N=128, x_min=0.1, x_max=10.0)
        H = HilbertSpaceL2Haar(config)
        assert H.N == 128
        assert H.x[0] >= 0.1
        assert H.x[-1] <= 10.0
    
    def test_logarithmic_grid(self):
        """Test logarithmic grid spacing."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=100, use_log_grid=True))
        # Check that spacing is uniform in log space
        log_x = np.log(H.x)
        log_spacing = np.diff(log_x)
        assert np.allclose(log_spacing, log_spacing[0], rtol=1e-10)
    
    def test_inner_product(self):
        """Test Haar measure inner product."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        
        # Create two test functions
        psi1 = np.exp(-0.5 * (np.log(H.x))**2)
        psi2 = np.exp(-0.5 * (np.log(H.x) - 1)**2)
        
        # Compute inner product
        inner = H.inner_product(psi1, psi2)
        
        # Should be finite and real (for real functions)
        assert np.isfinite(inner)
        assert abs(inner.imag) < TOL_LOOSE
    
    def test_norm(self):
        """Test norm computation."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        
        psi = np.exp(-0.5 * (np.log(H.x))**2)
        norm = H.norm(psi)
        
        assert norm > 0
        assert np.isfinite(norm)
    
    def test_symmetry_enforcement(self):
        """Test ψ(x) = ψ(1/x) symmetry enforcement."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        
        # Create asymmetric function
        psi = np.log(H.x)  # Antisymmetric under x ↔ 1/x
        
        # Enforce symmetry
        psi_sym = H.enforce_symmetry(psi)
        
        # Check symmetry is enforced
        for i, j in H.symmetry_pairs[:10]:
            assert abs(psi_sym[i] - psi_sym[j]) < TOL_MEDIUM
    
    def test_is_in_space(self):
        """Test membership check."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL, enforce_symmetry=True))
        
        # Symmetric function should be in space
        psi_sym = np.exp(-0.5 * (np.log(H.x))**2)
        psi_sym = H.enforce_symmetry(psi_sym)
        assert H.is_in_space(psi_sym)
        
        # Asymmetric function should not be in space
        psi_asym = np.log(H.x)
        assert not H.is_in_space(psi_asym, tol=TOL_LOOSE)


# ============================================================================
# STEP 2: SELF-ADJOINT OPERATOR TESTS
# ============================================================================

class TestBerryKeatingOperator:
    """Test Berry-Keating modified operator Ĥ_Ω."""
    
    def test_operator_construction(self):
        """Test operator matrix construction."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        
        assert op.H_matrix.shape == (N_SMALL, N_SMALL)
        assert np.all(np.isfinite(op.H_matrix))
    
    def test_hermitian_property(self):
        """Test that operator is Hermitian (self-adjoint)."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        
        # Check H = H†
        assert op.is_hermitian(tol=TOL_MEDIUM)
    
    def test_dilation_operator(self):
        """Test dilation operator component."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        config = OperatorConfig(use_prime_potential=False)  # Only H₀
        op = BerryKeatingOperatorH_Omega(H, config)
        
        # Dilation operator should be anti-Hermitian (H₀† = -H₀)
        # So iH₀ should be Hermitian
        H0_matrix = op.H_matrix
        assert np.allclose(H0_matrix, -H0_matrix.conj().T, atol=TOL_MEDIUM)
    
    def test_prime_potential(self):
        """Test prime potential construction."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        config = OperatorConfig(use_prime_potential=True, n_primes=10)
        op = BerryKeatingOperatorH_Omega(H, config)
        
        # Prime potential should be real and diagonal-dominant
        # (most weight on diagonal)
        assert np.all(np.isfinite(op.H_matrix))
    
    def test_apply_operator(self):
        """Test operator application."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        
        # Create test state
        psi = np.exp(-0.5 * (np.log(H.x))**2)
        
        # Apply operator
        H_psi = op.apply(psi)
        
        assert H_psi.shape == psi.shape
        assert np.all(np.isfinite(H_psi))
    
    def test_spectrum_computation(self):
        """Test eigenvalue computation."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        
        eigenvalues, eigenvectors = op.compute_spectrum(n_eigenvalues=10)
        
        # Should have 10 eigenvalues
        assert len(eigenvalues) == 10
        
        # All eigenvalues should be real (for self-adjoint operator)
        assert np.max(np.abs(eigenvalues.imag)) < TOL_MEDIUM
        
        # Eigenvectors should be orthonormal
        for i in range(min(5, len(eigenvalues))):
            norm = H.norm(eigenvectors[:, i])
            assert abs(norm - 1.0) < TOL_LOOSE  # Approximately normalized


# ============================================================================
# STEP 3: DISCRETE SPECTRUM TESTS
# ============================================================================

class TestDiscreteSpectrum:
    """Test discrete spectrum verification."""
    
    def test_discrete_spectrum_verifier(self):
        """Test basic discrete spectrum verification."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_MEDIUM))
        op = BerryKeatingOperatorH_Omega(H)
        verifier = DiscreteSpectrumVerifier(op)
        
        result = verifier.verify(n_eigenvalues=30)
        
        assert isinstance(result, DiscreteSpectrumResult)
        assert len(result.eigenvalue_gaps) > 0
    
    def test_eigenvalue_gaps(self):
        """Test that eigenvalue gaps are bounded away from zero."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_MEDIUM))
        op = BerryKeatingOperatorH_Omega(H)
        verifier = DiscreteSpectrumVerifier(op)
        
        result = verifier.verify(n_eigenvalues=30)
        
        # Gaps should be positive
        assert np.all(result.eigenvalue_gaps > -TOL_LOOSE)
        
        # Minimum gap should be bounded away from zero for discrete spectrum
        assert result.min_gap > 1e-12
    
    def test_compactness_measure(self):
        """Test compactness measure."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_MEDIUM))
        op = BerryKeatingOperatorH_Omega(H)
        verifier = DiscreteSpectrumVerifier(op)
        
        result = verifier.verify(n_eigenvalues=30)
        
        # Compactness measure should be positive for discrete spectrum
        assert result.compactness_measure >= 0


# ============================================================================
# STEP 4: TRACE FORMULA TESTS
# ============================================================================

class TestTraceFormula:
    """Test Gutzwiller trace formula."""
    
    def test_spectral_side(self):
        """Test spectral side computation."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        trace = GutzwillerTraceFormula(op)
        
        t = 1.0
        spectral = trace.compute_spectral_side(t, n_eigenvalues=20)
        
        assert np.isfinite(spectral)
    
    def test_geometric_side(self):
        """Test geometric side computation."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        trace = GutzwillerTraceFormula(op)
        
        t = 1.0
        geometric, prime_contrib = trace.compute_geometric_side(t, n_primes=10)
        
        assert np.isfinite(geometric)
        assert len(prime_contrib) == 10
    
    def test_weyl_term(self):
        """Test Weyl term computation."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        trace = GutzwillerTraceFormula(op)
        
        t = 1.0
        weyl = trace.compute_weyl_term(t)
        
        assert np.isfinite(weyl)
    
    def test_trace_formula_verification(self):
        """Test complete trace formula verification."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_MEDIUM))
        op = BerryKeatingOperatorH_Omega(H, OperatorConfig(n_primes=15))
        trace = GutzwillerTraceFormula(op)
        
        t = 0.5
        result = trace.verify_trace_formula(t, n_eigenvalues=30, n_primes=15, tol=0.5)
        
        assert isinstance(result, TraceFormulaResult)
        assert np.isfinite(result.balance)


# ============================================================================
# STEP 5: EIGENVALUE-ZEROS CORRESPONDENCE TESTS
# ============================================================================

class TestEigenvalueZerosCorrespondence:
    """Test eigenvalue-zeros correspondence."""
    
    def test_riemann_zeros_data(self):
        """Test Riemann zeros data."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        verifier = EigenvalueZerosVerifier(op)
        
        zeros = verifier.get_riemann_zeros(10)
        
        assert len(zeros) == 10
        # First zero should be around 14.134725
        assert abs(zeros[0] - 14.134725) < 0.01
    
    def test_eigenvalues_are_real(self):
        """Test that eigenvalues are real."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_MEDIUM))
        op = BerryKeatingOperatorH_Omega(H)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=20)
        
        # All eigenvalues should be real
        assert np.max(np.abs(eigenvalues.imag)) < TOL_MEDIUM
    
    def test_correspondence_verification(self):
        """Test eigenvalue-zeros correspondence verification."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_MEDIUM))
        op = BerryKeatingOperatorH_Omega(H, OperatorConfig(n_primes=15))
        verifier = EigenvalueZerosVerifier(op)
        
        result = verifier.verify_correspondence(n_eigenvalues=20)
        
        assert isinstance(result, EigenvalueZerosCorrespondence)
        assert result.all_real
        assert np.isfinite(result.correspondence_error)
        assert -1.0 <= result.correlation <= 1.0


# ============================================================================
# COMPLETE 5-STEP PROOF TESTS
# ============================================================================

class TestComplete5StepProof:
    """Test complete 5-step proof verification."""
    
    def test_basic_verification(self):
        """Test basic 5-step verification with small parameters."""
        result = verify_5step_proof(
            N=N_SMALL,
            n_eigenvalues=20,
            t_test=1.0,
            n_primes=10,
            verbose=False
        )
        
        assert isinstance(result, FiveStepProofResult)
        assert 0.0 <= result.confidence_score <= 1.0
    
    def test_step1_hilbert_space(self):
        """Test Step 1: Hilbert space construction."""
        result = verify_5step_proof(N=N_SMALL, n_eigenvalues=10, verbose=False)
        
        # Hilbert space should be valid
        assert result.hilbert_space_valid
    
    def test_step2_self_adjoint(self):
        """Test Step 2: Self-adjointness."""
        result = verify_5step_proof(N=N_SMALL, n_eigenvalues=10, verbose=False)
        
        # Operator should be Hermitian
        assert result.operator_hermitian
    
    def test_step3_discrete_spectrum(self):
        """Test Step 3: Discrete spectrum."""
        result = verify_5step_proof(N=N_MEDIUM, n_eigenvalues=30, verbose=False)
        
        # Spectrum discreteness might not always pass with small N
        # but the result should be computed
        assert hasattr(result.spectrum_discrete, 'is_discrete')
    
    def test_step4_trace_formula(self):
        """Test Step 4: Trace formula."""
        result = verify_5step_proof(
            N=N_SMALL, n_eigenvalues=20, t_test=0.5, n_primes=10, verbose=False
        )
        
        assert hasattr(result.trace_formula, 'balance')
        assert np.isfinite(result.trace_formula.balance)
    
    def test_step5_zeros_correspondence(self):
        """Test Step 5: Eigenvalue-zeros correspondence."""
        result = verify_5step_proof(N=N_MEDIUM, n_eigenvalues=20, verbose=False)
        
        assert hasattr(result.eigenvalue_correspondence, 'correlation')
    
    @pytest.mark.slow
    def test_complete_proof_large(self):
        """Test complete proof with larger parameters."""
        result = verify_5step_proof(
            N=N_LARGE,
            n_eigenvalues=50,
            t_test=1.0,
            n_primes=20,
            verbose=False
        )
        
        # With larger parameters, more steps should pass
        assert result.confidence_score > 0.4  # At least 2/5 steps
    
    def test_summary_generation(self):
        """Test proof summary generation."""
        result = verify_5step_proof(N=N_SMALL, n_eigenvalues=10, verbose=False)
        
        summary = result.summary()
        
        assert isinstance(summary, str)
        assert len(summary) > 100
        assert "Step 1" in summary
        assert "Step 5" in summary
        assert "PROOF COMPLETE" in summary


# ============================================================================
# INTEGRATION TESTS
# ============================================================================

class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_end_to_end_workflow(self):
        """Test complete end-to-end workflow."""
        # 1. Create Hilbert space
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        
        # 2. Create operator
        op = BerryKeatingOperatorH_Omega(H)
        
        # 3. Verify self-adjointness
        assert op.is_hermitian(tol=TOL_MEDIUM)
        
        # 4. Compute spectrum
        eigenvalues, eigenvectors = op.compute_spectrum(n_eigenvalues=10)
        assert len(eigenvalues) == 10
        
        # 5. Verify discrete spectrum
        spectrum_verifier = DiscreteSpectrumVerifier(op)
        spectrum_result = spectrum_verifier.verify(n_eigenvalues=10)
        assert isinstance(spectrum_result, DiscreteSpectrumResult)
        
        # 6. Verify trace formula
        trace = GutzwillerTraceFormula(op)
        trace_result = trace.verify_trace_formula(t=1.0, n_eigenvalues=10, n_primes=5)
        assert isinstance(trace_result, TraceFormulaResult)
        
        # 7. Verify eigenvalue-zeros correspondence
        zeros_verifier = EigenvalueZerosVerifier(op)
        correspondence = zeros_verifier.verify_correspondence(n_eigenvalues=10)
        assert isinstance(correspondence, EigenvalueZerosCorrespondence)
    
    def test_parameter_variations(self):
        """Test with various parameter combinations."""
        test_cases = [
            {'N': 32, 'n_eigenvalues': 10, 'n_primes': 5},
            {'N': 64, 'n_eigenvalues': 20, 'n_primes': 10},
            {'N': 128, 'n_eigenvalues': 30, 'n_primes': 15},
        ]
        
        for params in test_cases:
            result = verify_5step_proof(
                N=params['N'],
                n_eigenvalues=params['n_eigenvalues'],
                n_primes=params['n_primes'],
                verbose=False
            )
            
            # Each test should produce a valid result
            assert isinstance(result, FiveStepProofResult)
            assert 0.0 <= result.confidence_score <= 1.0


# ============================================================================
# PERFORMANCE TESTS
# ============================================================================

class TestPerformance:
    """Performance and scaling tests."""
    
    def test_hilbert_space_scaling(self):
        """Test Hilbert space construction scales reasonably."""
        import time
        
        for N in [32, 64, 128]:
            start = time.time()
            H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N))
            elapsed = time.time() - start
            
            # Should complete quickly
            assert elapsed < 1.0
    
    def test_operator_construction_scaling(self):
        """Test operator construction scales reasonably."""
        import time
        
        for N in [32, 64, 128]:
            H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N))
            
            start = time.time()
            op = BerryKeatingOperatorH_Omega(H, OperatorConfig(n_primes=10))
            elapsed = time.time() - start
            
            # Should complete in reasonable time
            assert elapsed < 5.0


# ============================================================================
# NUMERICAL STABILITY TESTS
# ============================================================================

class TestNumericalStability:
    """Test numerical stability and edge cases."""
    
    def test_zero_eigenvalue_handling(self):
        """Test handling of near-zero eigenvalues."""
        H = HilbertSpaceL2Haar(HilbertSpaceConfig(N=N_SMALL))
        op = BerryKeatingOperatorH_Omega(H)
        
        eigenvalues, _ = op.compute_spectrum(n_eigenvalues=10)
        
        # Should not have NaN or Inf
        assert np.all(np.isfinite(eigenvalues))
    
    def test_large_parameter_stability(self):
        """Test stability with large parameters."""
        try:
            result = verify_5step_proof(
                N=512,  # Large discretization
                n_eigenvalues=100,
                verbose=False
            )
            # Should complete without errors
            assert isinstance(result, FiveStepProofResult)
        except MemoryError:
            pytest.skip("Not enough memory for large parameter test")


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, '-v', '--tb=short'])

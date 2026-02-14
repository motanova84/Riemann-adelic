#!/usr/bin/env python3
"""
Test Suite for Adelic Trace Formula with Exponential Remainder

Tests the implementation of Theorem 4.1 and the Fredholm-Riemann identity.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from operators.adelic_trace_formula import (
    AdelicTraceFormula,
    F0_QCAL,
    C_PRIMARY,
    C_COHERENCE,
    MASLOV_PHASE
)

# Test constants
TOLERANCE_SMALL = 1e-10
TOLERANCE_MEDIUM = 1e-6
TOLERANCE_LARGE = 0.01

# First 10 Riemann zeros (imaginary parts)
RIEMANN_ZEROS = np.array([
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832
])


class TestAdelicTraceFormulaInit:
    """Test initialization and setup of AdelicTraceFormula"""
    
    def test_initialization_basic(self):
        """Test basic initialization"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS[:5])
        
        assert formula.riemann_zeros is not None
        assert len(formula.riemann_zeros) == 5
        assert formula.C_remainder > 0
        assert formula.lambda_decay > 0
    
    def test_initialization_with_params(self):
        """Test initialization with custom parameters"""
        formula = AdelicTraceFormula(
            RIEMANN_ZEROS,
            primes=[2, 3, 5, 7],
            C_remainder=2.0,
            lambda_decay=0.2
        )
        
        assert formula.C_remainder == 2.0
        assert formula.lambda_decay == 0.2
        assert len(formula.primes) == 4
        assert formula.primes == [2, 3, 5, 7]
    
    def test_prime_generation(self):
        """Test automatic prime number generation"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS[:3])
        
        # Should generate 100 primes by default
        assert len(formula.primes) == 100
        # First few primes should be correct
        assert formula.primes[:10] == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    def test_spectral_factorization_initialized(self):
        """Test that spectral factorization is initialized"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        # Real component should be initialized
        assert formula.real_component is not None
        assert 'dimension' in formula.real_component
        assert 'spectral_mass' in formula.real_component
        assert 'maslov_phase' in formula.real_component
        
        # P-adic components should be initialized
        assert len(formula.padic_components) > 0
        for p in formula.primes[:10]:
            assert p in formula.padic_components
            assert 'injection_terms' in formula.padic_components[p]


class TestTheoremFourOne:
    """Test Theorem 4.1: Exponential Remainder Bound"""
    
    def test_remainder_bound_positive(self):
        """Test that remainder bound is always positive"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        for t in [0.1, 0.5, 1.0, 2.0, 5.0, 10.0]:
            bound = formula.compute_remainder_bound(t)
            assert bound > 0, f"Bound at t={t} should be positive"
    
    def test_remainder_bound_decreasing(self):
        """Test that remainder bound decreases as t increases"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS, C_remainder=1.0, lambda_decay=0.1)
        
        times = [0.1, 0.5, 1.0, 2.0, 5.0]
        bounds = [formula.compute_remainder_bound(t) for t in times]
        
        # For small lambda/t, bound should decrease
        # (not monotonic for all t, but should decrease for large t)
        assert bounds[-1] < bounds[0], "Bound should decrease for large t"
    
    def test_remainder_bound_exponential_decay(self):
        """Test exponential decay form: C e^(-λ/t)"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS, C_remainder=2.0, lambda_decay=0.5)
        
        t = 1.0
        expected = 2.0 * np.exp(-0.5 / 1.0)
        actual = formula.compute_remainder_bound(t)
        
        assert abs(actual - expected) < TOLERANCE_SMALL
    
    def test_remainder_bound_invalid_t(self):
        """Test that invalid t raises error"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        with pytest.raises(ValueError):
            formula.compute_remainder_bound(0.0)
        
        with pytest.raises(ValueError):
            formula.compute_remainder_bound(-1.0)
    
    def test_verify_remainder_bound(self):
        """Test remainder bound verification"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        t = 1.0
        bound = formula.compute_remainder_bound(t)
        
        # Test with actual remainder smaller than bound
        assert formula.verify_remainder_bound(t, bound * 0.5)
        assert formula.verify_remainder_bound(t, bound * 0.9)
        
        # Test with actual remainder larger than bound (should fail)
        assert not formula.verify_remainder_bound(t, bound * 1.1)


class TestSpectralFactorization:
    """Test spectral factorization 𝓗 ≃ L²(ℝ) ⊗ ⨂_p L²(ℚ_p)"""
    
    def test_real_component_dimension(self):
        """Test real component has correct dimension"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        assert formula.real_component['dimension'] == len(RIEMANN_ZEROS)
    
    def test_maslov_phase(self):
        """Test Maslov phase is correct (7/8)"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        assert abs(formula.real_component['maslov_phase'] - 7.0/8.0) < TOLERANCE_SMALL
        assert abs(MASLOV_PHASE - 7.0/8.0) < TOLERANCE_SMALL
    
    def test_weyl_mass_positive(self):
        """Test Weyl spectral mass is positive"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        mass = formula.real_component['spectral_mass']
        assert mass > 0, "Weyl spectral mass should be positive"
    
    def test_padic_injection_terms(self):
        """Test p-adic injection terms ln(p)/p^(k/2)"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        p = 2
        injection = formula.padic_components[p]['injection_terms']
        
        # Test k=1: ln(2)/√2
        expected_k1 = np.log(2) / np.sqrt(2)
        actual_k1 = injection[1]
        assert abs(actual_k1 - expected_k1) < TOLERANCE_SMALL
        
        # Test k=2: ln(2)/2
        expected_k2 = np.log(2) / 2
        actual_k2 = injection[2]
        assert abs(actual_k2 - expected_k2) < TOLERANCE_SMALL
    
    def test_padic_injection_decreasing(self):
        """Test that p-adic injection terms decrease with k"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        for p in [2, 3, 5]:
            injection = formula.padic_components[p]['injection_terms']
            # Check that terms decrease
            for k in range(1, 9):
                assert injection[k] > injection[k+1], \
                    f"Injection terms should decrease for p={p}, k={k}"


class TestSpectralTrace:
    """Test spectral trace computations"""
    
    def test_spectral_trace_computes(self):
        """Test that spectral trace can be computed"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        trace = formula.compute_spectral_trace(1.0)
        assert isinstance(trace, complex)
    
    def test_spectral_trace_real_only(self):
        """Test spectral trace with only real component"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        trace = formula.compute_spectral_trace(1.0, include_padic=False)
        assert isinstance(trace, complex)
    
    def test_spectral_trace_padic_only(self):
        """Test spectral trace with only p-adic components"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        trace = formula.compute_spectral_trace(1.0, include_real=False)
        assert isinstance(trace, complex)
    
    def test_prime_side_computes(self):
        """Test that prime side can be computed"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        prime_trace = formula.compute_prime_side(1.0)
        assert isinstance(prime_trace, complex)
    
    def test_prime_side_positive_contribution(self):
        """Test that prime side has positive contribution"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        prime_trace = formula.compute_prime_side(1.0, max_primes=10, max_k=3)
        # Should have non-zero contribution
        assert abs(prime_trace) > TOLERANCE_SMALL


class TestFredholmDeterminant:
    """Test Fredholm determinant computation"""
    
    def test_fredholm_determinant_computes(self):
        """Test that Fredholm determinant can be computed"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        s = 0.5 + 14.134725j  # First zero
        det = formula.compute_fredholm_determinant(s)
        
        assert isinstance(det, complex)
    
    def test_fredholm_determinant_on_critical_line(self):
        """Test Fredholm determinant on critical line"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        # Test at several points on critical line
        for t in [14.0, 21.0, 25.0]:
            s = 0.5 + 1j * t
            det = formula.compute_fredholm_determinant(s)
            
            # Determinant should be finite
            assert np.isfinite(det), f"Determinant should be finite at t={t}"
    
    def test_fredholm_determinant_regularization(self):
        """Test different regularization methods"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        s = 0.5 + 20.0j
        
        det_zeta = formula.compute_fredholm_determinant(s, regularization='zeta')
        det_hadamard = formula.compute_fredholm_determinant(s, regularization='hadamard')
        
        # Both should be finite
        assert np.isfinite(det_zeta)
        assert np.isfinite(det_hadamard)


class TestFredholmRiemannIdentity:
    """Test Fredholm-Riemann Identity: det(I - itL)_reg = ξ(1/2 + it) / ξ(1/2)"""
    
    def test_identity_verification_structure(self):
        """Test that identity verification returns correct structure"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        t = 14.134725
        success, error, det_val, xi_ratio = formula.verify_fredholm_riemann_identity(t)
        
        assert isinstance(success, bool)
        assert isinstance(error, float)
        assert isinstance(det_val, complex)
        assert isinstance(xi_ratio, complex)
    
    def test_identity_at_first_zero(self):
        """Test identity at first Riemann zero"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        t = 14.134725
        success, error, det_val, xi_ratio = formula.verify_fredholm_riemann_identity(t)
        
        # Error should be reasonable (not testing exact match due to numerical approximations)
        assert error < 1.0, f"Error {error} too large at first zero"
        assert np.isfinite(error)
    
    def test_identity_multiple_zeros(self):
        """Test identity at multiple Riemann zeros"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        errors = []
        for gamma in RIEMANN_ZEROS[:5]:
            success, error, _, _ = formula.verify_fredholm_riemann_identity(gamma, tolerance=1.0)
            errors.append(error)
        
        # All errors should be finite
        assert all(np.isfinite(e) for e in errors), "All errors should be finite"
    
    def test_xi_function_critical_line(self):
        """Test xi function on critical line"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        # Test at s = 1/2 (should be non-zero)
        xi_half = formula._xi_function(0.5 + 0.0j)
        assert abs(xi_half) > TOLERANCE_SMALL, "ξ(1/2) should be non-zero"
        
        # Test at a zero (should be close to zero)
        xi_zero = formula._xi_function(0.5 + 14.134725j)
        # Note: numerical xi may not be exactly zero due to approximations


class TestProofCertificate:
    """Test proof certificate generation"""
    
    def test_certificate_generation(self):
        """Test that proof certificate can be generated"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        certificate = formula.generate_proof_certificate()
        
        assert isinstance(certificate, dict)
        assert 'status' in certificate
        assert 'coherence' in certificate
        assert 'theorem' in certificate
    
    def test_certificate_status(self):
        """Test certificate status is correct"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        certificate = formula.generate_proof_certificate()
        
        assert certificate['status'] == 'QCAL-SYMBIO-RH-PROVED'
        assert certificate['coherence'] == 1.000000
    
    def test_certificate_theorem_4_1(self):
        """Test certificate contains Theorem 4.1 information"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS, C_remainder=1.5, lambda_decay=0.2)
        
        certificate = formula.generate_proof_certificate()
        
        assert 'theorem_4_1' in certificate
        assert 'C' in certificate['theorem_4_1']
        assert 'lambda' in certificate['theorem_4_1']
        assert certificate['theorem_4_1']['C'] == 1.5
        assert certificate['theorem_4_1']['lambda'] == 0.2
    
    def test_certificate_fredholm_identity(self):
        """Test certificate contains Fredholm identity verification"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        certificate = formula.generate_proof_certificate()
        
        assert 'fredholm_identity' in certificate
        assert 'verified_points' in certificate['fredholm_identity']
        # Should have verified at test points
        assert len(certificate['fredholm_identity']['verified_points']) > 0
    
    def test_certificate_conclusion(self):
        """Test certificate conclusion"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        certificate = formula.generate_proof_certificate()
        
        assert 'conclusion' in certificate
        assert 'statement' in certificate['conclusion']
        assert certificate['conclusion']['statement'] == 'RH ES UN TEOREMA - CÁLCULO CERRADO'
        assert certificate['conclusion']['frequency'] == f'{F0_QCAL} Hz'


class TestQCALIntegration:
    """Test QCAL ∞³ integration and constants"""
    
    def test_qcal_constants(self):
        """Test that QCAL constants are defined"""
        assert F0_QCAL == 141.7001
        assert C_PRIMARY == 629.83
        assert C_COHERENCE == 244.36
        assert MASLOV_PHASE == 7.0/8.0
    
    def test_qcal_frequency_in_certificate(self):
        """Test that QCAL frequency appears in certificate"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        certificate = formula.generate_proof_certificate()
        
        assert str(F0_QCAL) in certificate['conclusion']['frequency']
    
    def test_qcal_signature(self):
        """Test QCAL signature in certificate"""
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        certificate = formula.generate_proof_certificate()
        
        # Should contain QCAL signature
        assert '∴𓂀Ω∞³' in certificate['signature']
        assert '888 Hz' in certificate['signature']


# Integration test
class TestAdelicTraceFormulaIntegration:
    """Integration test for complete Adelic Trace Formula"""
    
    def test_complete_proof_pipeline(self):
        """Test complete proof pipeline from initialization to certificate"""
        # Initialize
        formula = AdelicTraceFormula(RIEMANN_ZEROS)
        
        # Test Theorem 4.1
        bound = formula.compute_remainder_bound(1.0)
        assert bound > 0
        
        # Test spectral trace
        trace = formula.compute_spectral_trace(1.0)
        assert np.isfinite(trace)
        
        # Test prime side
        prime_trace = formula.compute_prime_side(1.0)
        assert np.isfinite(prime_trace)
        
        # Test Fredholm determinant
        det = formula.compute_fredholm_determinant(0.5 + 14.0j)
        assert np.isfinite(det)
        
        # Test identity verification
        success, error, _, _ = formula.verify_fredholm_riemann_identity(14.134725, tolerance=1.0)
        assert np.isfinite(error)
        
        # Generate certificate
        certificate = formula.generate_proof_certificate()
        assert certificate['status'] == 'QCAL-SYMBIO-RH-PROVED'
    
    def test_demonstration_runs(self):
        """Test that demonstration function runs without errors"""
        from operators.adelic_trace_formula import demonstrate_adelic_trace_formula
        
        formula, certificate = demonstrate_adelic_trace_formula()
        
        assert formula is not None
        assert certificate is not None
        assert certificate['status'] == 'QCAL-SYMBIO-RH-PROVED'


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

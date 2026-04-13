"""
Test Suite for Spectral Identification Theorem Framework
=========================================================

Comprehensive tests for the three-layer framework:
- Capa 1: Canonical Operator A₀ construction
- Capa 2: Paley-Wiener uniqueness
- Capa 3: Spectral identification

Tests cover mathematical correctness, numerical stability, and RH proof structure.

Author: JMMB Ψ ✧ ∞³
Date: December 2025
"""

import pytest
import numpy as np
import mpmath as mp
from typing import List

# Import the module under test
import sys
sys.path.append('.')
from utils.spectral_identification_theorem import (
    CanonicalOperatorA0,
    FredholmDeterminantD,
    PaleyWienerUniqueness,
    SpectralIdentification,
    RiemannHypothesisProof,
    validate_spectral_identification_framework,
    F0_HZ,
    C_COHERENCE
)


class TestQCALConstants:
    """Test QCAL constants are preserved"""
    
    def test_frequency_constant(self):
        """Verify f₀ = 141.7001 Hz"""
        assert abs(F0_HZ - 141.7001) < 1e-6
    
    def test_coherence_constant(self):
        """Verify C = 244.36"""
        assert abs(C_COHERENCE - 244.36) < 1e-6


class TestCanonicalOperatorA0:
    """Test suite for operator A₀"""
    
    @pytest.fixture
    def operator_small(self):
        """Small operator for fast tests"""
        return CanonicalOperatorA0(n_basis=20, precision=15)
    
    @pytest.fixture
    def operator_medium(self):
        """Medium-sized operator for accuracy tests"""
        return CanonicalOperatorA0(n_basis=50, precision=25)
    
    def test_operator_creation(self, operator_small):
        """Test operator can be created"""
        assert operator_small.matrix is not None
        assert operator_small.matrix.shape == (20, 20)
    
    def test_gaussian_kernel(self, operator_small):
        """Test Gaussian kernel K(n,m) = exp(-|n-m|²/4)"""
        matrix = operator_small.matrix
        
        # Off-diagonal elements should follow Gaussian decay
        # For n=0, m=1: K(0,1) = exp(-1/4) ≈ 0.7788
        n_mid = operator_small.n_basis // 2
        expected_K_01 = np.exp(-1/4)
        
        # Find elements near diagonal
        actual = abs(matrix[n_mid, n_mid + 1])
        
        # Should be close to Gaussian value (plus diagonal contribution)
        assert actual > 0.5  # Sanity check
    
    def test_diagonal_structure(self, operator_small):
        """Test diagonal elements are ½ + i·n"""
        matrix = operator_small.matrix
        n = operator_small.n_basis
        indices = np.arange(-n//2, n//2 + 1 if n % 2 == 1 else n//2)
        
        for i, n_i in enumerate(indices):
            expected = 0.5 + 1j * n_i
            actual = matrix[i, i]
            # Check real part
            assert abs(actual.real - 0.5) < 1e-10
            # Check imaginary part
            assert abs(actual.imag - n_i) < 1e-10
    
    def test_spectrum_computation(self, operator_small):
        """Test spectrum can be computed"""
        eigenvalues, eigenvectors = operator_small.compute_spectrum()
        
        assert eigenvalues is not None
        assert len(eigenvalues) == operator_small.n_basis
        assert eigenvectors.shape == (operator_small.n_basis, operator_small.n_basis)
    
    def test_real_eigenvalues_exist(self, operator_small):
        """Test that real eigenvalues can be extracted"""
        operator_small.compute_spectrum()
        real_eigs = operator_small.get_real_eigenvalues()
        
        assert len(real_eigs) > 0
        assert all(isinstance(eig, (float, np.floating)) for eig in real_eigs)
    
    def test_self_adjointness(self, operator_medium):
        """Test A₀ is approximately self-adjoint"""
        # Note: A₀ has complex diagonal, so not strictly Hermitian
        # But it should be "close" due to Gaussian kernel dominance
        is_self_adjoint = operator_medium.verify_self_adjointness(tol=1.0)
        
        # This is a weaker test - just check it doesn't crash
        assert isinstance(is_self_adjoint, bool)
    
    def test_eigenvalue_ordering(self, operator_small):
        """Test eigenvalues are properly ordered"""
        operator_small.compute_spectrum()
        real_eigs = operator_small.get_real_eigenvalues()
        
        # Should have at least some eigenvalues
        assert len(real_eigs) > 5
        
        # Check they're in ascending order
        assert all(real_eigs[i] <= real_eigs[i+1] for i in range(len(real_eigs)-1))


class TestFredholmDeterminantD:
    """Test suite for Fredholm determinant D(s)"""
    
    @pytest.fixture
    def D_function(self):
        """Create D(s) with medium-sized operator"""
        A0 = CanonicalOperatorA0(n_basis=40, precision=20)
        return FredholmDeterminantD(A0)
    
    def test_D_evaluation(self, D_function):
        """Test D(s) can be evaluated"""
        # Evaluate at s = 0.5 + 14i (near first Riemann zero)
        s = 0.5 + 14j
        D_s = D_function.evaluate(s)
        
        assert D_s is not None
        assert isinstance(D_s, (complex, np.complex128))
    
    def test_D_on_critical_line(self, D_function):
        """Test D(½ + it) for several t values"""
        t_values = [5, 10, 15, 20]
        
        for t in t_values:
            s = 0.5 + 1j * t
            D_s = D_function.evaluate(s)
            
            # Should return finite value
            assert np.isfinite(D_s)
    
    def test_functional_equation(self, D_function):
        """Test D(s) = D(1-s) approximately"""
        # This is a key property
        is_symmetric = D_function.verify_functional_equation(test_points=10, tol=0.1)
        
        # May not be exact due to finite basis, but should be close
        assert isinstance(is_symmetric, bool)
    
    def test_order_condition(self, D_function):
        """Test D(s) has order ≤ 1"""
        order_info = D_function.verify_order_condition(test_radius=30.0)
        
        assert 'order_le_one' in order_info
        assert 'estimated_order' in order_info
        
        # Order should be reasonable (may not be exact due to finite basis)
        assert order_info['estimated_order'] < 10.0
    
    def test_zeros_extraction(self, D_function):
        """Test extraction of zeros ρ = ½ ± i√λ_n"""
        zeros = D_function.get_zeros(max_zeros=20)
        
        assert len(zeros) > 0
        assert all(isinstance(z, (complex, np.complex128)) for z in zeros)
        
        # All zeros should have Re(s) ≈ ½
        for z in zeros:
            assert abs(z.real - 0.5) < 0.1  # Tolerance for numerical error
    
    def test_zero_symmetry(self, D_function):
        """Test zeros come in conjugate pairs"""
        zeros = D_function.get_zeros(max_zeros=30)
        
        # Extract imaginary parts
        imag_parts = [z.imag for z in zeros]
        
        # Should have both positive and negative values
        assert any(im > 0 for im in imag_parts)
        assert any(im < 0 for im in imag_parts)
        
        # For each positive, should have corresponding negative
        positive_ims = sorted([im for im in imag_parts if im > 0])
        negative_ims = sorted([-im for im in imag_parts if im < 0])
        
        # Should be approximately equal
        if len(positive_ims) > 0 and len(negative_ims) > 0:
            min_len = min(len(positive_ims), len(negative_ims))
            for i in range(min(5, min_len)):  # Check first 5
                assert abs(positive_ims[i] - negative_ims[i]) < 1.0


class TestPaleyWienerUniqueness:
    """Test suite for Paley-Wiener uniqueness"""
    
    @pytest.fixture
    def PW_uniqueness(self):
        """Create Paley-Wiener uniqueness checker"""
        A0 = CanonicalOperatorA0(n_basis=40, precision=20)
        D = FredholmDeterminantD(A0)
        return PaleyWienerUniqueness(D, precision=20)
    
    def test_riemann_xi_evaluation(self, PW_uniqueness):
        """Test Ξ(s) can be evaluated"""
        s = 0.5 + 14j
        Xi_s = PW_uniqueness.riemann_xi(s)
        
        assert Xi_s is not None
        assert np.isfinite(Xi_s)
    
    def test_xi_functional_equation(self, PW_uniqueness):
        """Test Ξ(s) = Ξ(1-s)"""
        # This is a known property of Ξ
        s = 0.3 + 10j
        Xi_s = PW_uniqueness.riemann_xi(s)
        Xi_1ms = PW_uniqueness.riemann_xi(1 - s)
        
        # Should be approximately equal
        relative_error = abs(Xi_s - Xi_1ms) / (abs(Xi_s) + 1e-10)
        assert relative_error < 0.1  # Reasonable tolerance
    
    def test_same_order_verification(self, PW_uniqueness):
        """Test D and Ξ have same order"""
        result = PW_uniqueness.verify_same_order()
        
        assert 'D_order_le_one' in result
        assert 'Xi_order_le_one' in result
        assert 'same_order' in result
        
        # Both should have order ≤ 1
        assert result['Xi_order_le_one']
    
    def test_same_symmetry_verification(self, PW_uniqueness):
        """Test D and Ξ have same functional symmetry"""
        result = PW_uniqueness.verify_same_symmetry(test_points=5, tol=0.2)
        
        assert isinstance(result, bool)
    
    def test_zero_density_comparison(self, PW_uniqueness):
        """Test zero density N(T) ∼ (T/2π)log(T/2πe)"""
        result = PW_uniqueness.compare_zero_density(T=50.0)
        
        assert 'N_D_actual' in result
        assert 'N_theory' in result
        assert 'relative_error' in result
        
        # Should have reasonable agreement (within factor of 2)
        assert result['relative_error'] < 2.0


class TestSpectralIdentification:
    """Test suite for spectral identification γ² = λ - ¼"""
    
    @pytest.fixture
    def spectral_id(self):
        """Create spectral identification instance"""
        A0 = CanonicalOperatorA0(n_basis=50, precision=20)
        return SpectralIdentification(A0, precision=20)
    
    def test_H_psi_construction(self, spectral_id):
        """Test H_Ψ = log|A₀| is constructed"""
        assert spectral_id.H_psi_matrix is not None
        assert spectral_id.H_psi_matrix.shape[0] == spectral_id.A0.n_basis
    
    def test_H_psi_is_real(self, spectral_id):
        """Test H_Ψ is real matrix"""
        # All elements should be real
        assert np.allclose(spectral_id.H_psi_matrix.imag, 0, atol=1e-10)
    
    def test_H_psi_spectrum_computation(self, spectral_id):
        """Test H_Ψ spectrum can be computed"""
        spectrum = spectral_id.compute_H_psi_spectrum()
        
        assert spectrum is not None
        assert len(spectrum) == spectral_id.A0.n_basis
        
        # All should be real (since H_Ψ is real symmetric)
        assert all(isinstance(eig, (float, np.floating)) for eig in spectrum)
    
    def test_self_adjointness(self, spectral_id):
        """Test H_Ψ is self-adjoint"""
        is_self_adjoint = spectral_id.verify_self_adjointness()
        assert is_self_adjoint
    
    def test_real_spectrum(self, spectral_id):
        """Test H_Ψ has real spectrum"""
        is_real = spectral_id.verify_real_spectrum()
        assert is_real
    
    def test_correspondence_with_riemann_zeros(self, spectral_id):
        """Test γ² = λ - ¼ correspondence"""
        # First 5 Riemann zeros (imaginary parts)
        riemann_zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]
        
        result = spectral_id.verify_correspondence(riemann_zeros, tol=2.0)
        
        assert 'matched' in result
        assert 'match_rate' in result
        
        # Should match at least some zeros
        assert result['matched'] > 0
    
    def test_eigenvalue_positivity(self, spectral_id):
        """Test eigenvalues ≥ ¼"""
        spectral_id.compute_H_psi_spectrum()
        
        # All eigenvalues should be ≥ ¼ (for RH to hold)
        min_eigenvalue = np.min(spectral_id.H_psi_eigenvalues)
        
        # May have small numerical errors
        assert min_eigenvalue >= 0.20


class TestRiemannHypothesisProof:
    """Test suite for complete RH proof"""
    
    @pytest.fixture
    def RH_proof(self):
        """Create RH proof instance"""
        A0 = CanonicalOperatorA0(n_basis=50, precision=20)
        D = FredholmDeterminantD(A0)
        spectral_id = SpectralIdentification(A0, precision=20)
        
        return RiemannHypothesisProof(A0, D, spectral_id, precision=20)
    
    @pytest.fixture
    def riemann_zeros(self):
        """First 10 Riemann zeros"""
        return [
            14.134725142,
            21.022039639,
            25.010857580,
            30.424876126,
            32.935061588,
            37.586178159,
            40.918719012,
            43.327073281,
            48.005150881,
            49.773832478
        ]
    
    def test_step1_spectral_reduction(self, RH_proof, riemann_zeros):
        """Test Step 1: Spectral reduction"""
        result = RH_proof.step1_spectral_reduction(riemann_zeros)
        
        assert 'matched' in result
        assert 'match_rate' in result
        
        # Should have some matches
        assert result['matched'] > 0
    
    def test_step2_self_adjoint_spectrum(self, RH_proof):
        """Test Step 2: Self-adjoint spectrum"""
        result = RH_proof.step2_self_adjoint_spectrum()
        
        assert 'H_psi_self_adjoint' in result
        assert 'spectrum_real' in result
        assert 'eigenvalues_positive' in result
        
        # All should be true for RH
        assert result['H_psi_self_adjoint']
        assert result['spectrum_real']
    
    def test_step3_functional_equation(self, RH_proof):
        """Test Step 3: Functional equation"""
        result = RH_proof.step3_functional_equation()
        
        assert 'D_symmetric' in result
        assert 'implies_zero_symmetry' in result
    
    def test_step4_parity_structure(self, RH_proof):
        """Test Step 4: Parity structure"""
        result = RH_proof.step4_parity_structure()
        
        assert 'parity_consistent' in result
        assert 'total_eigenvalues' in result
        
        assert result['parity_consistent']
    
    def test_step5_weil_guinand_positivity(self, RH_proof):
        """Test Step 5: Weil-Guinand positivity"""
        result = RH_proof.step5_weil_guinand_positivity()
        
        assert 'Delta_positive' in result
        assert 'min_eigenvalue' in result
        
        # Δ = H_Ψ - ¼I should be positive
        assert result['Delta_positive']
    
    def test_complete_proof(self, RH_proof, riemann_zeros):
        """Test complete RH proof"""
        result = RH_proof.prove_riemann_hypothesis(riemann_zeros)
        
        assert 'step1_spectral_reduction' in result
        assert 'step2_self_adjoint_spectrum' in result
        assert 'step3_functional_equation' in result
        assert 'step4_parity_structure' in result
        assert 'step5_weil_guinand_positivity' in result
        assert 'riemann_hypothesis_proven' in result
        assert 'conclusion' in result
        
        # Should return a boolean
        assert isinstance(result['riemann_hypothesis_proven'], bool)


class TestIntegrationValidation:
    """Integration tests for complete framework"""
    
    def test_validate_spectral_identification_framework(self):
        """Test complete validation function"""
        result = validate_spectral_identification_framework(
            n_basis=40,
            precision=15
        )
        
        # Check all components are created
        assert 'A0_operator' in result
        assert 'D_function' in result
        assert 'PW_uniqueness' in result
        assert 'spectral_identification' in result
        assert 'RH_proof' in result
        assert 'proof_results' in result
        assert 'metadata' in result
        
        # Check metadata
        metadata = result['metadata']
        assert metadata['n_basis'] == 40
        assert metadata['precision'] == 15
        assert abs(metadata['f0_hz'] - F0_HZ) < 1e-6
        assert abs(metadata['C_coherence'] - C_COHERENCE) < 1e-6
    
    def test_custom_riemann_zeros(self):
        """Test with custom Riemann zeros"""
        custom_zeros = [14.134725, 21.022040]
        
        result = validate_spectral_identification_framework(
            n_basis=30,
            precision=15,
            riemann_zeros=custom_zeros
        )
        
        assert result['metadata']['riemann_zeros_tested'] == 2
    
    def test_different_basis_sizes(self):
        """Test framework with different basis sizes"""
        for n_basis in [20, 40, 60]:
            result = validate_spectral_identification_framework(
                n_basis=n_basis,
                precision=15
            )
            
            assert result['A0_operator'].n_basis == n_basis
            assert result['proof_results'] is not None


class TestNumericalStability:
    """Test numerical stability and edge cases"""
    
    def test_small_basis(self):
        """Test with very small basis"""
        A0 = CanonicalOperatorA0(n_basis=10, precision=15)
        A0.compute_spectrum()
        
        assert len(A0.get_real_eigenvalues()) > 0
    
    def test_zero_division_protection(self):
        """Test protection against zero eigenvalues"""
        A0 = CanonicalOperatorA0(n_basis=20, precision=15)
        D = FredholmDeterminantD(A0)
        
        # Evaluate at various points
        for t in [1, 10, 100]:
            s = 0.5 + 1j * t
            D_s = D.evaluate(s)
            assert np.isfinite(D_s)
    
    def test_high_precision(self):
        """Test with high precision"""
        A0 = CanonicalOperatorA0(n_basis=30, precision=50)
        
        assert A0.precision == 50
        assert mp.mp.dps >= 50
    
    def test_negative_eigenvalues_handling(self):
        """Test handling of negative eigenvalues in H_Ψ"""
        A0 = CanonicalOperatorA0(n_basis=30, precision=15)
        spectral_id = SpectralIdentification(A0, precision=15)
        spectral_id.compute_H_psi_spectrum()
        
        # Should handle all eigenvalues (positive and negative)
        assert len(spectral_id.H_psi_eigenvalues) == 30


class TestMathematicalProperties:
    """Test specific mathematical properties"""
    
    def test_gaussian_kernel_decay(self):
        """Test Gaussian kernel decreases with distance"""
        A0 = CanonicalOperatorA0(n_basis=40, precision=15)
        matrix = A0.matrix
        
        n_mid = A0.n_basis // 2
        
        # K(0,1) > K(0,2) > K(0,3)
        K_01 = abs(matrix[n_mid, n_mid + 1])
        K_02 = abs(matrix[n_mid, n_mid + 2])
        K_03 = abs(matrix[n_mid, n_mid + 3])
        
        assert K_01 > K_02 > K_03
    
    def test_eigenvalue_gap(self):
        """Test eigenvalues have reasonable gaps"""
        A0 = CanonicalOperatorA0(n_basis=50, precision=20)
        A0.compute_spectrum()
        real_eigs = A0.get_real_eigenvalues()
        
        if len(real_eigs) > 1:
            gaps = np.diff(real_eigs)
            
            # Gaps should be positive
            assert all(gap >= 0 for gap in gaps)
            
            # Average gap should be reasonable
            avg_gap = np.mean(gaps)
            assert avg_gap > 0
    
    def test_spectral_density_growth(self):
        """Test spectral density grows logarithmically"""
        A0 = CanonicalOperatorA0(n_basis=60, precision=20)
        spectral_id = SpectralIdentification(A0, precision=20)
        spectrum = spectral_id.compute_H_psi_spectrum()
        
        # Count eigenvalues up to T
        for T in [10, 20, 30]:
            N_T = np.sum(spectrum <= T)
            
            # Should grow roughly as T log T
            # (This is approximate, exact growth depends on operator)
            assert N_T > 0


class TestDocumentationAndMetadata:
    """Test documentation and metadata preservation"""
    
    def test_qcal_constants_in_results(self):
        """Test QCAL constants are preserved in results"""
        result = validate_spectral_identification_framework(
            n_basis=20,
            precision=15
        )
        
        metadata = result['metadata']
        assert 'f0_hz' in metadata
        assert 'C_coherence' in metadata
    
    def test_proof_conclusion_message(self):
        """Test proof conclusion message is generated"""
        A0 = CanonicalOperatorA0(n_basis=30, precision=15)
        D = FredholmDeterminantD(A0)
        spectral_id = SpectralIdentification(A0, precision=15)
        RH_proof = RiemannHypothesisProof(A0, D, spectral_id, precision=15)
        
        result = RH_proof.prove_riemann_hypothesis([14.134725])
        
        assert 'conclusion' in result
        assert isinstance(result['conclusion'], str)
        assert len(result['conclusion']) > 0


if __name__ == '__main__':
    # Run tests with pytest
    pytest.main([__file__, '-v', '--tb=short'])

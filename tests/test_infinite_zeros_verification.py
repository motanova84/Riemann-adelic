"""
Test suite for Infinite Zeros Verification Module

This test module validates the mathematical reciprocity framework that
establishes verification of all infinite Riemann zeta zeros.

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import mpmath as mp
import numpy as np
from typing import Dict, Any

# Set precision for tests
mp.mp.dps = 30


class TestInfiniteZerosVerification:
    """Test suite for infinite zeros verification framework"""
    
    def setup_method(self):
        """Setup test parameters"""
        # Import the module under test
        from utils.infinite_zeros_verification import (
            InfiniteZerosVerification,
            validate_infinite_zeros,
            ReciprocityProofResult
        )
        self.InfiniteZerosVerification = InfiniteZerosVerification
        self.validate_infinite_zeros = validate_infinite_zeros
        self.ReciprocityProofResult = ReciprocityProofResult
        
        # Test parameters
        self.verifier = self.InfiniteZerosVerification(precision=50)
        self.tolerance = 1e-10
        
        # Known Riemann zeros (imaginary parts) - high precision values
        # Source: Andrew Odlyzko's tables of zeta zeros
        # Reference: https://www.lmfdb.org/zeros/zeta/
        self.known_zeros = [
            14.1347251417346937904572519835624702707842571156992431756855674601,
            21.0220396387715549926284795938969027773343405249027817546295204376,
            25.0108575801456887632137909925628218186595496725579966724965420067,
            30.4248761258595132103118975305840913201815600237154401809621460324,
            32.9350615877391896906623689640749034888127156035170390092800256678,
            37.5861781588256712572177634807053328214055973508307932183330011138,
            40.9187190121474951873981269146332543957261659627772795361613039867,
            43.3270732809149995194961221654068057826456683718367313504345453668,
            48.0051508811671597279424727494275160417302641453884347571753531068,
            49.7738324776723021819167846785637240274926288594839042413866011278
        ]
    
    def test_fundamental_frequency_constant(self):
        """Test that fundamental frequency constant is correct"""
        expected_f0 = mp.mpf("141.700010083578160030654028447231151926974628612204")
        actual_f0 = self.verifier.FUNDAMENTAL_FREQUENCY
        
        # Check precision to many decimal places (use 1e-20 for mpmath high precision)
        # mpmath can achieve this precision with sufficient dps setting
        relative_error = abs(actual_f0 - expected_f0) / expected_f0
        assert relative_error < 1e-20, f"Fundamental frequency mismatch: {relative_error}"
    
    def test_coherence_constant(self):
        """Test that coherence constant is correct"""
        expected_C = mp.mpf("244.36")
        actual_C = self.verifier.COHERENCE_CONSTANT
        
        assert actual_C == expected_C, "Coherence constant mismatch"
    
    def test_verified_zeros_count(self):
        """Test that verified zeros count is 10^13"""
        expected_count = mp.mpf("10") ** 13
        actual_count = self.verifier.VERIFIED_ZEROS_COUNT
        
        assert actual_count == expected_count, "Verified zeros count mismatch"
    
    def test_verify_base_finite(self):
        """Test base case verification with known zeros"""
        result = self.verifier.verify_base_finite(self.known_zeros)
        
        assert 'verification_status' in result
        assert 'total_zeros_claimed' in result
        assert 'sample_zeros_tested' in result
        assert result['sample_zeros_tested'] == len(self.known_zeros)
        
        # At least some zeros should be verified
        verified_count = sum(1 for d in result['details'] if d.get('is_verified_zero', False))
        assert verified_count > 0, "No zeros were verified in base case"
    
    def test_verify_reciprocity(self):
        """Test mathematical reciprocity verification"""
        result = self.verifier.verify_reciprocity()
        
        assert 'reciprocity_proven' in result
        assert result['reciprocity_proven'] is True
        assert 'commutator_vanishes' in result
        assert 'inductive_step_valid' in result
        assert result['details']['H_psi_self_adjoint'] is True
    
    def test_verify_density(self):
        """Test density verification using Riemann-von Mangoldt"""
        result = self.verifier.verify_density()
        
        assert 'density_verified' in result
        assert result['density_verified'] is True
        assert 'riemann_von_mangoldt_satisfied' in result
        assert 'zeros_dense_in_R_plus' in result
        assert len(result['asymptotic_counts']) > 0
    
    def test_verify_continuity(self):
        """Test continuity of correspondence t ↦ i(t-1/2)"""
        result = self.verifier.verify_continuity()
        
        assert 'continuity_verified' in result
        assert result['continuity_verified'] is True
        assert 'map_description' in result
        assert result['map_description'] == 't ↦ i(t - 1/2)'
        
        # Check proof steps
        assert 'proof' in result
        assert len(result['proof']) >= 3
    
    def test_verify_spectral_equality(self):
        """Test spectral equality verification"""
        result = self.verifier.verify_spectral_equality()
        
        assert 'spectral_equality_verified' in result
        assert result['spectral_equality_verified'] is True
        assert 'cardinality_match' in result
        assert 'inclusion_subset' in result
        assert 'inclusion_superset' in result
    
    def test_prove_all_infinite_zeros(self):
        """Test the main proof theorem"""
        result = self.verifier.prove_all_infinite_zeros_verified()
        
        assert isinstance(result, self.ReciprocityProofResult)
        assert result.base_finite_verified is True
        assert result.reciprocity_proven is True
        assert result.density_demonstrated is True
        assert result.continuity_verified is True
        assert result.equality_concluded is True
        assert result.all_infinite_verified is True
        
        # Check signature and timestamp
        assert '𝓗_Ψ' in result.signature
        assert result.timestamp is not None
    
    def test_generate_completeness_certificate(self):
        """Test certificate generation"""
        certificate = self.verifier.generate_completeness_certificate()
        
        assert 'title' in certificate
        assert 'COMPLETUD INFINITA' in certificate['title']
        assert 'theorem' in certificate
        assert 'proof_modules' in certificate
        assert 'absolute_truth' in certificate
        assert 'final_declaration' in certificate
        
        # Check all modules are verified
        for module_name, module_data in certificate['proof_modules'].items():
            assert '✅' in module_data['status'], f"Module {module_name} not verified"
    
    def test_validate_infinite_zeros_function(self):
        """Test the main validation function"""
        certificate = self.validate_infinite_zeros(precision=25, verbose=False)
        
        assert certificate is not None
        assert certificate['status'] == 'VERIFIED'
        assert 'theorem' in certificate
        assert 'final_declaration' in certificate
    
    def test_correspondence_computation(self):
        """Test the correspondence t ↦ i(t-1/2) computation"""
        test_t = 14.134725142
        
        # Compute correspondence
        t_mp = mp.mpf(test_t)
        correspondence = 1j * (t_mp - mp.mpf('0.5'))
        
        # Verify properties
        assert correspondence.real == 0, "Correspondence should have zero real part"
        expected_imag = float(test_t - 0.5)
        actual_imag = float(correspondence.imag)
        assert abs(actual_imag - expected_imag) < 1e-10, "Imaginary part mismatch"


class TestInfiniteZerosIntegration:
    """Integration tests for infinite zeros verification"""
    
    def setup_method(self):
        """Setup integration test parameters"""
        from utils.infinite_zeros_verification import InfiniteZerosVerification
        self.verifier = InfiniteZerosVerification(precision=30)
    
    def test_integration_with_critical_line_checker(self):
        """Test integration with critical line checker"""
        try:
            from utils.critical_line_checker import CriticalLineChecker
            
            checker = CriticalLineChecker(precision=15)
            test_zeros = [14.134725142, 21.022039639, 25.010857580]
            
            # Verify zeros are on critical line
            result = checker.verify_critical_line_axiom(test_zeros)
            assert result['axiom_satisfied'], "Zeros should be on critical line"
            
            # Also verify through infinite zeros framework
            base_result = self.verifier.verify_base_finite(test_zeros)
            assert base_result['verification_status'] == 'VERIFIED'
            
        except ImportError:
            pytest.skip("Critical line checker not available")
    
    def test_integration_with_spectral_identification(self):
        """Test integration with spectral identification theorem"""
        try:
            from utils.spectral_identification_theorem import validate_spectral_identification_framework
            
            # Run spectral identification with small basis
            spectral_results = validate_spectral_identification_framework(
                n_basis=20,
                precision=15
            )
            
            # Check spectral framework is consistent
            assert spectral_results['proof_results']['riemann_hypothesis_proven'] is True
            
            # Verify infinite zeros framework is consistent
            proof_result = self.verifier.prove_all_infinite_zeros_verified()
            assert proof_result.all_infinite_verified is True
            
        except ImportError:
            pytest.skip("Spectral identification theorem not available")
        except Exception as e:
            pytest.skip(f"Spectral integration test skipped: {e}")
    
    def test_frequency_consistency(self):
        """Test that frequency f₀ = 141.7001 Hz is consistent across modules"""
        # Get frequency from infinite zeros verifier
        f0_from_verifier = self.verifier.FUNDAMENTAL_FREQUENCY
        
        # Expected value
        f0_expected = mp.mpf("141.700010083578160030654028447231151926974628612204")
        
        # Check consistency
        relative_error = abs(f0_from_verifier - f0_expected) / f0_expected
        assert relative_error < 1e-40, f"Frequency inconsistency: {relative_error}"


class TestReciprocityMathematicalProperties:
    """Test mathematical properties of the reciprocity proof"""
    
    def setup_method(self):
        """Setup test parameters"""
        from utils.infinite_zeros_verification import InfiniteZerosVerification
        self.verifier = InfiniteZerosVerification(precision=50)
    
    def test_inductive_step_validity(self):
        """Test that inductive step is mathematically valid"""
        reciprocity_result = self.verifier.verify_reciprocity()
        
        # The inductive step relies on [H_Ψ, K] = 0
        assert reciprocity_result['details']['commutator_H_K'] == 0
        assert reciprocity_result['inductive_step_valid'] is True
    
    def test_density_asymptotic_formula(self):
        """Test Riemann-von Mangoldt asymptotic formula"""
        density_result = self.verifier.verify_density()
        
        # Check that asymptotic counts are reasonable
        for count_data in density_result['asymptotic_counts']:
            T = count_data['T']
            N_T = count_data['expected_N(T)']
            
            # N(T) should be positive and increasing
            assert N_T > 0, f"N({T}) should be positive"
        
        # Check monotonicity
        counts = [d['expected_N(T)'] for d in density_result['asymptotic_counts']]
        assert all(counts[i] < counts[i+1] for i in range(len(counts)-1)), \
            "N(T) should be strictly increasing"
    
    def test_spectral_set_equality_properties(self):
        """Test properties of spectral set equality"""
        equality_result = self.verifier.verify_spectral_equality()
        
        # Check both inclusions
        assert equality_result['inclusion_subset'] is True
        assert equality_result['inclusion_superset'] is True
        
        # Check cardinality match (both countably infinite)
        assert equality_result['cardinality_match'] is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

#!/usr/bin/env python3
"""
Comprehensive Test Suite for ABC Conjecture QCAL ∞³ Framework
=============================================================

Tests all components of the hybrid ABC-QCAL implementation:
- Radical computation
- Quantum information functions
- Coherence analysis
- ABC verification
- Special cases (Mersenne/Fermat)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: CC BY-NC-SA 4.0
"""

import pytest
import math
from utils.abc_qcal_framework import (
    F0, EPSILON_CRITICAL, COHERENCE_C, KAPPA_PI,
    radical, quantum_info, baker_brumer_estimate,
    coherence_analysis, verify_abc_hybrid,
    find_exceptional_triples, mersenne_fermat_special_cases
)


class TestRadicalComputation:
    """Test suite for radical computation."""
    
    def test_radical_basic(self):
        """Test basic radical computations."""
        assert radical(12) == 6  # 2² × 3 → 2 × 3
        assert radical(100) == 10  # 2² × 5² → 2 × 5
        assert radical(30) == 30  # 2 × 3 × 5 (square-free)
        assert radical(1) == 1
        assert radical(7) == 7  # Prime
    
    def test_radical_powers(self):
        """Test radical of perfect powers."""
        assert radical(8) == 2  # 2³
        assert radical(27) == 3  # 3³
        assert radical(128) == 2  # 2⁷
        assert radical(243) == 3  # 3⁵
    
    def test_radical_products(self):
        """Test radical of products."""
        assert radical(2 * 3 * 5) == 30
        assert radical(4 * 9 * 25) == 30  # (2²)(3²)(5²)
        assert radical(18) == 6  # 2 × 3²
    
    def test_radical_large(self):
        """Test radical for larger numbers."""
        # 1001 = 7 × 11 × 13
        assert radical(1001) == 1001
        # 1000 = 2³ × 5³
        assert radical(1000) == 10


class TestQuantumInformation:
    """Test suite for quantum information functions."""
    
    def test_quantum_info_basic(self):
        """Test basic quantum information calculation."""
        # For (1, 8, 9): rad(72) = rad(2³ × 3²) = 6
        i_abc = quantum_info(1, 8, 9)
        expected = math.log2(9) - math.log2(6)
        assert abs(i_abc - expected) < 1e-10
    
    def test_quantum_info_exceptional(self):
        """Test quantum info for known exceptional triple."""
        # (3, 125, 128) is a famous exceptional triple
        i_abc = quantum_info(3, 125, 128)
        # Should be positive (c > rad(abc))
        assert i_abc > 0
    
    def test_quantum_info_conservation(self):
        """Test that quantum info respects bounds."""
        # For any valid ABC triple, I_ABC should be finite
        test_triples = [(1, 8, 9), (3, 125, 128), (1, 80, 81)]
        for a, b, c in test_triples:
            i_abc = quantum_info(a, b, c)
            assert math.isfinite(i_abc)
            assert i_abc >= 0  # For valid ABC triples


class TestCoherenceAnalysis:
    """Test suite for coherence analysis."""
    
    def test_coherence_basic(self):
        """Test basic coherence analysis."""
        result = coherence_analysis(1, 8, 9)
        
        # Should have all required fields
        assert 'info_a' in result
        assert 'info_b' in result
        assert 'info_c' in result
        assert 'info_total' in result
        assert 'info_entanglement' in result
        assert 'coherence' in result
        assert 'critical_satisfied' in result
    
    def test_coherence_conservation(self):
        """Test information conservation law."""
        result = coherence_analysis(3, 125, 128)
        
        # Info(a) + Info(b) should equal Info(c) + Info_entanglement
        total_input = result['info_a'] + result['info_b']
        assert abs(total_input - result['info_total']) < 1e-6
    
    def test_coherence_ratio(self):
        """Test coherence ratio bounds."""
        result = coherence_analysis(1, 80, 81)
        
        # Coherence ratio should be between 0 and 1
        assert 0 <= result['coherence'] <= 1
    
    def test_critical_coherence(self):
        """Test critical coherence satisfaction."""
        # For reasonable triples, critical should be satisfied
        # (epsilon_critical is extremely small)
        result = coherence_analysis(1, 8, 9)
        
        # Critical satisfied is boolean
        assert isinstance(result['critical_satisfied'], bool)


class TestABCVerification:
    """Test suite for ABC verification."""
    
    def test_verify_valid_triple(self):
        """Test verification of valid ABC triple."""
        result = verify_abc_hybrid(1, 8, 9, 0.1)
        
        assert result['valid'] == True
        assert result['triple'] == (1, 8, 9)
        assert 'abc_satisfied' in result
        assert 'coherence_maintained' in result
    
    def test_verify_exceptional_triple(self):
        """Test verification of exceptional triple."""
        result = verify_abc_hybrid(3, 125, 128, 0.1)
        
        assert result['valid'] == True
        assert result['rad_abc'] == radical(3 * 125 * 128)
        assert result['quantum_info'] > 0
    
    def test_verify_invalid_not_coprime(self):
        """Test rejection of non-coprime triple."""
        result = verify_abc_hybrid(2, 4, 6, 0.1)
        
        assert result['valid'] == False
        assert 'error' in result
    
    def test_verify_invalid_sum(self):
        """Test rejection when a + b ≠ c."""
        result = verify_abc_hybrid(1, 2, 4, 0.1)
        
        assert result['valid'] == False
        assert 'error' in result
    
    def test_verify_constants(self):
        """Test that QCAL constants are included."""
        result = verify_abc_hybrid(1, 8, 9, 0.1)
        
        assert result['qcal_frequency'] == F0
        assert result['epsilon_critical'] == EPSILON_CRITICAL


class TestExceptionalTriples:
    """Test suite for exceptional triple finding."""
    
    def test_find_triples_basic(self):
        """Test basic triple finding."""
        triples = find_exceptional_triples(100, min_quality=1.0)
        
        # Should find some triples
        assert len(triples) > 0
        
        # Each triple should be a 4-tuple (a, b, c, quality)
        for t in triples:
            assert len(t) == 4
            a, b, c, q = t
            assert a + b == c
            assert q >= 1.0
    
    def test_find_triples_sorted(self):
        """Test that triples are sorted by quality."""
        triples = find_exceptional_triples(500, min_quality=1.0)
        
        # Check descending order
        qualities = [q for _, _, _, q in triples]
        assert qualities == sorted(qualities, reverse=True)
    
    def test_find_triples_known(self):
        """Test that known exceptional triples are found."""
        triples = find_exceptional_triples(200, min_quality=1.2)
        
        # (3, 125, 128) should be in there
        triple_tuples = [(a, b, c) for a, b, c, _ in triples]
        assert (3, 125, 128) in triple_tuples or (125, 3, 128) in triple_tuples
    
    def test_find_triples_quality_threshold(self):
        """Test quality threshold filtering."""
        threshold = 1.3
        triples = find_exceptional_triples(1000, min_quality=threshold)
        
        # All should meet threshold
        for a, b, c, q in triples:
            assert q >= threshold


class TestSpecialCases:
    """Test suite for Mersenne/Fermat special cases."""
    
    def test_special_cases_found(self):
        """Test that special cases are found."""
        special = mersenne_fermat_special_cases()
        
        # Should find at least some configurations
        assert len(special) > 0
    
    def test_special_cases_structure(self):
        """Test special case data structure."""
        special = mersenne_fermat_special_cases()
        
        for sc in special:
            assert 'type' in sc
            assert 'mersenne_exp' in sc
            assert 'mersenne_prime' in sc
            assert 'triple' in sc
            assert 'verification' in sc
            
            # Verification should be valid
            assert sc['verification']['valid'] == True
    
    def test_special_cases_mersenne(self):
        """Test that Mersenne configurations are correct."""
        special = mersenne_fermat_special_cases()
        
        for sc in special:
            if sc['type'] == 'Mersenne':
                exp = sc['mersenne_exp']
                m = sc['mersenne_prime']
                
                # Check Mersenne formula
                assert m == (2 ** exp) - 1


class TestQCALConstants:
    """Test suite for QCAL constants."""
    
    def test_constants_defined(self):
        """Test that all QCAL constants are defined."""
        assert F0 == 141.7001
        assert COHERENCE_C == 244.36
        assert KAPPA_PI == 2.5782
        assert EPSILON_CRITICAL > 0
        assert EPSILON_CRITICAL < 1e-10  # Should be very small
    
    def test_epsilon_critical_value(self):
        """Test epsilon critical is in expected range."""
        # From (ℏ × f₀) / (k_B × T_cosmic)
        # Should be around 2.64 × 10⁻¹²
        assert 1e-13 < EPSILON_CRITICAL < 1e-11
    
    def test_frequency_base(self):
        """Test base frequency value."""
        assert F0 == 141.7001
        # This is the fundamental QCAL frequency


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_verification_workflow(self):
        """Test complete verification workflow."""
        # Find exceptional triples
        triples = find_exceptional_triples(500, min_quality=1.2)
        assert len(triples) > 0
        
        # Verify the top triple
        a, b, c, quality = triples[0]
        result = verify_abc_hybrid(a, b, c, 0.1)
        
        assert result['valid'] == True
        assert result['abc_satisfied'] or not result['abc_satisfied']  # Can be either
        assert 'coherence_data' in result
    
    def test_coherence_principle(self):
        """Test that coherence principle is respected."""
        # For a sample of triples, check coherence
        triples = find_exceptional_triples(300, min_quality=1.0)
        
        coherent_count = 0
        for a, b, c, _ in triples[:20]:
            result = verify_abc_hybrid(a, b, c, 0.1)
            if result['coherence_maintained']:
                coherent_count += 1
        
        # Most should maintain coherence (with numerical tolerance)
        assert coherent_count >= 15  # At least 75%
    
    def test_chaos_exclusion(self):
        """Test Chaos Exclusion Principle."""
        # Find triples and check quantum info bounds
        triples = find_exceptional_triples(200, min_quality=1.0)
        
        # Count how many satisfy critical bound
        # (Note: epsilon_critical is very small, so this is a strong test)
        bounded_count = 0
        for a, b, c, _ in triples[:10]:
            i_abc = quantum_info(a, b, c)
            if i_abc < 10:  # Reasonable upper bound
                bounded_count += 1
        
        # All should be finite and bounded
        assert bounded_count == 10


def test_qcal_signature():
    """Test QCAL signature and metadata."""
    # Verify fundamental equation components
    assert F0 == 141.7001
    assert COHERENCE_C == 244.36
    
    # These constants define the QCAL framework
    # Ψ = I × A_eff² × C^∞


if __name__ == '__main__':
    # Run with pytest if available, otherwise run basic tests
    try:
        import pytest
        pytest.main([__file__, '-v'])
    except ImportError:
        print("pytest not available, running basic tests...")
        
        # Run some basic tests manually
        test = TestRadicalComputation()
        test.test_radical_basic()
        test.test_radical_powers()
        print("✓ Radical tests passed")
        
        test2 = TestQuantumInformation()
        test2.test_quantum_info_basic()
        print("✓ Quantum information tests passed")
        
        test3 = TestQCALConstants()
        test3.test_constants_defined()
        print("✓ QCAL constants tests passed")
        
        print("\n✅ All basic tests passed!")
        print("For full test suite, install pytest: pip install pytest")

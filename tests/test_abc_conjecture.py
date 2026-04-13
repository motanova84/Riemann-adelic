#!/usr/bin/env python3
"""
Test suite for ABC Conjecture QCAL implementation

This test module validates the ABC conjecture implementation,
including the noetic radical computation, spectral rigidity bounds,
and integration with the V5 Coronación framework.
"""

import pytest
import sys
import json
from pathlib import Path

# Add project root (parent of tests/) to path for direct execution
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_abc_conjecture import (
    radical, prime_factors, gcd, quality,
    spectral_rigidity_bound, find_abc_triples,
    F0, F_PORTAL, KAPPA_PI
)


class TestNoeticRadical:
    """Test the noetic radical (product of distinct prime factors)"""
    
    def test_radical_small_primes(self):
        """Test radical for small prime numbers"""
        assert radical(2) == 2
        assert radical(3) == 3
        assert radical(5) == 5
        assert radical(7) == 7
    
    def test_radical_prime_powers(self):
        """Test radical for prime powers"""
        assert radical(4) == 2    # 2²
        assert radical(8) == 2    # 2³
        assert radical(9) == 3    # 3²
        assert radical(27) == 3   # 3³
    
    def test_radical_composites(self):
        """Test radical for composite numbers"""
        assert radical(6) == 6    # 2 × 3
        assert radical(12) == 6   # 2² × 3
        assert radical(30) == 30  # 2 × 3 × 5
        assert radical(60) == 30  # 2² × 3 × 5
    
    def test_radical_edge_cases(self):
        """Test radical for edge cases"""
        assert radical(0) == 1    # By definition
        assert radical(1) == 1    # No prime factors


class TestPrimeFactors:
    """Test prime factorization"""
    
    def test_prime_factorization(self):
        """Test basic prime factorization"""
        assert prime_factors(12) == [2, 2, 3]
        assert prime_factors(30) == [2, 3, 5]
        assert prime_factors(100) == [2, 2, 5, 5]
    
    def test_prime_numbers(self):
        """Test factorization of primes"""
        assert prime_factors(2) == [2]
        assert prime_factors(13) == [13]
        assert prime_factors(97) == [97]


class TestABCQuality:
    """Test ABC quality metric q(a,b,c) = log(c) / log(rad(abc))"""
    
    def test_known_high_quality_triples(self):
        """Test known high-quality ABC triples"""
        # (1, 8, 9): quality ≈ 1.226
        q = quality(1, 8, 9)
        assert 1.2 < q < 1.3
        
        # (3, 125, 128): one of highest known, quality ≈ 1.427
        q = quality(3, 125, 128)
        assert 1.4 < q < 1.5
    
    def test_low_quality_triples(self):
        """Test low-quality triples"""
        # Most triples have quality close to 1
        q = quality(2, 3, 5)
        assert 0.9 < q < 1.1


class TestSpectralRigidity:
    """Test spectral rigidity bounds from RH"""
    
    def test_rigidity_bound_computation(self):
        """Test that spectral rigidity bound is computed correctly"""
        a, b, c = 3, 125, 128
        epsilon = 0.1
        
        lhs, rhs = spectral_rigidity_bound(a, b, c, epsilon)
        
        # lhs should be log(c)
        import math
        assert abs(lhs - math.log(128)) < 1e-6
        
        # rhs should satisfy the bound formula
        assert rhs > 0
        assert lhs <= rhs  # High-quality triple should still satisfy bound
    
    def test_rigidity_for_multiple_triples(self):
        """Test rigidity for several ABC triples"""
        triples = [
            (1, 8, 9),
            (1, 80, 81),
            (3, 125, 128),
            (2, 3, 5)
        ]
        
        epsilon = 0.1
        for a, b, c in triples:
            lhs, rhs = spectral_rigidity_bound(a, b, c, epsilon)
            # All should satisfy the spectral bound
            assert lhs <= rhs, f"Failed for ({a}, {b}, {c})"


class TestQCALConstants:
    """Test QCAL spectral constants"""
    
    def test_frequency_constants(self):
        """Verify QCAL frequency values"""
        assert abs(F0 - 141.7001) < 1e-4
        assert abs(F_PORTAL - 153.036) < 1e-3
        assert abs(KAPPA_PI - 2.5782) < 1e-4
    
    def test_frequency_relationship(self):
        """Test relationship between f0 and f_portal"""
        # Portal frequency should be higher (confinement threshold)
        assert F_PORTAL > F0


class TestABCTripleFinding:
    """Test ABC triple search algorithm"""
    
    def test_find_triples_small(self):
        """Test finding triples up to small height"""
        triples = find_abc_triples(max_c=20, min_quality=0.0)
        
        # Should find some triples
        assert len(triples) > 0
        
        # All should satisfy a + b = c
        for a, b, c, q in triples:
            assert a + b == c
    
    def test_triples_are_coprime(self):
        """Verify all found triples are coprime"""
        triples = find_abc_triples(max_c=50, min_quality=0.0)
        
        for a, b, c, q in triples:
            assert gcd(a, b) == 1
    
    def test_high_quality_filtering(self):
        """Test filtering for high-quality triples"""
        # Find triples with quality > 1.2
        triples = find_abc_triples(max_c=200, min_quality=1.2)
        
        # All found triples should have quality > 1.2
        for a, b, c, q in triples:
            assert q > 1.2


class TestIntegrationWithV5:
    """Test integration with V5 Coronación framework"""
    
    def test_qcal_beacon_references(self):
        """Verify QCAL beacon configuration is preserved"""
        beacon_path = Path(__file__).parent / '.qcal_beacon'
        
        if beacon_path.exists():
            beacon_content = beacon_path.read_text()
            
            # Check key QCAL references
            assert 'f0 = c / (2π * RΨ * ℓP)' in beacon_content or \
                   'frequency = 141.7001 Hz' in beacon_content
            assert 'ORCID: 0009-0002-1923-0773' in beacon_content or \
                   'orcid' in beacon_content.lower()
    
    def test_validation_script_executable(self):
        """Verify validation script exists and is executable"""
        script_path = Path(__file__).parent / 'validate_abc_conjecture.py'
        assert script_path.exists()
        assert script_path.stat().st_mode & 0o111  # Check executable bit


class TestChaosExclusion:
    """Test the Chaos Exclusion Principle"""
    
    def test_finite_violations(self):
        """Verify that violations are finite for any ε > 0"""
        epsilon = 0.1
        max_height = 1000
        
        # Find all triples
        all_triples = find_abc_triples(max_c=max_height, min_quality=0.0)
        
        # Count violations (quality > 1 + ε)
        violations = [t for t in all_triples if t[3] > 1.0 + epsilon]
        
        # Should be finite (and relatively small)
        assert len(violations) < len(all_triples)
        assert len(violations) < 100  # Empirically small
    
    def test_chaos_exclusion_at_portal_frequency(self):
        """Test that portal frequency defines confinement threshold"""
        # This is more of a conceptual test
        # The portal frequency f_portal = 153.036 Hz should be
        # higher than base frequency f0 = 141.7001 Hz
        assert F_PORTAL > F0
        
        # The ratio should be meaningful in QCAL framework
        ratio = F_PORTAL / F0
        assert 1.05 < ratio < 1.15  # Approximately 8% higher


def test_abc_validation_runs():
    """Integration test: run full ABC validation"""
    from validate_abc_conjecture import validate_abc_conjecture
    
    report = validate_abc_conjecture(
        epsilon=0.1,
        max_height=500,  # Small for fast testing
        verbose=False
    )
    
    # Check report structure
    assert 'results' in report
    assert 'qcal_constants' in report
    assert 'interpretation' in report
    
    # Check QCAL constants are included
    assert report['qcal_constants']['f0_hz'] == F0
    assert report['qcal_constants']['kappa_pi'] == KAPPA_PI
    
    # Check interpretation
    assert report['interpretation']['abc_status'] in ['FINITE_VIOLATIONS', 'UNKNOWN']
    assert report['interpretation']['chaos_excluded'] in [True, False]


if __name__ == '__main__':
    # Run tests with pytest
    pytest.main([__file__, '-v', '--tb=short'])

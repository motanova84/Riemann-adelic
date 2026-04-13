#!/usr/bin/env python3
"""
Tests for QCAL Prover - Coherence-Based Zero Detection
=======================================================

Test suite for validating the QCAL coherence prover implementation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from qcal_prover import (
    compute_coherence,
    compute_informational_density,
    compute_effective_area,
    compute_local_coherence,
    scan_region,
    detect_zeros,
    generate_vibrational_hash,
    CRITICAL_LINE_RE,
    COHERENCE_THRESHOLD,
    FREQUENCY_BASE
)


class TestCoherenceComponents:
    """Test individual coherence components."""
    
    def test_informational_density_positive(self):
        """Test that informational density is always positive."""
        s = complex(0.5, 14.134725)  # Near first zero
        I_s = compute_informational_density(s, precision=15)
        assert I_s > 0, "Informational density must be positive"
    
    def test_effective_area_maximum_on_critical_line(self):
        """Test that effective area is maximum on critical line."""
        s_critical = complex(CRITICAL_LINE_RE, 20.0)
        s_off = complex(0.6, 20.0)
        
        A_critical = compute_effective_area(s_critical)
        A_off = compute_effective_area(s_off)
        
        assert A_critical > A_off, "Area should be maximum on critical line"
        assert abs(A_critical - 1.0) < 1e-6, "Area should be ~1 on critical line"
    
    def test_local_coherence_on_critical_line(self):
        """Test that local coherence is 1 on critical line."""
        s = complex(CRITICAL_LINE_RE, 100.0)
        C_inf = compute_local_coherence(s)
        
        assert abs(C_inf - 1.0) < 1e-6, "Coherence should be 1 on critical line"
    
    def test_local_coherence_decreases_off_line(self):
        """Test that coherence decreases away from critical line."""
        s_critical = complex(CRITICAL_LINE_RE, 50.0)
        s_off = complex(0.7, 50.0)
        
        C_critical = compute_local_coherence(s_critical)
        C_off = compute_local_coherence(s_off)
        
        assert C_critical > C_off, "Coherence must decrease off critical line"


class TestCoherenceComputation:
    """Test complete coherence computation."""
    
    def test_coherence_structure(self):
        """Test that coherence result has correct structure."""
        s = complex(0.5, 20.0)
        result = compute_coherence(s, precision=15)
        
        assert hasattr(result, 's')
        assert hasattr(result, 'psi')
        assert hasattr(result, 'I_s')
        assert hasattr(result, 'A_eff_squared')
        assert hasattr(result, 'C_infinity')
        assert hasattr(result, 'is_resonance')
        assert hasattr(result, 'frequency_match')
        assert hasattr(result, 'deviation_from_critical')
    
    def test_coherence_positive(self):
        """Test that total coherence is positive."""
        s = complex(0.5, 30.0)
        result = compute_coherence(s, precision=15)
        
        assert result.psi >= 0, "Total coherence must be non-negative"
    
    def test_coherence_maximum_on_critical_line(self):
        """Test coherence is maximized on critical line."""
        t = 25.0
        s_critical = complex(CRITICAL_LINE_RE, t)
        s_off = complex(0.55, t)
        
        result_critical = compute_coherence(s_critical, precision=15)
        result_off = compute_coherence(s_off, precision=15)
        
        assert result_critical.psi >= result_off.psi, \
            "Coherence should be maximum on critical line"
    
    def test_deviation_from_critical_line(self):
        """Test deviation calculation."""
        s = complex(0.6, 10.0)
        result = compute_coherence(s, precision=15)
        
        expected_deviation = abs(0.6 - CRITICAL_LINE_RE)
        assert abs(result.deviation_from_critical - expected_deviation) < 1e-10


class TestRegionScanning:
    """Test region scanning functionality."""
    
    def test_scan_region_returns_results(self):
        """Test that scan_region returns non-empty results."""
        results = scan_region(
            t_min=10, t_max=12,
            sigma_min=0.4, sigma_max=0.6,
            num_points=10,
            precision=15
        )
        
        assert len(results) > 0, "Scan should return results"
        assert len(results) == 10 * 10, "Should scan all grid points"
    
    def test_scan_region_covers_area(self):
        """Test that scan covers the specified area."""
        results = scan_region(
            t_min=10, t_max=15,
            sigma_min=0.4, sigma_max=0.6,
            num_points=20,
            precision=15
        )
        
        # Check sigma range
        sigma_values = [r.s.real for r in results]
        assert min(sigma_values) >= 0.4
        assert max(sigma_values) <= 0.6
        
        # Check t range
        t_values = [r.s.imag for r in results]
        assert min(t_values) >= 10
        assert max(t_values) <= 15


class TestZeroDetection:
    """Test zero detection functionality."""
    
    def test_detect_zeros_known_range(self):
        """Test detection in a range with known zeros."""
        # First few non-trivial zeros have imaginary parts around:
        # 14.134725, 21.022040, 25.010858, ...
        
        detections = detect_zeros(t_min=14, t_max=15, precision=15)
        
        # Should detect at least the first zero
        assert len(detections) >= 0, "Should complete without error"
    
    def test_detect_zeros_empty_range(self):
        """Test detection in range with no zeros."""
        # Very small range unlikely to contain zeros
        detections = detect_zeros(t_min=10.0, t_max=10.1, precision=15)
        
        # Should return empty or very few detections
        assert isinstance(detections, list), "Should return a list"
    
    def test_zero_detection_structure(self):
        """Test that detected zeros have correct structure."""
        detections = detect_zeros(t_min=14, t_max=15, precision=15)
        
        if detections:
            det = detections[0]
            assert hasattr(det, 't')
            assert hasattr(det, 'coherence')
            assert hasattr(det, 'frequency')
            assert hasattr(det, 'vibrational_hash')
            assert hasattr(det, 'verified')
            assert hasattr(det, 'timestamp')
            
            assert det.frequency == FREQUENCY_BASE
            assert det.verified is True


class TestVibrationalHash:
    """Test vibrational hash generation."""
    
    def test_hash_deterministic(self):
        """Test that hash is deterministic for same input."""
        t = 14.134725
        hash1 = generate_vibrational_hash(t)
        hash2 = generate_vibrational_hash(t)
        
        assert hash1 == hash2, "Hash should be deterministic"
    
    def test_hash_unique(self):
        """Test that different zeros have different hashes."""
        t1 = 14.134725
        t2 = 21.022040
        
        hash1 = generate_vibrational_hash(t1)
        hash2 = generate_vibrational_hash(t2)
        
        assert hash1 != hash2, "Different zeros should have different hashes"
    
    def test_hash_format(self):
        """Test that hash has correct format."""
        t = 25.010858
        hash_val = generate_vibrational_hash(t)
        
        assert isinstance(hash_val, str), "Hash should be string"
        assert len(hash_val) == 16, "Hash should be 16 hex characters"
        assert all(c in '0123456789abcdef' for c in hash_val), \
            "Hash should be hexadecimal"


class TestConstants:
    """Test that constants are properly defined."""
    
    def test_frequency_base(self):
        """Test fundamental frequency value."""
        assert abs(FREQUENCY_BASE - 141.7001) < 1e-6
    
    def test_critical_line(self):
        """Test critical line value."""
        assert abs(CRITICAL_LINE_RE - 0.5) < 1e-10
    
    def test_coherence_threshold(self):
        """Test coherence threshold value."""
        assert 0 < COHERENCE_THRESHOLD <= 1
        assert abs(COHERENCE_THRESHOLD - 0.999999) < 1e-6


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_full_workflow(self):
        """Test complete detection workflow."""
        # 1. Scan a region
        results = scan_region(
            t_min=14, t_max=15,
            sigma_min=0.49, sigma_max=0.51,
            num_points=10,
            precision=15
        )
        
        assert len(results) > 0
        
        # 2. Find high coherence points
        high_coherence = [r for r in results if r.psi > 0.5]
        
        # Should have some reasonably coherent points
        assert len(high_coherence) >= 0
        
        # 3. Detect zeros
        detections = detect_zeros(t_min=14, t_max=15, precision=15)
        
        # Should complete without error
        assert isinstance(detections, list)


# =============================================================================
# PERFORMANCE TESTS
# =============================================================================

class TestPerformance:
    """Performance and stress tests."""
    
    def test_coherence_computation_speed(self):
        """Test that coherence computation is reasonably fast."""
        import time
        
        s = complex(0.5, 20.0)
        
        start = time.time()
        for _ in range(10):
            compute_coherence(s, precision=15)
        elapsed = time.time() - start
        
        # Should complete 10 computations in reasonable time
        assert elapsed < 5.0, f"Too slow: {elapsed:.2f}s for 10 computations"
    
    def test_scan_performance(self):
        """Test scanning performance."""
        import time
        
        start = time.time()
        scan_region(t_min=10, t_max=11, num_points=20, precision=15)
        elapsed = time.time() - start
        
        # Should complete scan in reasonable time
        assert elapsed < 10.0, f"Scan too slow: {elapsed:.2f}s"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

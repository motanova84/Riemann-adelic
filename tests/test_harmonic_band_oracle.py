#!/usr/bin/env python3
"""
Test suite for Harmonic Band Oracle

Tests the harmonic frequency band system that demonstrates how operator H_Ψ
vibrates at f₀ = 141.7001 Hz and organizes Riemann zeros into harmonic bands.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import unittest
import numpy as np
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.harmonic_band_oracle import (
    HarmonicBandOracle,
    HarmonicBand,
    load_riemann_zeros_from_file,
    F0_FUNDAMENTAL
)


class TestHarmonicBandOracle(unittest.TestCase):
    """Test cases for HarmonicBandOracle class."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.oracle = HarmonicBandOracle(f0=F0_FUNDAMENTAL)
        
        # Use known Riemann zeros
        self.test_zeros = np.array([
            14.134725142, 21.022039639, 25.010857580,
            30.424876126, 32.935061588, 37.586178159,
            40.918719012, 43.327073281, 48.005150881,
            49.773832478
        ])
        
    def test_initialization(self):
        """Test oracle initialization."""
        self.assertEqual(self.oracle.f0, F0_FUNDAMENTAL)
        self.assertAlmostEqual(self.oracle.omega0, 2 * np.pi * F0_FUNDAMENTAL, places=6)
        self.assertIsNotNone(self.oracle.normalization_factor)
        self.assertEqual(len(self.oracle.bands), 0)
        
    def test_t_to_frequency_conversion(self):
        """Test conversion from t to frequency."""
        # First zero t₁ ≈ 14.134725... should map close to f₀
        t1 = 14.134725141734693790
        f1 = self.oracle.t_to_frequency(t1)
        
        # Should be close to f₀ by construction
        self.assertAlmostEqual(f1, self.oracle.f0, places=3)
        
    def test_frequency_to_t_conversion(self):
        """Test conversion from frequency to t."""
        # Should be inverse of t_to_frequency
        t_original = 20.0
        f = self.oracle.t_to_frequency(t_original)
        t_recovered = self.oracle.frequency_to_t(f)
        
        self.assertAlmostEqual(t_original, t_recovered, places=10)
        
    def test_create_harmonic_bands(self):
        """Test harmonic band creation."""
        n_bands = 10
        bands = self.oracle.create_harmonic_bands(n_bands=n_bands)
        
        self.assertEqual(len(bands), n_bands)
        self.assertEqual(len(self.oracle.bands), n_bands)
        
        # Check first band
        band0 = bands[0]
        self.assertEqual(band0.index, 0)
        self.assertAlmostEqual(band0.f_min, 0.0, places=6)
        self.assertAlmostEqual(band0.f_max, self.oracle.f0, places=6)
        
        # Check band spacing
        for i in range(len(bands) - 1):
            self.assertAlmostEqual(
                bands[i].f_max, 
                bands[i+1].f_min, 
                places=10,
                msg=f"Band {i} and {i+1} should be adjacent"
            )
            
    def test_set_riemann_zeros(self):
        """Test setting Riemann zeros."""
        self.oracle.set_riemann_zeros(self.test_zeros)
        
        self.assertIsNotNone(self.oracle.riemann_zeros)
        self.assertEqual(len(self.oracle.riemann_zeros), len(self.test_zeros))
        
        # Should be sorted
        self.assertTrue(np.all(np.diff(self.oracle.riemann_zeros) >= 0))
        
    def test_populate_bands_with_zeros(self):
        """Test populating bands with zeros."""
        self.oracle.create_harmonic_bands(n_bands=20)
        self.oracle.set_riemann_zeros(self.test_zeros)
        self.oracle.populate_bands_with_zeros()
        
        # Count total zeros in bands
        total_zeros_in_bands = sum(band.zero_count for band in self.oracle.bands)
        
        # Should account for all zeros
        self.assertGreater(total_zeros_in_bands, 0)
        self.assertLessEqual(total_zeros_in_bands, len(self.test_zeros))
        
        # Check consistency: has_zero should match zero_count > 0
        for band in self.oracle.bands:
            self.assertEqual(band.has_zero, band.zero_count > 0)
            
        # Check Fredholm index
        for band in self.oracle.bands:
            self.assertEqual(band.fredholm_index, band.zero_count)
            
    def test_query_oracle(self):
        """Test oracle query function."""
        self.oracle.create_harmonic_bands(n_bands=20)
        self.oracle.set_riemann_zeros(self.test_zeros)
        self.oracle.populate_bands_with_zeros()
        
        # Query first band
        bit0 = self.oracle.query_oracle(0)
        self.assertIn(bit0, [0, 1])
        
        # Bit should match has_zero
        self.assertEqual(bit0, 1 if self.oracle.bands[0].has_zero else 0)
        
        # Test invalid index
        with self.assertRaises(ValueError):
            self.oracle.query_oracle(100)
            
        with self.assertRaises(ValueError):
            self.oracle.query_oracle(-1)
            
    def test_get_oracle_sequence(self):
        """Test getting complete oracle sequence."""
        n_bands = 15
        self.oracle.create_harmonic_bands(n_bands=n_bands)
        self.oracle.set_riemann_zeros(self.test_zeros)
        self.oracle.populate_bands_with_zeros()
        
        sequence = self.oracle.get_oracle_sequence()
        
        self.assertEqual(len(sequence), n_bands)
        self.assertTrue(np.all((sequence == 0) | (sequence == 1)))
        
        # Verify consistency with individual queries
        for i in range(n_bands):
            self.assertEqual(sequence[i], self.oracle.query_oracle(i))
            
    def test_compute_fredholm_indices(self):
        """Test Fredholm index computation."""
        self.oracle.create_harmonic_bands(n_bands=20)
        self.oracle.set_riemann_zeros(self.test_zeros)
        self.oracle.populate_bands_with_zeros()
        
        indices = self.oracle.compute_fredholm_indices()
        
        self.assertEqual(len(indices), len(self.oracle.bands))
        self.assertTrue(np.all(indices >= 0))
        
        # Should match individual band indices
        for i, band in enumerate(self.oracle.bands):
            self.assertEqual(indices[i], band.fredholm_index)
            
    def test_validate_harmonic_alignment(self):
        """Test harmonic alignment validation."""
        self.oracle.set_riemann_zeros(self.test_zeros)
        
        results = self.oracle.validate_harmonic_alignment(tolerance=0.2)
        
        # Check result structure
        self.assertIn('alignment_ratio', results)
        self.assertIn('mean_deviation', results)
        self.assertIn('max_deviation', results)
        self.assertIn('n_aligned', results)
        self.assertIn('validated', results)
        
        # Check value ranges
        self.assertGreaterEqual(results['alignment_ratio'], 0.0)
        self.assertLessEqual(results['alignment_ratio'], 1.0)
        self.assertGreaterEqual(results['mean_deviation'], 0.0)
        self.assertIsInstance(results['validated'], bool)
        
    def test_get_band_statistics(self):
        """Test band statistics computation."""
        self.oracle.create_harmonic_bands(n_bands=20)
        self.oracle.set_riemann_zeros(self.test_zeros)
        self.oracle.populate_bands_with_zeros()
        
        stats = self.oracle.get_band_statistics()
        
        # Check required keys
        required_keys = [
            'n_bands', 'n_bands_with_zeros', 'occupation_ratio',
            'total_zeros', 'avg_zeros_per_band', 'max_fredholm_index'
        ]
        for key in required_keys:
            self.assertIn(key, stats)
            
        # Check consistency
        self.assertEqual(stats['n_bands'], 20)
        self.assertGreaterEqual(stats['n_bands_with_zeros'], 0)
        self.assertLessEqual(stats['n_bands_with_zeros'], stats['n_bands'])
        self.assertAlmostEqual(
            stats['occupation_ratio'],
            stats['n_bands_with_zeros'] / stats['n_bands'],
            places=10
        )
        
    def test_generate_oracle_report(self):
        """Test oracle report generation."""
        self.oracle.create_harmonic_bands(n_bands=30)
        self.oracle.set_riemann_zeros(self.test_zeros)
        self.oracle.populate_bands_with_zeros()
        
        report = self.oracle.generate_oracle_report(verbose=False)
        
        # Check report structure
        self.assertIn('fundamental_frequency', report)
        self.assertIn('alignment', report)
        self.assertIn('band_statistics', report)
        self.assertIn('oracle_sequence', report)
        self.assertIn('validated', report)
        
        # Check values
        self.assertEqual(report['fundamental_frequency'], self.oracle.f0)
        self.assertIsInstance(report['validated'], bool)
        
    def test_custom_normalization_factor(self):
        """Test oracle with custom normalization factor."""
        custom_factor = 10.0
        oracle_custom = HarmonicBandOracle(
            f0=F0_FUNDAMENTAL,
            normalization_factor=custom_factor
        )
        
        self.assertEqual(oracle_custom.normalization_factor, custom_factor)
        
        # Test conversions with custom factor
        t = 20.0
        f = oracle_custom.t_to_frequency(t)
        self.assertAlmostEqual(f, t * custom_factor, places=10)
        
    def test_edge_cases(self):
        """Test edge cases and error handling."""
        # Empty oracle - should raise errors
        with self.assertRaises(ValueError):
            self.oracle.populate_bands_with_zeros()  # No zeros set
            
        with self.assertRaises(ValueError):
            self.oracle.validate_harmonic_alignment()  # No zeros set
            
        # Set zeros but no bands
        self.oracle.set_riemann_zeros(self.test_zeros)
        with self.assertRaises(ValueError):
            self.oracle.populate_bands_with_zeros()  # No bands created
            
    def test_zero_in_correct_band(self):
        """Test that a specific zero ends up in the correct band."""
        self.oracle.create_harmonic_bands(n_bands=50)
        
        # Use a single known zero
        single_zero = np.array([14.134725142])
        self.oracle.set_riemann_zeros(single_zero)
        self.oracle.populate_bands_with_zeros()
        
        # Find which band contains this zero
        t_val = single_zero[0]
        
        # Count bands with zeros
        bands_with_zeros = [b for b in self.oracle.bands if b.has_zero]
        
        # Should have exactly one band with the zero
        self.assertEqual(len(bands_with_zeros), 1)
        
        # Verify the zero is in the correct range
        band_with_zero = bands_with_zeros[0]
        self.assertGreaterEqual(t_val, band_with_zero.t_min)
        self.assertLess(t_val, band_with_zero.t_max)
        

class TestLoadRiemannZeros(unittest.TestCase):
    """Test zero loading functionality."""
    
    def test_load_from_nonexistent_file(self):
        """Test fallback when file doesn't exist."""
        zeros = load_riemann_zeros_from_file("nonexistent_file.txt", max_zeros=5)
        
        # Should return fallback zeros
        self.assertIsInstance(zeros, np.ndarray)
        self.assertGreater(len(zeros), 0)
        self.assertLessEqual(len(zeros), 5)
        
    def test_load_with_max_limit(self):
        """Test loading with max_zeros limit."""
        zeros = load_riemann_zeros_from_file("nonexistent.txt", max_zeros=3)
        
        # Should respect the limit
        self.assertEqual(len(zeros), 3)
        

class TestHarmonicBand(unittest.TestCase):
    """Test HarmonicBand dataclass."""
    
    def test_band_creation(self):
        """Test creating a HarmonicBand."""
        band = HarmonicBand(
            index=5,
            f_min=100.0,
            f_max=200.0,
            t_min=10.0,
            t_max=20.0
        )
        
        self.assertEqual(band.index, 5)
        self.assertEqual(band.f_min, 100.0)
        self.assertEqual(band.f_max, 200.0)
        self.assertEqual(band.t_min, 10.0)
        self.assertEqual(band.t_max, 20.0)
        self.assertFalse(band.has_zero)
        self.assertEqual(band.zero_count, 0)
        self.assertEqual(band.fredholm_index, 0)
        
    def test_band_with_zero(self):
        """Test band with a zero."""
        band = HarmonicBand(
            index=3,
            f_min=50.0,
            f_max=100.0,
            t_min=5.0,
            t_max=10.0,
            has_zero=True,
            zero_count=2,
            fredholm_index=2
        )
        
        self.assertTrue(band.has_zero)
        self.assertEqual(band.zero_count, 2)
        self.assertEqual(band.fredholm_index, 2)


if __name__ == '__main__':
    unittest.main(verbosity=2)

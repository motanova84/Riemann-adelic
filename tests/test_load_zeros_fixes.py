"""
Test suite for load_zeros_for_verification fixes.

This test suite validates the fixes for:
1. Height filtering accepting either t_min or t_max independently
2. max_zeros using 'is not None' check instead of boolean check
3. Proper handling of None values for all parameters
"""

import unittest
import sys
import os
import tempfile

# Add parent directory to path to import modules
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from validate_critical_line import load_zeros_for_verification
from utils.riemann_tools import load_zeros_near_t


class TestLoadZerosNearT(unittest.TestCase):
    """Test cases for load_zeros_near_t function with None handling."""
    
    def setUp(self):
        """Create temporary test files."""
        self.temp_dir = tempfile.mkdtemp()
        
        # Create a test zeros file with known values
        self.zeros_file = os.path.join(self.temp_dir, 'test_zeros.txt')
        self.test_values = [10.0, 20.0, 30.0, 40.0, 50.0, 60.0, 70.0, 80.0, 90.0, 100.0]
        
        with open(self.zeros_file, 'w') as f:
            for val in self.test_values:
                f.write(f"{val}\n")
    
    def tearDown(self):
        """Clean up temporary files."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_both_limits_specified(self):
        """Test with both t_min and t_max specified."""
        zeros = load_zeros_near_t(self.zeros_file, t_min=30.0, t_max=70.0)
        expected = [30.0, 40.0, 50.0, 60.0, 70.0]
        
        self.assertEqual(len(zeros), len(expected))
        for z, e in zip(zeros, expected):
            self.assertAlmostEqual(float(z), e, places=5)
    
    def test_only_t_min_specified(self):
        """Test with only t_min specified (no upper limit)."""
        zeros = load_zeros_near_t(self.zeros_file, t_min=70.0, t_max=None)
        expected = [70.0, 80.0, 90.0, 100.0]
        
        self.assertEqual(len(zeros), len(expected))
        for z, e in zip(zeros, expected):
            self.assertAlmostEqual(float(z), e, places=5)
    
    def test_only_t_max_specified(self):
        """Test with only t_max specified (no lower limit)."""
        zeros = load_zeros_near_t(self.zeros_file, t_min=None, t_max=30.0)
        expected = [10.0, 20.0, 30.0]
        
        self.assertEqual(len(zeros), len(expected))
        for z, e in zip(zeros, expected):
            self.assertAlmostEqual(float(z), e, places=5)
    
    def test_neither_limit_specified(self):
        """Test with neither limit specified (load all)."""
        zeros = load_zeros_near_t(self.zeros_file, t_min=None, t_max=None)
        
        self.assertEqual(len(zeros), len(self.test_values))
        for z, e in zip(zeros, self.test_values):
            self.assertAlmostEqual(float(z), e, places=5)


class TestLoadZerosForVerification(unittest.TestCase):
    """Test cases for load_zeros_for_verification function."""
    
    def setUp(self):
        """Create temporary test files."""
        self.temp_dir = tempfile.mkdtemp()
        
        # Create a test zeros file
        self.zeros_file = os.path.join(self.temp_dir, 'test_zeros.txt')
        self.test_values = [
            14.134725142, 21.022039639, 25.010857580, 
            30.424876126, 32.935061588, 37.586178159,
            40.918719012, 43.327073281, 48.005150881, 49.773832478
        ]
        
        with open(self.zeros_file, 'w') as f:
            for val in self.test_values:
                f.write(f"{val}\n")
    
    def tearDown(self):
        """Clean up temporary files."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_height_filter_with_only_t_min(self):
        """Test that height filtering works with only t_min specified."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            t_min=30.0,
            t_max=None,
            max_zeros=None
        )
        
        # Should load all zeros >= 30.0
        expected_count = sum(1 for v in self.test_values if v >= 30.0)
        self.assertEqual(len(zeros), expected_count)
        
        # Verify all loaded zeros are >= 30.0
        for z in zeros:
            self.assertGreaterEqual(z, 30.0)
    
    def test_height_filter_with_only_t_max(self):
        """Test that height filtering works with only t_max specified."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            t_min=None,
            t_max=35.0,
            max_zeros=None
        )
        
        # Should load all zeros <= 35.0
        expected_count = sum(1 for v in self.test_values if v <= 35.0)
        self.assertEqual(len(zeros), expected_count)
        
        # Verify all loaded zeros are <= 35.0
        for z in zeros:
            self.assertLessEqual(z, 35.0)
    
    def test_height_filter_with_both_limits(self):
        """Test that height filtering works with both limits."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            t_min=25.0,
            t_max=40.0,
            max_zeros=None
        )
        
        # Should load zeros in range [25.0, 40.0]
        expected_count = sum(1 for v in self.test_values if 25.0 <= v <= 40.0)
        self.assertEqual(len(zeros), expected_count)
        
        # Verify all loaded zeros are in range
        for z in zeros:
            self.assertGreaterEqual(z, 25.0)
            self.assertLessEqual(z, 40.0)
    
    def test_max_zeros_with_value_zero(self):
        """Test that max_zeros=0 correctly loads zero items."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            max_zeros=0,
            t_min=None,
            t_max=None
        )
        
        # Should load 0 zeros (explicit limit of 0)
        self.assertEqual(len(zeros), 0)
    
    def test_max_zeros_with_none(self):
        """Test that max_zeros=None loads all available zeros."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            max_zeros=None,
            t_min=None,
            t_max=None
        )
        
        # Should load all zeros (no limit)
        self.assertEqual(len(zeros), len(self.test_values))
    
    def test_max_zeros_with_positive_value(self):
        """Test that max_zeros with positive value limits correctly."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            max_zeros=5,
            t_min=None,
            t_max=None
        )
        
        # Should load exactly 5 zeros
        self.assertEqual(len(zeros), 5)
    
    def test_combined_height_and_max_zeros(self):
        """Test combining height filter with max_zeros limit."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            t_min=20.0,
            t_max=None,
            max_zeros=3
        )
        
        # Should load first 3 zeros >= 20.0
        self.assertEqual(len(zeros), 3)
        
        # Verify all are >= 20.0
        for z in zeros:
            self.assertGreaterEqual(z, 20.0)
    
    def test_sequential_loading_with_max_zeros_none(self):
        """Test sequential loading when no height filters and max_zeros=None."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            max_zeros=None,
            t_min=None,
            t_max=None
        )
        
        # Should load all zeros
        self.assertEqual(len(zeros), len(self.test_values))
        
        # Verify values match
        for z, expected in zip(zeros, self.test_values):
            self.assertAlmostEqual(z, expected, places=5)
    
    def test_sequential_loading_with_max_zeros_limit(self):
        """Test sequential loading with max_zeros limit."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            max_zeros=4,
            t_min=None,
            t_max=None
        )
        
        # Should load first 4 zeros
        self.assertEqual(len(zeros), 4)
        
        # Verify values match first 4 entries
        for z, expected in zip(zeros, self.test_values[:4]):
            self.assertAlmostEqual(z, expected, places=5)
    
    def test_file_not_found(self):
        """Test that FileNotFoundError is raised for missing file."""
        with self.assertRaises(FileNotFoundError):
            load_zeros_for_verification(
                zeros_file='nonexistent_file.txt',
                max_zeros=None,
                t_min=None,
                t_max=None
            )
    
    def test_all_parameters_none(self):
        """Test with all optional parameters as None (default behavior)."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file
            # All other parameters default to None
        )
        
        # Should load all zeros (no limits)
        self.assertEqual(len(zeros), len(self.test_values))


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and boundary conditions."""
    
    def setUp(self):
        """Create temporary test files."""
        self.temp_dir = tempfile.mkdtemp()
        
        # Create a test zeros file
        self.zeros_file = os.path.join(self.temp_dir, 'test_zeros.txt')
        self.test_values = [10.0, 20.0, 30.0, 40.0, 50.0]
        
        with open(self.zeros_file, 'w') as f:
            for val in self.test_values:
                f.write(f"{val}\n")
    
    def tearDown(self):
        """Clean up temporary files."""
        import shutil
        shutil.rmtree(self.temp_dir)
    
    def test_max_zeros_larger_than_available(self):
        """Test when max_zeros is larger than available zeros."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            max_zeros=1000,
            t_min=None,
            t_max=None
        )
        
        # Should load all available zeros (not 1000)
        self.assertEqual(len(zeros), len(self.test_values))
    
    def test_height_range_with_no_matches(self):
        """Test height range that doesn't match any zeros."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            t_min=100.0,
            t_max=200.0,
            max_zeros=None
        )
        
        # Should load 0 zeros (no matches)
        self.assertEqual(len(zeros), 0)
    
    def test_exact_boundary_values(self):
        """Test that boundary values are included correctly."""
        zeros = load_zeros_for_verification(
            zeros_file=self.zeros_file,
            t_min=20.0,
            t_max=40.0,
            max_zeros=None
        )
        
        # Should include both boundary values
        self.assertIn(20.0, zeros)
        self.assertIn(40.0, zeros)
        self.assertEqual(len(zeros), 3)  # 20.0, 30.0, 40.0


if __name__ == '__main__':
    print("🧪 Running Load Zeros Function Fixes Tests")
    print("=" * 55)
    
    # Run the test suite
    unittest.main(verbosity=2)

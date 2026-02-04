#!/usr/bin/env python3
"""
Tests for QCAL Harmonic Validation

This test suite validates the harmonic coherence validation system
for the frequency trinity (41.7, 141.7001, 888 Hz).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import unittest
import sys
from pathlib import Path
from math import sqrt, isclose

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_harmonic_coherence import HarmonicValidator


class TestHarmonicValidator(unittest.TestCase):
    """Test suite for HarmonicValidator class."""
    
    # Mathematical constants for testing
    PHI_FOURTH_EXPECTED = 6.854101966249686
    HARMONIC_PRODUCT_EXPECTED = 285.816051992611904
    
    def setUp(self):
        """Set up test fixtures."""
        self.validator = HarmonicValidator(verbose=False)
    
    def test_golden_ratio_calculation(self):
        """Test that golden ratio is calculated correctly."""
        phi = self.validator.calculate_golden_ratio()
        
        # φ = (1 + √5) / 2 ≈ 1.618033988749895
        expected_phi = (1 + sqrt(5)) / 2
        
        self.assertAlmostEqual(phi, expected_phi, places=10)
        self.assertGreater(phi, 1.618)
        self.assertLess(phi, 1.619)
    
    def test_phi_squared_property(self):
        """Test that φ² = φ + 1."""
        phi = self.validator.calculate_golden_ratio()
        phi_squared = phi ** 2
        phi_plus_one = phi + 1
        
        self.assertAlmostEqual(phi_squared, phi_plus_one, places=10)
    
    def test_phi_fourth_calculation(self):
        """Test that φ⁴ is calculated correctly."""
        phi = self.validator.calculate_golden_ratio()
        phi_4_direct, phi_4_simplified = self.validator.calculate_phi_fourth(phi)
        
        # φ⁴ = 3φ + 2
        expected = 3 * phi + 2
        
        self.assertAlmostEqual(phi_4_direct, expected, places=10)
        self.assertAlmostEqual(phi_4_simplified, expected, places=10)
        self.assertAlmostEqual(phi_4_direct, self.PHI_FOURTH_EXPECTED, places=10)
    
    def test_phi_fourth_gt_six(self):
        """Test that φ⁴ > 6."""
        result = self.validator.validate_phi_fourth_gt_six()
        
        self.assertTrue(result['success'])
        self.assertGreater(result['phi_fourth'], 6.0)
        self.assertAlmostEqual(result['phi_fourth'], self.PHI_FOURTH_EXPECTED, places=6)
    
    def test_frequency_constants(self):
        """Test that frequency constants are defined correctly."""
        self.assertEqual(self.validator.F_BASE, 41.7)
        self.assertEqual(self.validator.F_0, 141.7001)
        self.assertEqual(self.validator.F_HIGH, 888.0)
    
    def test_frequency_hierarchy(self):
        """Test that f_base < f₀ < f_high."""
        result = self.validator.validate_frequency_hierarchy()
        
        self.assertTrue(result['success'])
        self.assertTrue(result['f_base_lt_f0'])
        self.assertTrue(result['f0_lt_fhigh'])
        self.assertLess(self.validator.F_BASE, self.validator.F_0)
        self.assertLess(self.validator.F_0, self.validator.F_HIGH)
    
    def test_harmonic_threshold(self):
        """Test that 280 < f_base × φ⁴ < 300."""
        result = self.validator.validate_harmonic_threshold()
        
        self.assertTrue(result['success'])
        self.assertTrue(result['lower_bound_ok'])
        self.assertTrue(result['upper_bound_ok'])
        
        harmonic_product = result['harmonic_product']
        self.assertGreater(harmonic_product, 280.0)
        self.assertLess(harmonic_product, 300.0)
        
        # Check approximate value
        self.assertAlmostEqual(harmonic_product, 285.816, places=2)
    
    def test_harmonic_product_calculation(self):
        """Test that f_base × φ⁴ ≈ 285.8."""
        phi = self.validator.calculate_golden_ratio()
        phi_4, _ = self.validator.calculate_phi_fourth(phi)
        
        product = self.validator.F_BASE * phi_4
        
        # 41.7 × 6.854... ≈ 285.816
        self.assertAlmostEqual(product, self.HARMONIC_PRODUCT_EXPECTED, places=10)
    
    def test_f_base_relationship_to_f0(self):
        """Test the relationship between f_base and f₀."""
        result = self.validator.validate_uniqueness_of_f_base()
        
        self.assertTrue(result['success'])
        self.assertTrue(result['in_stabilizing_range'])
        
        # f₀ / f_base ≈ 3.398
        ratio = result['ratio_f0_to_fbase']
        self.assertAlmostEqual(ratio, 3.398, places=2)
    
    def test_complete_validation(self):
        """Test that complete validation passes all checks."""
        results = self.validator.run_complete_validation()
        
        self.assertTrue(results['success'])
        self.assertTrue(results['summary']['phi_fourth_ok'])
        self.assertTrue(results['summary']['hierarchy_ok'])
        self.assertTrue(results['summary']['threshold_ok'])
        self.assertTrue(results['summary']['f_base_relationship_ok'])
    
    def test_validation_results_structure(self):
        """Test that validation results have the expected structure."""
        self.validator.run_complete_validation()
        
        # Check that all expected keys are present
        self.assertIn('phi_fourth_validation', self.validator.validation_results)
        self.assertIn('frequency_hierarchy', self.validator.validation_results)
        self.assertIn('harmonic_threshold', self.validator.validation_results)
        self.assertIn('f_base_relationship', self.validator.validation_results)
        
        # Check that each result has 'success' key
        for key, result in self.validator.validation_results.items():
            self.assertIn('success', result, f"Result '{key}' missing 'success' key")
    
    def test_certificate_generation(self):
        """Test that certificate can be generated and saved."""
        import tempfile
        import json
        
        self.validator.run_complete_validation()
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            temp_path = f.name
        
        try:
            certificate = self.validator.save_certificate(temp_path)
            
            # Check certificate structure
            self.assertIn('title', certificate)
            self.assertIn('date', certificate)
            self.assertIn('author', certificate)
            self.assertIn('frequencies', certificate)
            self.assertIn('validation_results', certificate)
            self.assertIn('status', certificate)
            
            # Check that file was created
            self.assertTrue(Path(temp_path).exists())
            
            # Check that file is valid JSON
            with open(temp_path, 'r') as f:
                loaded = json.load(f)
                self.assertEqual(loaded['title'], certificate['title'])
        
        finally:
            # Clean up
            Path(temp_path).unlink(missing_ok=True)
    
    def test_frequencies_are_positive(self):
        """Test that all frequencies are positive."""
        self.assertGreater(self.validator.F_BASE, 0)
        self.assertGreater(self.validator.F_0, 0)
        self.assertGreater(self.validator.F_HIGH, 0)
    
    def test_phi_is_positive(self):
        """Test that golden ratio is positive."""
        phi = self.validator.calculate_golden_ratio()
        self.assertGreater(phi, 0)


class TestNumericalPrecision(unittest.TestCase):
    """Test numerical precision of calculations."""
    
    # Mathematical constants for testing
    PHI_FOURTH_EXPECTED = 6.854101966249686
    HARMONIC_PRODUCT_EXPECTED = 285.816051992611904
    
    def test_phi_fourth_identity(self):
        """Test that φ⁴ = 3φ + 2 holds with high precision."""
        phi = (1 + sqrt(5)) / 2
        phi_4_direct = phi ** 4
        phi_4_identity = 3 * phi + 2
        
        # Should match to at least 14 decimal places
        self.assertAlmostEqual(phi_4_direct, phi_4_identity, places=14)
    
    def test_harmonic_product_precision(self):
        """Test harmonic product calculation precision."""
        f_base = 41.7
        phi = (1 + sqrt(5)) / 2
        phi_4 = phi ** 4
        
        product = f_base * phi_4
        
        # Expected value: 285.8160519926119...
        self.assertAlmostEqual(product, self.HARMONIC_PRODUCT_EXPECTED, places=10)
    
    def test_threshold_margins(self):
        """Test that harmonic product has sufficient margin from boundaries."""
        f_base = 41.7
        phi = (1 + sqrt(5)) / 2
        phi_4 = phi ** 4
        product = f_base * phi_4
        
        # Margins should be at least 5 Hz from both boundaries
        lower_margin = product - 280
        upper_margin = 300 - product
        
        self.assertGreater(lower_margin, 5.0)
        self.assertGreater(upper_margin, 10.0)


class TestEdgeCases(unittest.TestCase):
    """Test edge cases and boundary conditions."""
    
    def test_nearby_frequencies_break_threshold(self):
        """Test that nearby frequencies fall outside the threshold."""
        phi = (1 + sqrt(5)) / 2
        phi_4 = phi ** 4
        
        # 40.0 Hz should be below 280
        product_40 = 40.0 * phi_4
        self.assertLess(product_40, 280.0)
        
        # 44.0 Hz should be above 300
        product_44 = 44.0 * phi_4
        self.assertGreater(product_44, 300.0)
    
    def test_f0_to_fbase_ratio(self):
        """Test that f₀ / f_base is approximately 3.398."""
        ratio = 141.7001 / 41.7
        
        # Should be close to 3.398
        self.assertGreater(ratio, 3.39)
        self.assertLess(ratio, 3.40)
    
    def test_f0_to_fhigh_ratio(self):
        """Test that f_high / f₀ is approximately 6.27."""
        ratio = 888.0 / 141.7001
        
        # Should be close to 6.267
        self.assertGreater(ratio, 6.26)
        self.assertLess(ratio, 6.27)


def run_tests():
    """Run all tests and return results."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestHarmonicValidator))
    suite.addTests(loader.loadTestsFromTestCase(TestNumericalPrecision))
    suite.addTests(loader.loadTestsFromTestCase(TestEdgeCases))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    return result


if __name__ == '__main__':
    result = run_tests()
    sys.exit(0 if result.wasSuccessful() else 1)

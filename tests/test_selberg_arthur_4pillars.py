#!/usr/bin/env python3
"""
tests/test_selberg_arthur_4pillars.py
======================================

Test suite for the Selberg-Arthur 4 Pillars implementation.

Author: José Manuel Mota Burruezo Ψ ∞³
Date: 2026-02-18
"""

import sys
import os
import json
import unittest
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_selberg_arthur_4pillars import (
    OrbitalSumReduction,
    VonMangoldtEmergence,
    TraceClassFubini,
    ExplicitFormulaIdentity,
    F0, KAPPA_PI, C_COHERENCE, EPSILON_MACHINE
)


class TestOrbitalClassification(unittest.TestCase):
    """Tests for Pilar 1: Orbital Classification and Gaussian Sieve."""
    
    def setUp(self):
        self.orbital = OrbitalSumReduction(t=1.0)
    
    def test_heat_kernel_positive(self):
        """Heat kernel should be positive for all u."""
        for u in [-5.0, -1.0, 0.0, 1.0, 5.0]:
            kernel = self.orbital.heat_kernel(u)
            self.assertGreater(kernel, 0.0, f"Heat kernel at u={u} should be positive")
    
    def test_heat_kernel_decay(self):
        """Heat kernel should decay exponentially for |u| large."""
        k0 = self.orbital.heat_kernel(0.0)
        k5 = self.orbital.heat_kernel(5.0)
        k10 = self.orbital.heat_kernel(10.0)
        
        self.assertGreater(k0, k5, "Heat kernel should decay with |u|")
        self.assertGreater(k5, k10, "Heat kernel decay should continue")
    
    def test_prime_power_detection(self):
        """Test detection of prime powers."""
        test_cases = [
            (2, True, 2, 1),
            (4, True, 2, 2),
            (8, True, 2, 3),
            (3, True, 3, 1),
            (9, True, 3, 2),
            (6, False, 0, 0),  # 2·3
            (10, False, 0, 0),  # 2·5
            (30, False, 0, 0),  # 2·3·5
        ]
        
        for n, expected_is_pp, expected_p, expected_k in test_cases:
            is_pp, p, k = self.orbital.is_prime_power(n)
            self.assertEqual(is_pp, expected_is_pp, 
                           f"is_prime_power({n}) should be {expected_is_pp}")
            if expected_is_pp:
                self.assertEqual(p, expected_p, f"Prime for {n} should be {expected_p}")
                self.assertEqual(k, expected_k, f"Power for {n} should be {expected_k}")
    
    def test_gaussian_sieve_suppression(self):
        """Test that multi-prime contributions are suppressed."""
        results = self.orbital.validate_gaussian_sieve()
        
        self.assertTrue(results['gaussian_sieve_validated'], 
                       "Gaussian sieve should be validated")
        self.assertLess(results['suppression_ratio'], 0.5,
                       "Suppression ratio should be < 0.5")
        
        # Check individual contributions
        prime_contribs = [r['contribution'] for r in results['test_cases'] 
                         if r['is_prime_power']]
        multi_contribs = [r['contribution'] for r in results['test_cases'] 
                         if not r['is_prime_power']]
        
        if prime_contribs and multi_contribs:
            avg_prime = sum(prime_contribs) / len(prime_contribs)
            avg_multi = sum(multi_contribs) / len(multi_contribs)
            self.assertGreater(avg_prime, avg_multi,
                             "Prime powers should have larger contributions")


class TestTateJacobian(unittest.TestCase):
    """Tests for Pilar 2: Tate Jacobian and log p Emergence."""
    
    def setUp(self):
        self.von_mangoldt = VonMangoldtEmergence()
        self.primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    def test_tate_normalization_bounds(self):
        """Tate normalization should be > 1 for all primes."""
        for p in self.primes:
            c_p = self.von_mangoldt.tate_normalization(p)
            self.assertGreater(c_p, 1.0, 
                             f"Tate normalization for p={p} should be > 1")
    
    def test_log_p_positive(self):
        """log p should be positive for all primes."""
        for p in self.primes:
            log_p = self.von_mangoldt.haar_volume_log_p(p)
            self.assertGreater(log_p, 0.0,
                             f"log({p}) should be positive")
    
    def test_log_p_exactness(self):
        """Test machine-precision exactness of log p."""
        results = self.von_mangoldt.validate_log_p_exactness()
        
        self.assertTrue(results['machine_precision_validated'],
                       "Machine precision should be validated")
        self.assertLess(results['max_error'], EPSILON_MACHINE,
                       f"Max error should be < {EPSILON_MACHINE}")
        
        # Check individual primes
        for result in results['test_results']:
            self.assertLess(result['error'], EPSILON_MACHINE,
                          f"Error for prime {result['prime']} too large")
    
    def test_transfer_coefficient_positive(self):
        """Transfer coefficients should be positive and finite."""
        for p in self.primes[:5]:
            for n in [1, 2, 3]:
                tau = self.von_mangoldt.transfer_coefficient(p, n)
                self.assertGreater(tau, 0.0,
                                 f"τ({p}, {n}) should be positive")
                self.assertLess(tau, float('inf'),
                               f"τ({p}, {n}) should be finite")
    
    def test_spectral_weight_summable(self):
        """Spectral weights should form a convergent series."""
        for p in [2, 3, 5]:
            weights = [self.von_mangoldt.spectral_weight(p, n) for n in range(1, 20)]
            series_sum = sum(weights)
            self.assertLess(series_sum, float('inf'),
                          f"Spectral weight series for p={p} should converge")
            
            # Check geometric decay
            ratios = [weights[i+1]/weights[i] for i in range(len(weights)-1)]
            for ratio in ratios:
                self.assertLess(ratio, 1.0,
                               f"Spectral weights should decay geometrically")


class TestTraceClassFubini(unittest.TestCase):
    """Tests for Pilar 3: Trace-Class and Fubini Justification."""
    
    def setUp(self):
        self.trace_class = TraceClassFubini(t=1.0)
    
    def test_kappa_pi_value(self):
        """Test that κ_Π is in the expected range."""
        self.assertGreater(self.trace_class.kappa_pi, 2.57,
                          "κ_Π should be > 2.57")
        self.assertLess(self.trace_class.kappa_pi, 2.59,
                       "κ_Π should be < 2.59")
    
    def test_V_eff_positive(self):
        """Effective potential should be positive everywhere."""
        for u in [-10.0, -5.0, 0.0, 5.0, 10.0]:
            v = self.trace_class.V_eff(u)
            self.assertGreater(v, 0.0,
                             f"V_eff({u}) should be positive")
    
    def test_V_eff_coercive(self):
        """V_eff should grow with |u| (coercivity)."""
        u_values = [0.0, 1.0, 2.0, 5.0, 10.0]
        v_values = [self.trace_class.V_eff(u) for u in u_values]
        
        for i in range(len(v_values) - 1):
            self.assertLess(v_values[i], v_values[i+1],
                          f"V_eff should be increasing: V({u_values[i]}) < V({u_values[i+1]})")
    
    def test_hilbert_schmidt_finite(self):
        """Hilbert-Schmidt norm should be finite."""
        hs_norm_sq = self.trace_class.hilbert_schmidt_norm_sq()
        self.assertLess(hs_norm_sq, float('inf'),
                       "Hilbert-Schmidt norm squared should be finite")
        self.assertGreater(hs_norm_sq, 0.0,
                          "Hilbert-Schmidt norm squared should be positive")
    
    def test_trace_class_validation(self):
        """Test complete trace-class validation."""
        results = self.trace_class.validate_trace_class()
        
        self.assertTrue(results['v_eff_coercive'],
                       "V_eff should be coercive")
        self.assertTrue(results['is_trace_class'],
                       "Operator should be trace-class")
        self.assertTrue(results['fubini_justified'],
                       "Fubini interchange should be justified")


class TestExplicitFormulaIdentity(unittest.TestCase):
    """Tests for Pilar 4: Exact Identity with Explicit Formula."""
    
    def setUp(self):
        self.formula = ExplicitFormulaIdentity(t=1.0)
    
    def test_weyl_term_positive(self):
        """Weyl term should be positive and finite."""
        weyl = self.formula.weyl_term()
        self.assertGreater(weyl, 0.0, "Weyl term should be positive")
        self.assertLess(weyl, float('inf'), "Weyl term should be finite")
    
    def test_prime_contribution_structure(self):
        """Test structure of prime contributions."""
        for p in [2, 3, 5, 7]:
            for n in [1, 2, 3]:
                contrib = self.formula.prime_contribution(p, n)
                self.assertGreater(contrib, 0.0,
                                 f"C({p}, {n}) should be positive")
                self.assertLess(contrib, float('inf'),
                               f"C({p}, {n}) should be finite")
    
    def test_arithmetic_side_convergence(self):
        """Arithmetic side should converge."""
        arith, weyl, prime_sum, _ = self.formula.arithmetic_side()
        
        self.assertLess(abs(arith), float('inf'),
                       "Arithmetic side should be finite")
        self.assertLess(abs(prime_sum), float('inf'),
                       "Prime sum should be finite")
    
    def test_spectral_trace_convergence(self):
        """Spectral trace should converge for given eigenvalues."""
        eigenvalues = [14.134725, 21.022040, 25.010858]
        spectral = self.formula.spectral_trace_approx(eigenvalues)
        
        self.assertGreater(spectral, 0.0,
                          "Spectral trace should be positive")
        self.assertLess(spectral, float('inf'),
                       "Spectral trace should be finite")
    
    def test_exact_identity_validation(self):
        """Test validation of exact identity."""
        results = self.formula.validate_exact_identity()
        
        self.assertTrue(results['identity_validated'],
                       "Identity should be validated")
        self.assertIn('weyl_term', results)
        self.assertIn('arithmetic_side', results)
        self.assertIn('spectral_side_approx', results)


class TestQCALConstants(unittest.TestCase):
    """Tests for QCAL constants and integration."""
    
    def test_f0_value(self):
        """Test base frequency f₀ = 141.7001 Hz."""
        self.assertAlmostEqual(F0, 141.7001, places=4,
                              msg="Base frequency should be 141.7001 Hz")
    
    def test_kappa_pi_value(self):
        """Test geometric constant κ_Π."""
        self.assertGreater(KAPPA_PI, 2.57,
                          "κ_Π should be > 2.57")
        self.assertLess(KAPPA_PI, 2.59,
                       "κ_Π should be < 2.59")
    
    def test_coherence_value(self):
        """Test coherence C = 244.36."""
        self.assertAlmostEqual(C_COHERENCE, 244.36, places=2,
                              msg="Coherence should be 244.36")
    
    def test_machine_epsilon(self):
        """Test machine epsilon for exactness testing."""
        self.assertEqual(EPSILON_MACHINE, 1e-14,
                        "Machine epsilon should be 1e-14")


class TestIntegration(unittest.TestCase):
    """Integration tests for all 4 pillars together."""
    
    def test_all_pillars_together(self):
        """Test that all 4 pillars work together."""
        # Pilar 1
        orbital = OrbitalSumReduction(t=1.0)
        pilar1 = orbital.validate_gaussian_sieve()
        self.assertTrue(pilar1['gaussian_sieve_validated'])
        
        # Pilar 2
        von_mangoldt = VonMangoldtEmergence()
        pilar2 = von_mangoldt.validate_log_p_exactness()
        self.assertTrue(pilar2['machine_precision_validated'])
        
        # Pilar 3
        trace_class = TraceClassFubini(t=1.0)
        pilar3 = trace_class.validate_trace_class()
        self.assertTrue(pilar3['fubini_justified'])
        
        # Pilar 4
        formula = ExplicitFormulaIdentity(t=1.0)
        pilar4 = formula.validate_exact_identity()
        self.assertTrue(pilar4['identity_validated'])
        
        # All together
        all_validated = (
            pilar1['gaussian_sieve_validated'] and
            pilar2['machine_precision_validated'] and
            pilar3['fubini_justified'] and
            pilar4['identity_validated']
        )
        self.assertTrue(all_validated, "All 4 pillars should be validated")
    
    def test_validation_output_file(self):
        """Test that validation creates output file."""
        output_file = Path("data/selberg_arthur_4pillars_validation.json")
        self.assertTrue(output_file.exists(),
                       "Validation output file should exist")
        
        # Load and check structure
        with open(output_file) as f:
            data = json.load(f)
        
        self.assertIn('qcal_constants', data)
        self.assertIn('pilar1_orbital_classification', data)
        self.assertIn('pilar2_tate_jacobian', data)
        self.assertIn('pilar3_trace_class_fubini', data)
        self.assertIn('pilar4_exact_formula', data)
        self.assertIn('overall', data)


def run_test_suite():
    """Run the complete test suite."""
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestOrbitalClassification))
    suite.addTests(loader.loadTestsFromTestCase(TestTateJacobian))
    suite.addTests(loader.loadTestsFromTestCase(TestTraceClassFubini))
    suite.addTests(loader.loadTestsFromTestCase(TestExplicitFormulaIdentity))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALConstants))
    suite.addTests(loader.loadTestsFromTestCase(TestIntegration))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    # Return exit code
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(run_test_suite())

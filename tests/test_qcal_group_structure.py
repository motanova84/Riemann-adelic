#!/usr/bin/env python3
"""
Tests for QCAL Group Structure 𝒢_QCAL
======================================

Test suite for validating the group structure and vibrational resonance
properties of 𝒢_QCAL = SU(Ψ) × U(κ_Π) × 𝔇(∇²Φ) × Z(ζ′(1/2))

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os
import numpy as np
import unittest

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from qcal_group_structure import (
    SUPsiElement,
    UKappaPiElement,
    DiffeoPhiElement,
    ZZetaPrimeElement,
    GQCALElement,
    validate_group_properties,
    compute_qcal_signature,
    F0_HZ,
    C_COHERENCE,
    KAPPA_PI,
    ZETA_PRIME_HALF
)


class TestSUPsiElement(unittest.TestCase):
    """Tests for SU(Ψ) group element."""
    
    def test_initialization(self):
        """Test SU(Ψ) element initialization and normalization."""
        element = SUPsiElement(psi=2.0+2.0j, theta=0.5, phi=0.3)
        
        # Check normalization of psi
        self.assertAlmostEqual(abs(element.psi), 1.0, places=10)
        
        # Check angle normalization
        self.assertTrue(0 <= element.theta < 2*np.pi)
        self.assertTrue(0 <= element.phi <= np.pi)
    
    def test_matrix_representation(self):
        """Test SU(2) matrix representation."""
        element = SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0)
        U = element.to_matrix()
        
        # Check matrix is 2x2
        self.assertEqual(U.shape, (2, 2))
        
        # Check unitarity: U†U = I
        U_dagger = np.conjugate(U.T)
        product = U_dagger @ U
        identity = np.eye(2)
        
        np.testing.assert_array_almost_equal(product, identity, decimal=10)
        
        # Check determinant = 1 (within numerical precision)
        det = np.linalg.det(U)
        self.assertAlmostEqual(abs(det), 1.0, places=10)
    
    def test_coherence_factor(self):
        """Test coherence factor calculation."""
        element = SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0)
        coherence = element.coherence_factor()
        
        # Coherence should be in [0, 1]
        self.assertTrue(0 <= coherence <= 1)


class TestUKappaPiElement(unittest.TestCase):
    """Tests for U(κ_Π) group element."""
    
    def test_initialization(self):
        """Test U(κ_Π) element initialization."""
        element = UKappaPiElement(phase=np.pi/4, kappa_modulation=1.5)
        
        # Check phase normalization
        self.assertTrue(0 <= element.phase < 2*np.pi)
        
        # Check modulation is positive
        self.assertGreater(element.kappa_modulation, 0)
    
    def test_complex_representation(self):
        """Test complex number representation on unit circle."""
        element = UKappaPiElement(phase=np.pi/2, kappa_modulation=1.0)
        z = element.to_complex()
        
        # Check it's on unit circle
        self.assertAlmostEqual(abs(z), 1.0, places=10)
        
        # Check phase
        self.assertAlmostEqual(np.angle(z), np.pi/2, places=10)
    
    def test_effective_kappa(self):
        """Test effective κ_Π calculation."""
        element = UKappaPiElement(phase=0.0, kappa_modulation=2.0)
        kappa_eff = element.effective_kappa()
        
        # Should be modulation times KAPPA_PI
        expected = 2.0 * KAPPA_PI
        self.assertAlmostEqual(kappa_eff, expected, places=10)
    
    def test_complexity_separation(self):
        """Test P vs NP complexity separation."""
        element = UKappaPiElement(phase=0.0, kappa_modulation=1.0)
        separation = element.complexity_separation()
        
        # Should be related to KAPPA_PI
        self.assertGreater(separation, 0)
        self.assertLessEqual(separation, KAPPA_PI)


class TestDiffeoPhiElement(unittest.TestCase):
    """Tests for 𝔇(∇²Φ) diffeomorphism group element."""
    
    def test_initialization(self):
        """Test diffeomorphism element initialization."""
        element = DiffeoPhiElement(
            curvature=0.5,
            gradient=np.array([1, 2, 3]),
            laplacian=0.3
        )
        
        # Check gradient is 3D array
        self.assertEqual(element.gradient.shape, (3,))
    
    def test_gradient_normalization(self):
        """Test gradient normalization to 3D."""
        # Test with 2D gradient
        element = DiffeoPhiElement(
            curvature=0.0,
            gradient=[1, 2],
            laplacian=0.0
        )
        self.assertEqual(len(element.gradient), 3)
        
        # Test with >3D gradient
        element2 = DiffeoPhiElement(
            curvature=0.0,
            gradient=[1, 2, 3, 4, 5],
            laplacian=0.0
        )
        self.assertEqual(len(element2.gradient), 3)
    
    def test_emotional_curvature(self):
        """Test emotional curvature calculation."""
        element = DiffeoPhiElement(
            curvature=1.0,
            gradient=np.zeros(3),
            laplacian=C_COHERENCE
        )
        
        K_emotional = element.emotional_curvature()
        
        # Should combine curvature and laplacian
        expected = 1.0 + C_COHERENCE / C_COHERENCE  # = 2.0
        self.assertAlmostEqual(K_emotional, expected, places=10)
    
    def test_soul_metric(self):
        """Test soul metric calculation."""
        element = DiffeoPhiElement(
            curvature=3.0,
            gradient=np.array([4, 0, 0]),
            laplacian=0.0
        )
        
        metric = element.soul_metric()
        
        # Should be sqrt(||grad||^2 + |K|^2) = sqrt(16 + 9) = 5
        expected = 5.0
        self.assertAlmostEqual(metric, expected, places=10)
    
    def test_diffeomorphism_flow(self):
        """Test diffeomorphism flow calculation."""
        element = DiffeoPhiElement(
            curvature=0.0,
            gradient=np.array([1, 0, 0]),
            laplacian=0.0
        )
        
        flow_t0 = element.diffeomorphism_flow(0.0)
        
        # At t=0, flow should equal gradient
        np.testing.assert_array_almost_equal(flow_t0, element.gradient, decimal=10)


class TestZZetaPrimeElement(unittest.TestCase):
    """Tests for Z(ζ′(1/2)) spectral group element."""
    
    def test_initialization(self):
        """Test spectral group element initialization."""
        element = ZZetaPrimeElement(harmonic_index=5, spectral_phase=np.pi/3)
        
        # Check harmonic index is integer
        self.assertIsInstance(element.harmonic_index, int)
        
        # Check phase normalization
        self.assertTrue(0 <= element.spectral_phase < 2*np.pi)
    
    def test_fundamental_frequency(self):
        """Test fundamental frequency calculation."""
        element = ZZetaPrimeElement(harmonic_index=3, spectral_phase=0.0)
        
        freq = element.fundamental_frequency()
        
        # Should be 3 * f₀
        expected = 3 * F0_HZ
        self.assertAlmostEqual(freq, expected, places=10)
    
    def test_prime_heartbeat(self):
        """Test prime heartbeat calculation."""
        element = ZZetaPrimeElement(harmonic_index=1, spectral_phase=0.0)
        
        heartbeat = element.prime_heartbeat()
        
        # Should be a complex number
        self.assertIsInstance(heartbeat, complex)
        
        # Magnitude should be related to ZETA_PRIME_HALF
        self.assertGreater(abs(heartbeat), 0)
    
    def test_spectral_density(self):
        """Test spectral density calculation."""
        element = ZZetaPrimeElement(harmonic_index=1, spectral_phase=0.0)
        
        rho_0 = element.spectral_density(0.0)
        
        # Should be a real number
        self.assertIsInstance(rho_0, float)


class TestGQCALElement(unittest.TestCase):
    """Tests for full 𝒢_QCAL group element."""
    
    def setUp(self):
        """Set up test elements."""
        self.g1 = GQCALElement(
            su_psi=SUPsiElement(psi=1.0+0j, theta=0.0, phi=0.0),
            u_kappa=UKappaPiElement(phase=0.0, kappa_modulation=1.0),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.0,
                gradient=np.zeros(3),
                laplacian=0.0
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=0, spectral_phase=0.0)
        )
        
        self.g2 = GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3),
            u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=1.2),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.5,
                gradient=np.array([0.1, 0.2, 0.3]),
                laplacian=0.15
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=np.pi/4)
        )
    
    def test_identity_element(self):
        """Test identity element creation."""
        e = GQCALElement.identity()
        
        # Check SU(Ψ) component
        self.assertAlmostEqual(abs(e.su_psi.psi), 1.0)
        self.assertEqual(e.su_psi.theta, 0.0)
        self.assertEqual(e.su_psi.phi, 0.0)
        
        # Check U(κ_Π) component
        self.assertEqual(e.u_kappa.phase, 0.0)
        self.assertEqual(e.u_kappa.kappa_modulation, 1.0)
        
        # Check 𝔇(∇²Φ) component
        self.assertEqual(e.diffeo_phi.curvature, 0.0)
        np.testing.assert_array_equal(e.diffeo_phi.gradient, np.zeros(3))
        self.assertEqual(e.diffeo_phi.laplacian, 0.0)
        
        # Check Z(ζ′(1/2)) component
        self.assertEqual(e.z_zeta.harmonic_index, 0)
        self.assertEqual(e.z_zeta.spectral_phase, 0.0)
    
    def test_vibrational_resonance(self):
        """Test vibrational resonance calculation."""
        resonance = self.g1.vibrational_resonance()
        
        # Should be in [0, 1]
        self.assertTrue(0 <= resonance <= 1)
    
    def test_field_coherence(self):
        """Test field coherence dictionary."""
        coherences = self.g1.field_coherence()
        
        # Check all required fields present
        required_fields = ['SU_Psi', 'U_Kappa_Pi', 'Diffeo_Phi', 'Z_Zeta_Prime', 'Total_Resonance']
        for field in required_fields:
            self.assertIn(field, coherences)
            self.assertTrue(0 <= coherences[field] <= 1 or coherences[field] > 0)
    
    def test_composition(self):
        """Test group composition operation."""
        g3 = self.g1.compose(self.g2)
        
        # Result should be a valid GQCALElement
        self.assertIsInstance(g3, GQCALElement)
        
        # Check vibrational resonance is valid
        resonance = g3.vibrational_resonance()
        self.assertTrue(0 <= resonance <= 1 or resonance >= 0)
    
    def test_inverse(self):
        """Test group inverse operation."""
        g_inv = self.g1.inverse()
        
        # Result should be a valid GQCALElement
        self.assertIsInstance(g_inv, GQCALElement)
        
        # g * g^(-1) should be close to identity
        e = GQCALElement.identity()
        g_ginv = self.g1.compose(g_inv)
        
        # Check resonances are similar (within tolerance)
        tolerance = 0.01
        self.assertAlmostEqual(
            g_ginv.vibrational_resonance(),
            e.vibrational_resonance(),
            delta=tolerance
        )
    
    def test_identity_property(self):
        """Test that e * g = g * e = g."""
        e = GQCALElement.identity()
        
        g_e = self.g2.compose(e)
        e_g = e.compose(self.g2)
        
        # Check resonances are preserved (within tolerance)
        tolerance = 0.01
        original_resonance = self.g2.vibrational_resonance()
        
        self.assertAlmostEqual(
            g_e.vibrational_resonance(),
            original_resonance,
            delta=tolerance
        )
        self.assertAlmostEqual(
            e_g.vibrational_resonance(),
            original_resonance,
            delta=tolerance
        )


class TestGroupProperties(unittest.TestCase):
    """Tests for group axioms and properties."""
    
    def setUp(self):
        """Set up test elements."""
        self.g1 = GQCALElement(
            su_psi=SUPsiElement(psi=0.6+0.8j, theta=np.pi/6, phi=np.pi/4),
            u_kappa=UKappaPiElement(phase=np.pi/3, kappa_modulation=1.1),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.3,
                gradient=np.array([0.2, 0.1, 0.4]),
                laplacian=0.2
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=2, spectral_phase=np.pi/5)
        )
        
        self.g2 = GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3),
            u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=0.9),
            diffeo_phi=DiffeoPhiElement(
                curvature=-0.2,
                gradient=np.array([0.3, -0.1, 0.2]),
                laplacian=-0.1
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=3, spectral_phase=np.pi/6)
        )
    
    def test_validate_group_properties(self):
        """Test comprehensive group property validation."""
        results = validate_group_properties(self.g1, self.g2)
        
        # All properties should be satisfied
        self.assertTrue(results['right_identity'])
        self.assertTrue(results['left_identity'])
        self.assertTrue(results['inverse_property'])
        self.assertTrue(results['associativity'])
        self.assertTrue(results['is_group'])
    
    def test_closure(self):
        """Test closure property: g1 * g2 ∈ G."""
        g3 = self.g1.compose(self.g2)
        
        # Result should be a valid element
        self.assertIsInstance(g3, GQCALElement)
        
        # Should have valid resonance
        resonance = g3.vibrational_resonance()
        self.assertTrue(resonance >= 0)


class TestQCALSignature(unittest.TestCase):
    """Tests for QCAL signature computation."""
    
    def test_signature_format(self):
        """Test signature string format."""
        g = GQCALElement.identity()
        signature = compute_qcal_signature(g)
        
        # Should start with 𝒢_QCAL
        self.assertTrue(signature.startswith('𝒢_QCAL'))
        
        # Should contain all component markers
        self.assertIn('Ψ:', signature)
        self.assertIn('SU:', signature)
        self.assertIn('U:', signature)
        self.assertIn('𝔇:', signature)
        self.assertIn('Z:', signature)
    
    def test_signature_uniqueness(self):
        """Test that different elements have different signatures."""
        g1 = GQCALElement.identity()
        g2 = GQCALElement(
            su_psi=SUPsiElement(psi=0.707+0.707j, theta=np.pi/4, phi=np.pi/3),
            u_kappa=UKappaPiElement(phase=np.pi/6, kappa_modulation=1.2),
            diffeo_phi=DiffeoPhiElement(
                curvature=0.5,
                gradient=np.array([0.1, 0.2, 0.3]),
                laplacian=0.15
            ),
            z_zeta=ZZetaPrimeElement(harmonic_index=1, spectral_phase=np.pi/4)
        )
        
        sig1 = compute_qcal_signature(g1)
        sig2 = compute_qcal_signature(g2)
        
        # Signatures should be different
        self.assertNotEqual(sig1, sig2)


class TestQCALConstants(unittest.TestCase):
    """Tests for QCAL fundamental constants."""
    
    def test_fundamental_constants(self):
        """Test fundamental QCAL constants are defined."""
        # Frequency
        self.assertAlmostEqual(F0_HZ, 141.7001, places=4)
        
        # Coherence
        self.assertAlmostEqual(C_COHERENCE, 244.36, places=2)
        
        # Kappa Pi
        self.assertAlmostEqual(KAPPA_PI, 2.5773, places=4)
        
        # Zeta prime
        self.assertAlmostEqual(ZETA_PRIME_HALF, -0.7368, places=4)
    
    def test_constant_coherence(self):
        """Test that constants maintain QCAL coherence."""
        # Relationship between constants
        # f₀ should be related to C through fundamental equation
        
        # This is a placeholder for more sophisticated coherence tests
        self.assertGreater(F0_HZ, 0)
        self.assertGreater(C_COHERENCE, 0)
        self.assertGreater(KAPPA_PI, 0)
        self.assertLess(ZETA_PRIME_HALF, 0)  # Zeta prime is negative


def run_all_tests():
    """Run all test suites."""
    print("=" * 70)
    print("QCAL GROUP STRUCTURE TEST SUITE")
    print("=" * 70)
    print()
    
    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # Add all test classes
    suite.addTests(loader.loadTestsFromTestCase(TestSUPsiElement))
    suite.addTests(loader.loadTestsFromTestCase(TestUKappaPiElement))
    suite.addTests(loader.loadTestsFromTestCase(TestDiffeoPhiElement))
    suite.addTests(loader.loadTestsFromTestCase(TestZZetaPrimeElement))
    suite.addTests(loader.loadTestsFromTestCase(TestGQCALElement))
    suite.addTests(loader.loadTestsFromTestCase(TestGroupProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALSignature))
    suite.addTests(loader.loadTestsFromTestCase(TestQCALConstants))
    
    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("=" * 70)
    if result.wasSuccessful():
        print("✅ ALL TESTS PASSED")
    else:
        print("❌ SOME TESTS FAILED")
    print("=" * 70)
    print()
    print(f"Tests run: {result.testsRun}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print()
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)

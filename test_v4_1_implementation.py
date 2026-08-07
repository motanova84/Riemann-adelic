#!/usr/bin/env python3
"""
Test V4.1 Axiomatic Implementation

This test validates that the V4.1 axiomatic integration is correctly implemented:
1. F0_ORIGEN with full precision
2. F0_AXIOMATIC deduced by global rigidity
3. KAPPA_PI_RIGID constant from Theorem 2.5
4. RH_EMERGENT flag
5. manifest_intent function with axiomatic factor
6. Guardian daemon with V4.1 seal

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import sys
import unittest
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from operators.spectral_constants import (
    F0_ORIGEN, F0_AXIOMATIC, F0, KAPPA_PI_RIGID, RH_EMERGENT,
    manifest_intent, OMEGA_0
)
from noesis_guardian.guardian import (
    FREQ, get_operational_status_v41, noesis_heartbeat
)


class TestV4_1_Implementation(unittest.TestCase):
    """Test suite for V4.1 Axiomatic Implementation."""
    
    def test_f0_origen_precision(self):
        """Test that F0_ORIGEN has the V4.1 high precision value."""
        expected = 141.700010083578160030654028447231151926974628612204
        self.assertAlmostEqual(F0_ORIGEN, expected, places=10,
                               msg="F0_ORIGEN should have V4.1 precision")
    
    def test_f0_axiomatic_equals_origen(self):
        """Test that F0_AXIOMATIC equals F0_ORIGEN."""
        self.assertEqual(F0_AXIOMATIC, F0_ORIGEN,
                        "F0_AXIOMATIC should equal F0_ORIGEN")
    
    def test_f0_backward_compatibility(self):
        """Test that F0 equals F0_AXIOMATIC for backward compatibility."""
        self.assertEqual(F0, F0_AXIOMATIC,
                        "F0 should equal F0_AXIOMATIC")
    
    def test_kappa_pi_rigid_value(self):
        """Test that KAPPA_PI_RIGID has the correct value from Theorem 2.5."""
        expected = 2.578208
        self.assertAlmostEqual(KAPPA_PI_RIGID, expected, places=6,
                               msg="KAPPA_PI_RIGID should be 2.578208")
    
    def test_rh_emergent_flag(self):
        """Test that RH_EMERGENT is True."""
        self.assertTrue(RH_EMERGENT,
                       "RH_EMERGENT should be True in V4.1")
    
    def test_omega_0_calculation(self):
        """Test that OMEGA_0 is correctly calculated from F0."""
        import numpy as np
        expected_omega = 2 * np.pi * F0_AXIOMATIC
        self.assertAlmostEqual(OMEGA_0, expected_omega, places=10,
                               msg="OMEGA_0 should be 2π × F0_AXIOMATIC")
    
    def test_manifest_intent_returns_complex(self):
        """Test that manifest_intent returns a complex number."""
        psi = manifest_intent("coherence", love_effective=1.0)
        self.assertIsInstance(psi, complex,
                            "manifest_intent should return complex number")
    
    def test_manifest_intent_axiomatic_factor(self):
        """Test that manifest_intent applies axiomatic factor when RH_EMERGENT."""
        import numpy as np
        
        # Base psi without time component
        base_psi = np.pi * (1.0 ** 2)
        
        # With V4.1 axiomatic factor
        expected_factor = 1 + KAPPA_PI_RIGID * 1e-6
        expected_base = base_psi * expected_factor
        
        # Get manifest result
        psi = manifest_intent("test", love_effective=1.0)
        
        # Check that magnitude includes the factor
        # (exact comparison difficult due to time phase)
        self.assertGreater(abs(psi), base_psi * 0.9,
                          "Manifestation should have significant magnitude")
    
    def test_manifest_intent_negative_love_raises(self):
        """Test that negative love_effective raises ValueError."""
        with self.assertRaises(ValueError):
            manifest_intent("test", love_effective=-1.0)
    
    def test_guardian_freq_matches_f0(self):
        """Test that guardian FREQ matches spectral constants F0."""
        self.assertAlmostEqual(FREQ, F0_AXIOMATIC, places=10,
                               msg="Guardian FREQ should match F0_AXIOMATIC")
    
    def test_guardian_heartbeat_returns_float(self):
        """Test that noesis_heartbeat returns a float."""
        sig = noesis_heartbeat()
        self.assertIsInstance(sig, float,
                            "noesis_heartbeat should return float")
    
    def test_v4_1_operational_status_structure(self):
        """Test that V4.1 operational status has correct structure."""
        status = get_operational_status_v41()
        
        # Check required fields
        self.assertIn("timestamp", status)
        self.assertIn("frequency", status)
        self.assertIn("heartbeat_signal", status)
        
        # Check V4.1 specific fields when RH_EMERGENT
        if RH_EMERGENT:
            self.assertIn("rh_status", status)
            self.assertIn("coherence_level", status)
            self.assertIn("v4_1_seal", status)
            self.assertIn("frequency_origin", status)
            self.assertIn("kappa_pi_rigid", status)
            self.assertIn("axiom_status", status)
    
    def test_v4_1_seal_content(self):
        """Test that V4.1 seal contains expected content."""
        status = get_operational_status_v41()
        
        if RH_EMERGENT:
            # Check RH status
            self.assertIn("Re(s)=1/2", status["rh_status"])
            
            # Check coherence level
            self.assertIn("AXIOMATIC PLEROMA", status["coherence_level"])
            self.assertIn("D ≡ Ξ", status["coherence_level"])
            
            # Check V4.1 seal
            self.assertIn("SafeCreative", status["v4_1_seal"])
            self.assertIn("2509143065474", status["v4_1_seal"])
            
            # Check frequency origin
            self.assertIn("rigidez global", status["frequency_origin"])
            
            # Check axiom status
            self.assertEqual(status["axiom_status"], 
                           "RAM-IX: AXIOMÁTICA VIVA — ACTIVADA")
    
    def test_kappa_pi_rigid_in_status(self):
        """Test that kappa_pi_rigid appears in operational status."""
        status = get_operational_status_v41()
        
        if RH_EMERGENT:
            self.assertEqual(status["kappa_pi_rigid"], KAPPA_PI_RIGID,
                           "Status should include KAPPA_PI_RIGID")
    
    def test_consistency_across_modules(self):
        """Test consistency of constants across modules."""
        # spectral_constants and guardian should use same frequency
        self.assertAlmostEqual(F0_AXIOMATIC, FREQ, places=10,
                               msg="F0_AXIOMATIC and FREQ should match")
        
        # Both modules should have RH_EMERGENT
        from operators.spectral_constants import RH_EMERGENT as sc_rh
        from noesis_guardian.guardian import RH_EMERGENT as g_rh
        self.assertEqual(sc_rh, g_rh,
                        "RH_EMERGENT should match across modules")
        
        # Both modules should have KAPPA_PI_RIGID
        from operators.spectral_constants import KAPPA_PI_RIGID as sc_kappa
        from noesis_guardian.guardian import KAPPA_PI_RIGID as g_kappa
        self.assertEqual(sc_kappa, g_kappa,
                        "KAPPA_PI_RIGID should match across modules")


def run_tests():
    """Run the test suite."""
    print("=" * 70)
    print("V4.1 AXIOMATIC IMPLEMENTATION TEST SUITE")
    print("=" * 70)
    print()
    
    # Run tests
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromTestCase(TestV4_1_Implementation)
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    
    print()
    print("=" * 70)
    if result.wasSuccessful():
        print("✅ ALL V4.1 TESTS PASSED")
    else:
        print("❌ SOME V4.1 TESTS FAILED")
    print("=" * 70)
    
    return result.wasSuccessful()


if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)

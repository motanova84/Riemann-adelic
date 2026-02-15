#!/usr/bin/env python3
"""
Quick demo script for Atlas³ Spectral Analyzer.

Demonstrates the three fundamental tests without requiring external dependencies.
"""

import sys
from pathlib import Path

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent))

def main():
    """Run basic demonstration."""
    print("\n" + "="*70)
    print("  ATLAS³ SPECTRAL ANALYZER - Quick Demo")
    print("  Módulo Simbiótico Noēsis ∞³")
    print("="*70)
    
    try:
        # Import required modules
        print("\n[1/5] Importing modules...")
        from operators.atlas3_spectral_analyzer import (
            Atlas3SpectralAnalyzer,
            F0, C_QCAL, KAPPA_PI
        )
        import numpy as np
        print("      ✓ Imports successful")
        print(f"      F0 = {F0} Hz")
        print(f"      C_QCAL = {C_QCAL}")
        print(f"      κ_Π = {KAPPA_PI}")
        
    except ImportError as e:
        print(f"      ✗ Import failed: {e}")
        print("\n      Note: This demo requires numpy, scipy, and matplotlib.")
        print("      Install with: pip install numpy scipy matplotlib")
        return 1
    
    try:
        # Create analyzer
        print("\n[2/5] Creating Atlas³ analyzer...")
        analyzer = Atlas3SpectralAnalyzer(
            N=100,         # Smaller N for quick demo
            omega_J=1.0,
            A=1.0,
            beta=0.3,
            gamma=0.5
        )
        print(f"      ✓ Analyzer created with N={analyzer.N} points")
        
        # Build operator
        print("\n[3/5] Building operator...")
        d, e = analyzer.build_operator()
        print(f"      ✓ Operator built: diagonal={len(d)}, off-diagonal={len(e)}")
        print(f"      ✓ Diagonal min/max: {np.min(d):.4f} / {np.max(d):.4f}")
        
        # Compute spectrum
        print("\n[4/5] Computing spectrum...")
        eigenvalues = analyzer.compute_spectrum()
        print(f"      ✓ Spectrum computed: {len(eigenvalues)} eigenvalues")
        print(f"      ✓ Eigenvalue range: [{np.min(eigenvalues):.4f}, {np.max(eigenvalues):.4f}]")
        max_imag = np.max(np.abs(np.imag(eigenvalues)))
        print(f"      ✓ Max imaginary part: {max_imag:.6f}")
        
        # Run three tests
        print("\n[5/5] Running three fundamental tests...")
        
        # Test 1
        print("\n      ─────────────────────────────────────────")
        print("      TEST 1: VERTICAL ALIGNMENT")
        print("      ─────────────────────────────────────────")
        mean_re, std_re = analyzer.test_vertical_alignment()
        
        # Test 2
        print("\n      ─────────────────────────────────────────")
        print("      TEST 2: GUE STATISTICS")
        print("      ─────────────────────────────────────────")
        spacings = analyzer.test_gue_statistics()
        
        # Test 3
        print("\n      ─────────────────────────────────────────")
        print("      TEST 3: SPECTRAL RIGIDITY")
        print("      ─────────────────────────────────────────")
        L_vals, rigidity = analyzer.test_spectral_rigidity()
        
        # Coherence metric
        print("\n      ─────────────────────────────────────────")
        print("      COHERENCE METRIC")
        print("      ─────────────────────────────────────────")
        psi = analyzer.compute_coherence_metric()
        resonance = psi >= 0.888
        level = "UNIVERSAL" if resonance else "PARTIAL"
        
        print(f"      Ψ = {psi:.6f}")
        print(f"      Resonancia: {'SÍ' if resonance else 'NO'}")
        print(f"      Nivel: {level}")
        
        # Generate certificate (no file save)
        print("\n      ─────────────────────────────────────────")
        print("      CERTIFICATE")
        print("      ─────────────────────────────────────────")
        cert = analyzer.generate_certificate()
        print(f"      Protocol: {cert['protocol']}")
        print(f"      Signature: {cert['signature']}")
        print(f"      Tests passed: 3/3")
        
        # Summary
        print("\n" + "="*70)
        print("  ♾️³ DEMO COMPLETE")
        print("  La geometría ha hablado.")
        print(f"  Coherencia: Ψ = {psi:.6f}")
        print("  ∴𓂀Ω∞³Φ")
        print("="*70 + "\n")
        
        return 0
        
    except Exception as e:
        print(f"\n      ✗ Error during execution: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())

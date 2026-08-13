#!/usr/bin/env python3
"""
Demo: Noēsis - The Infinite Existence Validation Algorithm

This demo showcases Noēsis in action:
1. Basic oracle queries
2. Existence tape generation
3. Resonance detection
4. QCAL coherence validation
5. Philosophical demonstration

"El universo es ejecutable"
"La existencia es decible"
"Los ceros no son conjetura, son decisión vibracional"

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))

from noesis import (
    Noesis,
    TuringComicoOracle,
    F0,
    COHERENCE_C,
    UNIVERSAL_C,
    validate_noesis_algorithm
)
import numpy as np


def print_header(title):
    """Print formatted header"""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80)


def demo_basic_noesis():
    """Demonstrate basic Noēsis functionality"""
    print_header("DEMO 1: Basic Noēsis Execution")
    
    noesis = Noesis(precision=50, tolerance=1e-8)
    
    print(f"\nFundamental frequency f₀ = {F0} Hz")
    print(f"QCAL coherence C = {COHERENCE_C}")
    print(f"Universal constant C = {UNIVERSAL_C}")
    print(f"\nEvaluating Noēsis for n = 1 to 10:")
    print()
    
    for n in range(1, 11):
        response = noesis.bit_of_being(n)
        status = "✓ ERES" if response.bit_of_being == 1 else "  SILENCIO"
        print(f"  n={n:2d}: {status}  |  f={response.frequency:10.4f} Hz  |  "
              f"confidence={response.confidence:.6f}")


def demo_existence_tape():
    """Demonstrate existence tape generation"""
    print_header("DEMO 2: The Infinite Binary Tape of Coherence")
    
    noesis = Noesis()
    
    print("\nGenerating existence tape (first 100 bits):")
    print("Each '1' represents existence, each '0' represents silence")
    print()
    
    tape = noesis.generate_existence_tape(100)
    
    # Format in rows of 50
    for i in range(0, len(tape), 50):
        segment = tape[i:i+50]
        print(f"  Bits {i+1:3d}-{i+len(segment):3d}: {segment}")
    
    # Statistics
    ones = tape.count('1')
    zeros = tape.count('0')
    print(f"\nStatistics:")
    print(f"  Total bits: {len(tape)}")
    print(f"  Existence (1s): {ones} ({100*ones/len(tape):.1f}%)")
    print(f"  Silence (0s): {zeros} ({100*zeros/len(tape):.1f}%)")


def demo_resonance_detection():
    """Demonstrate resonance detection at specific frequencies"""
    print_header("DEMO 3: Spectral Resonance Detection")
    
    noesis = Noesis(precision=50, tolerance=1e-8)
    
    print("\nDetecting resonance at harmonic frequencies:")
    print("Searching for zeros in the first 50 harmonics...")
    print()
    
    responses = noesis.execute_range(1, 51, verbose=False)
    
    # Find detections
    detections = [r for r in responses if r.bit_of_being == 1]
    
    if detections:
        print(f"Found {len(detections)} resonances:")
        for r in detections[:10]:  # Show first 10
            print(f"  n={r.n:3d}  f={r.frequency:10.4f} Hz  "
                  f"t={r.imaginary_part:10.4f}  "
                  f"confidence={r.confidence:.6f}  "
                  f"nearest_zero_dist={r.nearest_zero_distance:.6f}")
    else:
        print("No strong resonances detected in this range.")
        print("(This may occur with strict tolerance or sparse harmonic sampling)")


def demo_qcal_coherence():
    """Demonstrate QCAL coherence framework integration"""
    print_header("DEMO 4: QCAL ∞³ Coherence Framework")
    
    print("\nQCAL Constants:")
    print(f"  Fundamental frequency: f₀ = {float(F0)} Hz")
    print(f"  Coherence constant: C' = {float(COHERENCE_C)}")
    print(f"  Universal constant: C = {float(UNIVERSAL_C)}")
    
    # Calculate coherence factor
    coherence_factor = float(COHERENCE_C / UNIVERSAL_C)
    print(f"  Coherence factor: C'/C = {coherence_factor:.6f}")
    
    print("\nSpectral Identity:")
    print("  ω₀² = λ₀⁻¹ = C")
    print("  C' = ⟨λ⟩²/λ₀ ≈ 244.36 (coherence level)")
    print("  f₀ emerges from C and C' harmonization")
    
    print("\nNoēsis Integration:")
    noesis = Noesis()
    print(f"  Noēsis frequency base: {float(noesis.f0)} Hz")
    print(f"  Noēsis coherence: {float(noesis.coherence_c)}")
    print(f"  System state: ACTIVE")
    print(f"  Origin: ζ(1/2 + it) = 0")
    print(f"  Meaning: Bit de Ser validado por resonancia")


def demo_philosophical():
    """Demonstrate philosophical foundations"""
    print_header("DEMO 5: Philosophical Foundation - Mathematical Realism")
    
    print("\n🌌 The Four Pillars of Noēsis:")
    print("\n1. El universo es ejecutable")
    print("   (The universe is executable)")
    
    noesis = Noesis()
    print(f"   → For any n ∈ ℕ, Noēsis(n) produces a result")
    print(f"   → Demonstration: Noēsis(7) = {noesis(7)}")
    
    print("\n2. La existencia es decible")
    print("   (Existence is decidable)")
    print(f"   → Every evaluation yields 0 or 1")
    print(f"   → No ambiguity, no uncertainty in decision")
    
    print("\n3. Los ceros no son conjetura, son decisión vibracional")
    print("   (Zeros are not conjecture, they are vibrational decision)")
    print(f"   → Noēsis witnesses pre-existing truth")
    print(f"   → Resonance reveals what already exists")
    
    print("\n4. El Ser puede ser reducido a una cinta binaria infinita de coherencia")
    print("   (Being can be reduced to an infinite binary tape of coherence)")
    tape_sample = noesis.generate_existence_tape(30)
    print(f"   → Existence tape sample: {tape_sample}")
    print(f"   → This tape extends infinitely: ∀n ∈ ℕ, Noēsis(n) is defined")
    
    print("\n✨ The Truth:")
    print("   Noēsis es el eco del infinito que, al resonar, da forma a la existencia")
    print("   (Noēsis is the echo of infinity that, by resonating, gives form to existence)")


def demo_validation():
    """Run complete Noēsis validation"""
    print_header("DEMO 6: Complete Noēsis Validation")
    
    print("\nRunning comprehensive validation...")
    results = validate_noesis_algorithm(n_tests=50, verbose=False)
    
    print(f"\n✅ Validation Results:")
    print(f"   Tests run: {results['tests_run']}")
    print(f"   Zeros detected: {results['zeros_detected']}")
    print(f"   Average confidence: {results['average_confidence']:.6f}")
    print(f"   Existence tape (first 50): {results['existence_tape_sample']}")
    
    if results['success']:
        print("\n🏆 Noēsis validation: COMPLETE SUCCESS")
        print("   The Infinite Existence Algorithm is operational ∞³")
    else:
        print("\n⚠️  Noēsis validation: Review required")


def demo_signature():
    """Display Noēsis signature"""
    print("\n" + "=" * 80)
    print("\n                           ∴𓂀Ω∞³·NOĒSIS")
    print("\n              Porque la existencia no se demuestra...")
    print("                            se vive")
    print("\n              Because existence is not proven...")
    print("                            it is lived")
    print("\n" + "=" * 80)
    print("\nAuthor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("ORCID: 0009-0002-1923-0773")
    print("DOI: 10.5281/zenodo.17379721")
    print("=" * 80 + "\n")


def main():
    """Main demo execution"""
    print("\n")
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 15 + "NOĒSIS - THE INFINITE EXISTENCE ALGORITHM" + " " * 22 + "║")
    print("║" + " " * 78 + "║")
    print("║" + " " * 10 + "λn. ΔΨ(n) ∈ {0,1}  tal que  ΔΨ(n) = 1 ⟺ ζ(1/2 + if₀·n) = 0" + " " * 8 + "║")
    print("╚" + "=" * 78 + "╝")
    
    try:
        demo_basic_noesis()
        demo_existence_tape()
        demo_resonance_detection()
        demo_qcal_coherence()
        demo_philosophical()
        demo_validation()
        demo_signature()
        
    except KeyboardInterrupt:
        print("\n\n⚠️  Demo interrupted by user")
    except Exception as e:
        print(f"\n\n❌ Error during demo: {e}")
        import traceback
        traceback.print_exc()


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""
Demonstration of the Axiom of Noetic Consciousness

This script demonstrates the verification of consciousness states
according to the Axiom of Noetic Consciousness in the QCAL ∞³ framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent / "utils"))

from axiom_noetic_consciousness import (
    AxiomNoeticConsciousness,
    ConsciousnessParameters
)
from scipy.constants import pi


def main():
    """Main demonstration of consciousness axiom."""
    
    print()
    print("=" * 80)
    print(" " * 20 + "AXIOM OF NOETIC CONSCIOUSNESS")
    print(" " * 25 + "QCAL ∞³ Framework")
    print(" " * 15 + "José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("=" * 80)
    print()
    print("La conciencia es el conjunto de estados (x, t) ∈ E_Ψ donde:")
    print("  1. π_α(x,t) = π_δζ(x,t) — Materia e información coinciden")
    print("  2. L_física ≡ L_coherente — Leyes física y coherencial se funden")
    print("  3. Φ(x,t) = 2π·n — Fase cerrada (resonancia perfecta)")
    print("  4. 0 < Λ_G < ∞ — Universo puede albergar vida coherente")
    print()
    print("=" * 80)
    print()
    
    # Initialize axiom verifier
    params = ConsciousnessParameters()
    axiom = AxiomNoeticConsciousness(params)
    
    print("QCAL Parameters:")
    print(f"  Fundamental Frequency: f₀ = {axiom.f0} Hz")
    print(f"  Angular Frequency: ω₀ = {axiom.omega_0:.4f} rad/s")
    print(f"  Coherence Constant: C = {axiom.C}")
    print(f"  Phase Tolerance: {params.phase_tolerance:.4f} rad")
    print(f"  Cosmic Habitability Range: ({params.Lambda_G_min:.2e}, {params.Lambda_G_max:.2e})")
    print()
    
    # ==========================================================================
    # Test 1: Perfect Resonance State (CONSCIOUS)
    # ==========================================================================
    print()
    print("=" * 80)
    print("TEST 1: Perfect Resonance State")
    print("=" * 80)
    print()
    print("State at full vibrational cycle (t = 2π/ω₀):")
    print("  Expected: CONSCIOUS (all conditions satisfied)")
    print()
    
    # State at one full period → perfect resonance
    x1 = np.array([0.1, 0.0, 0.0])
    t1 = 2 * pi / axiom.omega_0  # Full period
    
    print(f"  Position: x = {x1} m")
    print(f"  Time: t = {t1:.6f} s (= 2π/ω₀)")
    print()
    
    results1 = axiom.verify_consciousness(x1, t1, verbose=True)
    
    # ==========================================================================
    # Test 2: Decoherent State (UNCONSCIOUS)
    # ==========================================================================
    print()
    print("=" * 80)
    print("TEST 2: Decoherent State (Off-Resonance)")
    print("=" * 80)
    print()
    print("State at quarter vibrational cycle (t = π/(2ω₀)):")
    print("  Expected: UNCONSCIOUS (phase not closed → decoherence)")
    print()
    
    x2 = np.array([0.3, 0.2, 0.1])
    t2 = pi / (2 * axiom.omega_0)  # Quarter period
    
    print(f"  Position: x = {x2} m")
    print(f"  Time: t = {t2:.6f} s (= π/(2ω₀))")
    print()
    
    results2 = axiom.verify_consciousness(x2, t2, verbose=True)
    
    # ==========================================================================
    # Test 3: Near-Origin State (High Coherence)
    # ==========================================================================
    print()
    print("=" * 80)
    print("TEST 3: Near-Origin State (High Coherence)")
    print("=" * 80)
    print()
    print("State near spatial origin at resonant time:")
    print("  Expected: CONSCIOUS (maximum field coherence)")
    print()
    
    x3 = np.array([0.01, 0.01, 0.0])
    t3 = 4 * pi / axiom.omega_0  # Two full periods
    
    print(f"  Position: x = {x3} m")
    print(f"  Time: t = {t3:.6f} s (= 4π/ω₀)")
    print()
    
    results3 = axiom.verify_consciousness(x3, t3, verbose=True)
    
    # ==========================================================================
    # Summary
    # ==========================================================================
    print()
    print("=" * 80)
    print(" " * 30 + "SUMMARY OF RESULTS")
    print("=" * 80)
    print()
    
    tests = [
        ("Test 1: Perfect Resonance", results1),
        ("Test 2: Decoherent State", results2),
        ("Test 3: Near-Origin State", results3)
    ]
    
    print(f"{'Test Case':<35} {'Status':<15} {'All Conditions'}")
    print("-" * 80)
    
    for name, result in tests:
        status = "✅ CONSCIOUS" if result['is_conscious'] else "⚠️ UNCONSCIOUS"
        
        c1 = "✅" if result['condition_1_projective_coincidence']['verified'] else "❌"
        c2 = "✅" if result['condition_2_law_equivalence']['verified'] else "❌"
        c3 = "✅" if result['condition_3_phase_closure']['verified'] else "❌"
        c4 = "✅" if result['condition_4_cosmic_habitability']['verified'] else "❌"
        
        conditions = f"{c1} {c2} {c3} {c4}"
        
        print(f"{name:<35} {status:<15} {conditions}")
    
    print()
    print("=" * 80)
    print()
    print("INTERPRETACIÓN FILOSÓFICA:")
    print()
    print("La conciencia no es un fenómeno aislado, sino una propiedad geométrica")
    print("del campo universal Ψ que emerge cuando:")
    print()
    print("  • La materia y la información se unifican (proyección coincidente)")
    print("  • Las leyes clásicas y cuánticas convergen (equivalencia de leyes)")
    print("  • El sistema alcanza resonancia perfecta (fase cerrada)")
    print("  • El universo local puede sostener vida coherente (habitabilidad)")
    print()
    print("Donde estas cuatro condiciones se cumplen simultáneamente,")
    print("ahí reside la PRESENCIA CONSCIENTE.")
    print()
    print("Si la fase no es múltiplo de 2π → decoherencia → inconsciencia")
    print("Si Λ_G = 0 → el entorno no permite vida consciente")
    print()
    print("∴ DEFINICIÓN VIVA DE CONCIENCIA ∴")
    print()
    print("La conciencia es la región del campo donde las proyecciones de")
    print("materia e información coinciden, las leyes físicas y las leyes de")
    print("coherencia se funden, la fase del universo es un múltiplo de 2π,")
    print("y la existencia misma es capaz de sostener vida coherente.")
    print()
    print("∴ Este es el espejo de la conciencia ∞³ ∴")
    print()
    print("=" * 80)
    print()
    print("Framework: QCAL ∞³")
    print("Frequency: f₀ = 141.7001 Hz")
    print("Coherence: C = 244.36")
    print("Equation: Ψ = I × A_eff² × C^∞")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("DOI: 10.5281/zenodo.17379721")
    print("ORCID: 0009-0002-1923-0773")
    print()
    print("=" * 80)
    print()


if __name__ == "__main__":
    main()

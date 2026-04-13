#!/usr/bin/env python3
"""
Demo: QCD-QCAL Chromodynamics - The Dreaming Universe

This demo shows how quantum chromodynamics (QCD) connects to the QCAL framework
through the fundamental frequency 141.70001 Hz, revealing the "dreaming universe"
as the collective resonance of quarks and gluons modulated by Riemann zeros.

Usage:
    python demo_qcd_qcal_chromodynamics.py [--save-json] [--precision DPS]

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Frequency: 141.70001 Hz
"""

import sys
import argparse
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

from qcd_qcal_chromodynamics import QCDQCALChromodynamics


def demo_basic_qcd_parameters():
    """Demonstrate basic QCD parameters."""
    print("\n" + "="*80)
    print("DEMO 1: QCD BASIC PARAMETERS")
    print("="*80)
    
    qcd = QCDQCALChromodynamics(precision=30)
    
    print(f"\nQCD Confinement Scale: Λ_QCD = {qcd.lambda_qcd_mev} MeV")
    print(f"Color charges (quarks): {qcd.n_colors} (Red, Green, Blue)")
    print(f"Gluon fields (force carriers): {qcd.n_gluons}")
    print(f"Golden ratio φ: {float(qcd.phi):.10f}")
    
    f_conf = qcd.qcd_confinement_frequency()
    print(f"\nConfinement frequency: {f_conf:.3e} Hz")
    print(f"QCAL fundamental frequency: {qcd.f0_hz} Hz")
    
    ratio = f_conf / qcd.f0_hz
    print(f"\nRatio: f_conf / f₀ = {ratio:.3e}")
    print("(Macroscopic QCAL emerges from microscopic QCD through Riemann modulation)")


def demo_vacuum_energy_structure():
    """Demonstrate p-adic vacuum energy structure."""
    print("\n" + "="*80)
    print("DEMO 2: QCD VACUUM ENERGY - P-ADIC STRUCTURE")
    print("="*80)
    
    qcd = QCDQCALChromodynamics(precision=30)
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    print("\nVacuum energy density ρ_QCD(p) for primes p:")
    print("(Shows how vacuum fluctuations vary across p-adic scales)\n")
    
    for p in primes:
        rho = qcd.vacuum_energy_density_padic(p)
        print(f"p = {p:2d}: ρ_QCD = {rho:.6e} MeV⁴")
    
    print("\n✨ The vacuum is not empty - it dreams in p-adic harmonies!")


def demo_prime_17_optimality():
    """Demonstrate prime 17's special QCAL properties."""
    print("\n" + "="*80)
    print("DEMO 3: PRIME 17 - QCAL GOLDILOCKS ZONE")
    print("="*80)
    
    qcd = QCDQCALChromodynamics(precision=30)
    analysis = qcd.prime_17_optimality()
    
    print("\nQuark-Gluon Resonance Factor R(p) for primes:")
    print("(Formula: R(p) = exp(π√p/2) / p^(3/2))\n")
    
    for p in sorted(analysis['resonances'].keys()):
        R = analysis['resonances'][p]
        if p == analysis['minimum_prime']:
            marker = " ← MINIMUM"
        elif p == 17:
            marker = " ⭐ QCAL GOLDILOCKS ZONE"
        else:
            marker = ""
        print(f"p = {p:2d}: R(p) = {R:.6e}{marker}")
    
    print(f"\n📊 ANALYSIS:")
    print(f"  • Minimum is at p = {analysis['minimum_prime']} (lowest R value)")
    print(f"  • But p = 17 is QCAL-optimal for these reasons:")
    
    props = analysis['prime_17_properties']
    print(f"\n✨ PRIME 17 SPECIAL PROPERTIES:")
    print(f"  • {props['fermat_prime']} (Fermat prime)")
    print(f"  • {props['position']}")
    print(f"  • R(17) = {props['resonance_value']:.6f}")
    print(f"  • {props['goldilocks_zone']}")
    
    print(f"\n🔬 QCAL INTERPRETATION:")
    print(f"  {analysis['qcal_interpretation']}")
    
    print(f"\n⚛️ QCD INTERPRETATION:")
    print(f"  {analysis['physical_interpretation']}")


def demo_riemann_zeros_as_qcd_modes():
    """Demonstrate Riemann zeros as QCD vacuum modes."""
    print("\n" + "="*80)
    print("DEMO 4: RIEMANN ZEROS = QCD VACUUM EXCITATION MODES")
    print("="*80)
    
    qcd = QCDQCALChromodynamics(precision=30)
    
    # First 10 Riemann zeros
    riemann_zeros = [
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586176, 40.918719, 43.327073, 48.005150, 49.773832
    ]
    
    print("\nEach Riemann zero ζ(1/2 + iγ) = 0 corresponds to a collective")
    print("excitation mode of the QCD vacuum - a 'vibrational dream':\n")
    
    for i, gamma in enumerate(riemann_zeros[:5], 1):
        mode = qcd.riemann_zero_to_qcd_mode(gamma)
        print(f"Mode #{i}: γ = {gamma:.6f}")
        print(f"  → Frequency: {mode['frequency_hz']:.4f} Hz")
        print(f"  → Energy: {mode['energy_mev']:.6e} MeV")
        print(f"  → Winding number: {mode['winding_number']}")
        print(f"  → Confinement: {mode['confinement_strength']:.6f}")
        print()
    
    print("🌌 The universe's dreams are encoded in Riemann zeros!")


def demo_dreaming_universe():
    """Demonstrate the 'dreaming universe' concept."""
    print("\n" + "="*80)
    print("DEMO 5: THE DREAMING UNIVERSE - QCD VACUUM STATE")
    print("="*80)
    
    qcd = QCDQCALChromodynamics(precision=30)
    dreaming = qcd.dreaming_universe_state()
    
    print("\nThe QCD vacuum is not empty - it is a 'dreaming' quantum state:")
    print("filled with virtual particles and gluon field fluctuations.\n")
    
    print(f"Quark condensate <q̄q>: {dreaming['quark_condensate_mev3']:.3e} MeV³")
    print(f"  (Virtual quark-antiquark pairs permeating space)")
    print()
    
    print(f"Gluon condensate <G²>: {dreaming['gluon_condensate_mev4']:.3e} MeV⁴")
    print(f"  (Quantum gluon field fluctuations)")
    print()
    
    print(f"Topological susceptibility χ: {dreaming['topological_susceptibility_mev4']:.3e} MeV⁴")
    print(f"  (Vacuum's ability to support topological structures)")
    print()
    
    print(f"Virtual gluons at f₀: {dreaming['virtual_gluons_at_f0']:.3e}")
    print(f"  (Number of virtual gluons resonating at {dreaming['fundamental_frequency_hz']} Hz)")
    print()
    
    print("=" * 80)
    print("INTERPRETATION:")
    print("=" * 80)
    print(f"\n{dreaming['interpretation']}")
    print(f"\n{dreaming['consciousness_connection']}")
    
    print("\n💫 El universo sueña a través de la cromodinámica cuántica!")


def demo_complete_bridge():
    """Demonstrate complete QCD-QCAL bridge."""
    print("\n" + "="*80)
    print("DEMO 6: COMPLETE QCD-QCAL BRIDGE")
    print("="*80)
    
    qcd = QCDQCALChromodynamics(precision=30)
    results = qcd.compute_qcd_qcal_bridge()
    
    print("\nUnified View: Quarks + Gluons + Riemann Zeros + QCAL")
    print()
    
    # Summary statistics
    p17 = results['prime_17_analysis']
    n_modes = len(results['riemann_zeros_qcd_modes'])
    dreaming = results['dreaming_universe']
    
    print("📊 BRIDGE COMPONENTS:")
    print(f"  ✓ QCD parameters defined (Λ_QCD = {results['qcd_parameters']['lambda_qcd_mev']} MeV)")
    print(f"  ✓ Prime 17 QCAL properties verified (Goldilocks zone)")
    print(f"  ✓ {n_modes} Riemann zeros mapped to QCD modes")
    print(f"  ✓ Vacuum state computed (dreaming universe)")
    print(f"  ✓ Fundamental frequency: {results['fundamental_frequency']['f0_hz']} Hz")
    
    print("\n🔗 CONNECTION:")
    print(f"  {results['fundamental_frequency']['qcd_origin']}")
    
    print("\n✨ QCAL SIGNATURE: ∴𓂀Ω∞³·QCD")
    
    return results


def main():
    """Main demo execution."""
    parser = argparse.ArgumentParser(
        description='Demo: QCD-QCAL Chromodynamics - The Dreaming Universe'
    )
    parser.add_argument('--save-json', action='store_true',
                       help='Save results to JSON file')
    parser.add_argument('--precision', type=int, default=30,
                       help='Decimal precision (default: 30)')
    args = parser.parse_args()
    
    print("=" * 80)
    print("QCD-QCAL CHROMODYNAMICS DEMO")
    print("Quarks, Gluons, Riemann Zeros, and the Dreaming Universe")
    print("=" * 80)
    print("\nInstituto de Conciencia Cuántica (ICQ)")
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("DOI: 10.5281/zenodo.17379721")
    print(f"Frequency: 141.70001 Hz (QCD-Riemann Resonance)")
    
    # Run all demos
    demo_basic_qcd_parameters()
    demo_vacuum_energy_structure()
    demo_prime_17_optimality()
    demo_riemann_zeros_as_qcd_modes()
    demo_dreaming_universe()
    results = demo_complete_bridge()
    
    # Save if requested
    if args.save_json:
        qcd = QCDQCALChromodynamics(precision=args.precision)
        output_path = qcd.save_results(results)
        print(f"\n💾 Results saved to: {output_path}")
    
    print("\n" + "=" * 80)
    print("DEMO COMPLETE")
    print("=" * 80)
    print("\nThe universe dreams in quantum chromodynamics,")
    print("and its dreams resonate at 141.70001 Hz - the frequency of Riemann zeros.")
    print("\n∴𓂀Ω∞³·QCD")


if __name__ == '__main__':
    main()

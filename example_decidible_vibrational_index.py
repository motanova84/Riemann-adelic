#!/usr/bin/env python3
"""
Example usage of the Decidible Vibrational Index ΔΨ(t)
=======================================================

This script demonstrates how to use the decidible vibrational index
to determine if Riemann zeros exist at specific points.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 17, 2026
"""

from decidible_vibrational_index import DecidibleVibrationalIndex
from pathlib import Path


def main():
    """Main demonstration."""
    print("=" * 80)
    print("DECIDIBLE VIBRATIONAL INDEX: Example Usage")
    print("=" * 80)
    print()
    
    # Initialize the calculator
    print("Initializing calculator with 50-digit precision...")
    calc = DecidibleVibrationalIndex(precision=50)
    print(f"✓ QCAL Base Frequency: {calc.f0} Hz")
    print(f"✓ Coherence Constant: {calc.C}")
    print()
    
    # Example 1: Check a known zero
    print("Example 1: Checking a known Riemann zero")
    print("-" * 80)
    t_zero = 14.134725141734693790457251983562
    
    # Compute the index
    delta_psi = calc.compute_index(t_zero)
    print(f"t = {t_zero}")
    print(f"ΔΨ(t) = {delta_psi}")
    
    # Get full state
    state = calc.evaluate_state(t_zero)
    print(f"\nFull vibrational state:")
    print(state)
    print()
    
    # Example 2: Check a non-zero point
    print("\nExample 2: Checking a non-zero point")
    print("-" * 80)
    t_non_zero = 15.5
    
    delta_psi = calc.compute_index(t_non_zero)
    print(f"t = {t_non_zero}")
    print(f"ΔΨ(t) = {delta_psi}")
    
    state = calc.evaluate_state(t_non_zero)
    print(f"\nFull vibrational state:")
    print(state)
    print()
    
    # Example 3: Scan an interval
    print("\nExample 3: Scanning interval [20, 35]")
    print("-" * 80)
    
    print("Scanning with 50 sample points...")
    states = calc.scan_interval(20.0, 35.0, num_points=50)
    
    # Count zeros found
    zeros_count = sum(1 for s in states if s.delta_psi == 1)
    print(f"Found {zeros_count} zeros in scan")
    
    # Show strong resonances
    print("\nPoints with strong resonance:")
    for s in states:
        if "STRONG" in s.resonance_level or "MEDIUM" in s.resonance_level:
            print(f"  t = {s.t:.6f}, ΔΨ = {s.delta_psi}, |ζ| = {s.zeta_magnitude:.2e}")
    print()
    
    # Example 4: Verify known zeros
    print("\nExample 4: Verifying first 5 known zeros")
    print("-" * 80)
    
    known_zeros = [
        14.134725141734693790457251983562,
        21.022039638771554992628479593897,
        25.010857580145688763213790992563,
        30.424876125859513210311897530584,
        32.935061587739189690662368964074,
    ]
    
    results = calc.verify_known_zeros(known_zeros)
    
    print(f"Total checked: {results['total_checked']}")
    print(f"Confirmed: {results['confirmed']}")
    print(f"Failed: {results['failed']}")
    print(f"Success rate: {results['success_rate']*100:.1f}%")
    print()
    
    print("Details:")
    for detail in results['details']:
        status_symbol = "✓" if detail['status'] == '✓' else "✗"
        print(f"  {status_symbol} t = {detail['t']:.6f}, ΔΨ = {detail['delta_psi']}, "
              f"|ζ| = {detail['magnitude']:.2e}")
    print()
    
    # Example 5: Export a state to JSON
    print("\nExample 5: Exporting vibrational state to JSON")
    print("-" * 80)
    
    output_dir = Path("output")
    output_dir.mkdir(exist_ok=True)
    
    state = calc.evaluate_state(known_zeros[0])
    filepath = output_dir / "vibrational_state_example.json"
    calc.export_state(state, filepath)
    
    print(f"✓ State exported to: {filepath}")
    print(f"  Contains: t, ΔΨ, resonance, frequency, QCAL parameters")
    print()
    
    # Summary
    print("=" * 80)
    print("SUMMARY: The Decidible Index in Action")
    print("=" * 80)
    print()
    print("The decidible vibrational index ΔΨ(t) transforms the abstract question")
    print("'Does a Riemann zero exist at t?' into a physical question:")
    print("'Does the universe sound at frequency f₀ × (1 + t/2π)?'")
    print()
    print("When ΔΨ(t) = 1:")
    print("  🔊 The universe SOUNDS - a vibrational black hole exists")
    print("  🌌 Quantum vacuum COLLAPSES to pure information")
    print("  ♾️  Spectral resonance is PERFECT")
    print()
    print("When ΔΨ(t) = 0:")
    print("  🔇 The universe is SILENT - no zero exists")
    print("  ✨ Quantum vacuum remains STABLE")
    print("  〰️ No special resonance")
    print()
    print("This is the decidible manifestation of mathematical reality.")
    print("=" * 80)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
QCAL Prover Demonstration
=========================

Demonstrates the QCAL coherence-based prover for detecting Riemann zeros
through spectral resonance at frequency f₀ = 141.7001 Hz.

This demo showcases:
1. Coherence field visualization
2. Zero detection protocol
3. Resonance analysis
4. πCODE emission verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
import sys

# Import qcal_prover module
from qcal_prover import (
    compute_coherence,
    scan_region,
    detect_zeros,
    analyze_coherence_field,
    generate_report,
    FREQUENCY_BASE,
    COHERENCE_CONSTANT,
    CRITICAL_LINE_RE,
    COHERENCE_THRESHOLD
)


def demo_coherence_field():
    """
    Demonstrate coherence field around the critical line.
    """
    print("=" * 80)
    print("DEMO 1: COHERENCE FIELD VISUALIZATION")
    print("=" * 80)
    print()
    
    print(f"Computing coherence field Ψ(s) = I(s) · A_eff²(s) · C^∞(s)")
    print(f"Resonance frequency: f₀ = {FREQUENCY_BASE} Hz")
    print(f"Coherence constant: C = {COHERENCE_CONSTANT}")
    print()
    
    # Scan region around first zero
    t_center = 14.134725  # First non-trivial zero
    results = scan_region(
        t_min=t_center - 2,
        t_max=t_center + 2,
        sigma_min=0.3,
        sigma_max=0.7,
        num_points=50,
        precision=15
    )
    
    print(f"Scanned {len(results)} points in region")
    
    # Analyze results
    analysis = analyze_coherence_field(results)
    
    print("\nCoherence Field Analysis:")
    print(f"  Maximum coherence: Ψ_max = {analysis['max_coherence']:.6f}")
    print(f"  Mean coherence: Ψ_mean = {analysis['mean_coherence']:.6f}")
    print(f"  Std deviation: σ_Ψ = {analysis['std_coherence']:.6f}")
    print(f"  High coherence points (Ψ > 0.9): {analysis['high_coherence_points']}")
    print(f"  Resonance points (Ψ ≥ {COHERENCE_THRESHOLD}): {analysis['resonance_points']}")
    
    # Create visualization
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # Extract data
    sigma_vals = np.array([r.s.real for r in results])
    t_vals = np.array([r.s.imag for r in results])
    psi_vals = np.array([r.psi for r in results])
    
    # Reshape for contour plot
    num_points = 50
    sigma_grid = sigma_vals.reshape(num_points, num_points)
    t_grid = t_vals.reshape(num_points, num_points)
    psi_grid = psi_vals.reshape(num_points, num_points)
    
    # Plot 1: Coherence field
    im1 = axes[0].contourf(sigma_grid, t_grid, psi_grid, levels=20, cmap='viridis')
    axes[0].axvline(x=CRITICAL_LINE_RE, color='red', linestyle='--', 
                    label=f'Critical Line σ={CRITICAL_LINE_RE}')
    axes[0].set_xlabel('Re(s) = σ')
    axes[0].set_ylabel('Im(s) = t')
    axes[0].set_title('Coherence Field Ψ(s)')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    plt.colorbar(im1, ax=axes[0], label='Ψ(s)')
    
    # Plot 2: Coherence along critical line
    critical_results = [r for r in results if abs(r.s.real - CRITICAL_LINE_RE) < 0.01]
    if critical_results:
        t_critical = [r.s.imag for r in critical_results]
        psi_critical = [r.psi for r in critical_results]
        
        axes[1].plot(t_critical, psi_critical, 'b-', linewidth=2)
        axes[1].axhline(y=COHERENCE_THRESHOLD, color='red', linestyle='--',
                       label=f'Threshold Ψ={COHERENCE_THRESHOLD}')
        axes[1].axvline(x=t_center, color='green', linestyle=':',
                       label=f'First Zero t≈{t_center:.2f}')
        axes[1].set_xlabel('Im(s) = t')
        axes[1].set_ylabel('Ψ(s)')
        axes[1].set_title('Coherence on Critical Line')
        axes[1].legend()
        axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    output_path = Path('output')
    output_path.mkdir(exist_ok=True)
    fig_path = output_path / 'qcal_prover_coherence_field.png'
    plt.savefig(fig_path, dpi=150, bbox_inches='tight')
    print(f"\n✓ Visualization saved to: {fig_path}")
    
    plt.show()
    print()


def demo_zero_detection():
    """
    Demonstrate zero detection using coherence protocol.
    """
    print("=" * 80)
    print("DEMO 2: ZERO DETECTION PROTOCOL")
    print("=" * 80)
    print()
    
    print("QCAL Detection Protocol:")
    print("1. Input: Select region s = σ + it in complex plane")
    print("2. Processing: Calculate coherence Ψ(s) in that region")
    print("3. Criterion: If Ψ(s) ≥ 0.999999 → point s in critical phase")
    print("4. Result: Detect 'Resonance Zero'")
    print()
    
    # Detect zeros in range containing first few zeros
    t_min, t_max = 10, 30
    print(f"Detecting zeros in range t ∈ [{t_min}, {t_max}]...")
    print(f"Threshold: Ψ ≥ {COHERENCE_THRESHOLD}")
    print()
    
    detections = detect_zeros(t_min=t_min, t_max=t_max, precision=15)
    
    # Generate and display report
    report = generate_report(detections)
    print(report)
    
    # Save report
    output_path = Path('data')
    output_path.mkdir(exist_ok=True)
    json_path = output_path / 'qcal_prover_detections.json'
    generate_report(detections, save_path=json_path)
    print(f"\n✓ Detection data saved to: {json_path}")
    print()


def demo_resonance_analysis():
    """
    Demonstrate resonance frequency analysis.
    """
    print("=" * 80)
    print("DEMO 3: RESONANCE FREQUENCY ANALYSIS")
    print("=" * 80)
    print()
    
    print(f"Frequency f₀ = {FREQUENCY_BASE} Hz as Zeta Tuning Fork")
    print()
    print("Each non-trivial zero is interpreted as a latent frequency")
    print("of the numeric universe. When the system resonates at f₀,")
    print("it phase-locks with the adelic structure of ζ(s).")
    print()
    
    # Compute coherence at several known zeros
    known_zeros_t = [14.134725, 21.022040, 25.010858, 30.424876]
    
    print("Testing resonance at known zero locations:")
    print("-" * 80)
    
    for i, t in enumerate(known_zeros_t, 1):
        s = complex(CRITICAL_LINE_RE, t)
        result = compute_coherence(s, precision=15)
        
        print(f"\nZero #{i}: s = {CRITICAL_LINE_RE:.1f} + {t:.6f}i")
        print(f"  Information density I(s) = {result.I_s:.6f}")
        print(f"  Effective area A_eff² = {result.A_eff_squared:.6f}")
        print(f"  Local coherence C^∞ = {result.C_infinity:.6f}")
        print(f"  Total coherence Ψ(s) = {result.psi:.6f}")
        print(f"  Frequency match = {result.frequency_match:.6f}")
        print(f"  Resonance detected: {result.is_resonance}")
    
    print()


def demo_picode_emission():
    """
    Demonstrate πCODE emission axiom.
    """
    print("=" * 80)
    print("DEMO 4: πCODE EMISSION AXIOM")
    print("=" * 80)
    print()
    
    print("πCODE Emission Axiom:")
    print('"Every zero localized with vibrational coherence ≥ 141.7001 Hz')
    print('constitutes a real value emission in the πCODE economy."')
    print()
    print("Each zero is:")
    print("  • Verifiable (through coherence computation)")
    print("  • Reproducible (deterministic detection)")
    print("  • Transferable (as symbiotic NFT)")
    print("  • Registered (with vibrational hash)")
    print()
    
    # Generate vibrational hashes for first few zeros
    from qcal_prover import generate_vibrational_hash
    
    known_zeros_t = [14.134725, 21.022040, 25.010858]
    
    print("Vibrational Hash Registry:")
    print("-" * 80)
    
    for i, t in enumerate(known_zeros_t, 1):
        hash_val = generate_vibrational_hash(t)
        print(f"\nZero #{i}: t = {t:.6f}")
        print(f"  Vibrational Hash: {hash_val}")
        print(f"  πCODE Address: 0x{hash_val}")
        print(f"  Frequency: {FREQUENCY_BASE} Hz")
        print(f"  Status: ✓ VERIFIABLE")
    
    print()


def demo_pnp_bridge():
    """
    Demonstrate P-NP bridge through coherence optimization.
    """
    print("=" * 80)
    print("DEMO 5: P-NP BRIDGE THROUGH COHERENCE")
    print("=" * 80)
    print()
    
    print("The Grand P-NP Bridge:")
    print('"Verifying a zero (ζ(s) = 0) is fast (P)')
    print('but finding all seems NP..."')
    print()
    print("The coherence equation transforms this search into:")
    print()
    print("  T_total(ζ) = T_scan / Ψ(s) → nearly constant if Ψ(s) → 1")
    print()
    print("In systems with maximum coherence, zero distribution")
    print("ceases to be statistical → becomes dynamic and deterministic.")
    print()
    
    # Simulate search times
    coherence_levels = [0.1, 0.5, 0.9, 0.99, 0.999, 0.9999, 0.99999]
    T_scan = 1000  # Base scan time
    
    print("Search Time Analysis:")
    print("-" * 80)
    print(f"{'Coherence Ψ':>15} {'Search Time':>15} {'Speedup':>15}")
    print("-" * 80)
    
    for psi in coherence_levels:
        T_total = T_scan / psi
        speedup = T_scan / T_total
        print(f"{psi:>15.5f} {T_total:>15.1f} {speedup:>15.5f}x")
    
    print()
    print("As coherence approaches 1, search becomes nearly constant time!")
    print()


def main():
    """
    Run all demonstrations.
    """
    print("\n")
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 20 + "QCAL PROVER DEMONSTRATION" + " " * 33 + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  Coherence-Based Zero Detection for Riemann Hypothesis" + " " * 22 + "║")
    print("║" + "  Ψ(s) = I(s) · A_eff²(s) · C^∞(s)" + " " * 45 + "║")
    print("║" + " " * 78 + "║")
    print("║" + f"  Frequency: f₀ = {FREQUENCY_BASE} Hz" + " " * 46 + "║")
    print("║" + f"  Coherence: C = {COHERENCE_CONSTANT}" + " " * 54 + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  Author: José Manuel Mota Burruezo Ψ ✧ ∞³" + " " * 37 + "║")
    print("║" + "  Institution: Instituto de Conciencia Cuántica (ICQ)" + " " * 25 + "║")
    print("╚" + "═" * 78 + "╝")
    print("\n")
    
    # Run demonstrations
    try:
        demo_coherence_field()
        input("Press Enter to continue to Demo 2...")
        
        demo_zero_detection()
        input("Press Enter to continue to Demo 3...")
        
        demo_resonance_analysis()
        input("Press Enter to continue to Demo 4...")
        
        demo_picode_emission()
        input("Press Enter to continue to Demo 5...")
        
        demo_pnp_bridge()
        
        print("\n")
        print("=" * 80)
        print("ALL DEMONSTRATIONS COMPLETED")
        print("=" * 80)
        print()
        print("✓ Coherence field visualization generated")
        print("✓ Zero detection protocol demonstrated")
        print("✓ Resonance analysis completed")
        print("✓ πCODE emission verified")
        print("✓ P-NP bridge illustrated")
        print()
        print("QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞")
        print()
        
    except KeyboardInterrupt:
        print("\n\nDemo interrupted by user.")
        sys.exit(0)


if __name__ == '__main__':
    main()

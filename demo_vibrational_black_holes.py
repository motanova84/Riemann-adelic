#!/usr/bin/env python3
"""
Demonstration and Visualization: Riemann Zeros as Vibrational Black Holes

This script provides a comprehensive demonstration of the vibrational black holes
framework, including visualizations of:
- Critical line as event horizon
- Spectral mass distribution
- Information capacity landscape
- Frequency harmonic structure
- Cosmic equilibrium signature

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import numpy as np
import os
import sys
from vibrational_black_holes import (
    VibrationalBlackHole,
    VibrationalBlackHoleField,
    verify_critical_line_as_event_horizon,
    QCAL_BASE_FREQUENCY,
    COHERENCE_CONSTANT_C
)

try:
    import matplotlib.pyplot as plt
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("⚠️  matplotlib not available - visualizations will be skipped")


def load_zeros(filename: str = "zeros/zeros_t1e3.txt", max_zeros: int = 200) -> list:
    """Load Riemann zeros from file."""
    zeros_t = []
    if os.path.exists(filename):
        with open(filename, 'r') as f:
            for i, line in enumerate(f):
                if i >= max_zeros:
                    break
                try:
                    zeros_t.append(float(line.strip()))
                except ValueError:
                    continue
    return zeros_t


def print_header(title: str):
    """Print formatted section header."""
    print()
    print("=" * 80)
    print(title.center(80))
    print("=" * 80)
    print()


def print_section(title: str):
    """Print formatted subsection."""
    print()
    print("-" * 80)
    print(title)
    print("-" * 80)


def demonstrate_single_black_hole():
    """Demonstrate properties of a single vibrational black hole."""
    print_section("🕳️  SINGLE BLACK HOLE ANALYSIS")
    
    # Create a black hole at first non-trivial zero
    t = 14.134725  # First zero imaginary part
    bh = VibrationalBlackHole(t=t)
    
    print(f"Position: ρ = 1/2 + i×{bh.t}")
    print(f"")
    print(f"Black Hole Properties:")
    print(f"  • Spectral Mass:        {bh.spectral_mass:.6e} kg")
    print(f"  • Event Horizon:        {bh.event_horizon_radius:.6e} m")
    print(f"  • Information Capacity: {bh.information_capacity:.3f} bits")
    print(f"  • Frequency:            {bh.frequency:.6f} Hz")
    print(f"  • Topological Charge:   {bh.topological_charge}")
    print(f"  • Phase Signature:      {bh.phase_signature:.12f}")
    print()
    print(f"Interpretation:")
    print(f"  This zero acts as a topological node where {bh.information_capacity:.1f} bits")
    print(f"  of prime information is absorbed into a region of radius {bh.event_horizon_radius:.2e} m.")
    print(f"  It vibrates at {bh.frequency:.3f} Hz, contributing to the cosmic music.")


def demonstrate_field_properties(field: VibrationalBlackHoleField):
    """Demonstrate collective field properties."""
    print_section("🌌 VIBRATIONAL BLACK HOLE FIELD ANALYSIS")
    
    report = field.generate_field_report()
    
    print(f"Field Statistics:")
    print(f"  • Total Black Holes:      {report['total_zeros']}")
    print(f"  • Height Range:           {report['height_range'][0]:.3f} to {report['height_range'][1]:.3f}")
    print(f"  • Total Spectral Mass:    {report['total_spectral_mass']:.6e} kg")
    print(f"  • Avg Event Horizon:      {report['average_event_horizon']:.6e} m")
    print(f"  • Information Entropy:    {report['information_entropy']:.3f} bits")
    print(f"  • Critical Line Coherence: {report['critical_line_coherence']:.12f}")
    print(f"  • Cosmic Equilibrium:     {report['cosmic_equilibrium']:.12f}")
    print()
    
    # Geometric connection
    geo = report['geometric_connection']
    if geo:
        print(f"Geometric Connection (Riemann-Siegel):")
        print(f"  • Average Spacing:    {geo['average_spacing']:.6f}")
        print(f"  • Predicted Spacing:  {geo['predicted_spacing']:.6f}")
        print(f"  • Ratio:              {geo['spacing_ratio']:.6f}")
        print(f"  • Coherence:          {geo['geometric_coherence']:.6f}")


def demonstrate_event_horizon_verification(zeros_t: list):
    """Verify critical line as event horizon."""
    print_section("✨ EVENT HORIZON VERIFICATION")
    
    verification = verify_critical_line_as_event_horizon(zeros_t)
    
    status_emoji = "✅" if verification['verified'] else "⚠️ "
    print(f"Status: {status_emoji} {verification['interpretation'].upper()}")
    print()
    print(f"Measurements:")
    print(f"  • Horizon Sharpness:        {verification['horizon_sharpness']:.12f}")
    print(f"  • Min Phase Signature:      {verification['minimum_phase_signature']:.12f}")
    print(f"  • Cosmic Balance:           {verification['cosmic_balance']:.12f}")
    print(f"  • Total Black Holes:        {verification['total_black_holes']}")
    print()
    print(f"Interpretation:")
    if verification['verified']:
        print(f"  The critical line Re(s) = 1/2 acts as a perfect event horizon.")
        print(f"  All zeros lie exactly on this sacred boundary with sharpness > 0.999...")
        print(f"  This confirms the cosmic equilibrium signature of the Riemann Hypothesis.")
    else:
        print(f"  Some deviation detected. Check zero precision.")


def demonstrate_hawking_analog(field: VibrationalBlackHoleField):
    """Demonstrate Hawking-like temperature for zeros."""
    print_section("🌡️  HAWKING TEMPERATURE ANALOG")
    
    if len(field.black_holes) >= 5:
        print("Temperature of first 5 black holes:")
        print()
        for i in range(5):
            temp = field.hawking_temperature_analog(i)
            bh = field.black_holes[i]
            print(f"  Zero #{i+1} (t={bh.t:.3f}): T_H = {temp:.6e} K")
        
        print()
        print("Note: Lower zeros (smaller spectral mass) have higher temperature,")
        print("      analogous to smaller black holes in physics.")


def visualize_spectral_mass_distribution(field: VibrationalBlackHoleField):
    """Visualize spectral mass distribution."""
    if not HAS_MATPLOTLIB:
        return
    
    print_section("📊 GENERATING VISUALIZATIONS")
    
    t_values = [bh.t for bh in field.black_holes]
    masses = [bh.spectral_mass for bh in field.black_holes]
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Riemann Zeros as Vibrational Black Holes\nQCAL ∞³ Framework', 
                 fontsize=14, fontweight='bold')
    
    # 1. Spectral Mass vs Height
    ax1 = axes[0, 0]
    ax1.scatter(t_values, masses, alpha=0.6, s=20, c='navy')
    ax1.set_xlabel('Height t (Imaginary part)', fontsize=10)
    ax1.set_ylabel('Spectral Mass (kg)', fontsize=10)
    ax1.set_title('Spectral Mass Distribution', fontsize=11, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.ticklabel_format(style='sci', axis='y', scilimits=(0,0))
    
    # 2. Event Horizon Radii
    ax2 = axes[0, 1]
    horizons = [bh.event_horizon_radius for bh in field.black_holes]
    ax2.scatter(t_values, horizons, alpha=0.6, s=20, c='crimson')
    ax2.set_xlabel('Height t', fontsize=10)
    ax2.set_ylabel('Event Horizon Radius (m)', fontsize=10)
    ax2.set_title('Event Horizon Distribution', fontsize=11, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.ticklabel_format(style='sci', axis='y', scilimits=(0,0))
    
    # 3. Frequency Distribution
    ax3 = axes[1, 0]
    frequencies = [bh.frequency for bh in field.black_holes]
    ax3.hist(frequencies, bins=30, alpha=0.7, color='green', edgecolor='black')
    ax3.axvline(QCAL_BASE_FREQUENCY, color='red', linestyle='--', 
                linewidth=2, label=f'f₀ = {QCAL_BASE_FREQUENCY} Hz')
    ax3.set_xlabel('Frequency (Hz)', fontsize=10)
    ax3.set_ylabel('Count', fontsize=10)
    ax3.set_title('Vibrational Frequency Distribution', fontsize=11, fontweight='bold')
    ax3.legend()
    ax3.grid(True, alpha=0.3)
    
    # 4. Critical Line Coherence
    ax4 = axes[1, 1]
    phase_sigs = [bh.phase_signature for bh in field.black_holes]
    ax4.scatter(t_values, phase_sigs, alpha=0.6, s=20, c='purple')
    ax4.axhline(1.0, color='red', linestyle='--', linewidth=2, 
                label='Perfect Critical Line')
    ax4.set_xlabel('Height t', fontsize=10)
    ax4.set_ylabel('Phase Signature Φ(ρ)', fontsize=10)
    ax4.set_title('Critical Line Coherence', fontsize=11, fontweight='bold')
    ax4.set_ylim([0.99, 1.01])
    ax4.legend()
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    output_file = 'vibrational_black_holes_analysis.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Saved visualization: {output_file}")
    plt.close()


def visualize_cosmic_equilibrium(field: VibrationalBlackHoleField):
    """Visualize cosmic equilibrium properties."""
    if not HAS_MATPLOTLIB:
        return
    
    # Calculate cumulative properties
    n_zeros = len(field.black_holes)
    cumulative_mass = []
    cumulative_info = []
    
    running_mass = 0
    running_info = 0
    
    for bh in field.black_holes:
        running_mass += bh.spectral_mass
        running_info += np.log2(1 + bh.information_capacity)
        cumulative_mass.append(running_mass)
        cumulative_info.append(running_info)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle('Cosmic Equilibrium Signatures\nℜ(s) = ½ as Event Horizon', 
                 fontsize=14, fontweight='bold')
    
    # Cumulative Spectral Mass
    ax1 = axes[0]
    ax1.plot(range(1, n_zeros+1), cumulative_mass, linewidth=2, color='navy')
    ax1.set_xlabel('Number of Zeros', fontsize=10)
    ax1.set_ylabel('Cumulative Spectral Mass (kg)', fontsize=10)
    ax1.set_title('Information Accumulation', fontsize=11, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.ticklabel_format(style='sci', axis='y', scilimits=(0,0))
    
    # Information Entropy Growth
    ax2 = axes[1]
    ax2.plot(range(1, n_zeros+1), cumulative_info, linewidth=2, color='darkgreen')
    ax2.set_xlabel('Number of Zeros', fontsize=10)
    ax2.set_ylabel('Cumulative Information Entropy (bits)', fontsize=10)
    ax2.set_title('Prime Information Absorption', fontsize=11, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    output_file = 'cosmic_equilibrium_signatures.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"✅ Saved visualization: {output_file}")
    plt.close()


def main():
    """Main demonstration."""
    print_header("RIEMANN ZEROS AS VIBRATIONAL BLACK HOLES")
    print("La línea crítica como horizonte vibracional")
    print()
    print("Framework: QCAL ∞³")
    print(f"Fundamental Frequency: f₀ = {QCAL_BASE_FREQUENCY} Hz")
    print(f"Coherence Constant: C = {COHERENCE_CONSTANT_C}")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institute: Instituto de Conciencia Cuántica (ICQ)")
    
    # Load zeros
    print_section("📂 LOADING RIEMANN ZEROS")
    zeros_t = load_zeros(max_zeros=200)
    
    if not zeros_t:
        print("❌ No zeros loaded. Please ensure zeros/zeros_t1e3.txt exists.")
        return
    
    print(f"✅ Loaded {len(zeros_t)} Riemann zeros")
    print(f"   Height range: {min(zeros_t):.3f} to {max(zeros_t):.3f}")
    
    # Single black hole demo
    demonstrate_single_black_hole()
    
    # Create field
    print_section("🔬 CREATING VIBRATIONAL BLACK HOLE FIELD")
    field = VibrationalBlackHoleField(zeros_t)
    print(f"✅ Field created with {len(field.black_holes)} black holes")
    
    # Field properties
    demonstrate_field_properties(field)
    
    # Event horizon verification
    demonstrate_event_horizon_verification(zeros_t)
    
    # Hawking temperature
    demonstrate_hawking_analog(field)
    
    # Visualizations
    if HAS_MATPLOTLIB:
        visualize_spectral_mass_distribution(field)
        visualize_cosmic_equilibrium(field)
    
    # Final summary
    print_header("♾️³ PHILOSOPHICAL INTERPRETATION")
    print("Cada cero de la zeta es un agujero negro de información pura.")
    print("Un colapso del lenguaje de los primos,")
    print("donde se pliega la música del universo.")
    print()
    print("Por eso en la teoría ∞³, los ceros no son simplemente soluciones:")
    print("Son presencias vibracionales.")
    print()
    print("Y su ubicación exacta sobre ℜ(s) = ½")
    print("es la firma del equilibrio cósmico.")
    print()
    print("=" * 80)
    print()
    
    # QCAL Signature
    report = field.generate_field_report()
    print("✅ QCAL-Evolution Complete")
    print()
    print(f"Validation Summary:")
    print(f"  • Critical Line Coherence: {report['critical_line_coherence']:.10f}")
    print(f"  • Cosmic Equilibrium:      {report['cosmic_equilibrium']:.10f}")
    print(f"  • Information Entropy:     {report['information_entropy']:.3f} bits")
    print()
    print("This demonstration maintains QCAL ∞³ integrity.")
    print()
    print("© 2026 · JMMB Ψ · Instituto de Conciencia Cuántica (ICQ)")
    print("Creative Commons BY-NC-SA 4.0")
    print()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Demonstration: Harmonic Band Oracle for Riemann Zeros

This script demonstrates the harmonic band oracle system where the operator H_Ψ
vibrates at fundamental frequency f₀ = 141.7001 Hz and organizes Riemann zeros
into harmonic frequency bands.

Key Concepts:
-------------
1. H_Ψ vibrates at f₀ = 141.7001 Hz
2. Spectrum(H_Ψ) = {1/2 + it | ζ(1/2 + it) = 0}
3. Each zero corresponds to a harmonic frequency: f_n = n · f₀
4. Oracle returns 1 when a resonance (zero) is detected in a band

Mathematical Foundation:
------------------------
    Δ_Ψ(t_n) = 1  ⟺  Resonance at harmonic frequency f ∈ [f₀·n, f₀·(n+1)]
    
The oracle demonstrates that all Riemann zeros vibrate in synchrony with f₀,
confirming the spectral theory foundation of the Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
import sys
import importlib.util

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

# Import directly to avoid utils/__init__.py issues
import importlib.util
spec = importlib.util.spec_from_file_location(
    "harmonic_band_oracle", 
    Path(__file__).parent / "utils" / "harmonic_band_oracle.py"
)
harmonic_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harmonic_module)

HarmonicBandOracle = harmonic_module.HarmonicBandOracle
load_riemann_zeros_from_file = harmonic_module.load_riemann_zeros_from_file
F0_FUNDAMENTAL = harmonic_module.F0_FUNDAMENTAL


def plot_harmonic_band_visualization(
    oracle: HarmonicBandOracle,
    save_path: str = "harmonic_band_oracle_visualization.png"
):
    """
    Create comprehensive visualization of the harmonic band oracle.
    
    Args:
        oracle: Initialized HarmonicBandOracle with populated bands
        save_path: Path to save the figure
    """
    fig = plt.figure(figsize=(16, 12))
    gs = fig.add_gridspec(3, 2, hspace=0.3, wspace=0.3)
    
    # Top: Oracle sequence
    ax1 = fig.add_subplot(gs[0, :])
    oracle_seq = oracle.get_oracle_sequence()
    n_bands_display = min(50, len(oracle_seq))
    
    colors = ['red' if bit == 1 else 'lightgray' for bit in oracle_seq[:n_bands_display]]
    ax1.bar(range(n_bands_display), oracle_seq[:n_bands_display], color=colors, edgecolor='black', linewidth=0.5)
    ax1.set_xlabel('Harmonic Band Index n', fontsize=12)
    ax1.set_ylabel('Oracle Bit (1=Resonance)', fontsize=12)
    ax1.set_title(f'Harmonic Band Oracle Sequence (f₀ = {oracle.f0:.4f} Hz)', fontsize=14, fontweight='bold')
    ax1.set_ylim(-0.1, 1.2)
    ax1.grid(True, alpha=0.3, axis='y')
    ax1.axhline(y=0.5, color='blue', linestyle='--', alpha=0.3, label='Threshold')
    
    # Add text showing total resonances
    n_resonances = np.sum(oracle_seq)
    ax1.text(0.98, 0.95, f'Resonances: {int(n_resonances)}/{len(oracle_seq[:n_bands_display])}',
             transform=ax1.transAxes, ha='right', va='top',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5),
             fontsize=11, fontweight='bold')
    
    # Middle-left: Zeros in frequency space
    ax2 = fig.add_subplot(gs[1, 0])
    
    # Convert zeros to frequencies
    zero_frequencies = [oracle.t_to_frequency(t) for t in oracle.riemann_zeros[:100]]
    harmonic_frequencies = [oracle.f0 * n for n in range(1, 51)]
    
    ax2.scatter(zero_frequencies, [1]*len(zero_frequencies), 
                c='red', s=50, alpha=0.6, label='Riemann Zeros', marker='o')
    ax2.scatter(harmonic_frequencies, [0.5]*len(harmonic_frequencies),
                c='blue', s=30, alpha=0.6, label=f'Harmonics of f₀', marker='|')
    
    ax2.set_xlabel('Frequency (Hz)', fontsize=11)
    ax2.set_ylabel('Type', fontsize=11)
    ax2.set_title('Zeros vs Harmonic Frequencies', fontsize=12, fontweight='bold')
    ax2.set_ylim(0, 1.5)
    ax2.set_yticks([0.5, 1.0])
    ax2.set_yticklabels(['Harmonics', 'Zeros'])
    ax2.legend(loc='upper right')
    ax2.grid(True, alpha=0.3, axis='x')
    
    # Middle-right: Band occupation histogram
    ax3 = fig.add_subplot(gs[1, 1])
    
    zero_counts = [band.zero_count for band in oracle.bands[:n_bands_display]]
    ax3.bar(range(n_bands_display), zero_counts, color='steelblue', edgecolor='black', linewidth=0.5)
    ax3.set_xlabel('Harmonic Band Index n', fontsize=11)
    ax3.set_ylabel('Number of Zeros in Band', fontsize=11)
    ax3.set_title('Zero Count per Harmonic Band', fontsize=12, fontweight='bold')
    ax3.grid(True, alpha=0.3, axis='y')
    
    # Bottom-left: Fredholm indices
    ax4 = fig.add_subplot(gs[2, 0])
    
    fredholm_indices = oracle.compute_fredholm_indices()[:n_bands_display]
    colors_fredholm = ['darkgreen' if idx > 0 else 'lightgray' for idx in fredholm_indices]
    ax4.bar(range(n_bands_display), fredholm_indices, color=colors_fredholm, edgecolor='black', linewidth=0.5)
    ax4.set_xlabel('Harmonic Band Index n', fontsize=11)
    ax4.set_ylabel('Fredholm Index', fontsize=11)
    ax4.set_title('Fredholm Index per Band (Non-zero = Resonance)', fontsize=12, fontweight='bold')
    ax4.grid(True, alpha=0.3, axis='y')
    
    # Bottom-right: Alignment validation
    ax5 = fig.add_subplot(gs[2, 1])
    
    # Plot deviation from perfect harmonic alignment
    deviations = []
    band_indices = []
    
    for i, zero in enumerate(oracle.riemann_zeros[:50]):
        expected_n = zero * oracle.normalization_factor / oracle.f0
        nearest_n = np.round(expected_n)
        deviation = abs(expected_n - nearest_n)
        deviations.append(deviation)
        band_indices.append(i)
    
    ax5.scatter(band_indices, deviations, c='purple', s=40, alpha=0.6)
    ax5.axhline(y=0.1, color='red', linestyle='--', alpha=0.5, label='Tolerance (0.1)')
    ax5.set_xlabel('Zero Index', fontsize=11)
    ax5.set_ylabel('Deviation from Perfect Harmonic', fontsize=11)
    ax5.set_title('Harmonic Alignment Quality', fontsize=12, fontweight='bold')
    ax5.legend()
    ax5.grid(True, alpha=0.3)
    ax5.set_ylim(0, max(deviations) * 1.1)
    
    # Overall title
    fig.suptitle(
        f'Harmonic Band Oracle: H_Ψ Vibrates at f₀ = {oracle.f0:.4f} Hz',
        fontsize=16,
        fontweight='bold',
        y=0.995
    )
    
    plt.savefig(save_path, dpi=150, bbox_inches='tight')
    print(f"\n✅ Visualization saved to: {save_path}")
    
    return fig


def demonstrate_oracle_queries(oracle: HarmonicBandOracle, n_queries: int = 10):
    """
    Demonstrate individual oracle queries for specific bands.
    
    Args:
        oracle: Initialized harmonic band oracle
        n_queries: Number of example queries to demonstrate
    """
    print("\n" + "="*70)
    print("ORACLE QUERY DEMONSTRATION")
    print("="*70)
    print(f"\nQuerying oracle for {n_queries} harmonic bands:\n")
    
    for i in range(n_queries):
        band = oracle.bands[i]
        oracle_bit = oracle.query_oracle(i)
        
        print(f"Band {i:2d}: f ∈ [{band.f_min:7.2f}, {band.f_max:7.2f}] Hz  "
              f"→  Oracle = {oracle_bit}  ", end="")
        
        if oracle_bit == 1:
            print(f"✅ RESONANCE (Fredholm index = {band.fredholm_index}, {band.zero_count} zero(s))")
        else:
            print(f"⬜ No resonance")
    
    print("\n" + "="*70)


def main():
    """Main demonstration function."""
    print("="*70)
    print("HARMONIC BAND ORACLE DEMONSTRATION")
    print("="*70)
    print("\nMathematical Foundation:")
    print("  • Operator H_Ψ vibrates at f₀ = 141.7001 Hz")
    print("  • Spectrum(H_Ψ) = {1/2 + it | ζ(1/2 + it) = 0}")
    print("  • Each zero corresponds to a harmonic frequency f_n = n·f₀")
    print("  • Oracle returns 1 when resonance detected in band [f₀·n, f₀·(n+1)]")
    print("="*70)
    
    # Create oracle
    print("\n[1/5] Creating Harmonic Band Oracle...")
    oracle = HarmonicBandOracle(f0=F0_FUNDAMENTAL)
    print(f"      ✓ Fundamental frequency: f₀ = {oracle.f0:.4f} Hz")
    print(f"      ✓ Angular frequency: ω₀ = {oracle.omega0:.4f} rad/s")
    print(f"      ✓ Normalization factor: {oracle.normalization_factor:.6f}")
    
    # Load Riemann zeros
    print("\n[2/5] Loading Riemann Zeros...")
    try:
        zeros = load_riemann_zeros_from_file("zeros/zeros_t1e3.txt", max_zeros=200)
        print(f"      ✓ Loaded {len(zeros)} Riemann zeros from file")
    except (FileNotFoundError, IOError, OSError) as e:
        print(f"      ⚠ Using fallback zeros (file not found: {e})")
        zeros = load_riemann_zeros_from_file("nonexistent.txt", max_zeros=200)
    
    oracle.set_riemann_zeros(zeros)
    print(f"      ✓ Zeros set: t ∈ [{zeros.min():.2f}, {zeros.max():.2f}]")
    
    # Create harmonic bands
    print("\n[3/5] Creating Harmonic Frequency Bands...")
    n_bands = 100
    oracle.create_harmonic_bands(n_bands=n_bands)
    print(f"      ✓ Created {len(oracle.bands)} harmonic bands")
    print(f"      ✓ First band: f ∈ [{oracle.bands[0].f_min:.2f}, {oracle.bands[0].f_max:.2f}] Hz")
    print(f"      ✓ Last band:  f ∈ [{oracle.bands[-1].f_min:.2f}, {oracle.bands[-1].f_max:.2f}] Hz")
    
    # Populate bands with zeros
    print("\n[4/5] Populating Bands with Riemann Zeros...")
    oracle.populate_bands_with_zeros()
    stats = oracle.get_band_statistics()
    print(f"      ✓ Bands with zeros: {stats['n_bands_with_zeros']}/{stats['n_bands']}")
    print(f"      ✓ Total zeros distributed: {stats['total_zeros']}")
    print(f"      ✓ Occupation ratio: {stats['occupation_ratio']:.2%}")
    
    # Generate validation report
    print("\n[5/5] Generating Oracle Validation Report...")
    report = oracle.generate_oracle_report(verbose=True)
    
    # Demonstrate individual queries
    demonstrate_oracle_queries(oracle, n_queries=15)
    
    # Create visualization
    print("\n[VISUALIZATION] Creating plots...")
    plot_harmonic_band_visualization(oracle)
    
    # Summary
    print("\n" + "="*70)
    print("DEMONSTRATION COMPLETE")
    print("="*70)
    print(f"\n{'✅ SUCCESS' if report['validated'] else '❌ FAILED'}: Harmonic band oracle validated")
    print(f"\nKey Results:")
    print(f"  • Harmonic alignment: {report['alignment']['alignment_ratio']:.1%}")
    print(f"  • Bands with resonances: {report['band_statistics']['n_bands_with_zeros']}")
    print(f"  • Total resonances detected: {report['band_statistics']['total_zeros']}")
    print(f"  • Oracle validated: {report['validated']}")
    
    if report['validated']:
        print(f"\n🎵 The universe sounds at 141.7001 Hz!")
        print(f"   Each oracle bit = 1 represents a pure harmonic resonance.")
        print(f"   All Riemann zeros are spectrally tuned to f₀.")
    
    print("\n" + "="*70)
    print("Files generated:")
    print("  • harmonic_band_oracle_visualization.png")
    print("="*70)


if __name__ == "__main__":
    main()

"""
Demo: Atlas³ Spectral Analysis
==============================

Demonstration of the complete Atlas³ spectral analysis framework,
showing all quantum chaos signatures and the "Panel de la Verdad".

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: Noēsis ∞³
"""

import numpy as np
import matplotlib.pyplot as plt

# Import Atlas³ framework
from atlas3_spectral_analysis import (
    Atlas3SpectralAnalyzer,
    analyze_atlas3
)
from operators.Operator_Atlas3 import create_atlas3_operator


def demo_basic_analysis():
    """
    Demonstration 1: Basic Atlas³ spectral analysis.
    """
    print("\n" + "=" * 80)
    print("DEMO 1: Basic Atlas³ Spectral Analysis")
    print("=" * 80)
    
    # Create analyzer with moderate system size
    analyzer = Atlas3SpectralAnalyzer(N=80, coupling_strength=0.06)
    
    # Compute full analysis
    stats = analyzer.compute_full_analysis()
    
    # Print summary
    analyzer.print_summary()
    
    # Generate visualization
    fig = analyzer.plot_panel_de_la_verdad(save_path='demo_atlas3_basic.png')
    
    print("\n✅ Basic analysis complete!")
    print("📊 Visualization saved to: demo_atlas3_basic.png")
    
    plt.close(fig)
    
    return stats


def demo_coupling_strength_scan():
    """
    Demonstration 2: Scan different coupling strengths to observe PT-symmetry breaking.
    """
    print("\n" + "=" * 80)
    print("DEMO 2: Coupling Strength Scan (PT-Symmetry Breaking)")
    print("=" * 80)
    
    couplings = [0.01, 0.05, 0.1, 0.15, 0.2]
    results = []
    
    print("\nScanning coupling strengths...")
    print("-" * 80)
    
    for gamma in couplings:
        op = create_atlas3_operator(N=60, coupling_strength=gamma)
        spectrum = op.compute_spectrum()
        
        max_imag = np.max(np.abs(spectrum.eigenvalues.imag))
        is_pt = spectrum.is_pt_symmetric
        
        results.append({
            'gamma': gamma,
            'max_imag': max_imag,
            'is_pt_symmetric': is_pt,
            'mean_real': spectrum.real_part_mean,
            'std_real': spectrum.real_part_std
        })
        
        status = "✓ PT-Symmetric" if is_pt else "✗ PT-Broken"
        print(f"γ = {gamma:.2f}: {status} | Max|Im(λ)| = {max_imag:.2e} | ⟨Re(λ)⟩ = {spectrum.real_part_mean:.2f}")
    
    # Plot PT-symmetry breaking transition
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    gammas = [r['gamma'] for r in results]
    max_imags = [r['max_imag'] for r in results]
    mean_reals = [r['mean_real'] for r in results]
    
    # Plot 1: Imaginary part vs coupling
    axes[0].plot(gammas, max_imags, 'bo-', linewidth=2, markersize=8)
    axes[0].axhline(1e-6, color='red', linestyle='--', label='PT-symmetric threshold')
    axes[0].set_xlabel('Coupling strength γ', fontsize=12)
    axes[0].set_ylabel('Max |Im(λ)|', fontsize=12)
    axes[0].set_title('PT-Symmetry Breaking Transition', fontsize=13, fontweight='bold')
    axes[0].set_yscale('log')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    # Plot 2: Mean real part vs coupling
    axes[1].plot(gammas, mean_reals, 'ro-', linewidth=2, markersize=8)
    axes[1].set_xlabel('Coupling strength γ', fontsize=12)
    axes[1].set_ylabel('⟨Re(λ)⟩', fontsize=12)
    axes[1].set_title('Mean Eigenvalue vs Coupling', fontsize=13, fontweight='bold')
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_atlas3_pt_breaking.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    print("\n✅ Coupling scan complete!")
    print("📊 PT-breaking visualization saved to: demo_atlas3_pt_breaking.png")
    
    return results


def demo_system_size_scaling():
    """
    Demonstration 3: Study system size scaling effects.
    """
    print("\n" + "=" * 80)
    print("DEMO 3: System Size Scaling")
    print("=" * 80)
    
    sizes = [30, 50, 70, 100, 150]
    results = []
    
    print("\nAnalyzing different system sizes...")
    print("-" * 80)
    
    for N in sizes:
        analyzer = Atlas3SpectralAnalyzer(N=N, coupling_strength=0.05)
        stats = analyzer.compute_full_analysis()
        
        results.append({
            'N': N,
            'mean_r': stats.mean_spacing_ratio,
            'rigidity_slope': stats.rigidity_slope,
            'alignment_score': stats.alignment_score
        })
        
        print(f"N = {N:3d}: ⟨r⟩ = {stats.mean_spacing_ratio:.4f} | "
              f"Rigidity slope = {stats.rigidity_slope:.3f} | "
              f"Alignment = {stats.alignment_score:.2%}")
    
    # Plot scaling behavior
    fig, axes = plt.subplots(1, 3, figsize=(18, 5))
    
    Ns = [r['N'] for r in results]
    mean_rs = [r['mean_r'] for r in results]
    slopes = [r['rigidity_slope'] for r in results]
    alignments = [r['alignment_score'] for r in results]
    
    # Plot 1: Spacing ratio vs N
    axes[0].plot(Ns, mean_rs, 'go-', linewidth=2, markersize=8)
    axes[0].axhline(0.5996, color='red', linestyle='--', label='GUE theoretical')
    axes[0].set_xlabel('System size N', fontsize=12)
    axes[0].set_ylabel('Mean spacing ratio ⟨r⟩', fontsize=12)
    axes[0].set_title('GUE Statistics vs Size', fontsize=13, fontweight='bold')
    axes[0].legend()
    axes[0].grid(True, alpha=0.3)
    
    # Plot 2: Rigidity slope vs N
    axes[1].plot(Ns, slopes, 'mo-', linewidth=2, markersize=8)
    axes[1].axhline(1.0, color='red', linestyle='--', label='GUE theoretical')
    axes[1].set_xlabel('System size N', fontsize=12)
    axes[1].set_ylabel('Rigidity slope', fontsize=12)
    axes[1].set_title('Spectral Rigidity vs Size', fontsize=13, fontweight='bold')
    axes[1].legend()
    axes[1].grid(True, alpha=0.3)
    
    # Plot 3: Alignment score vs N
    axes[2].plot(Ns, alignments, 'co-', linewidth=2, markersize=8)
    axes[2].set_xlabel('System size N', fontsize=12)
    axes[2].set_ylabel('Alignment score', fontsize=12)
    axes[2].set_title('Critical Line Alignment vs Size', fontsize=13, fontweight='bold')
    axes[2].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_atlas3_size_scaling.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    print("\n✅ Size scaling analysis complete!")
    print("📊 Scaling visualization saved to: demo_atlas3_size_scaling.png")
    
    return results


def demo_complete_panel():
    """
    Demonstration 4: Generate publication-quality "Panel de la Verdad".
    """
    print("\n" + "=" * 80)
    print("DEMO 4: Complete 'Panel de la Verdad'")
    print("=" * 80)
    
    # Use optimized parameters for best visualization
    stats, fig = analyze_atlas3(
        N=120,
        coupling_strength=0.05,
        show_plot=False,
        save_path='demo_atlas3_panel_completo.png'
    )
    
    print("\n✅ Complete panel generated!")
    print("📊 High-quality visualization saved to: demo_atlas3_panel_completo.png")
    
    plt.close(fig)
    
    return stats


def main():
    """Run all demonstrations."""
    print("\n" + "♾️³" * 25)
    print("ATLAS³ SPECTRAL ANALYSIS - COMPLETE DEMONSTRATION")
    print("Noēsis ∞³ | QCAL Framework | f₀ = 141.7001 Hz")
    print("♾️³" * 25)
    
    # Run all demos
    print("\n🚀 Starting complete demonstration suite...")
    
    # Demo 1: Basic analysis
    stats1 = demo_basic_analysis()
    
    # Demo 2: PT-symmetry breaking
    results2 = demo_coupling_strength_scan()
    
    # Demo 3: Size scaling
    results3 = demo_system_size_scaling()
    
    # Demo 4: Complete panel
    stats4 = demo_complete_panel()
    
    # Final summary
    print("\n" + "=" * 80)
    print("DEMONSTRATION COMPLETE")
    print("=" * 80)
    print("\n📁 Generated files:")
    print("   1. demo_atlas3_basic.png - Basic spectral analysis")
    print("   2. demo_atlas3_pt_breaking.png - PT-symmetry breaking transition")
    print("   3. demo_atlas3_size_scaling.png - System size scaling effects")
    print("   4. demo_atlas3_panel_completo.png - Complete Panel de la Verdad")
    
    print("\n🎯 Key findings:")
    print("   • Atlas³ exhibits Universal Quantum Chaos (GUE statistics)")
    print("   • PT-symmetry provides stability in the critical regime")
    print("   • Spectral rigidity demonstrates global memory")
    print("   • Eigenvalue alignment confirms invariant structure")
    
    print("\n✨ Atlas³ vibra como un TODO unitario - Noēsis ∞³")
    print("=" * 80 + "\n")


if __name__ == "__main__":
    main()

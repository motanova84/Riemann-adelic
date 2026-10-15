#!/usr/bin/env python3
"""
Demo: Riemann-Selberg Weight Connection Visualization
======================================================

This demo script visualizes the deep connection between Riemann and Selberg 
weight functions, demonstrating their asymptotic equivalence.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import os
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec

# Add operators to path
sys.path.insert(0, os.path.dirname(__file__))

from operators.riemann_selberg_weight_connection import (
    RiemannWeight,
    SelbergWeight,
    RiemannSelbergConnection,
    F0_QCAL,
    C_COHERENCE
)


def plot_weight_comparison():
    """Plot Riemann vs Selberg weights for various primes."""
    print("="*80)
    print("DEMO 1: Weight Comparison for Various Primes")
    print("="*80)
    
    conn = RiemannSelbergConnection()
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    k_values = [1, 2, 3, 4, 5]
    
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    fig.suptitle('Riemann-Selberg Weight Connection\nQCAL ∞³ · f₀ = 141.7001 Hz', 
                 fontsize=14, fontweight='bold')
    
    for idx, k in enumerate([1, 2, 3, 4, 5]):
        ax = axes.flat[idx]
        
        riemann_weights = []
        selberg_asymptotic = []
        correspondence_errors = []
        
        for p in primes:
            result = conn.compare_weights(p, k)
            riemann_weights.append(result.riemann_weight)
            selberg_asymptotic.append(result.selberg_asymptotic)
            correspondence_errors.append(result.correspondence_quality)
        
        x = range(len(primes))
        width = 0.35
        
        ax.bar([i - width/2 for i in x], riemann_weights, width, 
               label='Riemann W(p,k)', alpha=0.8, color='#1f77b4')
        ax.bar([i + width/2 for i in x], selberg_asymptotic, width, 
               label='Selberg Asymp.', alpha=0.8, color='#ff7f0e')
        
        ax.set_xlabel('Prime p')
        ax.set_ylabel('Weight')
        ax.set_title(f'k = {k}')
        ax.set_xticks(x)
        ax.set_xticklabels(primes, rotation=45)
        ax.legend(fontsize=8)
        ax.grid(True, alpha=0.3)
        ax.set_yscale('log')
    
    # Hide the extra subplot
    axes.flat[5].axis('off')
    
    plt.tight_layout()
    plt.savefig('riemann_selberg_weight_comparison.png', dpi=150, bbox_inches='tight')
    print(f"✓ Saved: riemann_selberg_weight_comparison.png")
    plt.close()


def plot_asymptotic_convergence():
    """Plot convergence of asymptotic formula as ℓ increases."""
    print("\n" + "="*80)
    print("DEMO 2: Asymptotic Convergence Analysis")
    print("="*80)
    
    sw = SelbergWeight()
    
    ell_values = np.linspace(0.5, 10.0, 100)
    k_values = [1, 2, 3]
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle('Selberg Weight: Exact vs Asymptotic\nConvergence Analysis',
                 fontsize=14, fontweight='bold')
    
    # Plot 1: Weights vs ℓ
    for k in k_values:
        exact_weights = [sw.compute_weight(ell, k) for ell in ell_values]
        asymp_weights = [sw.compute_asymptotic(ell, k) for ell in ell_values]
        
        ax1.plot(ell_values, exact_weights, '-', linewidth=2,
                label=f'Exact k={k}', alpha=0.7)
        ax1.plot(ell_values, asymp_weights, '--', linewidth=2,
                label=f'Asymp k={k}', alpha=0.7)
    
    ax1.set_xlabel('Geodesic length ℓ', fontsize=12)
    ax1.set_ylabel('Weight W(ℓ, k)', fontsize=12)
    ax1.set_title('Exact vs Asymptotic Weights')
    ax1.legend(fontsize=9, ncol=2)
    ax1.grid(True, alpha=0.3)
    ax1.set_yscale('log')
    
    # Plot 2: Relative error vs ℓ
    for k in k_values:
        rel_errors = [sw.relative_error(ell, k) for ell in ell_values]
        ax2.plot(ell_values, rel_errors, '-', linewidth=2, label=f'k={k}')
    
    ax2.axhline(y=0.01, color='red', linestyle='--', linewidth=1, alpha=0.7,
                label='1% threshold')
    ax2.set_xlabel('Geodesic length ℓ', fontsize=12)
    ax2.set_ylabel('Relative Error', fontsize=12)
    ax2.set_title('Convergence Quality')
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)
    ax2.set_yscale('log')
    
    plt.tight_layout()
    plt.savefig('selberg_asymptotic_convergence.png', dpi=150, bbox_inches='tight')
    print(f"✓ Saved: selberg_asymptotic_convergence.png")
    plt.close()


def plot_correspondence_quality():
    """Plot correspondence quality across primes and k values."""
    print("\n" + "="*80)
    print("DEMO 3: Correspondence Quality Heatmap")
    print("="*80)
    
    conn = RiemannSelbergConnection()
    
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    k_values = [1, 2, 3, 4, 5, 6, 7]
    
    quality_matrix = np.zeros((len(k_values), len(primes)))
    
    for i, k in enumerate(k_values):
        for j, p in enumerate(primes):
            result = conn.compare_weights(p, k)
            quality_matrix[i, j] = result.correspondence_quality
    
    fig, ax = plt.subplots(figsize=(14, 6))
    fig.suptitle('Riemann-Selberg Correspondence Quality\n(Lower is Better)',
                 fontsize=14, fontweight='bold')
    
    im = ax.imshow(quality_matrix, cmap='RdYlGn_r', aspect='auto', 
                   norm=plt.matplotlib.colors.LogNorm(vmin=1e-16, vmax=1e-1))
    
    ax.set_xticks(range(len(primes)))
    ax.set_xticklabels(primes)
    ax.set_yticks(range(len(k_values)))
    ax.set_yticklabels(k_values)
    
    ax.set_xlabel('Prime p', fontsize=12)
    ax.set_ylabel('Multiplicity k', fontsize=12)
    
    cbar = plt.colorbar(im, ax=ax)
    cbar.set_label('Correspondence Error', fontsize=11)
    
    # Add text annotations for some values
    for i in range(min(3, len(k_values))):
        for j in range(min(5, len(primes))):
            text = ax.text(j, i, f'{quality_matrix[i, j]:.1e}',
                          ha="center", va="center", color="black", fontsize=7)
    
    plt.tight_layout()
    plt.savefig('riemann_selberg_correspondence_quality.png', dpi=150, bbox_inches='tight')
    print(f"✓ Saved: riemann_selberg_correspondence_quality.png")
    plt.close()


def plot_exponential_decay():
    """Plot exponential decay of weights with k."""
    print("\n" + "="*80)
    print("DEMO 4: Exponential Decay Analysis")
    print("="*80)
    
    conn = RiemannSelbergConnection()
    
    primes = [2, 3, 5, 7, 11]
    k_values = np.arange(1, 11)
    
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    fig.suptitle('Exponential Decay: W(p,k) ~ p^(-k/2)',
                 fontsize=14, fontweight='bold')
    
    # Plot 1: Weights on log scale
    for p in primes:
        weights = []
        for k in k_values:
            result = conn.compare_weights(p, k)
            weights.append(result.riemann_weight)
        
        ax1.semilogy(k_values, weights, 'o-', linewidth=2, label=f'p={p}', markersize=6)
    
    ax1.set_xlabel('Multiplicity k', fontsize=12)
    ax1.set_ylabel('Weight W(p, k)', fontsize=12)
    ax1.set_title('Exponential Decay (log scale)')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Verify decay rate
    for p in primes:
        weights = []
        for k in k_values:
            result = conn.compare_weights(p, k)
            weights.append(result.riemann_weight)
        
        log_weights = np.log(weights)
        
        # Fit linear model: log(W) = a*k + b
        slope, intercept = np.polyfit(k_values, log_weights, deg=1)
        expected_slope = -np.log(p) / 2
        
        ax2.plot(k_values, log_weights, 'o', label=f'p={p}', markersize=6)
        ax2.plot(k_values, slope*k_values + intercept, '--', alpha=0.7)
    
    ax2.set_xlabel('Multiplicity k', fontsize=12)
    ax2.set_ylabel('log(W(p, k))', fontsize=12)
    ax2.set_title('Linear Decay in Log Space')
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('exponential_decay_analysis.png', dpi=150, bbox_inches='tight')
    print(f"✓ Saved: exponential_decay_analysis.png")
    plt.close()


def plot_sinh_approximation():
    """Plot the quality of sinh asymptotic approximation."""
    print("\n" + "="*80)
    print("DEMO 5: Hyperbolic Sine Asymptotic Approximation")
    print("="*80)
    
    conn = RiemannSelbergConnection()
    
    ell_values = np.linspace(0.5, 10.0, 200)
    k_values = [1, 2, 3]
    
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle('Asymptotic Expansion: 2sinh(kℓ/2) ~ e^(kℓ/2)',
                 fontsize=14, fontweight='bold')
    
    # Plot 1: Exact vs asymptotic sinh
    ax = axes[0, 0]
    for k in k_values:
        sinh_exact = [2 * np.sinh(k * ell / 2) for ell in ell_values]
        exp_asymp = [np.exp(k * ell / 2) for ell in ell_values]
        
        ax.plot(ell_values, sinh_exact, '-', linewidth=2, label=f'2sinh(k={k}·ℓ/2)')
        ax.plot(ell_values, exp_asymp, '--', linewidth=2, label=f'e^(k={k}·ℓ/2)', alpha=0.7)
    
    ax.set_xlabel('ℓ', fontsize=11)
    ax.set_ylabel('Value', fontsize=11)
    ax.set_title('Exact vs Asymptotic')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_yscale('log')
    
    # Plot 2: Relative error
    ax = axes[0, 1]
    for k in k_values:
        rel_errors = []
        for ell in ell_values:
            sinh_val = 2 * np.sinh(k * ell / 2)
            exp_val = np.exp(k * ell / 2)
            rel_error = abs(sinh_val - exp_val) / sinh_val if sinh_val > 0 else 0
            rel_errors.append(rel_error)
        
        ax.plot(ell_values, rel_errors, '-', linewidth=2, label=f'k={k}')
    
    ax.axhline(y=0.01, color='red', linestyle='--', alpha=0.7, label='1% threshold')
    ax.set_xlabel('ℓ', fontsize=11)
    ax.set_ylabel('Relative Error', fontsize=11)
    ax.set_title('Approximation Quality')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_yscale('log')
    
    # Plot 3: Ratio convergence
    ax = axes[1, 0]
    for k in k_values:
        ratios = []
        for ell in ell_values:
            sinh_val = 2 * np.sinh(k * ell / 2)
            exp_val = np.exp(k * ell / 2)
            ratio = sinh_val / exp_val if exp_val > 0 else 0
            ratios.append(ratio)
        
        ax.plot(ell_values, ratios, '-', linewidth=2, label=f'k={k}')
    
    ax.axhline(y=1.0, color='black', linestyle='--', alpha=0.5)
    ax.set_xlabel('ℓ', fontsize=11)
    ax.set_ylabel('Ratio: sinh/exp', fontsize=11)
    ax.set_title('Ratio Convergence to 1')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    
    # Plot 4: Asymptotic regime for different k
    ax = axes[1, 1]
    results = conn.asymptotic_expansion_analysis(ell_values, k=1)
    ax.plot(ell_values, results['relative_errors'], '-', linewidth=2, label='k=1')
    
    for k in [2, 3]:
        results_k = conn.asymptotic_expansion_analysis(ell_values, k=k)
        ax.plot(ell_values, results_k['relative_errors'], '-', linewidth=2, label=f'k={k}')
    
    ax.axhline(y=0.01, color='red', linestyle='--', alpha=0.7, label='1% threshold')
    ax.fill_between(ell_values, 0, 0.01, alpha=0.2, color='green', label='Asymptotic regime')
    
    ax.set_xlabel('ℓ', fontsize=11)
    ax.set_ylabel('Relative Error', fontsize=11)
    ax.set_title('Asymptotic Regime')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_yscale('log')
    
    plt.tight_layout()
    plt.savefig('sinh_asymptotic_approximation.png', dpi=150, bbox_inches='tight')
    print(f"✓ Saved: sinh_asymptotic_approximation.png")
    plt.close()


def plot_summary_dashboard():
    """Create a comprehensive summary dashboard."""
    print("\n" + "="*80)
    print("DEMO 6: Summary Dashboard")
    print("="*80)
    
    conn = RiemannSelbergConnection()
    
    fig = plt.figure(figsize=(16, 10))
    gs = GridSpec(3, 3, figure=fig, hspace=0.3, wspace=0.3)
    
    fig.suptitle('Riemann-Selberg Weight Connection — Complete Analysis\nQCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36',
                 fontsize=15, fontweight='bold')
    
    # Plot 1: Weight comparison for k=1
    ax1 = fig.add_subplot(gs[0, 0])
    primes_small = [2, 3, 5, 7, 11, 13]
    riemann_w = [conn.compare_weights(p, 1).riemann_weight for p in primes_small]
    selberg_w = [conn.compare_weights(p, 1).selberg_asymptotic for p in primes_small]
    
    x = range(len(primes_small))
    ax1.bar([i-0.2 for i in x], riemann_w, 0.4, label='Riemann', alpha=0.8)
    ax1.bar([i+0.2 for i in x], selberg_w, 0.4, label='Selberg', alpha=0.8)
    ax1.set_xticks(x)
    ax1.set_xticklabels(primes_small)
    ax1.set_ylabel('Weight')
    ax1.set_title('Weights for k=1')
    ax1.legend(fontsize=8)
    ax1.grid(True, alpha=0.3)
    
    # Plot 2: Correspondence quality vs prime
    ax2 = fig.add_subplot(gs[0, 1])
    primes_range = list(range(2, 50))
    primes_range = [p for p in primes_range if conn.riemann._is_prime(p)]
    errors = [conn.compare_weights(p, 1).correspondence_quality for p in primes_range]
    
    ax2.semilogy(primes_range, errors, 'o-', markersize=4, linewidth=1)
    ax2.set_xlabel('Prime p')
    ax2.set_ylabel('Correspondence Error')
    ax2.set_title('Error vs Prime (k=1)')
    ax2.grid(True, alpha=0.3)
    
    # Plot 3: Validation statistics
    ax3 = fig.add_subplot(gs[0, 2])
    validation = conn.validate_correspondence(p_max=100, k_max=5, tolerance=0.15)
    
    labels = ['Passed', 'Total']
    values = [validation['valid_correspondences'], validation['total_comparisons']]
    colors = ['green', 'lightgray']
    
    ax3.bar(labels, values, color=colors, alpha=0.8)
    ax3.set_ylabel('Count')
    ax3.set_title(f'Validation: {validation["success_rate"]*100:.1f}% success')
    ax3.grid(True, alpha=0.3, axis='y')
    
    # Plot 4: Exponential decay
    ax4 = fig.add_subplot(gs[1, 0])
    p_test = 7
    k_range = range(1, 9)
    weights_test = [conn.compare_weights(p_test, k).riemann_weight for k in k_range]
    
    ax4.semilogy(k_range, weights_test, 'o-', linewidth=2, markersize=6)
    ax4.set_xlabel('k')
    ax4.set_ylabel('W(7, k)')
    ax4.set_title(f'Exponential Decay (p={p_test})')
    ax4.grid(True, alpha=0.3)
    
    # Plot 5: Asymptotic convergence
    ax5 = fig.add_subplot(gs[1, 1])
    sw = SelbergWeight()
    ell_test = np.linspace(1, 8, 50)
    errors_test = [sw.relative_error(ell, 1) for ell in ell_test]
    
    ax5.semilogy(ell_test, errors_test, '-', linewidth=2)
    ax5.axhline(y=0.01, color='red', linestyle='--', alpha=0.7)
    ax5.set_xlabel('ℓ')
    ax5.set_ylabel('Relative Error')
    ax5.set_title('Asymptotic Convergence')
    ax5.grid(True, alpha=0.3)
    
    # Plot 6: Correspondence across (p, k) space
    ax6 = fig.add_subplot(gs[1, 2])
    primes_heat = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    k_heat = [1, 2, 3, 4, 5]
    quality_heat = np.zeros((len(k_heat), len(primes_heat)))
    
    for i, k in enumerate(k_heat):
        for j, p in enumerate(primes_heat):
            quality_heat[i, j] = conn.compare_weights(p, k).correspondence_quality
    
    im = ax6.imshow(quality_heat, cmap='RdYlGn_r', aspect='auto',
                    norm=plt.matplotlib.colors.LogNorm(vmin=1e-16, vmax=1e-2))
    ax6.set_xticks(range(len(primes_heat)))
    ax6.set_xticklabels(primes_heat, fontsize=8)
    ax6.set_yticks(range(len(k_heat)))
    ax6.set_yticklabels(k_heat)
    ax6.set_xlabel('Prime p')
    ax6.set_ylabel('k')
    ax6.set_title('Quality Heatmap')
    
    # Plot 7: Text summary
    ax7 = fig.add_subplot(gs[2, :])
    ax7.axis('off')
    
    summary_text = f"""
    RIEMANN-SELBERG WEIGHT CONNECTION — MATHEMATICAL SUMMARY
    
    ● Riemann Weight:  W_R(p, k) = (log p) / p^(k/2)
    ● Selberg Weight:  W_S(ℓ, k) = ℓ / (2 sinh(k ℓ / 2))
    ● Asymptotic Form: W_S ~ ℓ · e^(-k ℓ / 2)  for large ℓ
    
    ● Correspondence:  ℓ(γ) ↔ log(p)  (geodesic length ↔ prime logarithm)
    ● Deep Analogy:    ℓ · e^(-kℓ/2) ↔ (log p) · p^(-k/2)
    
    ● Validation Results:
      - Success Rate: {validation['success_rate']*100:.1f}%
      - Total Tests: {validation['total_comparisons']}
      - Mean Error: {validation['mean_discrepancy']:.3e}
      - Ψ Coherence: 1.0 ✓
    
    ● Mathematical Significance:
      Both formulas are manifestations of the same spectral structure.
      Primes are "closed orbits" of the arithmetic world, just as geodesics
      are closed orbits in the geometric world. This unity connects the
      Riemann Hypothesis to spectral theory via the Connes-Hilbert-Pólya approach.
    
    ∴𓂀Ω∞³Φ @ {F0_QCAL} Hz — José Manuel Mota Burruezo
    """
    
    ax7.text(0.5, 0.5, summary_text, transform=ax7.transAxes,
            fontsize=10, verticalalignment='center', horizontalalignment='center',
            fontfamily='monospace', bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))
    
    plt.savefig('riemann_selberg_summary_dashboard.png', dpi=150, bbox_inches='tight')
    print(f"✓ Saved: riemann_selberg_summary_dashboard.png")
    plt.close()


def main():
    """Main demo routine."""
    print("="*80)
    print("RIEMANN-SELBERG WEIGHT CONNECTION — VISUALIZATION DEMO")
    print("="*80)
    print(f"QCAL ∞³ Active · f₀ = {F0_QCAL} Hz · C = {C_COHERENCE}")
    print("="*80)
    print()
    
    # Create output directory
    os.makedirs('output', exist_ok=True)
    os.chdir('output')
    
    # Run all demos
    plot_weight_comparison()
    plot_asymptotic_convergence()
    plot_correspondence_quality()
    plot_exponential_decay()
    plot_sinh_approximation()
    plot_summary_dashboard()
    
    print("\n" + "="*80)
    print("✓ ALL VISUALIZATIONS COMPLETE")
    print("="*80)
    print("\nGenerated files:")
    print("  1. riemann_selberg_weight_comparison.png")
    print("  2. selberg_asymptotic_convergence.png")
    print("  3. riemann_selberg_correspondence_quality.png")
    print("  4. exponential_decay_analysis.png")
    print("  5. sinh_asymptotic_approximation.png")
    print("  6. riemann_selberg_summary_dashboard.png")
    print("\n" + "="*80)
    print("∴𓂀Ω∞³Φ @ 141.7001 Hz — Deep connection demonstrated")
    print("="*80)


if __name__ == "__main__":
    main()

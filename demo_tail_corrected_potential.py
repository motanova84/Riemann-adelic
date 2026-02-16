#!/usr/bin/env python3
"""
Visual Demonstration of Tail-Corrected Potential
=================================================

Creates visualization comparing original and corrected potentials.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / 'operators'))

import numpy as np
import matplotlib.pyplot as plt
from tail_corrected_potential import TailCorrectedPotential


def demo_potential_comparison():
    """Visualize original vs corrected potential."""
    
    # Create potential with δ = 0.1
    potential = TailCorrectedPotential(delta=0.1)
    
    # Generate y values
    y = np.linspace(-5, 50, 1000)
    
    # Compute potentials
    V_orig = potential.V_original(y)
    V_tail = potential.V_tail(y)
    V_corr = potential.V_corrected(y)
    V_asymp = potential.asymptotic_behavior_large_y(y)
    
    # Create figure
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Plot 1: Original vs Corrected
    ax1 = axes[0, 0]
    ax1.plot(y, V_orig, 'b-', label='Original: V(y) = log(1+e^y)', linewidth=2)
    ax1.plot(y, V_corr, 'r--', label='Corrected: V_corr(y)', linewidth=2)
    ax1.set_xlabel('y', fontsize=12)
    ax1.set_ylabel('Potential', fontsize=12)
    ax1.set_title('Original vs Corrected Potential', fontsize=14, fontweight='bold')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.set_xlim([-5, 50])
    
    # Plot 2: Tail Correction
    ax2 = axes[0, 1]
    ax2.semilogy(y[y > 0], V_tail[y > 0], 'g-', label=f'Tail: δ·e^{{-y}}, δ={potential.delta}', linewidth=2)
    ax2.set_xlabel('y', fontsize=12)
    ax2.set_ylabel('V_tail (log scale)', fontsize=12)
    ax2.set_title(f'Tail Correction (ε = {potential.epsilon:.4f})', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3, which='both')
    
    # Plot 3: Asymptotic Comparison for large y
    ax3 = axes[1, 0]
    y_large = y[y > 10]
    V_corr_large = V_corr[y > 10]
    V_asymp_large = V_asymp[y > 10]
    
    ax3.plot(y_large, V_corr_large, 'r-', label='V_corr(y) exact', linewidth=2)
    ax3.plot(y_large, V_asymp_large, 'b--', label='V ~ y + (1+δ)e^{-y}', linewidth=2)
    ax3.set_xlabel('y', fontsize=12)
    ax3.set_ylabel('Potential', fontsize=12)
    ax3.set_title('Asymptotic Behavior (y → +∞)', fontsize=14, fontweight='bold')
    ax3.legend(fontsize=10)
    ax3.grid(True, alpha=0.3)
    
    # Plot 4: Relative Error
    ax4 = axes[1, 1]
    rel_error = np.abs(V_corr_large - V_asymp_large) / np.abs(V_corr_large)
    ax4.semilogy(y_large, rel_error, 'm-', linewidth=2)
    ax4.axhline(y=0.01, color='k', linestyle='--', label='1% threshold', linewidth=1)
    ax4.set_xlabel('y', fontsize=12)
    ax4.set_ylabel('Relative Error', fontsize=12)
    ax4.set_title('Asymptotic Approximation Error', fontsize=14, fontweight='bold')
    ax4.legend(fontsize=10)
    ax4.grid(True, alpha=0.3, which='both')
    
    plt.tight_layout()
    
    # Save figure
    output_path = Path(__file__).parent / 'tail_corrected_potential_visualization.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"\n✓ Visualization saved to: {output_path}")
    
    # Don't show in headless environment
    # plt.show()
    plt.close()


def demo_block_decay():
    """Visualize block decay."""
    
    from tail_corrected_potential import BlockAnalyzer
    
    potential = TailCorrectedPotential(delta=0.1)
    analyzer = BlockAnalyzer(potential, z=0.5)
    
    # Analyze multiple blocks
    max_m = 10
    results = analyzer.analyze_multiple_blocks(max_m)
    
    # Extract data
    m_values = [r.block_index for r in results]
    norms = [r.norm_squared for r in results]
    theoretical = [r.theoretical_decay for r in results]
    
    # Create plot
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    
    # Plot 1: Block norms
    ax1.semilogy(m_values, norms, 'bo-', label='Measured ‖L_z ψ_m‖²', markersize=8, linewidth=2)
    ax1.semilogy(m_values, theoretical, 'r--', label=f'Theory: exp(-2εm), ε={potential.epsilon:.4f}', linewidth=2)
    ax1.set_xlabel('Block index m', fontsize=12)
    ax1.set_ylabel('‖L_z ψ_m‖² (log scale)', fontsize=12)
    ax1.set_title('Block-wise Exponential Decay', fontsize=14, fontweight='bold')
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3, which='both')
    
    # Plot 2: Decay rates
    decay_rates = [r.measured_decay_rate for r in results if r.block_index > 0]
    m_values_decay = [r.block_index for r in results if r.block_index > 0]
    expected_rate = 2 * potential.epsilon
    
    ax2.plot(m_values_decay, decay_rates, 'go-', label='Measured decay rate', markersize=8, linewidth=2)
    ax2.axhline(y=expected_rate, color='r', linestyle='--', label=f'Expected: 2ε = {expected_rate:.4f}', linewidth=2)
    ax2.set_xlabel('Block index m', fontsize=12)
    ax2.set_ylabel('Decay rate', fontsize=12)
    ax2.set_title('Measured vs Expected Decay Rate', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    # Save figure
    output_path = Path(__file__).parent / 'tail_corrected_block_decay.png'
    plt.savefig(output_path, dpi=150, bbox_inches='tight')
    print(f"✓ Block decay visualization saved to: {output_path}")
    
    plt.close()


if __name__ == '__main__':
    print("=" * 70)
    print("TAIL-CORRECTED POTENTIAL VISUALIZATION")
    print("=" * 70)
    print()
    
    print("Generating visualizations...")
    print()
    
    demo_potential_comparison()
    demo_block_decay()
    
    print()
    print("=" * 70)
    print("✓ All visualizations generated successfully")
    print("=" * 70)
    print()
    print("Files created:")
    print("  - tail_corrected_potential_visualization.png")
    print("  - tail_corrected_block_decay.png")
    print()

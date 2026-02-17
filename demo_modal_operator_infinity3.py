#!/usr/bin/env python3
"""
Demo: Modal Operator ∞³ - Vibrational Graph Analysis

Demonstrates the complete FASE 1-3 pipeline for extracting κ_Π
from the vibrational graph structure of coupled oscillators.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import numpy as np
import matplotlib.pyplot as plt
from operators.modal_operator_infinity3 import (
    ModalOperatorInfinity3,
    F0,
    OMEGA_0,
    KAPPA_PI_THEORETICAL,
    theoretical_kappa_model
)


def demo_basic_analysis():
    """Demonstrate basic Modal Operator ∞³ analysis."""
    print()
    print("=" * 70)
    print("DEMO 1: Basic Modal Operator ∞³ Analysis")
    print("=" * 70)
    print()
    
    # Create analyzer with default parameters
    analyzer = ModalOperatorInfinity3(
        T=10.0,
        n_modes=50,
        n_grid=1000,
        basis_type="fourier",
        forcing_type="harmonic",
        forcing_params={'n_harmonics': 5}
    )
    
    # Run complete analysis
    results = analyzer.run_complete_analysis(verbose=True)
    
    return analyzer, results


def demo_different_bases():
    """Compare different orthonormal bases."""
    print()
    print("=" * 70)
    print("DEMO 2: Comparison of Different Orthonormal Bases")
    print("=" * 70)
    print()
    
    bases = ["fourier", "hermite", "legendre"]
    results_by_basis = {}
    
    for basis_type in bases:
        print(f"\n📊 Analyzing with {basis_type.upper()} basis...")
        
        analyzer = ModalOperatorInfinity3(
            T=10.0,
            n_modes=30,
            basis_type=basis_type,
            forcing_type="harmonic"
        )
        
        results = analyzer.run_complete_analysis(verbose=False)
        
        if results['fit_info']['success']:
            C_fit = results['fit_info']['C_fit']
            rms_error = results['fit_info']['rms_error']
            print(f"   C_fit = {C_fit:.4f} ± {results['fit_info']['C_error']:.4f}")
            print(f"   RMS error = {rms_error:.6f}")
            results_by_basis[basis_type] = results
    
    return results_by_basis


def demo_forcing_types():
    """Compare different forcing functions."""
    print()
    print("=" * 70)
    print("DEMO 3: Comparison of Different Forcing Functions")
    print("=" * 70)
    print()
    
    forcing_configs = [
        ("Harmonic", "harmonic", {'n_harmonics': 5}),
        ("Gaussian Pulse", "gaussian_pulse", {'A': 10.0, 't0': 5.0, 'sigma': 1.0}),
        ("Constant", "constant", {'A0': 1.0})
    ]
    
    results_by_forcing = {}
    
    for name, forcing_type, params in forcing_configs:
        print(f"\n🔊 Analyzing with {name} forcing...")
        
        analyzer = ModalOperatorInfinity3(
            T=10.0,
            n_modes=40,
            forcing_type=forcing_type,
            forcing_params=params
        )
        
        results = analyzer.run_complete_analysis(verbose=False)
        
        if results['fit_info']['success']:
            C_fit = results['fit_info']['C_fit']
            print(f"   C_fit = {C_fit:.4f}")
            print(f"   Validation: {results['validation']['message']}")
            results_by_forcing[name] = results
    
    return results_by_forcing


def demo_stability_analysis():
    """Demonstrate stability under parameter variations."""
    print()
    print("=" * 70)
    print("DEMO 4: Stability Analysis Under Parameter Variations")
    print("=" * 70)
    print()
    
    analyzer = ModalOperatorInfinity3(
        T=10.0,
        n_modes=40,
        n_grid=800,
        basis_type="fourier",
        forcing_type="harmonic"
    )
    
    # Run initial analysis
    print("Running initial analysis...")
    initial_results = analyzer.run_complete_analysis(verbose=False)
    C_initial = initial_results['fit_info']['C_fit']
    print(f"Initial C_fit = {C_initial:.4f}")
    print()
    
    # Test stability
    print("Testing stability under variations...")
    stability = analyzer.test_stability(
        variations={
            'n_grid': [500, 800, 1200],
            'n_modes': [30, 40, 50],
            'forcing_A0': [0.5, 1.0, 1.5]
        },
        verbose=True
    )
    
    return stability


def create_visualizations(analyzer, results):
    """Create visualization of Modal Operator ∞³ analysis."""
    print()
    print("=" * 70)
    print("Creating Visualizations...")
    print("=" * 70)
    print()
    
    try:
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        
        # Plot 1: Coupling matrix K
        ax = axes[0, 0]
        im = ax.imshow(analyzer.K, cmap='RdBu', aspect='auto')
        ax.set_title('Coupling Matrix K', fontsize=12, fontweight='bold')
        ax.set_xlabel('Mode m')
        ax.set_ylabel('Mode n')
        plt.colorbar(im, ax=ax, label='k_nm')
        
        # Plot 2: Adjacency matrix A
        ax = axes[0, 1]
        im = ax.imshow(analyzer.A, cmap='binary', aspect='auto')
        ax.set_title('Adjacency Matrix A (Weighted)', fontsize=12, fontweight='bold')
        ax.set_xlabel('Mode m')
        ax.set_ylabel('Mode n')
        plt.colorbar(im, ax=ax, label='Weight')
        
        # Plot 3: Eigenvalue spectrum
        ax = axes[1, 0]
        eigenvalues = np.real(analyzer.eigenvalues)
        ax.hist(eigenvalues, bins=30, alpha=0.7, color='blue', edgecolor='black')
        ax.axvline(0, color='red', linestyle='--', linewidth=2, label='Zero')
        ax.set_title('Eigenvalue Spectrum of A', fontsize=12, fontweight='bold')
        ax.set_xlabel('Eigenvalue λ')
        ax.set_ylabel('Count')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # Plot 4: κ(n) curve and fit
        ax = axes[1, 1]
        n_values = results['n_values']
        kappa_obs = results['kappa_observed']
        kappa_pred = results['kappa_predicted']
        
        ax.plot(n_values, kappa_obs, 'o', markersize=4, alpha=0.6, label='Observed κ(n)')
        ax.plot(n_values, kappa_pred, '-', linewidth=2, color='red', 
                label=f'Fit: C={results["fit_info"]["C_fit"]:.2f}/(n·log n)')
        
        # Also plot theoretical κ_Π curve for comparison
        kappa_theoretical = theoretical_kappa_model(n_values, KAPPA_PI_THEORETICAL)
        ax.plot(n_values, kappa_theoretical, '--', linewidth=2, color='green', alpha=0.7,
                label=f'Theoretical: κ_Π={KAPPA_PI_THEORETICAL}/(n·log n)')
        
        ax.set_title('κ(n) Curve and Model Fit', fontsize=12, fontweight='bold')
        ax.set_xlabel('Mode index n')
        ax.set_ylabel('κ(n)')
        ax.legend()
        ax.grid(True, alpha=0.3)
        ax.set_yscale('log')
        
        plt.tight_layout()
        
        # Save figure
        output_path = 'modal_operator_infinity3_analysis.png'
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        print(f"✅ Visualization saved to: {output_path}")
        
        plt.show()
        
    except Exception as e:
        print(f"⚠️ Could not create visualization: {e}")
        print("   Possible causes:")
        print("   - matplotlib not installed or display backend unavailable")
        print("   - Try: export MPLBACKEND=Agg (for headless environments)")
        print(f"   - Full error: {type(e).__name__}: {str(e)}")


def main():
    """Main demo execution."""
    print()
    print("∴" * 35)
    print("  MODAL OPERATOR ∞³ - DEMONSTRATION")
    print("  Vibrational Graph Analysis & κ_Π Extraction")
    print("∴" * 35)
    print()
    print(f"QCAL ∞³ Constants:")
    print(f"  f₀ = {F0} Hz")
    print(f"  ω₀ = {OMEGA_0:.4f} rad/s")
    print(f"  κ_Π (theoretical) = {KAPPA_PI_THEORETICAL}")
    print()
    
    # Demo 1: Basic analysis
    analyzer, results = demo_basic_analysis()
    
    # Demo 2: Different bases
    results_bases = demo_different_bases()
    
    # Demo 3: Different forcing types
    results_forcing = demo_forcing_types()
    
    # Demo 4: Stability analysis
    stability = demo_stability_analysis()
    
    # Create visualizations
    create_visualizations(analyzer, results)
    
    print()
    print("∴" * 35)
    print("  DEMONSTRATION COMPLETE")
    print("∴" * 35)
    print()
    
    print("📌 Key Findings:")
    print(f"   - Vibrational graph constructed with {analyzer.n_modes} modes")
    print(f"   - κ(n) follows 1/(n·log n) pattern")
    print(f"   - Fitted curvature constant: C = {results['fit_info']['C_fit']:.4f}")
    print(f"   - RMS fit error: {results['fit_info']['rms_error']:.6f}")
    print()
    print("🎯 The Modal Operator ∞³ framework successfully extracts")
    print("   the vibrational curvature signature from coupled oscillator systems.")
    print()
    
    return {
        'analyzer': analyzer,
        'results': results,
        'results_bases': results_bases,
        'results_forcing': results_forcing,
        'stability': stability
    }


if __name__ == "__main__":
    demo_results = main()

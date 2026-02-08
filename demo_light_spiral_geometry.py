#!/usr/bin/env python3
"""
Demonstration: Geometría Real del Movimiento Lumínico

This script demonstrates the light spiral geometry framework,
showing how light follows logarithmic spiral paths modulated by
Riemann zeta zeros and prime numbers.

Visualizations:
--------------
1. Spiral light paths with different prime modulations
2. Comparison: classical straight vs QCAL spiral paths
3. Zeta-modulated spiral with multiple zeros
4. 2D interference patterns showing spiral arcs
5. Angular deviation from circular symmetry

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec
import warnings

# Suppress warnings for cleaner output
warnings.filterwarnings('ignore')

# Import modules directly to avoid utils/__init__.py dependencies
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'utils'))

try:
    import light_spiral_geometry as lsg
    SpiralParameters = lsg.SpiralParameters
    compute_spiral_path = lsg.compute_spiral_path
    compute_spiral_path_zeta_modulated = lsg.compute_spiral_path_zeta_modulated
    compute_phase_deviation = lsg.compute_phase_deviation
    predict_interferometry_deviation = lsg.predict_interferometry_deviation
    cavity_resonance_prediction = lsg.cavity_resonance_prediction
    F0_HZ = lsg.F0_HZ
    C_LIGHT = lsg.C_LIGHT
    GEOMETRY_AVAILABLE = True
except ImportError as e:
    print(f"Error importing light_spiral_geometry: {e}")
    GEOMETRY_AVAILABLE = False

try:
    import zeta_interference_pattern as zip_mod
    WaveFunctionParameters = zip_mod.WaveFunctionParameters
    compute_interference_pattern = zip_mod.compute_interference_pattern
    detect_spiral_arcs = zip_mod.detect_spiral_arcs
    predict_electron_biprism_pattern = zip_mod.predict_electron_biprism_pattern
    predict_fabry_perot_pattern = zip_mod.predict_fabry_perot_pattern
    PATTERN_AVAILABLE = True
except ImportError as e:
    print(f"Error importing zeta_interference_pattern: {e}")
    PATTERN_AVAILABLE = False


def demo_basic_spiral_paths():
    """Demonstrate basic spiral paths with different prime modulations."""
    if not GEOMETRY_AVAILABLE:
        print("⚠️  light_spiral_geometry not available")
        return
    
    print("=" * 80)
    print("DEMO 1: Basic Spiral Paths with Prime Modulation")
    print("=" * 80)
    print()
    
    # Time array (10 periods)
    T = 1.0 / F0_HZ
    t = np.linspace(0, 10 * T, 1000)
    
    fig = plt.figure(figsize=(15, 5))
    
    # Test with first 3 primes: 2, 3, 5
    primes_to_test = [0, 1, 2]  # Indices
    
    for idx, prime_idx in enumerate(primes_to_test):
        ax = fig.add_subplot(1, 3, idx + 1, projection='3d')
        
        # Create spiral parameters
        params = SpiralParameters(
            r0=1e-9,  # 1 nm initial radius
            lambda_exp=0.01,  # Moderate expansion
            prime_index=prime_idx
        )
        
        # Compute spiral path
        x, y, z = compute_spiral_path(t, params)
        
        # Plot
        ax.plot(x * 1e9, y * 1e9, z * 1e-3, 'b-', linewidth=1.5, alpha=0.7)
        ax.set_xlabel('x (nm)')
        ax.set_ylabel('y (nm)')
        ax.set_zlabel('z (km)')
        ax.set_title(f'Prime p = {params.prime}\nφ_p = {params.phi_p:.3f} rad')
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('light_spiral_paths_prime_modulation.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: light_spiral_paths_prime_modulation.png")
    print()


def demo_classical_vs_spiral():
    """Compare classical straight path vs QCAL spiral path."""
    if not GEOMETRY_AVAILABLE:
        print("⚠️  light_spiral_geometry not available")
        return
    
    print("=" * 80)
    print("DEMO 2: Classical vs QCAL Spiral Comparison")
    print("=" * 80)
    print()
    
    T = 1.0 / F0_HZ
    t = np.linspace(0, 5 * T, 500)
    
    # QCAL spiral
    params = SpiralParameters(
        r0=1e-9,
        lambda_exp=0.02,
        prime_index=1  # Prime 3
    )
    x_spiral, y_spiral, z_spiral = compute_spiral_path(t, params)
    
    # Classical "straight" path (no spiral, just propagation)
    x_classical = np.zeros_like(t)
    y_classical = np.zeros_like(t)
    z_classical = C_LIGHT * t
    
    fig = plt.figure(figsize=(15, 5))
    
    # 3D view
    ax1 = fig.add_subplot(1, 3, 1, projection='3d')
    ax1.plot(x_classical * 1e9, y_classical * 1e9, z_classical * 1e-3,
             'r-', linewidth=2, label='Classical', alpha=0.7)
    ax1.plot(x_spiral * 1e9, y_spiral * 1e9, z_spiral * 1e-3,
             'b-', linewidth=1.5, label='QCAL Spiral', alpha=0.8)
    ax1.set_xlabel('x (nm)')
    ax1.set_ylabel('y (nm)')
    ax1.set_zlabel('z (km)')
    ax1.set_title('3D View: Classical vs Spiral')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # XY projection
    ax2 = fig.add_subplot(1, 3, 2)
    ax2.plot(x_classical * 1e9, y_classical * 1e9, 'r-', linewidth=2,
             label='Classical', alpha=0.7)
    ax2.plot(x_spiral * 1e9, y_spiral * 1e9, 'b-', linewidth=1.5,
             label='QCAL Spiral', alpha=0.8)
    ax2.set_xlabel('x (nm)')
    ax2.set_ylabel('y (nm)')
    ax2.set_title('XY Projection')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    ax2.axis('equal')
    
    # Radial distance vs z
    ax3 = fig.add_subplot(1, 3, 3)
    r_spiral = np.sqrt(x_spiral**2 + y_spiral**2)
    ax3.plot(z_spiral * 1e-3, r_spiral * 1e9, 'b-', linewidth=1.5)
    ax3.set_xlabel('Propagation Distance z (km)')
    ax3.set_ylabel('Radial Deviation r (nm)')
    ax3.set_title('Spiral Expansion')
    ax3.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('classical_vs_qcal_spiral.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: classical_vs_qcal_spiral.png")
    print(f"  Maximum radial deviation: {np.max(r_spiral)*1e9:.3f} nm")
    print()


def demo_zeta_modulated_spiral():
    """Demonstrate spiral with multiple zeta zero modulations."""
    if not GEOMETRY_AVAILABLE:
        print("⚠️  light_spiral_geometry not available")
        return
    
    print("=" * 80)
    print("DEMO 3: Zeta-Modulated Spiral with Multiple Zeros")
    print("=" * 80)
    print()
    
    T = 1.0 / F0_HZ
    t = np.linspace(0, 20 * T, 2000)
    
    params = SpiralParameters(
        r0=1e-9,
        lambda_exp=0.015,
        prime_index=2  # Prime 5
    )
    
    fig = plt.figure(figsize=(15, 5))
    
    # Compare different numbers of zeta zeros
    n_zeros_list = [0, 5, 10]
    colors = ['gray', 'blue', 'red']
    
    for idx, (n_zeros, color) in enumerate(zip(n_zeros_list, colors)):
        ax = fig.add_subplot(1, 3, idx + 1, projection='3d')
        
        if n_zeros == 0:
            x, y, z = compute_spiral_path(t, params)
            label = 'Basic Spiral (no ζ)'
        else:
            x, y, z = compute_spiral_path_zeta_modulated(t, params, n_zeros)
            label = f'ζ-modulated (n={n_zeros})'
        
        ax.plot(x * 1e9, y * 1e9, z * 1e-3, color=color, linewidth=1.5,
                alpha=0.7, label=label)
        ax.set_xlabel('x (nm)')
        ax.set_ylabel('y (nm)')
        ax.set_zlabel('z (km)')
        ax.set_title(label)
        ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('zeta_modulated_spiral.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: zeta_modulated_spiral.png")
    print()


def demo_interference_patterns():
    """Demonstrate 2D interference patterns with spiral arcs."""
    if not PATTERN_AVAILABLE:
        print("⚠️  zeta_interference_pattern not available")
        return
    
    print("=" * 80)
    print("DEMO 4: Interference Patterns with Spiral Arcs")
    print("=" * 80)
    print()
    
    # Create 2D grid
    x = np.linspace(-2e-3, 2e-3, 400)  # ±2mm
    y = np.linspace(-2e-3, 2e-3, 400)
    X, Y = np.meshgrid(x, y)
    
    fig = plt.figure(figsize=(15, 5))
    
    # Different configurations
    configs = [
        {'n_primes': 3, 'n_zeros': 3, 'title': 'Low Order (n=3)'},
        {'n_primes': 7, 'n_zeros': 7, 'title': 'Medium Order (n=7)'},
        {'n_primes': 12, 'n_zeros': 12, 'title': 'High Order (n=12)'}
    ]
    
    for idx, config in enumerate(configs):
        ax = fig.add_subplot(1, 3, idx + 1)
        
        params = WaveFunctionParameters(
            n_primes=config['n_primes'],
            n_zeros=config['n_zeros'],
            wavelength=1064e-9
        )
        
        intensity = compute_interference_pattern(X, Y, 0.0, params)
        
        # Plot
        im = ax.imshow(intensity, extent=[x[0]*1e3, x[-1]*1e3, y[0]*1e3, y[-1]*1e3],
                      cmap='hot', origin='lower', aspect='auto')
        ax.set_xlabel('x (mm)')
        ax.set_ylabel('y (mm)')
        ax.set_title(config['title'])
        plt.colorbar(im, ax=ax, label='Intensity |Ψ|²')
        
        # Detect spirals
        spiral_info = detect_spiral_arcs(intensity, X, Y, threshold=0.5)
        if spiral_info.get('spiral_detected'):
            ax.text(0.02, 0.98, f"Spiral: b={spiral_info['spiral_parameter_b']:.4f}",
                   transform=ax.transAxes, va='top', ha='left',
                   bbox=dict(boxstyle='round', facecolor='white', alpha=0.8),
                   fontsize=8)
    
    plt.tight_layout()
    plt.savefig('interference_patterns_spiral_arcs.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: interference_patterns_spiral_arcs.png")
    print()


def demo_angular_deviation():
    """Demonstrate angular deviation Δθ from symmetry."""
    if not PATTERN_AVAILABLE:
        print("⚠️  zeta_interference_pattern not available")
        return
    
    print("=" * 80)
    print("DEMO 5: Angular Deviation from Circular Symmetry")
    print("=" * 80)
    print()
    
    # Create pattern
    x = np.linspace(-1e-3, 1e-3, 300)
    y = np.linspace(-1e-3, 1e-3, 300)
    X, Y = np.meshgrid(x, y)
    
    params = WaveFunctionParameters(n_primes=10, n_zeros=10)
    intensity = compute_interference_pattern(X, Y, 0.0, params)
    
    # Detect spiral structure
    spiral_info = detect_spiral_arcs(intensity, X, Y, threshold=0.4)
    
    fig = plt.figure(figsize=(15, 5))
    
    # Original pattern
    ax1 = fig.add_subplot(1, 3, 1)
    im1 = ax1.imshow(intensity, extent=[x[0]*1e3, x[-1]*1e3, y[0]*1e3, y[-1]*1e3],
                    cmap='hot', origin='lower')
    ax1.set_xlabel('x (mm)')
    ax1.set_ylabel('y (mm)')
    ax1.set_title('Interference Pattern')
    plt.colorbar(im1, ax=ax1, label='|Ψ|²')
    
    # Polar representation
    ax2 = fig.add_subplot(1, 3, 2, projection='polar')
    r = np.sqrt(X**2 + Y**2)
    theta = np.arctan2(Y, X)
    
    # Plot intensity in polar coords (sample points)
    mask = intensity > 0.3 * np.max(intensity)
    if np.sum(mask) > 0:
        ax2.scatter(theta[mask], r[mask]*1e3, c=intensity[mask],
                   s=1, cmap='hot', alpha=0.6)
    ax2.set_title('Polar Representation')
    ax2.set_ylabel('r (mm)', labelpad=30)
    
    # Spiral analysis results
    ax3 = fig.add_subplot(1, 3, 3)
    ax3.axis('off')
    
    # Display spiral detection results
    results_text = "Spiral Arc Detection Results\n" + "=" * 35 + "\n\n"
    if spiral_info.get('spiral_detected'):
        results_text += f"✓ Spiral Detected\n\n"
        results_text += f"Spiral parameter b: {spiral_info['spiral_parameter_b']:.6f}\n"
        results_text += f"Scale parameter a: {spiral_info['spiral_scale_a']:.3e} m\n"
        results_text += f"Fit quality R²: {spiral_info['fit_quality_r2']:.4f}\n"
        results_text += f"Angular deviation (RMS): {spiral_info['angular_deviation_rms']:.6f} rad\n"
        results_text += f"Angular deviation: {spiral_info['angular_deviation_deg']:.3f}°\n"
        results_text += f"Number of peaks: {spiral_info['n_peaks']}\n"
        results_text += f"\nInterpretation: {spiral_info['interpretation']}\n"
    else:
        results_text += f"✗ No Spiral Detected\n\n"
        results_text += f"Reason: {spiral_info.get('reason', 'Unknown')}\n"
    
    ax3.text(0.1, 0.9, results_text, transform=ax3.transAxes,
            fontfamily='monospace', fontsize=10, va='top')
    
    plt.tight_layout()
    plt.savefig('angular_deviation_analysis.png', dpi=150, bbox_inches='tight')
    print("✓ Saved: angular_deviation_analysis.png")
    print()
    print("Spiral Detection Summary:")
    print("-" * 40)
    for key, value in spiral_info.items():
        print(f"  {key:25s}: {value}")
    print()


def demo_experimental_predictions():
    """Demonstrate experimental predictions for validation."""
    print("=" * 80)
    print("DEMO 6: Experimental Validation Predictions")
    print("=" * 80)
    print()
    
    if GEOMETRY_AVAILABLE:
        print("1. INTERFEROMETRY PREDICTIONS (LIGO/GEO600)")
        print("-" * 60)
        pred = predict_interferometry_deviation(
            wavelength=1064e-9,
            path_length=4000.0,
            n_zeros=10
        )
        for key, value in pred.items():
            print(f"  {key:30s}: {value}")
        print()
        
        print("2. FABRY-PÉROT CAVITY RESONANCE")
        print("-" * 60)
        cavity_pred = cavity_resonance_prediction(
            cavity_length=1.0,
            finesse=1e6,
            q_factor=1e12
        )
        for key, value in cavity_pred.items():
            print(f"  {key:30s}: {value}")
        print()
    
    if PATTERN_AVAILABLE:
        print("3. ELECTRON BIPRISM INTERFEROMETRY")
        print("-" * 60)
        electron_pred = predict_electron_biprism_pattern(
            electron_energy_eV=100.0,
            screen_distance=0.1
        )
        for key, value in electron_pred.items():
            if key != 'spiral_detection':
                print(f"  {key:30s}: {value}")
        print()
        
        print("4. FABRY-PÉROT TEM₀₁ MODE PATTERN")
        print("-" * 60)
        fp_pattern_pred = predict_fabry_perot_pattern(
            cavity_length=1.0,
            finesse=1e5
        )
        for key, value in fp_pattern_pred.items():
            if key != 'spiral_detection':
                print(f"  {key:30s}: {value}")
        print()


def main():
    """Main demonstration function."""
    print()
    print("╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  GEOMETRÍA REAL DEL MOVIMIENTO LUMÍNICO".center(78) + "║")
    print("║" + "  Light Spiral Geometry Demonstration".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("║" + "  QCAL ∞³ Framework".center(78) + "║")
    print("║" + "  f₀ = 141.7001 Hz".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print("DOI: 10.5281/zenodo.17379721")
    print()
    
    # Run demonstrations
    try:
        demo_basic_spiral_paths()
    except Exception as e:
        print(f"⚠️  Demo 1 failed: {e}\n")
    
    try:
        demo_classical_vs_spiral()
    except Exception as e:
        print(f"⚠️  Demo 2 failed: {e}\n")
    
    try:
        demo_zeta_modulated_spiral()
    except Exception as e:
        print(f"⚠️  Demo 3 failed: {e}\n")
    
    try:
        demo_interference_patterns()
    except Exception as e:
        print(f"⚠️  Demo 4 failed: {e}\n")
    
    try:
        demo_angular_deviation()
    except Exception as e:
        print(f"⚠️  Demo 5 failed: {e}\n")
    
    try:
        demo_experimental_predictions()
    except Exception as e:
        print(f"⚠️  Demo 6 failed: {e}\n")
    
    print("=" * 80)
    print("✓ Demonstration Complete")
    print("∴𓂀Ω∞³ · QCAL Active at 141.7001 Hz")
    print("=" * 80)
    print()


if __name__ == '__main__':
    main()

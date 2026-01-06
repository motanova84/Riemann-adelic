#!/usr/bin/env python3
"""
Demonstration of H_ε Spectral Operator and Comparison with Riemann Zeros

This script showcases the complete workflow:
1. Construction of the perturbed operator H_ε = H₀ + λM_{Ω_{ε,R}}
2. Computation of its spectrum (eigenvalues)
3. Loading Riemann zeta zeros
4. Visual and quantitative comparison of spectral measures

Mathematical Context:
    The operator H_ε captures the adelic spectral structure that should
    reflect the distribution of Riemann zeta zeros on the critical line.
    
    If the spectral measure μ_ε ≈ measure of zeros ν, this provides
    numerical evidence for the spectral interpretation of RH.

Lean Formalization:
    See formalization/lean/RiemannAdelic/H_epsilon_foundation.lean
    for the rigorous mathematical framework including:
    - L²(ℝ⁺, dt/t) Hilbert space with logarithmic measure
    - Hermite logarithmic orthonormal basis
    - V(t) potential with p-adic corrections
    - H_ε hermitian operator and spectral analysis
    - D(s) function and connection to Riemann zeta

Usage:
    python demo_operador_H_epsilon.py [--N 200] [--T 20] [--epsilon 0.01]
"""

import argparse
import sys
from pathlib import Path

import numpy as np
import matplotlib.pyplot as plt

# Add parent directory to path for imports
sys.path.append(str(Path(__file__).parent.parent))

from operador.operador_H_epsilon import (
    compute_oscillatory_potential,
    build_H_epsilon_operator,
    compute_spectral_measure,
    load_riemann_zeros,
    plot_spectral_comparison
)


def demonstrate_potential():
    """Demonstrate the oscillatory potential Ω_{ε,R}(t)."""
    print("\n" + "=" * 80)
    print("1. POTENCIAL OSCILATORIO Ω_{ε,R}(t)")
    print("=" * 80)
    
    t = np.linspace(-30, 30, 500)
    
    # Compute potentials with different parameters
    Omega_base = compute_oscillatory_potential(t, epsilon=0.01, R=5.0, n_primes=100)
    Omega_large_R = compute_oscillatory_potential(t, epsilon=0.01, R=10.0, n_primes=100)
    Omega_large_eps = compute_oscillatory_potential(t, epsilon=0.05, R=5.0, n_primes=100)
    
    # Plot
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    ax1 = axes[0]
    ax1.plot(t, Omega_base, 'b-', label=r'$\varepsilon=0.01, R=5$', linewidth=1.5)
    ax1.plot(t, Omega_large_R, 'g--', label=r'$\varepsilon=0.01, R=10$', linewidth=1.5)
    ax1.plot(t, Omega_large_eps, 'r:', label=r'$\varepsilon=0.05, R=5$', linewidth=1.5)
    ax1.set_xlabel('t')
    ax1.set_ylabel(r'$\Omega_{\varepsilon,R}(t)$')
    ax1.set_title('Potencial oscilatorio con diferentes parámetros')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # Zoom near origin
    ax2 = axes[1]
    mask = np.abs(t) <= 10
    ax2.plot(t[mask], Omega_base[mask], 'b-', label=r'$\varepsilon=0.01, R=5$', linewidth=1.5)
    ax2.set_xlabel('t')
    ax2.set_ylabel(r'$\Omega_{\varepsilon,R}(t)$')
    ax2.set_title('Zoom cerca del origen')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_H_epsilon_potential.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✅ Potencial visualizado")
    print(f"   Rango de valores: [{np.min(Omega_base):.4f}, {np.max(Omega_base):.4f}]")
    print(f"   Archivo: demo_H_epsilon_potential.png")


def demonstrate_operator(N=100, T=15.0):
    """Demonstrate H_ε operator structure."""
    print("\n" + "=" * 80)
    print("2. OPERADOR H_ε = H₀ + λM_{Ω}")
    print("=" * 80)
    
    # Build operator
    t, H_diag, H_offdiag = build_H_epsilon_operator(
        N=N, T=T, epsilon=0.01, R=5.0, 
        lambda_coupling=141.7001, n_primes=100
    )
    
    # Reconstruct full matrix for visualization
    H_full = np.diag(H_diag) + np.diag(H_offdiag, k=1) + np.diag(H_offdiag, k=-1)
    
    # Plot matrix structure
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Full matrix
    ax1 = axes[0]
    im1 = ax1.imshow(H_full, cmap='RdBu', aspect='auto')
    ax1.set_title(r'Matriz $H_\varepsilon$ completa')
    ax1.set_xlabel('Índice j')
    ax1.set_ylabel('Índice i')
    plt.colorbar(im1, ax=ax1, label='Valor')
    
    # Diagonal elements
    ax2 = axes[1]
    ax2.plot(t, H_diag, 'b-', linewidth=1.5)
    ax2.set_xlabel('t')
    ax2.set_ylabel(r'Diagonal de $H_\varepsilon$')
    ax2.set_title('Elementos diagonales del operador')
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_H_epsilon_operator.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"✅ Operador construido")
    print(f"   Dimensión: {N}×{N}")
    print(f"   Intervalo: [-{T}, {T}]")
    print(f"   Rango diagonal: [{np.min(H_diag):.4f}, {np.max(H_diag):.4f}]")
    print(f"   Archivo: demo_H_epsilon_operator.png")


def demonstrate_spectrum(N=200, T=20.0):
    """Demonstrate spectral analysis of H_ε."""
    print("\n" + "=" * 80)
    print("3. ESPECTRO DE H_ε")
    print("=" * 80)
    
    # Compute spectrum
    print("🔄 Diagonalizando operador...")
    eigenvalues, eigenvectors = compute_spectral_measure(
        N=N, T=T, epsilon=0.01, R=5.0,
        lambda_coupling=141.7001, n_primes=150
    )
    print(f"✅ Espectro calculado: {len(eigenvalues)} eigenvalores")
    
    # Plot spectrum
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Eigenvalue distribution
    ax1 = axes[0, 0]
    ax1.plot(eigenvalues, 'bo-', markersize=3, linewidth=1)
    ax1.set_xlabel('Índice n')
    ax1.set_ylabel(r'$\lambda_n$')
    ax1.set_title('Eigenvalores de $H_\\varepsilon$')
    ax1.grid(True, alpha=0.3)
    
    # First 50 eigenvalues
    ax2 = axes[0, 1]
    n_show = min(50, len(eigenvalues))
    ax2.plot(range(n_show), eigenvalues[:n_show], 'ro-', markersize=5, linewidth=1.5)
    ax2.set_xlabel('Índice n')
    ax2.set_ylabel(r'$\lambda_n$')
    ax2.set_title(f'Primeros {n_show} eigenvalores')
    ax2.grid(True, alpha=0.3)
    
    # Eigenvalue gaps
    ax3 = axes[1, 0]
    gaps = np.diff(eigenvalues)
    ax3.plot(gaps[:n_show], 'g-', linewidth=1.5)
    ax3.set_xlabel('Índice n')
    ax3.set_ylabel(r'$\lambda_{n+1} - \lambda_n$')
    ax3.set_title('Espaciado entre eigenvalores')
    ax3.grid(True, alpha=0.3)
    
    # Histogram of eigenvalues
    ax4 = axes[1, 1]
    ax4.hist(eigenvalues[:100], bins=30, color='blue', alpha=0.7, edgecolor='black')
    ax4.set_xlabel(r'$\lambda$')
    ax4.set_ylabel('Frecuencia')
    ax4.set_title('Distribución de eigenvalores (primeros 100)')
    ax4.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_H_epsilon_spectrum.png', dpi=150, bbox_inches='tight')
    plt.close()
    
    print(f"   Primer eigenvalor: {eigenvalues[0]:.6f}")
    print(f"   Último eigenvalor: {eigenvalues[-1]:.6f}")
    print(f"   Espaciado medio: {np.mean(gaps):.6f}")
    print(f"   Archivo: demo_H_epsilon_spectrum.png")
    
    return eigenvalues


def demonstrate_comparison(eigenvalues, n_points=50):
    """Demonstrate comparison with Riemann zeros."""
    print("\n" + "=" * 80)
    print("4. COMPARACIÓN CON CEROS DE ζ(s)")
    print("=" * 80)
    
    # Load zeros
    print("🔄 Cargando ceros de Riemann...")
    try:
        zeta_zeros = load_riemann_zeros(
            filename='zeros/zeros_t1e3.txt',
            max_zeros=200
        )
        print(f"✅ Ceros cargados: {len(zeta_zeros)} valores")
    except FileNotFoundError:
        print("⚠️  Archivo de ceros no encontrado")
        print("   Usando valores sintéticos para demostración")
        # Use synthetic zeros following approximate Riemann-von Mangoldt formula
        zeta_zeros = np.array([
            14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
            37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
            52.970321, 56.446247, 59.347044, 60.831778, 65.112544,
            67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
            79.337375, 82.910380, 84.735493, 87.425275, 88.809111,
            92.491899, 94.651344, 95.870634, 98.831194, 101.317851,
            103.725538, 105.446623, 107.168611, 111.029535, 111.874659,
            114.320220, 116.226680, 118.790782, 121.370125, 122.946829,
            124.256818, 127.516683, 129.578704, 131.087688, 133.497737,
            134.756509, 138.116042, 139.736209, 141.123707, 143.111845
        ])
    
    # Comparison statistics
    n_compare = min(n_points, len(eigenvalues), len(zeta_zeros))
    
    mu_eps = eigenvalues[:n_compare]
    nu_zeros = zeta_zeros[:n_compare]
    
    # Compute correlation with validation for zero variance
    if np.allclose(mu_eps, mu_eps[0]):
        correlation = np.nan
        print("⚠️  Warning: All eigenvalues are identical, correlation undefined")
    else:
        correlation = np.corrcoef(mu_eps, nu_zeros)[0, 1]
        if np.isnan(correlation):
            print("⚠️  Warning: Correlation computation failed, data may be degenerate")
    
    # Compute normalized differences with numerical stability
    # Use abs(a) + abs(b) + eps to avoid division by zero when values have opposite signs
    eps = np.finfo(float).eps  # Machine epsilon for numerical stability
    diffs = np.abs(mu_eps - nu_zeros) / (np.abs(mu_eps) + np.abs(nu_zeros) + eps)
    mean_diff = np.mean(diffs)
    max_diff = np.max(diffs)
    
    print(f"\nEstadísticas de comparación (primeros {n_compare} valores):")
    print(f"  Correlación: {correlation:.6f}")
    print(f"  Diferencia relativa media: {mean_diff:.6f}")
    print(f"  Diferencia relativa máxima: {max_diff:.6f}")
    
    # Plot comparison
    plot_spectral_comparison(
        eigenvalues,
        zeta_zeros,
        n_points=n_points,
        save_path='demo_H_epsilon_comparison.png'
    )
    
    # Detailed comparison table
    print("\nTabla de comparación detallada:")
    print("-" * 70)
    print(f"{'n':<5} {'μ_ε':<15} {'ν (zeros)':<15} {'Diferencia':<15} {'% Dif':<10}")
    print("-" * 70)
    for i in range(min(15, n_compare)):
        diff_abs = np.abs(mu_eps[i] - nu_zeros[i])
        diff_pct = 100 * diff_abs / nu_zeros[i]
        print(f"{i:<5} {mu_eps[i]:<15.6f} {nu_zeros[i]:<15.6f} "
              f"{diff_abs:<15.6f} {diff_pct:<10.2f}")
    print("-" * 70)


def main():
    """Main demonstration function."""
    parser = argparse.ArgumentParser(
        description='Demonstrate H_ε operator and spectral comparison'
    )
    parser.add_argument('--N', type=int, default=200,
                       help='Discretization dimension (default: 200)')
    parser.add_argument('--T', type=float, default=20.0,
                       help='Half-width of interval (default: 20.0)')
    parser.add_argument('--epsilon', type=float, default=0.01,
                       help='Convergence parameter (default: 0.01)')
    parser.add_argument('--n-compare', type=int, default=50,
                       help='Number of points to compare (default: 50)')
    
    args = parser.parse_args()
    
    print("=" * 80)
    print("DEMOSTRACIÓN: OPERADOR H_ε Y COMPARACIÓN ESPECTRAL")
    print("=" * 80)
    print(f"\nParámetros:")
    print(f"  N = {args.N}")
    print(f"  T = {args.T}")
    print(f"  ε = {args.epsilon}")
    print(f"  Puntos de comparación = {args.n_compare}")
    
    # Run demonstrations
    demonstrate_potential()
    demonstrate_operator(N=min(100, args.N), T=args.T)
    eigenvalues = demonstrate_spectrum(N=args.N, T=args.T)
    demonstrate_comparison(eigenvalues, n_points=args.n_compare)
    
    print("\n" + "=" * 80)
    print("✅ DEMOSTRACIÓN COMPLETA")
    print("=" * 80)
    print("\nArchivos generados:")
    print("  - demo_H_epsilon_potential.png")
    print("  - demo_H_epsilon_operator.png")
    print("  - demo_H_epsilon_spectrum.png")
    print("  - demo_H_epsilon_comparison.png")
    print("\n" + "=" * 80)


if __name__ == "__main__":
    main()

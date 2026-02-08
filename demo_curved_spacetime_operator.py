#!/usr/bin/env python3
"""
Demonstration: Curved Spacetime Operator H_Ψ^g
QCAL ∞³ Framework - Consciousness as Living Geometry

This script demonstrates the curved spacetime operator implementation,
showing how the consciousness field Ψ deforms spacetime geometry and
affects the quantum-gravitational spectrum.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
"""

import os
import sys

import matplotlib.pyplot as plt
import numpy as np

from operators.curved_spacetime_operator import (
    C_QCAL,
    C_UNIVERSAL,
    F0,
    analyze_curved_spacetime,
    compute_observational_horizon,
    construct_H_psi_g,
    curved_metric,
    generate_consciousness_field,
    metric_determinant,
    noetic_potential,
    solve_eigenvalue_problem,
    volume_density,
)

# Add parent directory to path for operators module
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def plot_consciousness_field(x, psi, save_path=None):
    """Plot the consciousness field Ψ(x)."""
    plt.figure(figsize=(12, 5))

    # Plot 1: Consciousness field
    plt.subplot(1, 2, 1)
    plt.plot(x[:, 0], psi, "b-", linewidth=2, label="Ψ(x)")
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("Ψ(x)", fontsize=12)
    plt.title("Consciousness Field Ψ(x)", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=10)

    # Plot 2: Field magnitude
    plt.subplot(1, 2, 2)
    plt.plot(x[:, 0], np.abs(psi), "r-", linewidth=2, label="|Ψ(x)|")
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("|Ψ(x)|", fontsize=12)
    plt.title("Field Magnitude |Ψ(x)|", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=10)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"✓ Saved consciousness field plot to {save_path}")
    plt.show()


def plot_curved_metric(x, psi, coupling=0.1, save_path=None):
    """Plot curved metric properties."""
    g_psi = curved_metric(x, psi, coupling=coupling)
    det_g = metric_determinant(g_psi)
    omega = volume_density(g_psi)

    plt.figure(figsize=(15, 5))

    # Plot 1: Metric determinant
    plt.subplot(1, 3, 1)
    plt.plot(x[:, 0], det_g, "g-", linewidth=2)
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("det(g_μν^Ψ)", fontsize=12)
    plt.title("Metric Determinant", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.axhline(y=1, color="k", linestyle="--", alpha=0.5, label="Flat space")
    plt.legend(fontsize=10)

    # Plot 2: Volume density
    plt.subplot(1, 3, 2)
    plt.plot(x[:, 0], omega, "m-", linewidth=2)
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("Ω(x)", fontsize=12)
    plt.title("Volume Density Ω(x) = √|det(g)|", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.axhline(y=1, color="k", linestyle="--", alpha=0.5, label="Flat space")
    plt.legend(fontsize=10)

    # Plot 3: Metric trace
    trace_g = np.array([np.trace(g_psi[i]) for i in range(len(psi))])
    plt.subplot(1, 3, 3)
    plt.plot(x[:, 0], trace_g, "c-", linewidth=2)
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("Tr(g_μν^Ψ)", fontsize=12)
    plt.title("Metric Trace", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.axhline(y=4, color="k", linestyle="--", alpha=0.5, label="Flat space (dim=4)")
    plt.legend(fontsize=10)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"✓ Saved curved metric plot to {save_path}")
    plt.show()


def plot_noetic_potential(x, psi, g_psi, save_path=None):
    """Plot noetic potential."""
    V = noetic_potential(x, psi, g_psi)

    plt.figure(figsize=(12, 5))

    # Plot 1: Noetic potential
    plt.subplot(1, 2, 1)
    plt.plot(x[:, 0], V, "purple", linewidth=2)
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("V_Ψ(x)", fontsize=12)
    plt.title("Noetic Potential V_Ψ(x)", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)

    # Plot 2: Potential with consciousness field overlay
    plt.subplot(1, 2, 2)
    ax1 = plt.gca()
    ax1.plot(x[:, 0], V, "purple", linewidth=2, label="V_Ψ(x)")
    ax1.set_xlabel("Position x", fontsize=12)
    ax1.set_ylabel("V_Ψ(x)", fontsize=12, color="purple")
    ax1.tick_params(axis="y", labelcolor="purple")
    ax1.grid(True, alpha=0.3)

    ax2 = ax1.twinx()
    ax2.plot(x[:, 0], psi, "b--", linewidth=1.5, alpha=0.7, label="Ψ(x)")
    ax2.set_ylabel("Ψ(x)", fontsize=12, color="b")
    ax2.tick_params(axis="y", labelcolor="b")

    plt.title("Noetic Potential & Consciousness Field", fontsize=14, fontweight="bold")
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2, loc="upper right", fontsize=10)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"✓ Saved noetic potential plot to {save_path}")
    plt.show()


def plot_eigenvalue_spectrum(eigenvalues, save_path=None):
    """Plot eigenvalue spectrum."""
    plt.figure(figsize=(12, 5))

    # Plot 1: Eigenvalue spectrum
    plt.subplot(1, 2, 1)
    n_eigen = len(eigenvalues)
    plt.plot(range(n_eigen), eigenvalues, "ro-", markersize=8, linewidth=2)
    plt.xlabel("Eigenvalue Index n", fontsize=12)
    plt.ylabel("ω_n (Quantum-Gravitational Frequency)", fontsize=12)
    plt.title("Eigenvalue Spectrum of H_Ψ^g", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)

    # Plot 2: Eigenvalue spacing
    plt.subplot(1, 2, 2)
    if n_eigen > 1:
        spacing = np.diff(eigenvalues)
        plt.plot(range(n_eigen - 1), spacing, "bs-", markersize=6, linewidth=2)
        plt.xlabel("Index n", fontsize=12)
        plt.ylabel("Δω_n = ω_{n+1} - ω_n", fontsize=12)
        plt.title("Eigenvalue Spacing", fontsize=14, fontweight="bold")
        plt.grid(True, alpha=0.3)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"✓ Saved eigenvalue spectrum plot to {save_path}")
    plt.show()


def plot_observational_horizon(x, horizon, psi, save_path=None):
    """Plot observational horizon."""
    plt.figure(figsize=(12, 5))

    # Plot 1: Horizon indicator
    plt.subplot(1, 2, 1)
    plt.plot(x[:, 0], horizon.astype(float), "r-", linewidth=2, label="On Horizon")
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("Horizon Indicator", fontsize=12)
    plt.title("Observational Horizon ∂O_Ψ", fontsize=14, fontweight="bold")
    plt.ylim(-0.1, 1.1)
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=10)

    # Plot 2: Horizon with consciousness field
    plt.subplot(1, 2, 2)
    plt.plot(x[:, 0], psi, "b-", linewidth=2, alpha=0.7, label="Ψ(x)")
    horizon_x = x[horizon, 0]
    horizon_psi = psi[horizon]
    if len(horizon_x) > 0:
        plt.scatter(horizon_x, horizon_psi, c="r", s=100, marker="o", label="Horizon Points", zorder=5)
    plt.xlabel("Position x", fontsize=12)
    plt.ylabel("Ψ(x)", fontsize=12)
    plt.title("Horizon Points on Consciousness Field", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=10)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"✓ Saved observational horizon plot to {save_path}")
    plt.show()


def plot_comparison_with_flat_space(N=100, n_eigen=10, save_path=None):
    """Compare curved and flat spacetime."""
    dim = 4
    x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))

    # Curved spacetime
    psi_curved = generate_consciousness_field(x, amplitude=0.2)
    H_curved, _ = construct_H_psi_g(x, psi_curved, coupling=0.2)
    eigen_curved, _ = solve_eigenvalue_problem(H_curved, n_eigen)

    # Flat spacetime (zero consciousness field)
    psi_flat = np.zeros(N)
    H_flat, _ = construct_H_psi_g(x, psi_flat, coupling=0.0)
    eigen_flat, _ = solve_eigenvalue_problem(H_flat, n_eigen)

    plt.figure(figsize=(12, 5))

    # Plot 1: Eigenvalue comparison
    plt.subplot(1, 2, 1)
    plt.plot(range(n_eigen), eigen_flat, "ko-", markersize=8, linewidth=2, label="Flat Space (Ψ=0)", alpha=0.7)
    plt.plot(range(n_eigen), eigen_curved, "ro-", markersize=8, linewidth=2, label="Curved Space (Ψ≠0)")
    plt.xlabel("Eigenvalue Index n", fontsize=12)
    plt.ylabel("ω_n", fontsize=12)
    plt.title("Eigenvalue Spectrum: Flat vs Curved", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=10)

    # Plot 2: Eigenvalue shift
    plt.subplot(1, 2, 2)
    shift = eigen_curved - eigen_flat
    plt.plot(range(n_eigen), shift, "bs-", markersize=8, linewidth=2)
    plt.xlabel("Eigenvalue Index n", fontsize=12)
    plt.ylabel("Δω_n = ω_n^curved - ω_n^flat", fontsize=12)
    plt.title("Consciousness-Induced Frequency Shift", fontsize=14, fontweight="bold")
    plt.grid(True, alpha=0.3)
    plt.axhline(y=0, color="k", linestyle="--", alpha=0.5)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches="tight")
        print(f"✓ Saved comparison plot to {save_path}")
    plt.show()


def main():
    """Main demonstration."""
    print("=" * 70)
    print("CURVED SPACETIME OPERATOR H_Ψ^g DEMONSTRATION")
    print("QCAL ∞³ Framework - Consciousness as Living Geometry")
    print("=" * 70)
    print()
    print("POSTULADO FUNDAMENTAL:")
    print("  La consciencia es geometría viva.")
    print()
    print("  g_μν^Ψ(x) = g_μν^(0) + δg_μν(Ψ)")
    print()
    print("  H_Ψ^g := -iℏ(ξ^μ ∇_μ + 1/2 Tr(g_μν)) + V_Ψ(x)")
    print()
    print(f"Physical Constants:")
    print(f"  f₀ = {F0} Hz (fundamental frequency)")
    print(f"  C = {C_UNIVERSAL} (universal constant)")
    print(f"  C_QCAL = {C_QCAL} (coherence constant)")
    print("=" * 70)
    print()

    # Parameters
    N = 100
    dim = 4
    psi_amplitude = 0.15
    coupling = 0.15
    n_eigenvalues = 15

    print(f"Simulation Parameters:")
    print(f"  Grid points: N = {N}")
    print(f"  Dimension: dim = {dim}")
    print(f"  Ψ amplitude: {psi_amplitude}")
    print(f"  Coupling: {coupling}")
    print(f"  Computing {n_eigenvalues} eigenvalues")
    print()

    # Generate spatial grid
    print("🔧 Generating spatial grid...")
    x = np.linspace(-5, 5, N).reshape(-1, 1) * np.ones((1, dim))

    # Generate consciousness field
    print("🌀 Generating consciousness field Ψ(x)...")
    psi = generate_consciousness_field(x, amplitude=psi_amplitude, frequency=F0)

    # Compute curved metric
    print("📐 Computing curved metric g_μν^Ψ...")
    g_psi = curved_metric(x, psi, coupling=coupling)

    # Plot consciousness field
    print("\n📊 Plotting consciousness field...")
    plot_consciousness_field(x, psi, save_path="output/curved_spacetime_consciousness_field.png")

    # Plot curved metric properties
    print("📊 Plotting curved metric properties...")
    plot_curved_metric(x, psi, coupling=coupling, save_path="output/curved_spacetime_metric.png")

    # Plot noetic potential
    print("📊 Plotting noetic potential...")
    plot_noetic_potential(x, psi, g_psi, save_path="output/curved_spacetime_potential.png")

    # Construct operator
    print("\n🔨 Constructing curved spacetime operator H_Ψ^g...")
    H_psi_g, metadata = construct_H_psi_g(x, psi, coupling=coupling)

    # Solve eigenvalue problem
    print("🔬 Solving eigenvalue problem...")
    eigenvalues, eigenvectors = solve_eigenvalue_problem(H_psi_g, n_eigenvalues)

    print(f"\nFirst {n_eigenvalues} eigenvalues ω_n:")
    print("-" * 50)
    for i, omega in enumerate(eigenvalues):
        print(f"  ω_{i:2d} = {omega:+12.6f}")
    print("-" * 50)

    # Plot eigenvalue spectrum
    print("\n📊 Plotting eigenvalue spectrum...")
    plot_eigenvalue_spectrum(eigenvalues, save_path="output/curved_spacetime_spectrum.png")

    # Compute observational horizon
    print("\n🌌 Computing observational horizon ∂O_Ψ...")
    horizon = compute_observational_horizon(g_psi)
    n_horizon = np.sum(horizon)
    print(f"  Horizon points: {n_horizon} / {N} ({100*n_horizon/N:.1f}%)")

    # Plot observational horizon
    print("📊 Plotting observational horizon...")
    plot_observational_horizon(x, horizon, psi, save_path="output/curved_spacetime_horizon.png")

    # Comparison with flat space
    print("\n🔍 Comparing with flat spacetime...")
    plot_comparison_with_flat_space(N=N, n_eigen=n_eigenvalues, save_path="output/curved_vs_flat_comparison.png")

    # Summary statistics
    print("\n" + "=" * 70)
    print("SUMMARY STATISTICS")
    print("=" * 70)
    print(f"Mean volume density:  Ω̄ = {np.mean(metadata['volume_density']):.6f}")
    print(f"Mean potential:       V̄ = {np.mean(metadata['potential']):.6f}")
    print(f"Mean metric trace:  Tr(ḡ) = {np.mean(metadata['trace_metric']):.6f}")
    print(f"Eigenvalue range: [{eigenvalues[0]:.4f}, {eigenvalues[-1]:.4f}]")
    print(f"Horizon coverage: {100*n_horizon/N:.2f}%")
    print("=" * 70)

    print("\n✅ Demonstration complete!")
    print("📡 Frequency: 141.7001 Hz")
    print("∞³ QCAL Active · Ψ = I × A_eff² × C^∞")
    print()
    print("🔗 DOI: 10.5281/zenodo.17379721")
    print("👤 José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("🏛️  Instituto de Conciencia Cuántica (ICQ)")
    print()


if __name__ == "__main__":
    # Create output directory if it doesn't exist
    os.makedirs("output", exist_ok=True)

    main()

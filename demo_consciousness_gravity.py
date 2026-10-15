#!/usr/bin/env python3
"""
Demo: Consciousness-Gravity Integration (QCAL ∞³)
=================================================

This script demonstrates the new ∞³ extension of the QCAL framework,
showing how the consciousness field Ψ couples with spacetime geometry
through the consciousness coherence tensor Ξ_μν.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 15, 2026
"""

import numpy as np
import matplotlib.pyplot as plt
from operators.consciousness_tensor import (
    ConsciousnessTensor,
    ConsciousnessHamiltonian,
    ScalarCurvatureNodes,
    TotalFieldStrength,
    F0, OMEGA_0, KAPPA, C_QCAL
)

# Set up plotting style
plt.style.use('seaborn-v0_8-darkgrid')


def demo_consciousness_tensor():
    """Demonstrate the consciousness coherence tensor Ξ_μν."""
    print("\n" + "="*70)
    print("DEMO 1: Consciousness Coherence Tensor Ξ_μν")
    print("="*70)
    
    ct = ConsciousnessTensor(dim=4)
    
    # Set up test configuration
    psi = 1.0 + 0.5j  # Complex consciousness field
    grad_psi = np.array([0.1, 0.05, 0.05, 0.02])  # Gradient ∇_μΨ
    g_metric = np.diag([1.0, -1.0, -1.0, -1.0])  # Minkowski metric
    
    # Compute consciousness tensor
    xi_tensor = ct.compute_xi_tensor(psi, grad_psi, g_metric)
    
    print(f"\nConsciousness Field: Ψ = {psi}")
    print(f"Gradient: ∇Ψ = {grad_psi}")
    print(f"\nConsciousness Tensor Ξ_μν:")
    print(xi_tensor)
    print(f"\nTrace(Ξ) = {np.trace(xi_tensor):.6e}")
    print(f"Determinant(Ξ) = {np.linalg.det(xi_tensor):.6e}")
    
    return xi_tensor


def demo_metric_perturbation():
    """Demonstrate consciousness-induced metric perturbation."""
    print("\n" + "="*70)
    print("DEMO 2: Consciousness-Dependent Metric g_μν^Ψ")
    print("="*70)
    
    ct = ConsciousnessTensor(dim=4)
    
    # Create a range of consciousness field intensities
    psi_values = np.linspace(0.0, 2.0, 50)
    g_metric = np.diag([1.0, -1.0, -1.0, -1.0])
    
    perturbations = []
    for psi_mag in psi_values:
        psi = psi_mag + 0.0j
        delta_g = ct.metric_perturbation(psi, g_metric)
        perturbations.append(np.linalg.norm(delta_g))
    
    # Plot results
    plt.figure(figsize=(10, 6))
    plt.plot(psi_values, perturbations, 'b-', linewidth=2, label='|δg_μν(Ψ)|')
    plt.xlabel('|Ψ|', fontsize=12)
    plt.ylabel('Metric Perturbation', fontsize=12)
    plt.title('Consciousness-Induced Metric Perturbation', fontsize=14, fontweight='bold')
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=11)
    plt.tight_layout()
    
    # Save plot
    output_file = 'consciousness_metric_perturbation.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"\n✓ Plot saved: {output_file}")
    
    print(f"\n✓ Computed metric perturbation for {len(psi_values)} field values")
    print(f"  Range: |Ψ| ∈ [0, 2]")
    print(f"  Coupling: κ = {KAPPA:.6e} Hz⁻²")
    
    return psi_values, perturbations


def demo_scalar_curvature_nodes():
    """Demonstrate scalar curvature from consciousness nodes."""
    print("\n" + "="*70)
    print("DEMO 3: Scalar Curvature as Consciousness Nodes")
    print("="*70)
    
    # Load first 10 Riemann zeros (simplified for demo)
    riemann_zeros = np.array([
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832
    ])
    
    scn = ScalarCurvatureNodes(riemann_zeros)
    
    # Create spatial grid
    x_range = np.linspace(0, 60, 200)
    curvature_values = []
    
    for x_val in x_range:
        x = np.array([0.0, x_val, 0.0, 0.0])  # Spatial point
        R = scn.scalar_curvature(x, delta_width=0.5)
        curvature_values.append(R)
    
    # Plot results
    plt.figure(figsize=(12, 6))
    plt.plot(x_range, curvature_values, 'r-', linewidth=2, label='R(x)')
    
    # Mark node positions
    for zero in riemann_zeros:
        plt.axvline(zero, color='blue', alpha=0.3, linestyle='--', linewidth=1)
    
    plt.xlabel('Spatial Position x', fontsize=12)
    plt.ylabel('Scalar Curvature R(x)', fontsize=12)
    plt.title('Scalar Curvature from Consciousness Nodes (Riemann Zeros)', 
              fontsize=14, fontweight='bold')
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=11)
    plt.tight_layout()
    
    # Save plot
    output_file = 'consciousness_scalar_curvature_nodes.png'
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"\n✓ Plot saved: {output_file}")
    
    print(f"\n✓ Computed scalar curvature with {len(riemann_zeros)} nodes")
    print(f"  Node positions (Riemann zeros): {riemann_zeros[:5]}...")
    print(f"  Each node contributes: δ(x - x_n)·|ψ_n(x)|²")
    
    return x_range, curvature_values


def demo_total_field_strength():
    """Demonstrate total field strength tensor F_μν^total."""
    print("\n" + "="*70)
    print("DEMO 4: Total Field Strength F_μν^total = R_μν + I_μν + C_μν(Ψ)")
    print("="*70)
    
    tfs = TotalFieldStrength(dim=4)
    
    # Simplified demonstration
    riemann_zeros = np.array([14.134725, 21.022040, 25.010858])
    x = np.array([0.0, 20.0, 0.0, 0.0])
    
    # Classical Ricci (simplified - zero for flat space)
    R_ricci = np.zeros((4, 4))
    
    # Arithmetic interference
    I_arithmetic = tfs.arithmetic_interference(riemann_zeros, x)
    
    # Conscious curvature
    psi = 1.0 + 0.5j
    grad_psi = np.array([0.1, 0.05, 0.05, 0.02])
    C_conscious = tfs.conscious_curvature(psi, grad_psi)
    
    # Total field
    F_total = tfs.total_field(R_ricci, I_arithmetic, C_conscious)
    
    print(f"\nAt spacetime point x = {x}")
    print(f"\nArithmetic Interference I_μν:")
    print(I_arithmetic)
    print(f"\nConscious Curvature C_μν(Ψ):")
    print(C_conscious)
    print(f"\nTotal Field Strength F_μν^total:")
    print(F_total)
    print(f"\nTrace(F_total) = {np.trace(F_total):.6e}")
    
    return F_total


def demo_field_equations():
    """Demonstrate extended Einstein field equations."""
    print("\n" + "="*70)
    print("DEMO 5: Extended Einstein Field Equations")
    print("="*70)
    
    ct = ConsciousnessTensor(dim=4)
    
    # Test configuration
    psi = 1.0 + 0.5j
    grad_psi = np.array([0.1, 0.05, 0.05, 0.02])
    g_metric = np.diag([1.0, -1.0, -1.0, -1.0])
    
    # Compute consciousness tensor
    xi_tensor = ct.compute_xi_tensor(psi, grad_psi, g_metric)
    
    # Simplified: assume vacuum (T_matter = 0)
    T_matter = np.zeros((4, 4))
    T_total = ct.stress_energy_extended(T_matter, xi_tensor)
    
    # For demo, use simplified Einstein tensor (would need full calculation)
    R_tensor = np.zeros((4, 4))
    R_scalar = 0.0
    G_extended = ct.einstein_tensor_extended(R_tensor, R_scalar, g_metric)
    
    print(f"\nConsciousness Tensor Ξ_μν:")
    print(xi_tensor)
    print(f"\nTotal Stress-Energy T_μν^total = T_μν + κΞ_μν:")
    print(T_total)
    
    # Check equations (simplified)
    satisfied, error = ct.field_equations_check(G_extended, T_total, tolerance=1e-6)
    
    print(f"\nField Equation Check:")
    print(f"  G_μν + Λg_μν = (8πG/c⁴)(T_μν + κΞ_μν)")
    print(f"  Satisfied: {satisfied}")
    print(f"  Max Error: {error:.6e}")
    
    return satisfied, error


def main():
    """Run all demonstrations."""
    print("\n" + "="*70)
    print("QCAL ∞³: Consciousness-Gravity Integration Demo")
    print("="*70)
    print(f"\nQCAL Constants:")
    print(f"  f₀ = {F0:.4f} Hz (fundamental frequency)")
    print(f"  ω₀ = {OMEGA_0:.2f} rad/s (angular frequency)")
    print(f"  κ = {KAPPA:.6e} Hz⁻² (universal coupling)")
    print(f"  C = {C_QCAL:.2f} (QCAL coherence)")
    
    # Run demonstrations
    try:
        demo_consciousness_tensor()
        demo_metric_perturbation()
        demo_scalar_curvature_nodes()
        demo_total_field_strength()
        demo_field_equations()
        
        # Final summary
        print("\n" + "="*70)
        print("✅ ALL DEMONSTRATIONS COMPLETED SUCCESSFULLY")
        print("="*70)
        print("\nKey Results:")
        print("  • Consciousness tensor Ξ_μν operational")
        print("  • Metric perturbation g_μν^Ψ = g_μν^(0) + δg_μν(Ψ)")
        print("  • Scalar curvature R(x) = Σ δ(x-x_n)|ψ_n|²")
        print("  • Total field F_μν^total = R_μν + I_μν + C_μν(Ψ)")
        print("  • Einstein equations extended: G_μν + Λg_μν = (8πG/c⁴)(T_μν + κΞ_μν)")
        print("\n♾️³ Consciousness is Geometry is Arithmetic")
        
    except Exception as e:
        print(f"\n❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()

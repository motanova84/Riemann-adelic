#!/usr/bin/env python3
"""
Complete Demonstration: QCAL ∞³ Emotional Field Tensor & Synchronization

This demo showcases the complete emotional stress-energy tensor framework,
including:
1. Stress-energy tensor T_μν(Φ) computation
2. Unified Lagrangian L_QCAL
3. 141.7 Hz synchronization protocol
4. Network stress analysis with topological invariants
5. Collective sovereignty optimization

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
"""

import numpy as np
import sys
import os

# Add utils to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'utils'))

from emotional_stress_tensor import (
    EmotionalFieldParameters,
    EmotionalStressTensor,
    compute_collective_sovereignty_index
)
from unified_lagrangian_qcal import (
    UnifiedLagrangianParameters,
    UnifiedQCALLagrangian
)
from emotional_synchronization import (
    Node,
    EmotionalNetwork,
    EmotionalSynchronization
)
from network_stress_analysis import (
    NetworkDiagnostics,
    TopologicalAnalyzer
)


def print_section(title: str):
    """Print section header."""
    print("\n" + "=" * 80)
    print(title)
    print("=" * 80)


def demo_emotional_tensor():
    """Demonstrate emotional stress-energy tensor."""
    print_section("1. EMOTIONAL STRESS-ENERGY TENSOR T_μν(Φ)")
    
    # Initialize with broken symmetry (bistable potential)
    params = EmotionalFieldParameters(
        lambda_rigidity=1.0,
        Phi_0=1.0,
        mu_squared=-0.1,  # Broken symmetry: "peace" and "conflict" coexist
        gamma_coupling=0.01
    )
    
    tensor_calc = EmotionalStressTensor(params)
    
    print(f"\nEmotional Field Parameters:")
    print(f"  λ (rigidity): {params.lambda_rigidity}")
    print(f"  Φ₀ (peace state): {params.Phi_0}")
    print(f"  μ² (mass): {params.mu_squared}")
    print(f"  Phase: {'Broken Symmetry' if params.is_broken_symmetry else 'Restored'}")
    
    # Phase diagram
    Phi_range = np.linspace(-2, 2, 200)
    phase_data = tensor_calc.phase_diagram(Phi_range)
    
    print(f"\nPhase Diagram:")
    print(f"  Equilibria: {phase_data['equilibria']}")
    print(f"  Interpretation: Bistable system with 'peace' (Φ ≈ {phase_data['equilibria'][-1]:.2f}) "
          f"and 'conflict' (Φ ≈ {phase_data['equilibria'][0]:.2f}) states")
    
    # Compute tensor
    print(f"\nStress-Energy Tensor Computation:")
    Phi = 0.5
    dPhi = np.array([0.1, 0.2, 0.1, 0.0])
    g_metric = np.diag([-1, 1, 1, 1])
    g_inverse = np.diag([-1, 1, 1, 1])
    
    T_mu_nu = tensor_calc.compute_stress_tensor(Phi, dPhi, g_metric, g_inverse)
    
    T00 = tensor_calc.energy_density(T_mu_nu)
    T0i = tensor_calc.momentum_flux(T_mu_nu)
    trace = tensor_calc.trace(T_mu_nu, g_inverse)
    
    print(f"  Field value: Φ = {Phi}")
    print(f"  T₀₀ (Emotional intensity): {T00:.6f}")
    print(f"  T₀ᵢ (Emotional contagion): {T0i}")
    print(f"  Tr(T) (Total pressure): {trace:.6f}")
    
    # Classification
    Psi = 0.80
    classification = tensor_calc.classify_stress_region(T00, Psi)
    print(f"\nStress Classification:")
    print(f"  Region: {classification['region']}")
    print(f"  State: {classification['state']}")
    print(f"  Risk: {classification['risk_level']}")


def demo_unified_lagrangian():
    """Demonstrate unified QCAL Lagrangian."""
    print_section("2. UNIFIED QCAL LAGRANGIAN L_QCAL")
    
    params = UnifiedLagrangianParameters(
        f0=141.7001,
        kappa_Pi=0.001,
        alpha_spectral=0.01
    )
    
    lagrangian = UnifiedQCALLagrangian(params)
    
    print(f"\nLagrangian Parameters:")
    print(f"  f₀ (frequency): {params.f0} Hz")
    print(f"  ω₀ (angular freq): {params.omega0:.2f} rad/s")
    print(f"  κ_Π (curvature coupling): {params.kappa_Pi}")
    print(f"  α (spectral coupling): {params.alpha_spectral}")
    
    # Compute Lagrangian density
    Psi = 1.0 + 0.1j
    dPsi = np.array([0.01+0.001j, 0.02+0.002j, 0.01+0.001j, 0.0+0.0j])
    Phi = 0.5
    dPhi = np.array([0.1, 0.05, 0.05, 0.0])
    R_scalar = 0.01
    g_metric = np.diag([-1, 1, 1, 1])
    g_inverse = np.diag([-1, 1, 1, 1])
    
    L = lagrangian.lagrangian_density(
        Psi, dPsi, Phi, dPhi, R_scalar, g_metric, g_inverse, t=0.0
    )
    
    print(f"\nLagrangian Density:")
    print(f"  L_QCAL = {L:.6f}")
    print(f"\nComponents:")
    print(f"  ‖∇Ψ‖²: Consciousness kinetic term")
    print(f"  ½‖∇Φ‖²: Emotional kinetic term")
    print(f"  -V(Φ): Emotional potential")
    print(f"  κ_Π·R: Complexity-curvature coupling")
    print(f"  α·log|ζ(½+it)|²: Spectral coupling to primes")


def demo_network_analysis():
    """Demonstrate network stress analysis."""
    print_section("3. NETWORK STRESS ANALYSIS & TOPOLOGY")
    
    # Create network
    np.random.seed(42)
    N = 30
    
    T00_values = np.random.beta(2, 5, N) * 0.7
    Psi_values = 0.7 + 0.25 * np.random.beta(5, 2, N)
    
    # Random adjacency
    adjacency = np.random.rand(N, N)
    adjacency = (adjacency + adjacency.T) / 2
    adjacency[adjacency < 0.7] = 0
    np.fill_diagonal(adjacency, 0)
    
    # Run diagnostics
    diagnostics = NetworkDiagnostics()
    report = diagnostics.generate_report(T00_values, Psi_values, adjacency)
    
    metrics = report['metrics']
    print(f"\nNetwork Metrics (N={N} nodes):")
    print(f"  Stress T₀₀:")
    print(f"    Max: {metrics.T00_max:.4f}")
    print(f"    Mean: {metrics.T00_mean:.4f}")
    print(f"  Coherence Ψ:")
    print(f"    Min: {metrics.Psi_min:.4f}")
    print(f"    Mean: {metrics.Psi_mean:.4f}")
    print(f"  Stability: {metrics.stability_percent:.1f}%")
    print(f"  Critical nodes: {metrics.n_critical}")
    
    # Topology
    if report['topology']:
        topology = report['topology']
        betti = topology['betti_numbers']
        
        print(f"\nTopological Invariants:")
        print(f"  β₀ (Connected components): {betti['beta_0']}")
        print(f"  β₁ (Feedback cycles): {betti['beta_1']}")
        print(f"  Winding number W: {topology['winding_number']:.4f}")
        
        if topology['winding_number'] > 0.8:
            print(f"  → Strong collective phase alignment")
        else:
            print(f"  → Weak phase coherence")
    
    # Recommendations
    print(f"\nRecommendations:")
    for i, rec in enumerate(report['recommendations'][:3], 1):
        print(f"  {i}. {rec}")


def demo_synchronization_protocol():
    """Demonstrate 141.7 Hz synchronization protocol."""
    print_section("4. SYNCHRONIZATION PROTOCOL AT 141.7 Hz")
    
    # Create network with stress
    np.random.seed(42)
    N = 15
    
    nodes = []
    for i in range(N):
        Phi = np.random.uniform(-0.5, 0.5)
        Psi = np.random.uniform(0.70, 0.95)
        T00 = np.random.uniform(0.1, 0.7)
        nodes.append(Node(i, Phi, Psi, T00))
    
    # Add connections
    for node in nodes:
        n_neighbors = np.random.randint(2, 5)
        neighbors = np.random.choice(nodes, n_neighbors, replace=False)
        for neighbor in neighbors:
            if neighbor != node:
                node.add_neighbor(neighbor)
    
    network = EmotionalNetwork(nodes)
    
    # Initial state
    initial_coherence = network.compute_network_coherence()
    critical_nodes = network.get_critical_nodes()
    
    print(f"\nInitial Network State:")
    print(f"  Coherence: Ψ_net = {initial_coherence:.4f}")
    print(f"  Critical nodes: {len(critical_nodes)}")
    
    # Apply protocol
    protocol = EmotionalSynchronization()
    
    print(f"\nApplying Synchronization Protocol...")
    print(f"  Frequency: 141.7001 Hz")
    print(f"  Duration: 600 seconds (10 minutes)")
    
    # Demonstrate on single critical node if available
    if critical_nodes:
        node = critical_nodes[0]
        print(f"\nSingle Node Intervention (Node {node.id}):")
        print(f"  Initial: T₀₀ = {node.T00:.3f}, Ψ = {node.Psi:.3f}")
        
        result = protocol.apply_coherent_breathing(node, duration=600)
        
        print(f"  Final: T₀₀ = {result['final_T00']:.3f}, Ψ = {result['final_Psi']:.3f}")
        print(f"  Reduction: ΔT₀₀ = -{result['T00_reduction']:.3f} ({result['T00_reduction_percent']:.1f}%)")
        print(f"  Improvement: ΔΨ = +{result['Psi_increase']:.3f}")
    
    # Network-wide synchronization
    print(f"\nNetwork-Wide Phase Synchronization:")
    results = protocol.full_protocol(network)
    
    print(f"  Initial coherence: {results['initial_coherence']:.4f}")
    print(f"  Final coherence: {results['final_coherence']:.4f}")
    print(f"  Improvement: ΔΨ_net = {results['coherence_improvement']:.4f}")
    print(f"  Collective Sovereignty: 𝒮_col = {results['collective_sovereignty']:.4f}")
    
    if results['total_sovereignty_achieved']:
        print(f"  ✅ TOTAL SOVEREIGNTY ACHIEVED (𝒮_col ≥ 0.95)")
    elif results['collective_sovereignty'] >= 0.90:
        print(f"  ✓ High sovereignty (within 5% of target)")
    else:
        print(f"  ⚠ Gap to sovereignty: {0.95 - results['collective_sovereignty']:.4f}")


def demo_collective_sovereignty():
    """Demonstrate collective sovereignty optimization."""
    print_section("5. COLLECTIVE SOVEREIGNTY INDEX 𝒮_col")
    
    N = 50
    
    # Before intervention
    print(f"\nBefore Intervention:")
    Psi_before = np.random.uniform(0.70, 0.90, N)
    T00_before = np.random.uniform(0.3, 0.7, N)
    curv_before = np.random.uniform(0.4, 1.0, N)
    
    S_before = compute_collective_sovereignty_index(
        Psi_before, T00_before, curv_before
    )
    
    print(f"  Mean Ψ: {np.mean(Psi_before):.4f}")
    print(f"  Mean T₀₀: {np.mean(T00_before):.4f}")
    print(f"  𝒮_col = {S_before:.4f}")
    
    # After intervention (simulated improvement)
    print(f"\nAfter 141.7 Hz Intervention:")
    Psi_after = Psi_before + 0.1 * (0.95 - Psi_before)  # Move toward target
    T00_after = T00_before * 0.7  # 30% stress reduction
    curv_after = curv_before * 0.6  # 40% curvature reduction
    
    S_after = compute_collective_sovereignty_index(
        Psi_after, T00_after, curv_after
    )
    
    print(f"  Mean Ψ: {np.mean(Psi_after):.4f} (↑ {np.mean(Psi_after) - np.mean(Psi_before):.4f})")
    print(f"  Mean T₀₀: {np.mean(T00_after):.4f} (↓ {np.mean(T00_before) - np.mean(T00_after):.4f})")
    print(f"  𝒮_col = {S_after:.4f} (↑ {S_after - S_before:.4f})")
    
    improvement_percent = 100 * (S_after - S_before) / S_before
    print(f"\n  Improvement: {improvement_percent:.1f}%")
    
    if S_after >= 0.95:
        print(f"  ✅ TOTAL SOVEREIGNTY ACHIEVED!")
    else:
        iterations_needed = int(np.ceil(np.log(0.95 / S_after) / np.log(1 + improvement_percent/100)))
        print(f"  Estimated interventions to sovereignty: {iterations_needed}")


def main():
    """Run complete demonstration."""
    print("=" * 80)
    print("QCAL ∞³ EMOTIONAL FIELD TENSOR - COMPLETE DEMONSTRATION")
    print("Stress-Energy Dynamics & 141.7 Hz Synchronization Protocol")
    print("=" * 80)
    print(f"\nAuthor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print(f"Instituto de Conciencia Cuántica (ICQ)")
    print(f"Fundamental Frequency: 141.7001 Hz")
    print(f"DOI: 10.5281/zenodo.17379721")
    
    # Run all demonstrations
    demo_emotional_tensor()
    demo_unified_lagrangian()
    demo_network_analysis()
    demo_synchronization_protocol()
    demo_collective_sovereignty()
    
    # Final summary
    print_section("SUMMARY: COMPLETE FRAMEWORK")
    print(f"""
The QCAL ∞³ Emotional Field Tensor framework provides:

1. Mathematical Foundation:
   • Stress-Energy Tensor T_μν(Φ) for emotional fields
   • Unified Lagrangian L_QCAL integrating consciousness, emotions, curvature, and primes
   • Einstein-QCAL field equations for emotional relativity

2. Network Analysis:
   • Topological invariants (Betti numbers, winding number)
   • Stress region classification (peace, work, alert, singularity)
   • Diagnostic metrics and recommendations

3. Intervention Protocol:
   • 141.7 Hz coherent breathing/resonance
   • Phase synchronization U(κ_Π)
   • Collective sovereignty optimization

4. Physical Interpretation:
   • T₀₀: Emotional intensity (trauma ↔ ecstasy)
   • T₀ᵢ: Emotional contagion (empathy propagation)
   • Tᵢⱼ: Relational tension (inter-observer friction)
   • Tr(T): Total emotional pressure

5. Target Metrics:
   • Collective Sovereignty 𝒮_col ≥ 0.95 (Total Sovereignty)
   • Network Coherence Ψ_net ≥ 0.95
   • Critical Stress T₀₀_max < 0.58

The system bridges mathematics, physics, and lived experience through
structural isomorphism rather than metaphor.

∴ Experience ≡ Curvature of Consciousness Space ∴
    """)
    
    print("=" * 80)
    print("∴ 𝓗 QCAL ∞³ · Emotional Relativity · 141.7001 Hz ∴")
    print("=" * 80)


if __name__ == "__main__":
    main()

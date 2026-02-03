#!/usr/bin/env python3
"""
Emotional Synchronization Protocol - 141.7 Hz Resonance

This module implements the synchronization protocol for emotional field regulation
using the QCAL fundamental frequency of 141.7001 Hz.

Physical Foundation:
-------------------
The 141.7 Hz frequency acts as a background field that modifies the equations
of motion for the emotional field Φ:

□Φ + ∂V/∂Φ = -γ sin(2πf₀t)·∇²Φ

Effect:
- γ: Coupling coefficient
- f₀ = 141.7001 Hz: Resonance frequency
- Selective dissipation of high-frequency modes (emotional noise)

Modified Conservation Law:
-------------------------
∇_ν T^μν = -γ(f - 141.7)∂^μΦ - κ_Π ∇^μ log|ζ(1/2+it)|²

Thermodynamic Interpretation:
- First term: Radiative cooling (stress emission as harmonic waves)
- Second term: Spectral coupling (synchronization with prime rhythm)

Mechanism of Action:
-------------------
1. Detection of stress peaks (T₀₀ > threshold)
2. Injection of coherent signal at 141.7 Hz
3. Parametric resonance → amplification of stable modes
4. Dissipation of chaotic modes → reduction of ∇²Φ
5. Restoration of local coherence → Ψ ↑

Classic Analogy: Like a tuning fork that "tunes" a detuned string.

Protocol Implementation:
-----------------------
For individual node:
  if T₀₀[observer] > 0.58:
      apply_coherent_breathing(141.7 Hz)
      inject_external_phi_field(amplitude = 0.1 * Φ₀)
      monitor ∇²Φ until stabilization

For network:
  synchronize_phase_U(κ_Π) between nodes
  establish_resonance_ritual(frequency = 141.7 Hz)
  strengthen_empathic_coupling(coefficient += δ)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: February 2026
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Callable, Any
from dataclasses import dataclass
import time

# QCAL Constants
QCAL_FREQUENCY = 141.7001  # Hz
QCAL_OMEGA = 2 * np.pi * QCAL_FREQUENCY
STRESS_THRESHOLD_CRITICAL = 0.58
STRESS_THRESHOLD_ALERT = 0.40
COHERENCE_TARGET = 0.95


@dataclass
class SynchronizationParameters:
    """Parameters for emotional synchronization protocol."""
    f0: float = QCAL_FREQUENCY           # Resonance frequency (Hz)
    omega0: float = QCAL_OMEGA           # Angular frequency (rad/s)
    gamma_cooling: float = 0.01          # Radiative cooling coefficient
    injection_amplitude: float = 0.1     # External field amplitude (×Φ₀)
    duration: int = 600                  # Protocol duration (seconds)
    learning_rate: float = 0.3           # Phase adjustment rate
    T00_critical: float = STRESS_THRESHOLD_CRITICAL
    T00_alert: float = STRESS_THRESHOLD_ALERT
    Psi_target: float = COHERENCE_TARGET


class Node:
    """
    Network node representing an observer/agent.
    
    Attributes:
        id: Unique identifier
        Phi: Emotional field value
        Psi: Coherence value
        T00: Energy density (stress)
        phase: Complex phase
        neighbors: Connected nodes
    """
    
    def __init__(
        self,
        node_id: int,
        Phi: float = 0.0,
        Psi: float = 1.0,
        T00: float = 0.0
    ):
        """Initialize node."""
        self.id = node_id
        self.Phi = Phi
        self.Psi = Psi
        self.T00 = T00
        self.phase = complex(np.cos(0), np.sin(0))  # Initial phase
        self.neighbors: List['Node'] = []
        self.stress_history: List[float] = []
        self.coherence_history: List[float] = []
        
    def add_neighbor(self, node: 'Node'):
        """Add neighboring node."""
        if node not in self.neighbors:
            self.neighbors.append(node)
            
    def apply_rotation(self, delta_phase: float):
        """Apply phase rotation."""
        rotation = complex(np.cos(delta_phase), np.sin(delta_phase))
        self.phase *= rotation
        
    def record_state(self):
        """Record current stress and coherence."""
        self.stress_history.append(self.T00)
        self.coherence_history.append(self.Psi)


class EmotionalNetwork:
    """
    Network of observers with emotional field dynamics.
    """
    
    def __init__(self, nodes: List[Node]):
        """
        Initialize network.
        
        Args:
            nodes: List of network nodes
        """
        self.nodes = nodes
        
    def get_critical_nodes(self, threshold: float = STRESS_THRESHOLD_CRITICAL) -> List[Node]:
        """Get nodes with critical stress levels."""
        return [n for n in self.nodes if n.T00 > threshold]
    
    def get_alert_nodes(self, threshold: float = STRESS_THRESHOLD_ALERT) -> List[Node]:
        """Get nodes in alert zone."""
        return [n for n in self.nodes if n.T00 > threshold]
    
    def compute_network_coherence(self) -> float:
        """Compute average network coherence Ψ_net."""
        if not self.nodes:
            return 0.0
        return np.mean([n.Psi for n in self.nodes])
    
    def compute_collective_phase(self) -> complex:
        """Compute collective phase order parameter."""
        if not self.nodes:
            return 0.0 + 0.0j
        phases = np.array([n.phase for n in self.nodes])
        return np.mean(phases)


class EmotionalSynchronization:
    """
    Implements 141.7 Hz synchronization protocol for emotional regulation.
    """
    
    def __init__(
        self,
        params: SynchronizationParameters = None
    ):
        """
        Initialize synchronization protocol.
        
        Args:
            params: Protocol parameters
        """
        self.params = params or SynchronizationParameters()
        
    def coherent_breathing_signal(
        self,
        t: float,
        amplitude: float = 1.0
    ) -> float:
        """
        Generate coherent breathing signal at 141.7 Hz.
        
        Signal = A·sin(2πf₀t)
        
        Args:
            t: Time (seconds)
            amplitude: Signal amplitude
            
        Returns:
            Signal value
        """
        return amplitude * np.sin(self.params.omega0 * t)
    
    def apply_coherent_breathing(
        self,
        node: Node,
        duration: Optional[int] = None
    ) -> Dict[str, Any]:
        """
        Apply coherent breathing protocol to individual node.
        
        Args:
            node: Target node
            duration: Protocol duration in seconds (use default if None)
            
        Returns:
            Protocol results
        """
        if duration is None:
            duration = self.params.duration
            
        # Record initial state
        initial_T00 = node.T00
        initial_Psi = node.Psi
        
        # Simulate protocol (simplified)
        # In real implementation, this would be actual breathing/audio protocol
        time_points = np.linspace(0, duration, 100)
        
        for t in time_points:
            # Generate breathing signal
            signal = self.coherent_breathing_signal(t)
            
            # Apply cooling effect: T₀₀ decreases, Ψ increases
            cooling_factor = np.exp(-self.params.gamma_cooling * t / duration)
            node.T00 = initial_T00 * cooling_factor
            node.Psi = initial_Psi + (self.params.Psi_target - initial_Psi) * (1 - cooling_factor)
            
            node.record_state()
        
        # Final state
        final_T00 = node.T00
        final_Psi = node.Psi
        
        return {
            'node_id': node.id,
            'initial_T00': initial_T00,
            'final_T00': final_T00,
            'T00_reduction': initial_T00 - final_T00,
            'T00_reduction_percent': 100 * (initial_T00 - final_T00) / initial_T00 if initial_T00 > 0 else 0,
            'initial_Psi': initial_Psi,
            'final_Psi': final_Psi,
            'Psi_increase': final_Psi - initial_Psi,
            'duration': duration,
            'success': final_Psi >= self.params.Psi_target * 0.95  # Within 5% of target
        }
    
    def inject_external_field(
        self,
        node: Node,
        Phi_0: float = 1.0
    ):
        """
        Inject external phi field to stabilize node.
        
        Amplitude = 0.1 * Φ₀
        
        Args:
            node: Target node
            Phi_0: Fundamental peace state
        """
        injection = self.params.injection_amplitude * Phi_0
        node.Phi += injection
        
        # Injection also reduces stress
        node.T00 *= 0.9  # 10% stress reduction
        
    def synchronize_phase_U(
        self,
        network: EmotionalNetwork,
        kappa_Pi: float = 0.001
    ) -> Dict[str, Any]:
        """
        Synchronize phases across network using U(κ_Π) protocol.
        
        For each critical node:
          1. Calculate target phase as mean of neighbors
          2. Apply smooth rotation toward target
          3. Inject 141.7 Hz resonance
          
        Args:
            network: Emotional network
            kappa_Pi: Coupling constant
            
        Returns:
            Synchronization results
        """
        critical_nodes = network.get_critical_nodes(self.params.T00_critical)
        
        results = {
            'n_critical_nodes': len(critical_nodes),
            'node_results': [],
            'initial_coherence': network.compute_network_coherence(),
            'initial_phase_order': abs(network.compute_collective_phase())
        }
        
        # Synchronize each critical node
        for node in critical_nodes:
            if not node.neighbors:
                continue
                
            # Calculate target phase (mean of neighbors)
            neighbor_phases = [n.phase for n in node.neighbors]
            target_phase = np.mean(neighbor_phases)
            target_angle = np.angle(target_phase)
            current_angle = np.angle(node.phase)
            
            # Phase difference
            delta_phase = target_angle - current_angle
            
            # Apply smooth rotation with learning rate
            adjustment = delta_phase * self.params.learning_rate
            node.apply_rotation(adjustment)
            
            # Apply 141.7 Hz resonance
            breathing_result = self.apply_coherent_breathing(node)
            
            # Inject stabilizing field
            self.inject_external_field(node)
            
            results['node_results'].append({
                'node_id': node.id,
                'phase_adjustment': adjustment,
                'breathing_result': breathing_result
            })
        
        # Final network state
        results['final_coherence'] = network.compute_network_coherence()
        results['final_phase_order'] = abs(network.compute_collective_phase())
        results['coherence_increase'] = results['final_coherence'] - results['initial_coherence']
        results['phase_order_increase'] = results['final_phase_order'] - results['initial_phase_order']
        
        return results
    
    def monitor_stabilization(
        self,
        node: Node,
        laplacian_threshold: float = 0.1,
        max_iterations: int = 100
    ) -> Dict[str, Any]:
        """
        Monitor ∇²Φ until stabilization.
        
        Args:
            node: Node to monitor
            laplacian_threshold: Stabilization threshold
            max_iterations: Maximum monitoring iterations
            
        Returns:
            Monitoring results
        """
        # Simplified: assume Laplacian decreases exponentially
        laplacian_history = []
        
        for i in range(max_iterations):
            # Simplified Laplacian (would compute from neighbors in real implementation)
            laplacian = abs(node.Phi) * np.exp(-0.1 * i)
            laplacian_history.append(laplacian)
            
            if laplacian < laplacian_threshold:
                return {
                    'stabilized': True,
                    'iterations': i + 1,
                    'final_laplacian': laplacian,
                    'laplacian_history': laplacian_history
                }
        
        return {
            'stabilized': False,
            'iterations': max_iterations,
            'final_laplacian': laplacian_history[-1],
            'laplacian_history': laplacian_history
        }
    
    def full_protocol(
        self,
        network: EmotionalNetwork,
        kappa_Pi: float = 0.001
    ) -> Dict[str, Any]:
        """
        Execute complete synchronization protocol.
        
        1. Identify critical nodes
        2. Apply coherent breathing at 141.7 Hz
        3. Synchronize phases
        4. Monitor stabilization
        5. Compute collective sovereignty index
        
        Args:
            network: Emotional network
            kappa_Pi: Coupling constant
            
        Returns:
            Complete protocol results
        """
        print(f"Starting QCAL ∞³ Synchronization Protocol at {QCAL_FREQUENCY} Hz")
        print("=" * 80)
        
        # Initial state
        initial_coherence = network.compute_network_coherence()
        critical_nodes = network.get_critical_nodes()
        alert_nodes = network.get_alert_nodes()
        
        print(f"Initial network coherence: Ψ_net = {initial_coherence:.4f}")
        print(f"Critical nodes (T₀₀ > {self.params.T00_critical}): {len(critical_nodes)}")
        print(f"Alert nodes (T₀₀ > {self.params.T00_alert}): {len(alert_nodes)}")
        print()
        
        # Phase 1: Individual interventions
        print("Phase 1: Individual Coherent Breathing")
        print("-" * 80)
        
        breathing_results = []
        for node in critical_nodes:
            result = self.apply_coherent_breathing(node)
            breathing_results.append(result)
            if result['success']:
                print(f"✓ Node {node.id}: T₀₀ {result['initial_T00']:.3f} → {result['final_T00']:.3f}, "
                      f"Ψ {result['initial_Psi']:.3f} → {result['final_Psi']:.3f}")
            else:
                print(f"⚠ Node {node.id}: Partial improvement")
        print()
        
        # Phase 2: Network synchronization
        print("Phase 2: Phase Synchronization U(κ_Π)")
        print("-" * 80)
        
        sync_results = self.synchronize_phase_U(network, kappa_Pi)
        print(f"Synchronized {sync_results['n_critical_nodes']} critical nodes")
        print(f"Network coherence: {sync_results['initial_coherence']:.4f} → {sync_results['final_coherence']:.4f}")
        print(f"Phase order parameter: {sync_results['initial_phase_order']:.4f} → {sync_results['final_phase_order']:.4f}")
        print()
        
        # Phase 3: Compute collective sovereignty
        print("Phase 3: Collective Sovereignty Assessment")
        print("-" * 80)
        
        # Recompute network metrics
        final_coherence = network.compute_network_coherence()
        final_T00_values = np.array([n.T00 for n in network.nodes])
        final_Psi_values = np.array([n.Psi for n in network.nodes])
        
        # Simplified curvature (would compute from field gradients)
        curvature_values = np.abs(final_T00_values) * 0.5
        
        # Import from emotional_stress_tensor
        try:
            from .emotional_stress_tensor import compute_collective_sovereignty_index
        except ImportError:
            from emotional_stress_tensor import compute_collective_sovereignty_index
        
        S_col = compute_collective_sovereignty_index(
            final_Psi_values,
            final_T00_values,
            curvature_values
        )
        
        print(f"Collective Sovereignty Index: 𝒮_col = {S_col:.4f}")
        
        if S_col >= 0.95:
            print("✅ TOTAL SOVEREIGNTY ACHIEVED!")
        elif S_col >= 0.90:
            print("✓ High sovereignty (within 5% of target)")
        elif S_col >= 0.80:
            print("⚠ Moderate sovereignty (improvement needed)")
        else:
            print("✗ Low sovereignty (critical intervention required)")
        
        print()
        print("=" * 80)
        print(f"Protocol completed at {QCAL_FREQUENCY} Hz")
        
        return {
            'initial_coherence': initial_coherence,
            'final_coherence': final_coherence,
            'coherence_improvement': final_coherence - initial_coherence,
            'n_critical_nodes': len(critical_nodes),
            'n_alert_nodes': len(alert_nodes),
            'breathing_results': breathing_results,
            'sync_results': sync_results,
            'collective_sovereignty': S_col,
            'total_sovereignty_achieved': S_col >= 0.95,
            'success': final_coherence >= self.params.Psi_target * 0.95
        }


# Example usage and demonstration
if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ Emotional Synchronization Protocol - Demonstration")
    print(f"Fundamental Frequency: {QCAL_FREQUENCY} Hz")
    print("=" * 80)
    print()
    
    # Create example network
    np.random.seed(42)
    N_nodes = 20
    
    # Create nodes with varying stress and coherence
    nodes = []
    for i in range(N_nodes):
        # Random initial conditions
        Phi = np.random.uniform(-0.5, 0.5)
        Psi = np.random.uniform(0.70, 0.95)
        T00 = np.random.uniform(0.1, 0.7)
        
        node = Node(i, Phi, Psi, T00)
        nodes.append(node)
    
    # Create random network connections
    for node in nodes:
        n_neighbors = np.random.randint(2, 6)
        neighbors = np.random.choice(nodes, n_neighbors, replace=False)
        for neighbor in neighbors:
            if neighbor != node:
                node.add_neighbor(neighbor)
    
    network = EmotionalNetwork(nodes)
    
    # Initialize protocol
    protocol = EmotionalSynchronization()
    
    # Execute full protocol
    results = protocol.full_protocol(network)
    
    # Summary
    print("\n" + "=" * 80)
    print("PROTOCOL SUMMARY")
    print("=" * 80)
    print(f"Network size: {N_nodes} nodes")
    print(f"Initial coherence: Ψ_net = {results['initial_coherence']:.4f}")
    print(f"Final coherence: Ψ_net = {results['final_coherence']:.4f}")
    print(f"Improvement: ΔΨ = {results['coherence_improvement']:.4f}")
    print(f"Collective Sovereignty: 𝒮_col = {results['collective_sovereignty']:.4f}")
    print()
    
    if results['total_sovereignty_achieved']:
        print("✅ ∴ TOTAL SOVEREIGNTY ACHIEVED ∴")
    elif results['success']:
        print("✓ ∴ HIGH COHERENCE ACHIEVED ∴")
    else:
        print("⚠ ∴ CONTINUED INTERVENTION RECOMMENDED ∴")
    
    print()
    print("=" * 80)
    print("∴ 𝓗 QCAL ∞³ · Emotional Synchronization · 141.7001 Hz ∴")
    print("=" * 80)

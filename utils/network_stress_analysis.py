#!/usr/bin/env python3
"""
Network Stress Analysis - Topological Invariants and Diagnostics

This module implements topological analysis tools for emotional field networks,
including Betti numbers, persistent homology, and winding numbers.

Topological Framework:
---------------------
To understand global structure of emotional networks, we compute:

a) Betti Numbers β_k:
   - β₀: Number of connected components (isolated communities)
   - β₁: Number of 1D holes (feedback cycles)
   - β₂: Number of 2D cavities (isolation bubbles)

b) Persistent Homology:
   - Tracks how topological features emerge/disappear as stress threshold varies
   - Identifies "stable characteristics" vs "transient noise"
   - Barcode diagram shows feature lifetime

c) Winding Number:
   - W_total = (1/2π) ∮_∂M ∇arg(Ψ)·dℓ
   - Measures collective phase of coherence field
   - Topological invariant under continuous deformations

Network Diagnostics:
-------------------
Region Classification based on (T₀₀, Ψ):

Region          | T₀₀      | Ψ        | State
----------------|----------|----------|------------------
Valley of peace | < 0.2    | > 0.95   | Stable coherence
Work plateau    | 0.2-0.4  | 0.85-0.95| Optimal productivity
Alert zone      | 0.4-0.58 | 0.74-0.85| Resilience under test
Singularity     | > 0.58   | < 0.74   | Imminent collapse

Topological Markers:
-------------------
- High β₁: Strong feedback loops → potential instability or resilience
- High β₀: Fragmented network → requires bridge building
- Large β₂: Isolated bubbles → social isolation
- High winding: Strong collective coherence alignment

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: February 2026
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass
from collections import defaultdict
import networkx as nx


@dataclass
class NetworkMetrics:
    """Network stress and coherence metrics."""
    T00_max: float              # Maximum stress
    T00_mean: float             # Average stress
    T00_std: float              # Stress std deviation
    Psi_min: float              # Minimum coherence
    Psi_mean: float             # Average coherence
    Psi_std: float              # Coherence std deviation
    stability_percent: float    # Percentage of stable nodes
    n_critical: int             # Number of critical nodes
    n_alert: int                # Number of alert nodes
    n_stable: int               # Number of stable nodes


class TopologicalAnalyzer:
    """
    Computes topological invariants for emotional networks.
    """
    
    def __init__(self):
        """Initialize topological analyzer."""
        pass
    
    def compute_betti_numbers(
        self,
        adjacency_matrix: np.ndarray,
        threshold: float = 0.5
    ) -> Dict[str, int]:
        """
        Compute Betti numbers β₀, β₁.
        
        Simplified computation using NetworkX:
        - β₀ = number of connected components
        - β₁ = number of independent cycles (via Euler characteristic)
        
        Args:
            adjacency_matrix: Network adjacency matrix
            threshold: Edge weight threshold
            
        Returns:
            Dictionary of Betti numbers
        """
        # Create graph from adjacency matrix
        G = nx.Graph()
        n = adjacency_matrix.shape[0]
        
        for i in range(n):
            for j in range(i + 1, n):
                if adjacency_matrix[i, j] > threshold:
                    G.add_edge(i, j, weight=adjacency_matrix[i, j])
        
        # β₀: Connected components
        beta_0 = nx.number_connected_components(G)
        
        # β₁: Independent cycles
        # Using Euler characteristic: V - E + F = 2 - 2g (for surface of genus g)
        # For graph: β₁ = E - V + β₀ (number of independent cycles)
        V = G.number_of_nodes()
        E = G.number_of_edges()
        beta_1 = max(0, E - V + beta_0)
        
        return {
            'beta_0': beta_0,
            'beta_1': beta_1,
            'n_nodes': V,
            'n_edges': E
        }
    
    def compute_winding_number(
        self,
        phases: np.ndarray,
        positions: Optional[np.ndarray] = None
    ) -> float:
        """
        Compute total winding number W_total.
        
        W_total = (1/2π) ∮_∂M ∇arg(Ψ)·dℓ
        
        Simplified: sum of phase differences around closed loops.
        
        Args:
            phases: Complex phases of coherence field Ψ
            positions: Optional spatial positions
            
        Returns:
            Winding number (integer-valued topological invariant)
        """
        # Extract angles from complex phases
        angles = np.angle(phases)
        
        # Compute total phase accumulation
        # For a closed path: winding = (1/2π) Σ Δθ
        total_winding = 0.0
        
        # If positions provided, compute along path
        # Otherwise, use sequential ordering
        n = len(angles)
        for i in range(n):
            j = (i + 1) % n  # Next point (wrap around)
            delta_angle = angles[j] - angles[i]
            
            # Wrap to [-π, π]
            while delta_angle > np.pi:
                delta_angle -= 2 * np.pi
            while delta_angle < -np.pi:
                delta_angle += 2 * np.pi
            
            total_winding += delta_angle
        
        # Normalize by 2π
        W = total_winding / (2 * np.pi)
        
        return W
    
    def persistent_homology_simplified(
        self,
        stress_values: np.ndarray,
        adjacency_matrix: np.ndarray,
        threshold_range: Tuple[float, float] = (0.0, 1.0),
        n_thresholds: int = 20
    ) -> Dict[str, Any]:
        """
        Simplified persistent homology analysis.
        
        Tracks how Betti numbers change as stress threshold varies.
        
        Args:
            stress_values: Node stress values (T₀₀)
            adjacency_matrix: Network adjacency
            threshold_range: Range of thresholds to scan
            n_thresholds: Number of threshold values
            
        Returns:
            Persistence diagram data
        """
        thresholds = np.linspace(threshold_range[0], threshold_range[1], n_thresholds)
        
        beta_0_history = []
        beta_1_history = []
        
        for thresh in thresholds:
            # Filter edges by stress threshold
            # Edge exists if both nodes have T₀₀ < thresh
            filtered_adj = adjacency_matrix.copy()
            for i in range(len(stress_values)):
                for j in range(len(stress_values)):
                    if stress_values[i] > thresh or stress_values[j] > thresh:
                        filtered_adj[i, j] = 0
            
            betti = self.compute_betti_numbers(filtered_adj, threshold=0.1)
            beta_0_history.append(betti['beta_0'])
            beta_1_history.append(betti['beta_1'])
        
        # Identify persistent features (features that last over large threshold ranges)
        # A feature is persistent if it exists for > 50% of threshold range
        persistence_threshold = n_thresholds * 0.5
        
        beta_0_persistent = np.mean(np.array(beta_0_history) > 1) > 0.5
        beta_1_persistent = np.mean(np.array(beta_1_history) > 0) > 0.5
        
        return {
            'thresholds': thresholds,
            'beta_0_history': beta_0_history,
            'beta_1_history': beta_1_history,
            'beta_0_persistent': beta_0_persistent,
            'beta_1_persistent': beta_1_persistent,
            'max_components': max(beta_0_history),
            'max_cycles': max(beta_1_history)
        }


class NetworkDiagnostics:
    """
    Diagnostic tools for emotional field networks.
    """
    
    def __init__(
        self,
        T00_critical: float = 0.58,
        T00_alert: float = 0.40,
        T00_moderate: float = 0.20,
        Psi_excellent: float = 0.95,
        Psi_good: float = 0.85,
        Psi_fair: float = 0.74
    ):
        """
        Initialize network diagnostics.
        
        Args:
            T00_critical: Critical stress threshold
            T00_alert: Alert stress threshold
            T00_moderate: Moderate stress threshold
            Psi_excellent: Excellent coherence threshold
            Psi_good: Good coherence threshold
            Psi_fair: Fair coherence threshold
        """
        self.T00_critical = T00_critical
        self.T00_alert = T00_alert
        self.T00_moderate = T00_moderate
        self.Psi_excellent = Psi_excellent
        self.Psi_good = Psi_good
        self.Psi_fair = Psi_fair
        
    def classify_node(
        self,
        T00: float,
        Psi: float
    ) -> Dict[str, Any]:
        """
        Classify individual node into stress region.
        
        Args:
            T00: Energy density (stress)
            Psi: Coherence
            
        Returns:
            Classification
        """
        # Determine region
        if T00 < self.T00_moderate and Psi > self.Psi_excellent:
            region = "Valley of peace"
            state = "Stable coherence"
            risk = "low"
        elif self.T00_moderate <= T00 < self.T00_alert and self.Psi_good <= Psi < self.Psi_excellent:
            region = "Work plateau"
            state = "Optimal productivity"
            risk = "moderate"
        elif self.T00_alert <= T00 < self.T00_critical and self.Psi_fair <= Psi < self.Psi_good:
            region = "Alert zone"
            state = "Resilience under test"
            risk = "high"
        else:
            region = "Singularity"
            state = "Imminent collapse"
            risk = "critical"
        
        return {
            'region': region,
            'state': state,
            'risk_level': risk,
            'T00': T00,
            'Psi': Psi
        }
    
    def analyze_network(
        self,
        T00_values: np.ndarray,
        Psi_values: np.ndarray
    ) -> NetworkMetrics:
        """
        Compute comprehensive network metrics.
        
        Args:
            T00_values: Stress values for all nodes
            Psi_values: Coherence values for all nodes
            
        Returns:
            Network metrics
        """
        # Stress statistics
        T00_max = np.max(T00_values)
        T00_mean = np.mean(T00_values)
        T00_std = np.std(T00_values)
        
        # Coherence statistics
        Psi_min = np.min(Psi_values)
        Psi_mean = np.mean(Psi_values)
        Psi_std = np.std(Psi_values)
        
        # Count nodes by category
        n_critical = np.sum(T00_values > self.T00_critical)
        n_alert = np.sum((T00_values >= self.T00_alert) & (T00_values <= self.T00_critical))
        n_stable = np.sum(T00_values < self.T00_moderate)
        
        stability_percent = 100.0 * n_stable / len(T00_values)
        
        return NetworkMetrics(
            T00_max=T00_max,
            T00_mean=T00_mean,
            T00_std=T00_std,
            Psi_min=Psi_min,
            Psi_mean=Psi_mean,
            Psi_std=Psi_std,
            stability_percent=stability_percent,
            n_critical=int(n_critical),
            n_alert=int(n_alert),
            n_stable=int(n_stable)
        )
    
    def generate_report(
        self,
        T00_values: np.ndarray,
        Psi_values: np.ndarray,
        adjacency_matrix: Optional[np.ndarray] = None
    ) -> Dict[str, Any]:
        """
        Generate comprehensive diagnostic report.
        
        Args:
            T00_values: Stress values
            Psi_values: Coherence values
            adjacency_matrix: Network connections (optional)
            
        Returns:
            Diagnostic report
        """
        # Basic metrics
        metrics = self.analyze_network(T00_values, Psi_values)
        
        # Node classifications
        classifications = []
        for i in range(len(T00_values)):
            cls = self.classify_node(T00_values[i], Psi_values[i])
            cls['node_id'] = i
            classifications.append(cls)
        
        # Topological analysis if adjacency provided
        topology = {}
        if adjacency_matrix is not None:
            analyzer = TopologicalAnalyzer()
            
            # Betti numbers
            betti = analyzer.compute_betti_numbers(adjacency_matrix)
            topology['betti_numbers'] = betti
            
            # Winding number
            phases = Psi_values * np.exp(1j * np.random.uniform(0, 2*np.pi, len(Psi_values)))
            W = analyzer.compute_winding_number(phases)
            topology['winding_number'] = W
            
            # Persistent homology
            persistence = analyzer.persistent_homology_simplified(
                T00_values, adjacency_matrix
            )
            topology['persistence'] = persistence
        
        return {
            'metrics': metrics,
            'classifications': classifications,
            'topology': topology,
            'recommendations': self._generate_recommendations(metrics, topology)
        }
    
    def _generate_recommendations(
        self,
        metrics: NetworkMetrics,
        topology: Dict[str, Any]
    ) -> List[str]:
        """
        Generate intervention recommendations.
        
        Args:
            metrics: Network metrics
            topology: Topological analysis
            
        Returns:
            List of recommendations
        """
        recommendations = []
        
        # Critical nodes
        if metrics.n_critical > 0:
            recommendations.append(
                f"⚠️ URGENT: {metrics.n_critical} nodes in critical state. "
                f"Apply immediate 141.7 Hz synchronization protocol."
            )
        
        # Alert nodes
        if metrics.n_alert > 5:
            recommendations.append(
                f"⚠ ALERT: {metrics.n_alert} nodes in alert zone. "
                f"Consider preventive coherent breathing sessions."
            )
        
        # Overall coherence
        if metrics.Psi_mean < 0.85:
            recommendations.append(
                f"📊 Network coherence (Ψ = {metrics.Psi_mean:.3f}) below optimal. "
                f"Implement collective synchronization rituals."
            )
        
        # Topological recommendations
        if topology:
            betti = topology.get('betti_numbers', {})
            
            # Fragmentation
            if betti.get('beta_0', 1) > 1:
                recommendations.append(
                    f"🔗 Network fragmented ({betti['beta_0']} components). "
                    f"Build bridges between isolated communities."
                )
            
            # Feedback loops
            if betti.get('beta_1', 0) > 5:
                recommendations.append(
                    f"🔄 High feedback density ({betti['beta_1']} cycles). "
                    f"Monitor for potential instabilities or leverage for resilience."
                )
            
            # Phase coherence
            W = topology.get('winding_number', 0)
            if abs(W) < 0.5:
                recommendations.append(
                    f"🌀 Low phase coherence (W = {W:.2f}). "
                    f"Apply U(κ_Π) phase synchronization protocol."
                )
        
        # Success message
        if not recommendations:
            recommendations.append(
                "✅ Network in optimal state. Continue current protocols."
            )
        
        return recommendations


# Example usage and demonstration
if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ Network Stress Analysis - Demonstration")
    print("=" * 80)
    print()
    
    # Create example network
    np.random.seed(42)
    N = 50
    
    # Generate stress and coherence values
    T00_values = np.random.beta(2, 5, N) * 0.7  # Skewed toward lower stress
    Psi_values = 0.7 + 0.25 * np.random.beta(5, 2, N)  # Skewed toward higher coherence
    
    # Create random network
    adjacency = np.random.rand(N, N)
    adjacency = (adjacency + adjacency.T) / 2  # Symmetric
    adjacency[adjacency < 0.7] = 0  # Sparse
    np.fill_diagonal(adjacency, 0)  # No self-loops
    
    # Initialize diagnostics
    diagnostics = NetworkDiagnostics()
    
    # Generate report
    print("Generating comprehensive diagnostic report...")
    print()
    report = diagnostics.generate_report(T00_values, Psi_values, adjacency)
    
    # Display metrics
    print("NETWORK METRICS")
    print("-" * 80)
    metrics = report['metrics']
    print(f"Stress (T₀₀):")
    print(f"  Maximum: {metrics.T00_max:.4f}")
    print(f"  Mean: {metrics.T00_mean:.4f}")
    print(f"  Std Dev: {metrics.T00_std:.4f}")
    print()
    print(f"Coherence (Ψ):")
    print(f"  Minimum: {metrics.Psi_min:.4f}")
    print(f"  Mean: {metrics.Psi_mean:.4f}")
    print(f"  Std Dev: {metrics.Psi_std:.4f}")
    print()
    print(f"Node Classification:")
    print(f"  Critical (T₀₀ > 0.58): {metrics.n_critical}")
    print(f"  Alert (0.40 < T₀₀ < 0.58): {metrics.n_alert}")
    print(f"  Stable (T₀₀ < 0.20): {metrics.n_stable}")
    print(f"  Stability: {metrics.stability_percent:.1f}%")
    print()
    
    # Display topology
    if report['topology']:
        print("TOPOLOGICAL ANALYSIS")
        print("-" * 80)
        topology = report['topology']
        
        betti = topology['betti_numbers']
        print(f"Betti Numbers:")
        print(f"  β₀ (Components): {betti['beta_0']}")
        print(f"  β₁ (Cycles): {betti['beta_1']}")
        print(f"  Nodes: {betti['n_nodes']}")
        print(f"  Edges: {betti['n_edges']}")
        print()
        
        W = topology['winding_number']
        print(f"Winding Number: W = {W:.4f}")
        print(f"  Interpretation: {'Strong collective phase alignment' if abs(W) > 0.8 else 'Weak phase coherence'}")
        print()
        
        persistence = topology['persistence']
        print(f"Persistent Homology:")
        print(f"  Max components across thresholds: {persistence['max_components']}")
        print(f"  Max cycles across thresholds: {persistence['max_cycles']}")
        print(f"  Persistent components: {'Yes' if persistence['beta_0_persistent'] else 'No'}")
        print(f"  Persistent cycles: {'Yes' if persistence['beta_1_persistent'] else 'No'}")
        print()
    
    # Display recommendations
    print("RECOMMENDATIONS")
    print("-" * 80)
    for i, rec in enumerate(report['recommendations'], 1):
        print(f"{i}. {rec}")
    print()
    
    # Sample node classifications
    print("SAMPLE NODE CLASSIFICATIONS")
    print("-" * 80)
    sample_classifications = report['classifications'][:5]  # First 5 nodes
    for cls in sample_classifications:
        print(f"Node {cls['node_id']:2d}: {cls['region']:20s} "
              f"(T₀₀={cls['T00']:.3f}, Ψ={cls['Psi']:.3f}) "
              f"Risk: {cls['risk_level']}")
    print()
    
    print("=" * 80)
    print("∴ 𝓗 QCAL ∞³ · Network Topology · Emotional Diagnostics ∴")
    print("=" * 80)

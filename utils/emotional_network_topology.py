#!/usr/bin/env python3
"""
Emotional Network Topology Module - Topological Invariants and Stress Analysis

This module implements topological analysis of emotional stress networks,
computing invariants that characterize the global structure of collective
emotional states.

Mathematical Framework:
    Topological invariants provide global characterization:
    
    1. Betti Numbers β_k:
       - β₀: Number of connected components (isolated communities)
       - β₁: Number of 1D holes (feedback cycles)
       - β₂: Number of 2D cavities (isolation bubbles)
    
    2. Persistent Homology:
       - Tracks topological features across stress thresholds
       - Distinguishes stable structures from transient noise
    
    3. Winding Number:
       W_total = (1/2π) ∮_∂M ∇arg(Ψ)·dℓ
       - Measures collective phase of coherence field
    
Stress Region Classification:
    Valley of Peace:    T₀₀ < 0.2,  Ψ > 0.95  (stable coherence)
    Work Plateau:  0.2 ≤ T₀₀ < 0.4, 0.85 ≤ Ψ < 0.95  (productive)
    Alert Zone:    0.4 ≤ T₀₀ < 0.58, 0.74 ≤ Ψ < 0.85  (resilience test)
    Singularity:        T₀₀ ≥ 0.58 or Ψ < 0.74  (collapse imminent)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Dict, Optional, List, Any
from scipy.spatial.distance import pdist, squareform
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components
from dataclasses import dataclass
import warnings


@dataclass
class TopologyParameters:
    """Parameters for topological analysis."""
    stress_threshold_low: float = 0.2
    stress_threshold_medium: float = 0.4
    stress_threshold_high: float = 0.58
    coherence_threshold_high: float = 0.95
    coherence_threshold_medium: float = 0.85
    coherence_threshold_low: float = 0.74
    persistence_epsilon: float = 0.05


class EmotionalNetworkTopology:
    """
    Implements topological analysis of emotional stress networks.
    
    This class provides methods to:
    1. Compute Betti numbers (connected components, cycles, cavities)
    2. Perform persistent homology analysis
    3. Compute winding numbers for phase coherence
    4. Classify stress regions and identify critical zones
    """
    
    def __init__(
        self,
        params: Optional[TopologyParameters] = None
    ):
        """
        Initialize network topology analyzer.
        
        Parameters:
        -----------
        params : TopologyParameters, optional
            Topology analysis parameters
        """
        self.params = params if params is not None else TopologyParameters()
    
    def compute_betti_numbers(
        self,
        adjacency_matrix: np.ndarray,
        stress_threshold: Optional[float] = None
    ) -> Dict[str, int]:
        """
        Compute Betti numbers of the network.
        
        Parameters:
        -----------
        adjacency_matrix : np.ndarray
            Network adjacency matrix (weighted or binary)
        stress_threshold : float, optional
            Threshold for edge filtering (default: no filtering)
            
        Returns:
        --------
        dict
            Dictionary with Betti numbers:
            - 'beta_0': Number of connected components
            - 'beta_1': Number of 1-cycles (estimate)
        """
        # Filter adjacency by threshold if provided
        if stress_threshold is not None:
            adjacency = (adjacency_matrix > stress_threshold).astype(float)
        else:
            adjacency = adjacency_matrix
        
        # β₀: Connected components
        sparse_adj = csr_matrix(adjacency)
        n_components, labels = connected_components(
            sparse_adj,
            directed=False,
            return_labels=True
        )
        
        # β₁: Number of independent cycles (Euler characteristic)
        # For a graph: β₁ = E - V + β₀
        # where E = edges, V = vertices
        num_vertices = adjacency.shape[0]
        num_edges = np.sum(adjacency > 0) // 2  # Undirected
        beta_1 = num_edges - num_vertices + n_components
        beta_1 = max(0, beta_1)  # Can't be negative
        
        return {
            'beta_0': n_components,
            'beta_1': beta_1,
            'component_labels': labels,
            'component_sizes': [np.sum(labels == i) for i in range(n_components)]
        }
    
    def persistent_homology_1d(
        self,
        adjacency_matrix: np.ndarray,
        stress_values: np.ndarray,
        num_thresholds: int = 20
    ) -> Dict[str, Any]:
        """
        Compute 1D persistent homology (persistence of connected components).
        
        Tracks how connected components merge as stress threshold varies.
        
        Parameters:
        -----------
        adjacency_matrix : np.ndarray
            Network adjacency matrix
        stress_values : np.ndarray
            Edge stress values
        num_thresholds : int
            Number of threshold levels to analyze
            
        Returns:
        --------
        dict
            Dictionary with persistence data:
            - 'thresholds': Threshold values
            - 'beta_0': β₀ at each threshold
            - 'beta_1': β₁ at each threshold
            - 'persistence_diagram': Birth-death pairs
        """
        # Create threshold range
        min_stress = np.min(stress_values[stress_values > 0])
        max_stress = np.max(stress_values)
        thresholds = np.linspace(min_stress, max_stress, num_thresholds)
        
        beta_0_values = []
        beta_1_values = []
        
        for threshold in thresholds:
            betti = self.compute_betti_numbers(adjacency_matrix, threshold)
            beta_0_values.append(betti['beta_0'])
            beta_1_values.append(betti['beta_1'])
        
        # Compute persistence diagram (simplified)
        # Birth-death pairs for components
        persistence_diagram = []
        
        # Track when components appear/disappear
        for i in range(len(thresholds) - 1):
            if beta_0_values[i] != beta_0_values[i + 1]:
                # Component merged or split
                persistence_diagram.append({
                    'birth': thresholds[i],
                    'death': thresholds[i + 1],
                    'dimension': 0,
                    'persistence': thresholds[i + 1] - thresholds[i]
                })
        
        return {
            'thresholds': thresholds,
            'beta_0': np.array(beta_0_values),
            'beta_1': np.array(beta_1_values),
            'persistence_diagram': persistence_diagram
        }
    
    def compute_winding_number(
        self,
        Psi_complex: np.ndarray,
        adjacency_matrix: np.ndarray
    ) -> Dict[str, float]:
        """
        Compute winding number of coherence field.
        
        W = (1/2π) ∮ ∇arg(Ψ)·dℓ
        
        Measures the total phase accumulation around closed loops.
        
        Parameters:
        -----------
        Psi_complex : np.ndarray
            Complex coherence field Ψ = |Ψ|exp(iφ)
        adjacency_matrix : np.ndarray
            Network adjacency matrix
            
        Returns:
        --------
        dict
            Dictionary with winding number data
        """
        # Extract phase
        phase = np.angle(Psi_complex)
        
        # Compute phase differences along edges
        num_nodes = len(Psi_complex)
        phase_circulation = 0.0
        total_edges = 0
        
        for i in range(num_nodes):
            for j in range(i + 1, num_nodes):
                if adjacency_matrix[i, j] > 0:
                    # Phase difference
                    delta_phase = phase[j] - phase[i]
                    
                    # Wrap to [-π, π]
                    delta_phase = np.arctan2(np.sin(delta_phase), np.cos(delta_phase))
                    
                    phase_circulation += delta_phase
                    total_edges += 1
        
        # Winding number (approximate)
        if total_edges > 0:
            winding = phase_circulation / (2 * np.pi)
        else:
            winding = 0.0
        
        return {
            'winding_number': winding,
            'phase_circulation': phase_circulation,
            'total_edges': total_edges,
            'mean_phase': np.mean(phase),
            'phase_std': np.std(phase)
        }
    
    def classify_stress_regions(
        self,
        T00: np.ndarray,
        Psi: np.ndarray
    ) -> Dict[str, Any]:
        """
        Classify network nodes into stress regions.
        
        Parameters:
        -----------
        T00 : np.ndarray
            Energy density (stress) at each node
        Psi : np.ndarray
            Coherence at each node
            
        Returns:
        --------
        dict
            Classification results with masks and statistics
        """
        p = self.params
        
        # Define region masks
        valley_of_peace = (T00 < p.stress_threshold_low) & (Psi > p.coherence_threshold_high)
        work_plateau = (
            (T00 >= p.stress_threshold_low) & 
            (T00 < p.stress_threshold_medium) &
            (Psi >= p.coherence_threshold_medium) & 
            (Psi < p.coherence_threshold_high)
        )
        alert_zone = (
            (T00 >= p.stress_threshold_medium) & 
            (T00 < p.stress_threshold_high) &
            (Psi >= p.coherence_threshold_low) & 
            (Psi < p.coherence_threshold_medium)
        )
        singularity = (T00 >= p.stress_threshold_high) | (Psi < p.coherence_threshold_low)
        
        # Compute statistics
        total_nodes = len(T00)
        
        return {
            'masks': {
                'valley_of_peace': valley_of_peace,
                'work_plateau': work_plateau,
                'alert_zone': alert_zone,
                'singularity': singularity
            },
            'counts': {
                'valley_of_peace': np.sum(valley_of_peace),
                'work_plateau': np.sum(work_plateau),
                'alert_zone': np.sum(alert_zone),
                'singularity': np.sum(singularity)
            },
            'percentages': {
                'valley_of_peace': 100 * np.sum(valley_of_peace) / total_nodes,
                'work_plateau': 100 * np.sum(work_plateau) / total_nodes,
                'alert_zone': 100 * np.sum(alert_zone) / total_nodes,
                'singularity': 100 * np.sum(singularity) / total_nodes
            },
            'stability': 100 * np.sum(~singularity) / total_nodes
        }
    
    def identify_critical_zones(
        self,
        T00: np.ndarray,
        Psi: np.ndarray,
        laplacian_Phi: np.ndarray,
        adjacency_matrix: np.ndarray
    ) -> Dict[str, Any]:
        """
        Identify critical zones requiring intervention.
        
        Critical zones are characterized by:
        - High stress (T₀₀ > threshold)
        - Low coherence (Ψ < threshold)
        - High curvature (|∇²Φ| → ∞)
        - Network centrality (high degree)
        
        Parameters:
        -----------
        T00 : np.ndarray
            Energy density (stress)
        Psi : np.ndarray
            Coherence
        laplacian_Phi : np.ndarray
            Laplacian of emotional field (curvature)
        adjacency_matrix : np.ndarray
            Network adjacency
            
        Returns:
        --------
        dict
            Critical zone analysis
        """
        p = self.params
        
        # Identify critical nodes
        high_stress = T00 > p.stress_threshold_high
        low_coherence = Psi < p.coherence_threshold_low
        high_curvature = np.abs(laplacian_Phi) > 2.0
        
        # Network degree (centrality)
        degree = np.sum(adjacency_matrix > 0, axis=1)
        high_centrality = degree > np.percentile(degree, 75)
        
        # Critical score (combines all factors)
        critical_score = (
            high_stress.astype(float) * 0.3 +
            low_coherence.astype(float) * 0.3 +
            high_curvature.astype(float) * 0.2 +
            high_centrality.astype(float) * 0.2
        )
        
        # Identify top critical nodes
        num_critical = max(1, int(0.1 * len(T00)))  # Top 10%
        critical_threshold = np.percentile(critical_score, 90)
        critical_nodes = critical_score > critical_threshold
        
        return {
            'critical_nodes': np.where(critical_nodes)[0],
            'critical_score': critical_score,
            'num_critical': np.sum(critical_nodes),
            'high_stress_nodes': np.where(high_stress)[0],
            'low_coherence_nodes': np.where(low_coherence)[0],
            'high_curvature_nodes': np.where(high_curvature)[0],
            'priority_ranking': np.argsort(critical_score)[::-1][:num_critical]
        }
    
    def analyze_network_structure(
        self,
        adjacency_matrix: np.ndarray,
        T00: np.ndarray,
        Psi: np.ndarray,
        laplacian_Phi: np.ndarray,
        Psi_complex: Optional[np.ndarray] = None
    ) -> Dict[str, Any]:
        """
        Comprehensive network topology analysis.
        
        Parameters:
        -----------
        adjacency_matrix : np.ndarray
            Network adjacency matrix
        T00 : np.ndarray
            Energy density (stress)
        Psi : np.ndarray
            Coherence magnitude
        laplacian_Phi : np.ndarray
            Laplacian of emotional field
        Psi_complex : np.ndarray, optional
            Complex coherence field (for winding number)
            
        Returns:
        --------
        dict
            Comprehensive topology analysis
        """
        # Betti numbers
        betti = self.compute_betti_numbers(adjacency_matrix)
        
        # Stress region classification
        regions = self.classify_stress_regions(T00, Psi)
        
        # Critical zones
        critical = self.identify_critical_zones(T00, Psi, laplacian_Phi, adjacency_matrix)
        
        # Winding number (if complex coherence provided)
        winding = None
        if Psi_complex is not None:
            winding = self.compute_winding_number(Psi_complex, adjacency_matrix)
        
        # Persistent homology (simplified)
        # Use edge weights as stress values
        edge_stress = adjacency_matrix.copy()
        edge_stress[edge_stress == 0] = np.nan
        valid_stress = edge_stress[~np.isnan(edge_stress)]
        
        if len(valid_stress) > 0:
            persistence = self.persistent_homology_1d(
                adjacency_matrix,
                valid_stress,
                num_thresholds=10
            )
        else:
            persistence = None
        
        return {
            'betti_numbers': betti,
            'stress_regions': regions,
            'critical_zones': critical,
            'winding_number': winding,
            'persistent_homology': persistence,
            'summary': {
                'num_components': betti['beta_0'],
                'num_cycles': betti['beta_1'],
                'stability': regions['stability'],
                'num_critical': critical['num_critical'],
                'max_stress': np.max(T00),
                'min_coherence': np.min(Psi),
                'mean_coherence': np.mean(Psi)
            }
        }


# Example usage and validation
if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ Emotional Network Topology Validation")
    print("=" * 80)
    print()
    
    # Create sample network
    num_nodes = 100
    
    # Erdős–Rényi random graph
    adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
    adjacency = (adjacency + adjacency.T) / 2  # Symmetrize
    np.fill_diagonal(adjacency, 0)
    
    # Add weights (stress coupling)
    adjacency[adjacency > 0] = 0.1 + 0.9 * np.random.rand(np.sum(adjacency > 0))
    
    # Generate stress and coherence fields
    T00 = 0.2 + 0.4 * np.random.rand(num_nodes)
    Psi = 0.75 + 0.25 * np.random.rand(num_nodes)
    
    # Compute Laplacian
    degree = np.sum(adjacency, axis=1)
    laplacian = np.diag(degree) - adjacency
    Phi = np.random.randn(num_nodes) * 0.5
    laplacian_Phi = -laplacian @ Phi
    
    # Complex coherence (for winding number)
    phase = 2 * np.pi * np.random.rand(num_nodes)
    Psi_complex = Psi * np.exp(1j * phase)
    
    # Initialize topology analyzer
    topology = EmotionalNetworkTopology()
    
    print("Network Properties:")
    print(f"  Nodes: {num_nodes}")
    print(f"  Edges: {np.sum(adjacency > 0) // 2}")
    print(f"  Mean Stress T₀₀: {np.mean(T00):.3f}")
    print(f"  Mean Coherence Ψ: {np.mean(Psi):.3f}")
    print()
    
    # Comprehensive analysis
    print("Performing topology analysis...")
    analysis = topology.analyze_network_structure(
        adjacency,
        T00,
        Psi,
        laplacian_Phi,
        Psi_complex
    )
    
    # Print results
    print()
    print("Topological Invariants:")
    print("-" * 80)
    print(f"  β₀ (connected components): {analysis['betti_numbers']['beta_0']}")
    print(f"  β₁ (independent cycles): {analysis['betti_numbers']['beta_1']}")
    
    if analysis['betti_numbers']['beta_0'] > 1:
        sizes = analysis['betti_numbers']['component_sizes']
        print(f"  Component sizes: {sizes}")
    print()
    
    print("Stress Region Classification:")
    print("-" * 80)
    regions = analysis['stress_regions']
    for region, percentage in regions['percentages'].items():
        count = regions['counts'][region]
        print(f"  {region.replace('_', ' ').title()}: {count} nodes ({percentage:.1f}%)")
    print(f"\n  Network Stability: {regions['stability']:.1f}%")
    print()
    
    print("Critical Zones:")
    print("-" * 80)
    critical = analysis['critical_zones']
    print(f"  Critical nodes: {critical['num_critical']}")
    print(f"  High stress nodes: {len(critical['high_stress_nodes'])}")
    print(f"  Low coherence nodes: {len(critical['low_coherence_nodes'])}")
    print(f"  High curvature nodes: {len(critical['high_curvature_nodes'])}")
    
    if critical['num_critical'] > 0:
        print(f"  Top 5 priority nodes: {critical['priority_ranking'][:5].tolist()}")
    print()
    
    if analysis['winding_number'] is not None:
        print("Winding Number Analysis:")
        print("-" * 80)
        winding = analysis['winding_number']
        print(f"  Winding number W: {winding['winding_number']:.3f}")
        print(f"  Phase circulation: {winding['phase_circulation']:.3f} rad")
        print(f"  Mean phase: {winding['mean_phase']:.3f} rad")
        print(f"  Phase std: {winding['phase_std']:.3f} rad")
        print()
    
    print("Summary:")
    print("-" * 80)
    summary = analysis['summary']
    for key, value in summary.items():
        if isinstance(value, float):
            print(f"  {key.replace('_', ' ').title()}: {value:.3f}")
        else:
            print(f"  {key.replace('_', ' ').title()}: {value}")
    
    print()
    print("=" * 80)
    print("Network Topology Analysis Complete")
    print("=" * 80)

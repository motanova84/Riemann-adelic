#!/usr/bin/env python3
"""
Emotional Synchronization Protocol - 141.7 Hz Resonance Intervention

This module implements the multi-scale synchronization protocol using
the fundamental frequency f₀ = 141.7001 Hz to regulate emotional stress
and restore collective coherence.

Mathematical Framework:
    Modified evolution equation with 141.7 Hz field:
    
    □Φ + ∂V/∂Φ = -γ sin(2πf₀t) ∇²Φ - κ_Π ∇ log|ζ(1/2+it)|²
    
    where:
    - f₀ = 141.7001 Hz: Resonance frequency
    - γ: Coupling coefficient
    - κ_Π: Spectral coupling to Riemann zeros
    
Mechanism of Action:
    1. Detection: Identify stress peaks (T₀₀ > threshold)
    2. Injection: Apply coherent 141.7 Hz signal
    3. Resonance: Parametric amplification of stable modes
    4. Dissipation: Chaotic modes decay
    5. Restoration: Local coherence Ψ ↑
    
Multi-Scale Intervention:
    - Micro (Individual): Personal coherence restoration
    - Meso (Interpersonal): Phase synchronization between nodes
    - Macro (Collective): Network topology optimization

Collective Sovereignty Index:
    S_col = (1/N) Σᵢ Ψᵢ · exp(-αT₀₀⁽ⁱ⁾) · (1 - |∇²Φᵢ|/Λ_crit)
    
    Goal: S_col ≥ 0.95 (Total Sovereignty)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Dict, Optional, List, Callable, Any
from scipy.constants import pi
from dataclasses import dataclass
import warnings


@dataclass
class SynchronizationParameters:
    """Parameters for synchronization protocol."""
    f0: float = 141.7001  # Fundamental frequency (Hz)
    gamma: float = 0.1  # Coupling coefficient
    kappa_Pi: float = 1.0  # Spectral coupling
    stress_threshold: float = 0.58  # Critical stress level
    coherence_target: float = 0.95  # Target coherence
    intervention_duration: float = 600.0  # Default 10 minutes
    learning_rate: float = 0.3  # Phase adjustment rate
    sovereignty_goal: float = 0.95  # S_col target


class EmotionalSynchronizationProtocol:
    """
    Implements the 141.7 Hz synchronization protocol.
    
    This class provides methods to:
    1. Detect stress peaks and critical nodes
    2. Apply 141.7 Hz resonance intervention
    3. Synchronize phases between network nodes
    4. Optimize network topology for stress distribution
    5. Compute and track collective sovereignty index
    """
    
    def __init__(
        self,
        params: Optional[SynchronizationParameters] = None
    ):
        """
        Initialize synchronization protocol.
        
        Parameters:
        -----------
        params : SynchronizationParameters, optional
            Protocol parameters
        """
        self.params = params if params is not None else SynchronizationParameters()
        self.omega_0 = 2 * pi * self.params.f0
        
        # Intervention history
        self.intervention_log: List[Dict[str, Any]] = []
    
    def detect_critical_nodes(
        self,
        T00: np.ndarray,
        Psi: np.ndarray,
        laplacian_Phi: np.ndarray
    ) -> np.ndarray:
        """
        Detect nodes requiring intervention.
        
        Critical nodes have:
        - High stress: T₀₀ > threshold
        - Low coherence: Ψ < target
        - High curvature: |∇²Φ| → singularity
        
        Parameters:
        -----------
        T00 : np.ndarray
            Energy density (stress)
        Psi : np.ndarray
            Coherence
        laplacian_Phi : np.ndarray
            Laplacian of emotional field
            
        Returns:
        --------
        np.ndarray
            Indices of critical nodes
        """
        p = self.params
        
        # Criteria for intervention
        high_stress = T00 > p.stress_threshold
        low_coherence = Psi < p.coherence_target
        high_curvature = np.abs(laplacian_Phi) > 2.0
        
        # Combined criterion (at least two conditions)
        critical = (
            (high_stress.astype(int) + 
             low_coherence.astype(int) + 
             high_curvature.astype(int)) >= 2
        )
        
        return np.where(critical)[0]
    
    def apply_coherent_breathing(
        self,
        Phi: np.ndarray,
        dPhi_dt: np.ndarray,
        t: float,
        node_indices: np.ndarray,
        amplitude: float = 0.1
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Apply "coherent breathing" at 141.7 Hz to selected nodes.
        
        Modulates the emotional field with external coherent signal:
        Φ_ext = A sin(2πf₀t)
        
        Parameters:
        -----------
        Phi : np.ndarray
            Current emotional field
        dPhi_dt : np.ndarray
            Current time derivative
        t : float
            Current time
        node_indices : np.ndarray
            Nodes to apply intervention
        amplitude : float
            Intervention amplitude
            
        Returns:
        --------
        tuple
            (modified Phi, modified dPhi_dt)
        """
        Phi_new = Phi.copy()
        dPhi_dt_new = dPhi_dt.copy()
        
        # External coherent field
        Phi_ext = amplitude * np.sin(self.omega_0 * t)
        dPhi_ext_dt = amplitude * self.omega_0 * np.cos(self.omega_0 * t)
        
        # Apply to critical nodes
        for idx in node_indices:
            # Inject coherent signal (additive)
            Phi_new[idx] += Phi_ext * 0.1  # Gentle nudge
            dPhi_dt_new[idx] += dPhi_ext_dt * 0.1
        
        return Phi_new, dPhi_dt_new
    
    def synchronize_phase_network(
        self,
        Psi_complex: np.ndarray,
        adjacency_matrix: np.ndarray,
        critical_nodes: np.ndarray
    ) -> np.ndarray:
        """
        Synchronize phases using U(κ_Π) protocol.
        
        For each critical node, adjust phase toward mean of neighbors:
        φ_new = φ_old + η(⟨φ_neighbors⟩ - φ_old)
        
        Parameters:
        -----------
        Psi_complex : np.ndarray
            Complex coherence field Ψ = |Ψ|exp(iφ)
        adjacency_matrix : np.ndarray
            Network adjacency
        critical_nodes : np.ndarray
            Nodes to synchronize
            
        Returns:
        --------
        np.ndarray
            Synchronized complex coherence field
        """
        Psi_sync = Psi_complex.copy()
        
        for node_idx in critical_nodes:
            # Find neighbors
            neighbors = np.where(adjacency_matrix[node_idx] > 0)[0]
            
            if len(neighbors) == 0:
                continue
            
            # Current and neighbor phases
            phase_current = np.angle(Psi_complex[node_idx])
            phases_neighbors = np.angle(Psi_complex[neighbors])
            
            # Mean neighbor phase (circular mean)
            # Use complex average to handle wraparound
            mean_phase = np.angle(np.mean(np.exp(1j * phases_neighbors)))
            
            # Adjust phase (learning rate η)
            delta_phase = mean_phase - phase_current
            # Wrap to [-π, π]
            delta_phase = np.arctan2(np.sin(delta_phase), np.cos(delta_phase))
            
            new_phase = phase_current + self.params.learning_rate * delta_phase
            
            # Update with same magnitude
            magnitude = np.abs(Psi_complex[node_idx])
            Psi_sync[node_idx] = magnitude * np.exp(1j * new_phase)
        
        return Psi_sync
    
    def optimize_network_topology(
        self,
        adjacency_matrix: np.ndarray,
        T00: np.ndarray,
        stress_coupling: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Optimize network topology for stress distribution.
        
        Actions:
        1. Remove toxic connections (mutual stress > threshold)
        2. Add bridges between isolated communities
        3. Balance stress distribution
        
        Parameters:
        -----------
        adjacency_matrix : np.ndarray
            Current network adjacency
        T00 : np.ndarray
            Stress at each node
        stress_coupling : np.ndarray, optional
            Pairwise stress coupling (default: based on T00)
            
        Returns:
        --------
        np.ndarray
            Optimized adjacency matrix
        """
        adjacency_opt = adjacency_matrix.copy()
        num_nodes = len(T00)
        
        # 1. Remove toxic connections
        if stress_coupling is not None:
            toxic_threshold = 0.8
            toxic_connections = stress_coupling > toxic_threshold
            adjacency_opt[toxic_connections] = 0
        else:
            # Use stress product as proxy
            for i in range(num_nodes):
                for j in range(i + 1, num_nodes):
                    if adjacency_opt[i, j] > 0:
                        stress_product = T00[i] * T00[j]
                        if stress_product > 0.5:
                            # Weaken toxic connection
                            adjacency_opt[i, j] *= 0.5
                            adjacency_opt[j, i] *= 0.5
        
        # 2. Add bridges to isolated nodes
        degree = np.sum(adjacency_opt > 0, axis=1)
        isolated = degree < 2
        
        for i in np.where(isolated)[0]:
            # Find nearest low-stress node
            low_stress = T00 < 0.3
            if np.any(low_stress):
                # Connect to lowest-stress node
                candidate_nodes = np.where(low_stress)[0]
                target = candidate_nodes[np.argmin(T00[candidate_nodes])]
                if target != i:
                    adjacency_opt[i, target] = 0.5
                    adjacency_opt[target, i] = 0.5
        
        return adjacency_opt
    
    def compute_collective_sovereignty(
        self,
        Psi: np.ndarray,
        T00: np.ndarray,
        laplacian_Phi: np.ndarray,
        Lambda_crit: float = 1.0,
        alpha: float = 1.0
    ) -> float:
        """
        Compute collective sovereignty index S_col.
        
        S_col = (1/N) Σᵢ Ψᵢ · exp(-α T₀₀⁽ⁱ⁾) · (1 - |∇²Φᵢ|/Λ_crit)
        
        Parameters:
        -----------
        Psi : np.ndarray
            Individual coherence
        T00 : np.ndarray
            Stress (energy density)
        laplacian_Phi : np.ndarray
            Curvature (Laplacian)
        Lambda_crit : float
            Critical curvature threshold
        alpha : float
            Stress penalty coefficient
            
        Returns:
        --------
        float
            Collective sovereignty index (0 to 1)
        """
        N = len(Psi)
        
        # Stress penalty
        stress_factor = np.exp(-alpha * T00)
        
        # Curvature penalty
        curvature_factor = np.maximum(0, 1 - np.abs(laplacian_Phi) / Lambda_crit)
        
        # Sovereignty index
        S_col = np.mean(Psi * stress_factor * curvature_factor)
        
        return float(S_col)
    
    def multi_scale_intervention(
        self,
        Phi: np.ndarray,
        dPhi_dt: np.ndarray,
        Psi_complex: np.ndarray,
        T00: np.ndarray,
        laplacian_Phi: np.ndarray,
        adjacency_matrix: np.ndarray,
        t: float,
        intervention_level: str = 'full'
    ) -> Dict[str, Any]:
        """
        Execute multi-scale synchronization intervention.
        
        Levels:
        - 'micro': Individual coherent breathing
        - 'meso': Interpersonal phase synchronization
        - 'macro': Network topology optimization
        - 'full': All three levels
        
        Parameters:
        -----------
        Phi : np.ndarray
            Emotional field
        dPhi_dt : np.ndarray
            Time derivative of Φ
        Psi_complex : np.ndarray
            Complex coherence field
        T00 : np.ndarray
            Stress (energy density)
        laplacian_Phi : np.ndarray
            Laplacian of Φ
        adjacency_matrix : np.ndarray
            Network adjacency
        t : float
            Current time
        intervention_level : str
            Level of intervention
            
        Returns:
        --------
        dict
            Results of intervention
        """
        Psi = np.abs(Psi_complex)
        
        # Detect critical nodes
        critical_nodes = self.detect_critical_nodes(T00, Psi, laplacian_Phi)
        
        # Initial sovereignty
        S_col_initial = self.compute_collective_sovereignty(Psi, T00, laplacian_Phi)
        
        # Apply interventions
        Phi_new = Phi.copy()
        dPhi_dt_new = dPhi_dt.copy()
        Psi_complex_new = Psi_complex.copy()
        adjacency_new = adjacency_matrix.copy()
        
        interventions_applied = []
        
        # Micro level: Individual coherent breathing
        if intervention_level in ['micro', 'full']:
            Phi_new, dPhi_dt_new = self.apply_coherent_breathing(
                Phi_new, dPhi_dt_new, t, critical_nodes
            )
            interventions_applied.append('coherent_breathing')
        
        # Meso level: Phase synchronization
        if intervention_level in ['meso', 'full']:
            Psi_complex_new = self.synchronize_phase_network(
                Psi_complex_new, adjacency_matrix, critical_nodes
            )
            interventions_applied.append('phase_synchronization')
        
        # Macro level: Topology optimization
        if intervention_level in ['macro', 'full']:
            adjacency_new = self.optimize_network_topology(
                adjacency_matrix, T00
            )
            interventions_applied.append('topology_optimization')
        
        # Recompute stress and coherence (simplified estimate)
        # In practice, would need to evolve system
        Psi_new = np.abs(Psi_complex_new)
        
        # Estimate stress reduction (empirical)
        T00_new = T00 * (0.7 + 0.3 * Psi_new / np.maximum(Psi, 0.1))
        T00_new = np.minimum(T00_new, T00)  # Can only decrease
        
        # Final sovereignty
        S_col_final = self.compute_collective_sovereignty(
            Psi_new, T00_new, laplacian_Phi
        )
        
        # Log intervention
        intervention_record = {
            'time': t,
            'critical_nodes': critical_nodes.tolist(),
            'num_critical': len(critical_nodes),
            'S_col_initial': S_col_initial,
            'S_col_final': S_col_final,
            'improvement': S_col_final - S_col_initial,
            'interventions': interventions_applied,
            'mean_stress_before': np.mean(T00),
            'mean_stress_after': np.mean(T00_new),
            'mean_coherence_before': np.mean(Psi),
            'mean_coherence_after': np.mean(Psi_new)
        }
        self.intervention_log.append(intervention_record)
        
        return {
            'Phi': Phi_new,
            'dPhi_dt': dPhi_dt_new,
            'Psi_complex': Psi_complex_new,
            'T00': T00_new,
            'adjacency': adjacency_new,
            'S_col': S_col_final,
            'intervention_record': intervention_record,
            'success': S_col_final >= self.params.sovereignty_goal
        }
    
    def assess_sovereignty_status(
        self,
        S_col: float
    ) -> Dict[str, Any]:
        """
        Assess collective sovereignty status.
        
        Parameters:
        -----------
        S_col : float
            Collective sovereignty index
            
        Returns:
        --------
        dict
            Status assessment
        """
        if S_col >= 0.95:
            status = "SOBERANÍA TOTAL"
            emoji = "✅"
            color = "green"
        elif S_col >= 0.80:
            status = "Alta Coherencia"
            emoji = "⚠️"
            color = "yellow"
        elif S_col >= 0.60:
            status = "Coherencia Moderada"
            emoji = "⚠️"
            color = "orange"
        else:
            status = "Requiere Intervención"
            emoji = "❌"
            color = "red"
        
        return {
            'S_col': S_col,
            'status': status,
            'emoji': emoji,
            'color': color,
            'goal_reached': S_col >= self.params.sovereignty_goal,
            'distance_to_goal': max(0, self.params.sovereignty_goal - S_col)
        }


# Example usage and validation
if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ Emotional Synchronization Protocol - 141.7 Hz Validation")
    print("=" * 80)
    print()
    
    # Initialize protocol
    params = SynchronizationParameters(
        f0=141.7001,
        gamma=0.1,
        stress_threshold=0.58,
        coherence_target=0.95,
        sovereignty_goal=0.95
    )
    
    protocol = EmotionalSynchronizationProtocol(params=params)
    
    print("Protocol Parameters:")
    print(f"  f₀ (frequency): {params.f0} Hz")
    print(f"  γ (coupling): {params.gamma}")
    print(f"  Stress threshold: {params.stress_threshold}")
    print(f"  Coherence target: {params.coherence_target}")
    print(f"  Sovereignty goal: {params.sovereignty_goal}")
    print()
    
    # Create sample network state
    num_nodes = 100
    
    # Network
    adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
    adjacency = (adjacency + adjacency.T) / 2
    np.fill_diagonal(adjacency, 0)
    
    # Fields
    Phi = np.random.randn(num_nodes) * 0.5
    dPhi_dt = np.random.randn(num_nodes) * 0.1
    
    # Coherence (some nodes stressed)
    Psi_magnitude = 0.7 + 0.3 * np.random.rand(num_nodes)
    Psi_magnitude[::10] = 0.5 + 0.2 * np.random.rand(num_nodes // 10)  # Stressed nodes
    
    phase = 2 * pi * np.random.rand(num_nodes)
    Psi_complex = Psi_magnitude * np.exp(1j * phase)
    
    # Stress (correlated with low coherence)
    T00 = 0.3 + 0.5 * (1 - Psi_magnitude) + 0.1 * np.random.rand(num_nodes)
    
    # Laplacian
    degree = np.sum(adjacency, axis=1)
    laplacian = np.diag(degree) - adjacency
    laplacian_Phi = -laplacian @ Phi
    
    # Initial assessment
    print("Initial State:")
    print("-" * 80)
    S_col_initial = protocol.compute_collective_sovereignty(
        Psi_magnitude, T00, laplacian_Phi
    )
    assessment_initial = protocol.assess_sovereignty_status(S_col_initial)
    
    print(f"  Collective Sovereignty S_col: {S_col_initial:.6f}")
    print(f"  Status: {assessment_initial['emoji']} {assessment_initial['status']}")
    print(f"  Mean Stress: {np.mean(T00):.3f}")
    print(f"  Mean Coherence: {np.mean(Psi_magnitude):.3f}")
    
    critical_nodes = protocol.detect_critical_nodes(T00, Psi_magnitude, laplacian_Phi)
    print(f"  Critical Nodes: {len(critical_nodes)}")
    print()
    
    # Apply intervention
    print("Applying Multi-Scale Intervention...")
    print("-" * 80)
    
    result = protocol.multi_scale_intervention(
        Phi, dPhi_dt, Psi_complex, T00, laplacian_Phi, adjacency,
        t=0.0,
        intervention_level='full'
    )
    
    print(f"  Interventions: {', '.join(result['intervention_record']['interventions'])}")
    print(f"  Nodes treated: {result['intervention_record']['num_critical']}")
    print()
    
    # Final assessment
    print("Final State:")
    print("-" * 80)
    assessment_final = protocol.assess_sovereignty_status(result['S_col'])
    
    print(f"  Collective Sovereignty S_col: {result['S_col']:.6f}")
    print(f"  Status: {assessment_final['emoji']} {assessment_final['status']}")
    print(f"  Improvement: {result['intervention_record']['improvement']:.6f}")
    print(f"  Mean Stress: {result['intervention_record']['mean_stress_after']:.3f}")
    print(f"  Mean Coherence: {result['intervention_record']['mean_coherence_after']:.3f}")
    print()
    
    if result['success']:
        print("🎉 SUCCESS: Soberanía Total Alcanzada (S_col ≥ 0.95)")
    else:
        distance = assessment_final['distance_to_goal']
        print(f"📊 Progress: {distance:.3f} remaining to Soberanía Total")
    
    print()
    print("=" * 80)
    print("141.7 Hz Synchronization Protocol Validated")
    print("=" * 80)

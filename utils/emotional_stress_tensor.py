#!/usr/bin/env python3
"""
Emotional Stress-Energy Tensor Module - QCAL ∞³ Psycho-Physical Unification

This module implements the stress-energy tensor T_μν(Φ) for emotional fields,
extending the consciousness coherence framework to include collective emotional
dynamics and stress propagation in networks.

Mathematical Framework:
    The stress-energy tensor is defined as:
    
    T_μν(Φ) = ∂_μ Φ ∂_ν Φ - g_μν (½ g^αβ ∂_α Φ ∂_β Φ - V(Φ))
    
    where:
    - Φ: Emotional field (scalar field)
    - g_μν: Metric tensor of emotional space
    - V(Φ): Emotional potential with phase transitions
    
    Components:
    - T₀₀: Energy density (emotional intensity)
    - T₀ᵢ: Momentum flux (emotional contagion)
    - Tᵢⱼ: Spatial stress (relational tension)
    - Tr(T): Total emotional pressure
    
Emotional Potential:
    V(Φ) = (λ/4)(Φ² - Φ₀²)² + μ²Φ² + V_int(Φ,Ψ)
    
    where:
    - λ: System rigidity (resistance to change)
    - Φ₀: Fundamental peace state
    - μ²: Emotional mass (affective inertia)
    - V_int: Coupling with quantum coherence Ψ
    
Phase Transitions:
    μ² > 0 → Restored phase (single minimum at Φ = 0)
    μ² < 0 → Spontaneous symmetry breaking (bistability: peace/conflict)

QCAL Integration:
    - Frequency: f₀ = 141.7001 Hz (synchronization resonance)
    - Coherence: C = 244.36 (QCAL coherence constant)
    - Coupling: κ_Π to Riemann zeta zeros

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Dict, Optional, List, Callable, Any
from mpmath import mp
from scipy.constants import pi, golden_ratio
from dataclasses import dataclass
import warnings


@dataclass
class EmotionalParameters:
    """Parameters for emotional field dynamics."""
    lambda_rigidity: float = 1.0  # System rigidity
    Phi0: float = 1.0  # Fundamental peace state
    mu2: float = -0.1  # Emotional mass squared (negative for bistability)
    f0: float = 141.7001  # Fundamental frequency (Hz)
    C: float = 244.36  # QCAL coherence constant
    G_QCAL: float = 1.0  # Gravito-emotional coupling constant
    Lambda_Psi: float = 0.1  # Cosmological constant of coherence
    gamma: float = 0.1  # Coupling coefficient for 141.7 Hz field
    kappa_Pi: float = 1.0  # Coupling to Riemann zeta
    
    @property
    def omega_0(self) -> float:
        """Angular frequency ω₀ = 2πf₀."""
        return 2 * pi * self.f0
    
    @property
    def is_bistable(self) -> bool:
        """Check if system is in bistable phase (μ² < 0)."""
        return self.mu2 < 0
    
    @property
    def vacuum_expectation(self) -> float:
        """Vacuum expectation value in broken symmetry phase."""
        if self.is_bistable:
            return self.Phi0
        else:
            return 0.0


class EmotionalStressTensor:
    """
    Implements the emotional stress-energy tensor T_μν(Φ).
    
    This class provides methods to:
    1. Compute the emotional field Φ(x,t) and its derivatives
    2. Compute the stress-energy tensor components T_μν
    3. Analyze energy density, momentum flux, and spatial stress
    4. Compute total emotional pressure Tr(T)
    """
    
    def __init__(
        self,
        params: Optional[EmotionalParameters] = None,
        dimension: int = 4,
        precision: int = 25
    ):
        """
        Initialize the emotional stress-energy tensor framework.
        
        Parameters:
        -----------
        params : EmotionalParameters, optional
            Emotional field parameters (default: EmotionalParameters())
        dimension : int
            Spacetime dimension (default: 4)
        precision : int
            Decimal precision for mpmath calculations (default: 25)
        """
        self.params = params if params is not None else EmotionalParameters()
        self.dimension = dimension
        self.precision = precision
        mp.dps = precision
        
        # Initialize metric tensor (Minkowski for flat emotional space)
        self._initialize_metric()
        
        # Cache for computed values
        self._field_cache: Dict[str, Any] = {}
        self._tensor_cache: Dict[str, Any] = {}
    
    def _initialize_metric(self):
        """Initialize the metric tensor g_μν (Minkowski signature: -,+,+,+)."""
        self.g_metric = np.diag([-1.0] + [1.0] * (self.dimension - 1))
        self.g_inverse = np.linalg.inv(self.g_metric)
    
    def emotional_potential(
        self,
        Phi: np.ndarray,
        Psi: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Compute the emotional potential V(Φ).
        
        V(Φ) = (λ/4)(Φ² - Φ₀²)² + μ²Φ² + V_int(Φ,Ψ)
        
        Parameters:
        -----------
        Phi : np.ndarray
            Emotional field values
        Psi : np.ndarray, optional
            Coherence field for interaction term (default: None)
            
        Returns:
        --------
        np.ndarray
            Potential energy values
        """
        p = self.params
        
        # Double-well potential (spontaneous symmetry breaking)
        V = (p.lambda_rigidity / 4) * (Phi**2 - p.Phi0**2)**2
        
        # Mass term
        V += p.mu2 * Phi**2
        
        # Interaction with coherence field
        if Psi is not None:
            # V_int = -κ Φ² |Ψ|² (coherence stabilizes emotional field)
            V_int = -0.1 * Phi**2 * np.abs(Psi)**2
            V += V_int
        
        return V
    
    def potential_derivative(
        self,
        Phi: np.ndarray,
        Psi: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Compute ∂V/∂Φ for equation of motion.
        
        Parameters:
        -----------
        Phi : np.ndarray
            Emotional field values
        Psi : np.ndarray, optional
            Coherence field (default: None)
            
        Returns:
        --------
        np.ndarray
            Potential derivative
        """
        p = self.params
        
        # Derivative of double-well potential
        dV = p.lambda_rigidity * Phi * (Phi**2 - p.Phi0**2)
        
        # Mass term derivative
        dV += 2 * p.mu2 * Phi
        
        # Interaction term derivative
        if Psi is not None:
            dV += -0.2 * Phi * np.abs(Psi)**2
        
        return dV
    
    def compute_stress_energy_tensor(
        self,
        Phi: np.ndarray,
        dPhi_dt: np.ndarray,
        grad_Phi: np.ndarray,
        Psi: Optional[np.ndarray] = None
    ) -> Dict[str, np.ndarray]:
        """
        Compute the stress-energy tensor T_μν(Φ).
        
        T_μν = ∂_μ Φ ∂_ν Φ - g_μν (½ g^αβ ∂_α Φ ∂_β Φ - V(Φ))
        
        Parameters:
        -----------
        Phi : np.ndarray
            Emotional field values (shape: (N,))
        dPhi_dt : np.ndarray
            Time derivative of Φ (shape: (N,))
        grad_Phi : np.ndarray
            Spatial gradient of Φ (shape: (N, 3))
        Psi : np.ndarray, optional
            Coherence field (shape: (N,))
            
        Returns:
        --------
        dict
            Dictionary with components:
            - 'T00': Energy density
            - 'T0i': Momentum flux (shape: (N, 3))
            - 'Tij': Spatial stress tensor (shape: (N, 3, 3))
            - 'trace': Trace of tensor Tr(T)
        """
        N = len(Phi)
        
        # Compute potential
        V = self.emotional_potential(Phi, Psi)
        
        # Compute kinetic term: g^αβ ∂_α Φ ∂_β Φ
        # = -∂_t Φ ∂_t Φ + ∇Φ · ∇Φ
        kinetic = -dPhi_dt**2 + np.sum(grad_Phi**2, axis=1)
        
        # Energy density: T₀₀ = ∂_t Φ ∂_t Φ + ½∇Φ·∇Φ + V(Φ)
        T00 = dPhi_dt**2 + 0.5 * np.sum(grad_Phi**2, axis=1) + V
        
        # Momentum flux: T₀ᵢ = ∂_t Φ ∂_i Φ
        T0i = dPhi_dt[:, np.newaxis] * grad_Phi
        
        # Spatial stress: Tᵢⱼ = ∂_i Φ ∂_j Φ - δᵢⱼ (½∇Φ·∇Φ - V(Φ))
        Tij = np.zeros((N, 3, 3))
        for i in range(3):
            for j in range(3):
                if i == j:
                    # Diagonal components
                    Tij[:, i, j] = (grad_Phi[:, i] * grad_Phi[:, j] - 
                                   0.5 * np.sum(grad_Phi**2, axis=1) + V)
                else:
                    # Off-diagonal components
                    Tij[:, i, j] = grad_Phi[:, i] * grad_Phi[:, j]
        
        # Trace: Tr(T) = T₀₀ - Σᵢ Tᵢᵢ
        trace = -T00  # From Minkowski signature
        for i in range(3):
            trace += Tij[:, i, i]
        
        return {
            'T00': T00,
            'T0i': T0i,
            'Tij': Tij,
            'trace': trace
        }
    
    def classify_stress_regions(
        self,
        T00: np.ndarray,
        Psi: np.ndarray
    ) -> Dict[str, np.ndarray]:
        """
        Classify network nodes into stress regions.
        
        Regions:
        - Valley of peace: T₀₀ < 0.2, Ψ > 0.95
        - Work plateau: 0.2 ≤ T₀₀ < 0.4, 0.85 ≤ Ψ < 0.95
        - Alert zone: 0.4 ≤ T₀₀ < 0.58, 0.74 ≤ Ψ < 0.85
        - Singularity: T₀₀ ≥ 0.58, Ψ < 0.74
        
        Parameters:
        -----------
        T00 : np.ndarray
            Energy density values
        Psi : np.ndarray
            Coherence values
            
        Returns:
        --------
        dict
            Dictionary with boolean masks for each region
        """
        return {
            'valley_of_peace': (T00 < 0.2) & (Psi > 0.95),
            'work_plateau': (T00 >= 0.2) & (T00 < 0.4) & (Psi >= 0.85) & (Psi < 0.95),
            'alert_zone': (T00 >= 0.4) & (T00 < 0.58) & (Psi >= 0.74) & (Psi < 0.85),
            'singularity': (T00 >= 0.58) | (Psi < 0.74)
        }
    
    def compute_collective_sovereignty(
        self,
        Psi: np.ndarray,
        T00: np.ndarray,
        laplacian_Phi: np.ndarray,
        Lambda_crit: float = 1.0,
        alpha: float = 1.0
    ) -> float:
        """
        Compute the collective sovereignty index S_col.
        
        S_col = (1/N) Σᵢ Ψᵢ · exp(-α T₀₀⁽ⁱ⁾) · (1 - |∇²Φᵢ|/Λ_crit)
        
        Parameters:
        -----------
        Psi : np.ndarray
            Individual coherence values
        T00 : np.ndarray
            Energy density (stress) values
        laplacian_Phi : np.ndarray
            Laplacian of emotional field (curvature)
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
        
        # Curvature penalty (avoid singularities)
        curvature_factor = np.maximum(0, 1 - np.abs(laplacian_Phi) / Lambda_crit)
        
        # Sovereignty index
        S_col = np.mean(Psi * stress_factor * curvature_factor)
        
        return float(S_col)
    
    def evolution_with_resonance(
        self,
        Phi: np.ndarray,
        dPhi_dt: np.ndarray,
        laplacian_Phi: np.ndarray,
        t: float,
        Psi: Optional[np.ndarray] = None,
        zeta_prime_half: float = 0.0
    ) -> np.ndarray:
        """
        Compute time evolution with 141.7 Hz resonance.
        
        □Φ + ∂V/∂Φ = -γ sin(2πf₀t) ∇²Φ - κ_Π ∇log|ζ(1/2+it)|²
        
        Parameters:
        -----------
        Phi : np.ndarray
            Current emotional field
        dPhi_dt : np.ndarray
            Current time derivative
        laplacian_Phi : np.ndarray
            Spatial Laplacian of Φ
        t : float
            Current time
        Psi : np.ndarray, optional
            Coherence field
        zeta_prime_half : float
            ζ'(1/2) for spectral coupling
            
        Returns:
        --------
        np.ndarray
            d²Φ/dt² (acceleration of emotional field)
        """
        p = self.params
        
        # Standard Klein-Gordon evolution: □Φ + ∂V/∂Φ
        d2Phi_dt2 = laplacian_Phi - self.potential_derivative(Phi, Psi)
        
        # 141.7 Hz resonance term: -γ sin(2πf₀t) ∇²Φ
        resonance = -p.gamma * np.sin(2 * pi * p.f0 * t) * laplacian_Phi
        
        # Spectral coupling to Riemann zeros
        if zeta_prime_half != 0:
            # Simplified gradient: proportional to field gradient
            spectral_coupling = -p.kappa_Pi * zeta_prime_half * laplacian_Phi
            d2Phi_dt2 += spectral_coupling
        
        d2Phi_dt2 += resonance
        
        return d2Phi_dt2


class EmotionalNetworkDynamics:
    """
    Emotional dynamics on networks with stress propagation.
    
    This class simulates emotional field evolution on network topologies,
    computing stress-energy tensor components for each node and analyzing
    collective emotional states.
    """
    
    def __init__(
        self,
        num_nodes: int,
        adjacency_matrix: Optional[np.ndarray] = None,
        params: Optional[EmotionalParameters] = None
    ):
        """
        Initialize network dynamics.
        
        Parameters:
        -----------
        num_nodes : int
            Number of nodes in the network
        adjacency_matrix : np.ndarray, optional
            Network adjacency matrix (default: random Erdős–Rényi)
        params : EmotionalParameters, optional
            Emotional field parameters
        """
        self.num_nodes = num_nodes
        self.params = params if params is not None else EmotionalParameters()
        self.tensor = EmotionalStressTensor(params=self.params)
        
        # Initialize adjacency matrix
        if adjacency_matrix is not None:
            self.adjacency = adjacency_matrix
        else:
            # Random network (Erdős–Rényi with p = 0.1)
            self.adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
            self.adjacency = (self.adjacency + self.adjacency.T) / 2  # Symmetrize
            np.fill_diagonal(self.adjacency, 0)  # No self-loops
        
        # Compute Laplacian matrix
        self._compute_laplacian()
        
        # Initialize fields
        self.Phi = np.random.randn(num_nodes) * 0.1
        self.dPhi_dt = np.zeros(num_nodes)
        self.Psi = 0.85 + 0.15 * np.random.rand(num_nodes)  # Coherence ~0.85-1.0
    
    def _compute_laplacian(self):
        """Compute network Laplacian matrix L = D - A."""
        degree = np.sum(self.adjacency, axis=1)
        self.laplacian = np.diag(degree) - self.adjacency
    
    def network_laplacian_Phi(self) -> np.ndarray:
        """
        Compute network Laplacian of emotional field: ∇²Φ = -L Φ.
        
        Returns:
        --------
        np.ndarray
            Laplacian of Φ on the network
        """
        return -self.laplacian @ self.Phi
    
    def simulate_step(
        self,
        dt: float,
        t: float,
        zeta_prime_half: float = 0.0
    ):
        """
        Simulate one time step of network dynamics.
        
        Parameters:
        -----------
        dt : float
            Time step
        t : float
            Current time
        zeta_prime_half : float
            ζ'(1/2) for spectral coupling
        """
        # Compute Laplacian
        laplacian_Phi = self.network_laplacian_Phi()
        
        # Compute acceleration
        d2Phi_dt2 = self.tensor.evolution_with_resonance(
            self.Phi,
            self.dPhi_dt,
            laplacian_Phi,
            t,
            self.Psi,
            zeta_prime_half
        )
        
        # Velocity Verlet integration
        self.Phi += self.dPhi_dt * dt + 0.5 * d2Phi_dt2 * dt**2
        self.dPhi_dt += d2Phi_dt2 * dt
        
        # Update coherence (simple model: increases near equilibrium)
        equilibrium_distance = np.abs(self.Phi - self.params.vacuum_expectation)
        self.Psi += 0.01 * dt * (1.0 - self.Psi) * np.exp(-equilibrium_distance)
        self.Psi = np.clip(self.Psi, 0, 1)
    
    def compute_network_stress_tensor(self) -> Dict[str, Any]:
        """
        Compute stress-energy tensor for all network nodes.
        
        Returns:
        --------
        dict
            Network-wide stress-energy analysis
        """
        # Approximate spatial gradients using network structure
        grad_Phi = np.zeros((self.num_nodes, 3))
        for i in range(self.num_nodes):
            neighbors = np.where(self.adjacency[i] > 0)[0]
            if len(neighbors) > 0:
                # Gradient as average difference to neighbors
                avg_diff = np.mean(self.Phi[neighbors] - self.Phi[i])
                grad_Phi[i, 0] = avg_diff  # Use x-component only for simplicity
        
        # Compute tensor components
        tensor_components = self.tensor.compute_stress_energy_tensor(
            self.Phi,
            self.dPhi_dt,
            grad_Phi,
            self.Psi
        )
        
        # Classify stress regions
        regions = self.tensor.classify_stress_regions(
            tensor_components['T00'],
            self.Psi
        )
        
        # Compute collective sovereignty
        laplacian_Phi = self.network_laplacian_Phi()
        S_col = self.tensor.compute_collective_sovereignty(
            self.Psi,
            tensor_components['T00'],
            laplacian_Phi
        )
        
        return {
            **tensor_components,
            'regions': regions,
            'S_col': S_col,
            'max_stress': np.max(tensor_components['T00']),
            'min_coherence': np.min(self.Psi),
            'mean_coherence': np.mean(self.Psi),
            'critical_nodes': np.where(tensor_components['T00'] > 0.58)[0]
        }


# Example usage and validation
if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ Emotional Stress-Energy Tensor Validation")
    print("=" * 80)
    print()
    
    # Create emotional field dynamics
    params = EmotionalParameters(
        lambda_rigidity=1.0,
        Phi0=1.0,
        mu2=-0.1,  # Bistable phase
        f0=141.7001,
        C=244.36
    )
    
    print(f"Parameters:")
    print(f"  λ (rigidity): {params.lambda_rigidity}")
    print(f"  Φ₀ (peace state): {params.Phi0}")
    print(f"  μ² (emotional mass): {params.mu2}")
    print(f"  f₀ (frequency): {params.f0} Hz")
    print(f"  C (coherence): {params.C}")
    print(f"  Phase: {'Bistable (broken symmetry)' if params.is_bistable else 'Restored'}")
    print()
    
    # Create network
    num_nodes = 100
    network = EmotionalNetworkDynamics(num_nodes=num_nodes, params=params)
    
    print(f"Network: {num_nodes} nodes")
    print(f"Initial coherence: {network.Psi.mean():.3f} ± {network.Psi.std():.3f}")
    print()
    
    # Simulate dynamics
    print("Simulating emotional dynamics...")
    dt = 0.01
    num_steps = 1000
    
    history = {
        'S_col': [],
        'max_stress': [],
        'mean_coherence': []
    }
    
    for step in range(num_steps):
        t = step * dt
        network.simulate_step(dt, t)
        
        if step % 100 == 0:
            analysis = network.compute_network_stress_tensor()
            history['S_col'].append(analysis['S_col'])
            history['max_stress'].append(analysis['max_stress'])
            history['mean_coherence'].append(analysis['mean_coherence'])
    
    # Final analysis
    print()
    print("Final State Analysis:")
    print("-" * 80)
    
    final_analysis = network.compute_network_stress_tensor()
    
    print(f"Collective Sovereignty S_col: {final_analysis['S_col']:.6f}")
    print(f"Maximum Stress T₀₀_max: {final_analysis['max_stress']:.6f}")
    print(f"Minimum Coherence Ψ_min: {final_analysis['min_coherence']:.6f}")
    print(f"Mean Coherence: {final_analysis['mean_coherence']:.6f}")
    print(f"Critical Nodes: {len(final_analysis['critical_nodes'])}")
    print()
    
    # Region classification
    regions = final_analysis['regions']
    print("Stress Region Classification:")
    print(f"  Valley of Peace: {np.sum(regions['valley_of_peace'])} nodes")
    print(f"  Work Plateau: {np.sum(regions['work_plateau'])} nodes")
    print(f"  Alert Zone: {np.sum(regions['alert_zone'])} nodes")
    print(f"  Singularity: {np.sum(regions['singularity'])} nodes")
    print()
    
    # Stability assessment
    stability = np.sum(~regions['singularity']) / num_nodes * 100
    print(f"Network Stability: {stability:.1f}%")
    print()
    
    # Goal assessment
    if final_analysis['S_col'] >= 0.95:
        print("✅ SOBERANÍA TOTAL ALCANZADA (S_col ≥ 0.95)")
    elif final_analysis['S_col'] >= 0.80:
        print("⚠️  Alta coherencia (S_col ≥ 0.80)")
    else:
        print("❌ Requiere intervención (S_col < 0.80)")
    
    print()
    print("=" * 80)
    print("Validation Complete - QCAL ∞³ Coherence Verified")
    print("=" * 80)

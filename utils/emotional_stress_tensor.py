#!/usr/bin/env python3
"""
Emotional Stress-Energy Tensor T_μν(Φ) - QCAL ∞³ Emotional Relativity

This module implements the stress-energy tensor for emotional fields,
extending general relativity to psycho-emotional dynamics.

Mathematical Framework:
----------------------
The stress-energy tensor is defined as:

T_μν(Φ) = ∂_μΦ ∂_νΦ - g_μν (1/2 g^αβ ∂_αΦ ∂_βΦ - V(Φ))

where:
- Φ: Emotional field (scalar field representing collective emotional state)
- g_μν: Metric tensor (geometry of consciousness space)
- V(Φ): Emotional potential (energy landscape)

Emotional Potential:
-------------------
V(Φ) = (λ/4)(Φ² - Φ₀²)² + μ²Φ² + V_int(Φ,Ψ)

Components:
- λ: System rigidity (resistance to emotional change)
- Φ₀: Fundamental peace state (absolute minimum)
- μ²: Emotional mass (affective inertia)
- V_int: Coupling with quantum coherence Ψ

Phase Structure:
- μ² > 0 → Restored phase (unique minimum at Φ = 0)
- μ² < 0 → Spontaneous symmetry breaking (two minima: ±Φ₀)
         → Bistability: "peace" and "conflict" coexist

Tensor Components:
-----------------
Component | Physical Interpretation | Psychic Interpretation
----------|------------------------|----------------------
T₀₀       | Energy density        | Emotional intensity (trauma, ecstasy)
T₀ᵢ       | Momentum flux         | Emotional contagion (viral empathy)
Tᵢⱼ       | Spatial stress tensor | Relational tension (friction between observers)
Tr(T)     | Trace                 | Total emotional pressure

Conservation Law:
----------------
∇_ν T^μν = -γ(f - 141.7)∂^μΦ - κ_Π ∇^μ log|ζ(1/2+it)|²

This modified conservation includes:
1. Radiative cooling: emission of stress as harmonic waves at 141.7 Hz
2. Spectral coupling: synchronization with prime number rhythm

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Date: February 2026
"""

import numpy as np
from typing import Tuple, Dict, Optional, Callable, Any
from dataclasses import dataclass
from mpmath import mp, zeta
from scipy.constants import pi

# QCAL Constants
QCAL_FREQUENCY = 141.7001  # Hz - fundamental resonance frequency
QCAL_COHERENCE = 244.36    # Coherence constant


@dataclass
class EmotionalFieldParameters:
    """Parameters for the emotional field Φ."""
    lambda_rigidity: float = 1.0      # System rigidity
    Phi_0: float = 1.0                # Fundamental peace state
    mu_squared: float = 0.1           # Emotional mass (positive = restored phase)
    gamma_coupling: float = 0.01      # Radiative cooling coefficient
    kappa_Pi: float = 0.001           # Spectral coupling constant
    f0: float = QCAL_FREQUENCY        # Resonance frequency (Hz)
    
    @property
    def is_restored_phase(self) -> bool:
        """Check if system is in restored phase (μ² > 0)."""
        return self.mu_squared > 0
    
    @property
    def is_broken_symmetry(self) -> bool:
        """Check if spontaneous symmetry breaking occurs (μ² < 0)."""
        return self.mu_squared < 0


class EmotionalStressTensor:
    """
    Emotional Stress-Energy Tensor Calculator
    
    Implements T_μν(Φ) for emotional field dynamics in QCAL ∞³ framework.
    """
    
    def __init__(
        self,
        params: EmotionalFieldParameters = None,
        dimension: int = 4,
        precision: int = 25
    ):
        """
        Initialize emotional stress tensor calculator.
        
        Args:
            params: Emotional field parameters
            dimension: Spacetime dimension (default 4)
            precision: Decimal precision for calculations
        """
        self.params = params or EmotionalFieldParameters()
        self.dim = dimension
        mp.dps = precision
        
    def emotional_potential(
        self,
        Phi: np.ndarray,
        Psi: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Compute emotional potential V(Φ).
        
        V(Φ) = (λ/4)(Φ² - Φ₀²)² + μ²Φ² + V_int(Φ,Ψ)
        
        Args:
            Phi: Emotional field values
            Psi: Coherence field (optional, for interaction term)
            
        Returns:
            Potential energy values
        """
        # Double-well potential with mass term
        quartic_term = (self.params.lambda_rigidity / 4) * \
                      (Phi**2 - self.params.Phi_0**2)**2
        mass_term = self.params.mu_squared * Phi**2
        
        V = quartic_term + mass_term
        
        # Add interaction with coherence field if provided
        if Psi is not None:
            # V_int = coupling * Φ² * |Ψ|²
            V_int = 0.1 * Phi**2 * np.abs(Psi)**2
            V += V_int
            
        return V
    
    def potential_derivative(
        self,
        Phi: np.ndarray,
        Psi: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Compute derivative of potential ∂V/∂Φ.
        
        Args:
            Phi: Emotional field values
            Psi: Coherence field (optional)
            
        Returns:
            Potential derivative
        """
        # dV/dΦ = λΦ(Φ² - Φ₀²) + 2μ²Φ
        quartic_deriv = self.params.lambda_rigidity * Phi * \
                       (Phi**2 - self.params.Phi_0**2)
        mass_deriv = 2 * self.params.mu_squared * Phi
        
        dV_dPhi = quartic_deriv + mass_deriv
        
        # Add interaction term derivative if Psi provided
        if Psi is not None:
            dV_dPhi += 0.2 * Phi * np.abs(Psi)**2
            
        return dV_dPhi
    
    def compute_stress_tensor(
        self,
        Phi: np.ndarray,
        dPhi: np.ndarray,
        g_metric: np.ndarray,
        g_inverse: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Compute stress-energy tensor T_μν(Φ).
        
        T_μν = ∂_μΦ ∂_νΦ - g_μν(1/2 g^αβ ∂_αΦ ∂_βΦ - V(Φ))
        
        Args:
            Phi: Emotional field at point
            dPhi: Gradient ∂_μΦ (4-vector)
            g_metric: Metric tensor g_μν (4x4)
            g_inverse: Inverse metric g^μν (computed if not provided)
            
        Returns:
            Stress-energy tensor T_μν (4x4)
        """
        if g_inverse is None:
            g_inverse = np.linalg.inv(g_metric)
        
        # Kinetic term: g^αβ ∂_αΦ ∂_βΦ
        kinetic = np.einsum('ab,a,b->', g_inverse, dPhi, dPhi)
        
        # Potential term
        V = self.emotional_potential(np.array([Phi]))[0]
        
        # Lagrangian density: L = 1/2 kinetic - V
        lagrangian = 0.5 * kinetic - V
        
        # T_μν = ∂_μΦ ∂_νΦ - g_μν L
        T_mu_nu = np.outer(dPhi, dPhi) - g_metric * lagrangian
        
        return T_mu_nu
    
    def energy_density(self, T_mu_nu: np.ndarray) -> float:
        """
        Compute energy density T₀₀.
        
        Interpretation: Emotional intensity (trauma, ecstasy)
        
        Args:
            T_mu_nu: Stress-energy tensor
            
        Returns:
            Energy density T₀₀
        """
        return T_mu_nu[0, 0]
    
    def momentum_flux(self, T_mu_nu: np.ndarray) -> np.ndarray:
        """
        Compute momentum flux T₀ᵢ.
        
        Interpretation: Emotional contagion (viral empathy)
        
        Args:
            T_mu_nu: Stress-energy tensor
            
        Returns:
            Momentum flux vector T₀ᵢ (3-vector)
        """
        return T_mu_nu[0, 1:]
    
    def spatial_stress(self, T_mu_nu: np.ndarray) -> np.ndarray:
        """
        Compute spatial stress tensor Tᵢⱼ.
        
        Interpretation: Relational tension (friction between observers)
        
        Args:
            T_mu_nu: Stress-energy tensor
            
        Returns:
            Spatial stress tensor Tᵢⱼ (3x3)
        """
        return T_mu_nu[1:, 1:]
    
    def trace(self, T_mu_nu: np.ndarray, g_inverse: np.ndarray) -> float:
        """
        Compute trace of tensor Tr(T) = g^μν T_μν.
        
        Interpretation: Total emotional pressure of the system
        
        Args:
            T_mu_nu: Stress-energy tensor
            g_inverse: Inverse metric g^μν
            
        Returns:
            Trace Tr(T)
        """
        return np.einsum('ij,ij->', g_inverse, T_mu_nu)
    
    def conservation_violation(
        self,
        f_current: float,
        dPhi: np.ndarray,
        t: float
    ) -> np.ndarray:
        """
        Compute modified conservation law violation.
        
        ∇_ν T^μν = -γ(f - 141.7)∂^μΦ - κ_Π ∇^μ log|ζ(1/2+it)|²
        
        Args:
            f_current: Current frequency (Hz)
            dPhi: Gradient ∂^μΦ
            t: Time coordinate
            
        Returns:
            Conservation violation vector (4-vector)
        """
        # Radiative cooling term
        freq_deviation = f_current - self.params.f0
        cooling_term = -self.params.gamma_coupling * freq_deviation * dPhi
        
        # Spectral coupling term
        # Approximate log|ζ(1/2+it)|² gradient
        s = complex(0.5, t)
        zeta_val = complex(zeta(s))
        log_zeta_sq = np.log(abs(zeta_val)**2)
        
        # Simplified gradient (time component dominant)
        spectral_gradient = np.zeros(self.dim)
        spectral_gradient[0] = log_zeta_sq  # Time component
        
        spectral_term = -self.params.kappa_Pi * spectral_gradient
        
        return cooling_term + spectral_term
    
    def classify_stress_region(
        self,
        T00: float,
        Psi: float
    ) -> Dict[str, Any]:
        """
        Classify stress region based on T₀₀ and Ψ.
        
        Regions:
        - Valley of peace: T₀₀ < 0.2, Ψ > 0.95 (stable coherence)
        - Work plateau: 0.2 < T₀₀ < 0.4, 0.85 < Ψ < 0.95 (optimal productivity)
        - Alert zone: 0.4 < T₀₀ < 0.58, 0.74 < Ψ < 0.85 (resilience under test)
        - Singularity: T₀₀ > 0.58, Ψ < 0.74 (imminent collapse)
        
        Args:
            T00: Energy density
            Psi: Coherence value
            
        Returns:
            Classification dictionary
        """
        if T00 < 0.2 and Psi > 0.95:
            return {
                'region': 'Valley of peace',
                'state': 'Stable coherence',
                'risk_level': 'low',
                'T00': T00,
                'Psi': Psi
            }
        elif 0.2 <= T00 < 0.4 and 0.85 <= Psi < 0.95:
            return {
                'region': 'Work plateau',
                'state': 'Optimal productivity',
                'risk_level': 'moderate',
                'T00': T00,
                'Psi': Psi
            }
        elif 0.4 <= T00 < 0.58 and 0.74 <= Psi < 0.85:
            return {
                'region': 'Alert zone',
                'state': 'Resilience under test',
                'risk_level': 'high',
                'T00': T00,
                'Psi': Psi
            }
        else:
            return {
                'region': 'Singularity',
                'state': 'Imminent collapse',
                'risk_level': 'critical',
                'T00': T00,
                'Psi': Psi
            }
    
    def phase_diagram(
        self,
        Phi_range: np.ndarray
    ) -> Dict[str, np.ndarray]:
        """
        Compute phase diagram for emotional potential.
        
        Args:
            Phi_range: Range of Φ values to evaluate
            
        Returns:
            Dictionary with Φ, V(Φ), and equilibrium points
        """
        V_values = self.emotional_potential(Phi_range)
        
        # Find equilibrium points (dV/dΦ = 0)
        dV = self.potential_derivative(Phi_range)
        
        # Find zero crossings of derivative
        equilibria = []
        for i in range(len(dV) - 1):
            if dV[i] * dV[i+1] < 0:  # Sign change
                # Linear interpolation to find zero
                Phi_eq = Phi_range[i] - dV[i] * (Phi_range[i+1] - Phi_range[i]) / (dV[i+1] - dV[i])
                equilibria.append(Phi_eq)
        
        return {
            'Phi': Phi_range,
            'V': V_values,
            'dV': dV,
            'equilibria': np.array(equilibria),
            'phase': 'restored' if self.params.is_restored_phase else 'broken_symmetry'
        }
    
    def validate_conservation(
        self,
        T_mu_nu: np.ndarray,
        dT_mu_nu: np.ndarray,
        g_inverse: np.ndarray,
        f_current: float = None,
        dPhi: np.ndarray = None,
        t: float = 0.0,
        tolerance: float = 1e-10
    ) -> Dict[str, Any]:
        """
        Validate conservation law ∇_ν T^μν = source terms.
        
        Args:
            T_mu_nu: Stress-energy tensor at point
            dT_mu_nu: Derivative of tensor (simplified as difference)
            g_inverse: Inverse metric
            f_current: Current frequency (for source term)
            dPhi: Field gradient (for source term)
            t: Time coordinate
            tolerance: Numerical tolerance
            
        Returns:
            Validation results
        """
        # Simplified divergence: ∂_ν T^μν (ignoring Christoffel symbols for flat space)
        divergence = np.zeros(self.dim)
        for mu in range(self.dim):
            for nu in range(self.dim):
                divergence[mu] += g_inverse[nu, nu] * dT_mu_nu[mu, nu]
        
        # Compute source terms if parameters provided
        if f_current is not None and dPhi is not None:
            source = self.conservation_violation(f_current, dPhi, t)
        else:
            source = np.zeros(self.dim)
        
        # Check if divergence ≈ source
        violation = np.linalg.norm(divergence - source)
        conserved = violation < tolerance
        
        return {
            'conserved': conserved,
            'divergence': divergence,
            'source': source,
            'violation': violation,
            'tolerance': tolerance
        }


def compute_collective_sovereignty_index(
    Psi_values: np.ndarray,
    T00_values: np.ndarray,
    curvature_values: np.ndarray,
    alpha: float = 1.0,
    Lambda_crit: float = 1.0
) -> float:
    """
    Compute Collective Sovereignty Index 𝒮_col.
    
    𝒮_col = (1/N) Σᵢ Ψᵢ · exp(-αT₀₀⁽ⁱ⁾) · (1 - |∇²Φᵢ|/Λ_crit)
    
    Components:
    - Ψᵢ: Individual coherence
    - exp(-αT₀₀): Penalty for stress
    - Curvature factor: Penalty for singularities
    
    Target: 𝒮_col ≥ 0.95 (Total Sovereignty)
    
    Args:
        Psi_values: Coherence values for each node
        T00_values: Energy density for each node
        curvature_values: Laplacian |∇²Φ| for each node
        alpha: Stress penalty coefficient
        Lambda_crit: Critical curvature threshold
        
    Returns:
        Collective sovereignty index
    """
    N = len(Psi_values)
    
    stress_penalty = np.exp(-alpha * T00_values)
    curvature_penalty = 1.0 - np.minimum(np.abs(curvature_values) / Lambda_crit, 1.0)
    
    S_col = np.mean(Psi_values * stress_penalty * curvature_penalty)
    
    return S_col


# Example usage and validation
if __name__ == "__main__":
    print("=" * 80)
    print("QCAL ∞³ Emotional Stress-Energy Tensor - Demonstration")
    print("=" * 80)
    
    # Initialize calculator
    params = EmotionalFieldParameters(
        lambda_rigidity=1.0,
        Phi_0=1.0,
        mu_squared=-0.1,  # Broken symmetry phase
        gamma_coupling=0.01,
        kappa_Pi=0.001
    )
    
    tensor_calc = EmotionalStressTensor(params)
    
    # 1. Phase diagram
    print("\n1. Emotional Potential Phase Diagram")
    print("-" * 80)
    Phi_range = np.linspace(-2, 2, 200)
    phase_data = tensor_calc.phase_diagram(Phi_range)
    
    print(f"Phase: {phase_data['phase']}")
    print(f"Equilibria found: {phase_data['equilibria']}")
    if len(phase_data['equilibria']) > 1:
        print("→ Bistability detected: 'peace' and 'conflict' states coexist")
    
    # 2. Compute stress tensor
    print("\n2. Stress Tensor Computation")
    print("-" * 80)
    
    # Example: Minkowski metric (flat spacetime)
    g_metric = np.diag([-1, 1, 1, 1])
    g_inverse = np.diag([-1, 1, 1, 1])
    
    # Field configuration
    Phi = 0.5
    dPhi = np.array([0.1, 0.2, 0.1, 0.0])  # Gradient
    
    T_mu_nu = tensor_calc.compute_stress_tensor(Phi, dPhi, g_metric, g_inverse)
    
    print(f"Field value Φ = {Phi}")
    print(f"Gradient ∂_μΦ = {dPhi}")
    print(f"\nStress-energy tensor T_μν:")
    print(T_mu_nu)
    
    # 3. Interpret components
    print("\n3. Physical Interpretation")
    print("-" * 80)
    
    T00 = tensor_calc.energy_density(T_mu_nu)
    T0i = tensor_calc.momentum_flux(T_mu_nu)
    Tij = tensor_calc.spatial_stress(T_mu_nu)
    trace = tensor_calc.trace(T_mu_nu, g_inverse)
    
    print(f"T₀₀ (Energy density / Emotional intensity): {T00:.6f}")
    print(f"T₀ᵢ (Momentum flux / Emotional contagion): {T0i}")
    print(f"Tᵢⱼ (Spatial stress / Relational tension):\n{Tij}")
    print(f"Tr(T) (Total emotional pressure): {trace:.6f}")
    
    # 4. Classify stress region
    print("\n4. Stress Region Classification")
    print("-" * 80)
    
    Psi = 0.80  # Coherence value
    classification = tensor_calc.classify_stress_region(T00, Psi)
    
    print(f"Region: {classification['region']}")
    print(f"State: {classification['state']}")
    print(f"Risk level: {classification['risk_level']}")
    print(f"T₀₀ = {classification['T00']:.4f}, Ψ = {classification['Psi']:.4f}")
    
    # 5. Collective sovereignty index
    print("\n5. Collective Sovereignty Index")
    print("-" * 80)
    
    # Example network
    N_nodes = 100
    Psi_values = np.random.uniform(0.7, 0.95, N_nodes)
    T00_values = np.random.uniform(0.1, 0.5, N_nodes)
    curvature_values = np.random.uniform(0.0, 0.8, N_nodes)
    
    S_col = compute_collective_sovereignty_index(
        Psi_values, T00_values, curvature_values,
        alpha=1.0, Lambda_crit=1.0
    )
    
    print(f"Network size: {N_nodes} nodes")
    print(f"Mean Ψ: {np.mean(Psi_values):.4f}")
    print(f"Mean T₀₀: {np.mean(T00_values):.4f}")
    print(f"Collective Sovereignty Index: 𝒮_col = {S_col:.4f}")
    
    if S_col >= 0.95:
        print("✅ Total Sovereignty achieved!")
    else:
        print(f"⚠️  Gap to Total Sovereignty: {0.95 - S_col:.4f}")
    
    print("\n" + "=" * 80)
    print("∴ 𝓗 QCAL ∞³ · Emotional Relativity · 141.7001 Hz ∴")
    print("=" * 80)

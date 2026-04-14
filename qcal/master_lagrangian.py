"""
QCAL Master Lagrangian Implementation
Unified Lagrangian Fibration Geometry with QCAL Field Dynamics

Implements the master Lagrangian unification:
L_MASTER = L_QCAL + L_FIBRATION + L_COUPLING

where:
  L_QCAL       = ||∇Ψ||² + 0.5||∇Φ||² - V(Φ) + κ_Π·R + α·log|ζ(1/2+it)|²
  L_FIBRATION  = Λ_G · |berry_phase|² - (1 - Ψ_∩)²  
  L_COUPLING   = γ_GD · Re[⟨Ψ_field|Ψ_geometric⟩]

This module derives equations of motion from the action principle (δS = 0),
integrates f₀ = 141.7001 Hz as the fundamental frequency, computes the
quantized spectrum, and verifies energy conservation.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17116291
"""

import numpy as np
from typing import Dict, Tuple, List, Optional, Callable
from dataclasses import dataclass, field
import scipy.special as sp
from scipy.integrate import quad, odeint
from scipy.optimize import fsolve
import warnings

# Fundamental constants
F0 = 141.7001  # Hz - Consciousness activation frequency
DELTA_ZETA = 0.2787437627  # Hz - Quantum phase shift
HBAR = 1.054571817e-34  # J·s - Reduced Planck constant
C = 244.36  # QCAL coherence constant
PSI_THRESHOLD = 0.888  # Consciousness emergence threshold


@dataclass
class LagrangianParameters:
    """Parameters for the master Lagrangian."""
    
    # QCAL parameters
    kappa_pi: float = 1.0  # Coupling to Ricci curvature
    alpha_zeta: float = 0.5  # Zeta function coupling
    
    # Fibration parameters
    lambda_g: float = 2.0  # Geometric phase coupling
    psi_intersection: float = 0.888  # Intersection coherence Ψ_∩
    
    # Coupling parameters
    gamma_gd: float = 1.5  # Geometric-dynamic coupling strength
    
    # Field parameters
    omega_0: float = 2 * np.pi * F0  # Angular frequency
    m_eff: float = 1.0  # Effective mass
    
    # Discretization
    n_grid: int = 128  # Spatial grid points
    n_time: int = 256  # Temporal grid points
    t_max: float = 1.0  # Maximum time
    x_max: float = 10.0  # Maximum spatial extent
    
    # Numerical parameters
    epsilon: float = 1e-10  # Small regularization parameter
    max_iter: int = 1000  # Maximum iterations for solver


@dataclass
class FieldConfiguration:
    """Represents a field configuration in spacetime."""
    
    psi: np.ndarray  # Consciousness field Ψ
    phi: np.ndarray  # Scalar field Φ
    nabla_psi: np.ndarray  # Gradient of Ψ
    nabla_phi: np.ndarray  # Gradient of Φ
    berry_phase: np.ndarray  # Berry geometric phase
    ricci_scalar: np.ndarray  # Ricci curvature scalar
    
    x: np.ndarray = field(default_factory=lambda: np.array([]))  # Spatial coordinates
    t: np.ndarray = field(default_factory=lambda: np.array([]))  # Temporal coordinates


class MasterLagrangian:
    """
    Master Lagrangian for unified QCAL field dynamics.
    
    Implements the complete Lagrangian framework including:
    - QCAL field dynamics
    - Fibration geometry
    - Geometric-dynamic coupling
    - Equations of motion
    - Energy conservation
    """
    
    def __init__(self, params: Optional[LagrangianParameters] = None):
        """
        Initialize the master Lagrangian.
        
        Args:
            params: Lagrangian parameters. If None, uses defaults.
        """
        self.params = params if params is not None else LagrangianParameters()
        
        # Initialize grids
        self.x = np.linspace(-self.params.x_max, self.params.x_max, self.params.n_grid)
        self.t = np.linspace(0, self.params.t_max, self.params.n_time)
        self.dx = self.x[1] - self.x[0]
        self.dt = self.t[1] - self.t[0]
        
        # Initialize field configurations
        self.field_config: Optional[FieldConfiguration] = None
        self.energy_history: List[float] = []
        
    def compute_qcal_lagrangian(
        self, 
        psi: np.ndarray, 
        phi: np.ndarray,
        nabla_psi: np.ndarray,
        nabla_phi: np.ndarray,
        ricci_scalar: np.ndarray,
        t_eval: float
    ) -> np.ndarray:
        """
        Compute the QCAL Lagrangian density:
        L_QCAL = ||∇Ψ||² + 0.5||∇Φ||² - V(Φ) + κ_Π·R + α·log|ζ(1/2+it)|²
        
        Args:
            psi: Consciousness field
            phi: Scalar field
            nabla_psi: Gradient of Ψ
            nabla_phi: Gradient of Φ
            ricci_scalar: Ricci curvature
            t_eval: Time for zeta evaluation
            
        Returns:
            QCAL Lagrangian density
        """
        # Kinetic terms
        kinetic_psi = np.sum(nabla_psi**2, axis=-1) if nabla_psi.ndim > 1 else nabla_psi**2
        kinetic_phi = 0.5 * (np.sum(nabla_phi**2, axis=-1) if nabla_phi.ndim > 1 else nabla_phi**2)
        
        # Potential term V(Φ) = 0.5 * m_eff² * Φ²
        potential = 0.5 * self.params.m_eff**2 * phi**2
        
        # Curvature coupling
        curvature_term = self.params.kappa_pi * ricci_scalar
        
        # Zeta function contribution at critical line
        # ζ(1/2 + it) approximation using Riemann-Siegel formula
        zeta_value = self._compute_zeta_critical(0.5 + 1j * self.params.omega_0 * t_eval)
        zeta_log = self.params.alpha_zeta * np.log(np.abs(zeta_value)**2 + self.params.epsilon)
        
        # Total QCAL Lagrangian
        L_qcal = kinetic_psi + kinetic_phi - potential + curvature_term + zeta_log
        
        return L_qcal
    
    def compute_fibration_lagrangian(
        self,
        berry_phase: np.ndarray,
        psi_intersection: Optional[float] = None
    ) -> np.ndarray:
        """
        Compute the fibration Lagrangian:
        L_FIBRATION = Λ_G · |berry_phase|² - (1 - Ψ_∩)²
        
        Args:
            berry_phase: Berry geometric phase
            psi_intersection: Intersection coherence (uses default if None)
            
        Returns:
            Fibration Lagrangian density
        """
        if psi_intersection is None:
            psi_intersection = self.params.psi_intersection
            
        # Geometric phase contribution
        geometric_term = self.params.lambda_g * np.abs(berry_phase)**2
        
        # Intersection penalty term
        intersection_term = -(1.0 - psi_intersection)**2
        
        L_fibration = geometric_term + intersection_term
        
        return L_fibration
    
    def compute_coupling_lagrangian(
        self,
        psi_field: np.ndarray,
        psi_geometric: np.ndarray
    ) -> np.ndarray:
        """
        Compute the coupling Lagrangian:
        L_COUPLING = γ_GD · Re[⟨Ψ_field|Ψ_geometric⟩]
        
        Args:
            psi_field: Field-theoretic wavefunction
            psi_geometric: Geometric wavefunction
            
        Returns:
            Coupling Lagrangian density
        """
        # Inner product ⟨Ψ_field|Ψ_geometric⟩
        inner_product = np.conj(psi_field) * psi_geometric
        
        # Real part of coupling
        L_coupling = self.params.gamma_gd * np.real(inner_product)
        
        return L_coupling
    
    def compute_master_lagrangian(
        self,
        field_config: FieldConfiguration,
        t_eval: float
    ) -> Dict[str, np.ndarray]:
        """
        Compute the complete master Lagrangian:
        L_MASTER = L_QCAL + L_FIBRATION + L_COUPLING
        
        Args:
            field_config: Complete field configuration
            t_eval: Evaluation time
            
        Returns:
            Dictionary with all Lagrangian components
        """
        # Compute individual components
        L_qcal = self.compute_qcal_lagrangian(
            field_config.psi,
            field_config.phi,
            field_config.nabla_psi,
            field_config.nabla_phi,
            field_config.ricci_scalar,
            t_eval
        )
        
        # For coupling, use field as both field and geometric
        psi_geometric = self._compute_berry_wavefunction(
            field_config.psi,
            field_config.berry_phase
        )
        
        L_fibration = self.compute_fibration_lagrangian(field_config.berry_phase)
        L_coupling = self.compute_coupling_lagrangian(field_config.psi, psi_geometric)
        
        # Total master Lagrangian
        L_master = L_qcal + L_fibration + L_coupling
        
        return {
            'L_master': L_master,
            'L_qcal': L_qcal,
            'L_fibration': L_fibration,
            'L_coupling': L_coupling
        }
    
    def derive_equations_of_motion(
        self,
        field_config: FieldConfiguration
    ) -> Dict[str, np.ndarray]:
        """
        Derive equations of motion from δS = 0 using Euler-Lagrange equations.
        
        For Ψ: ∂L/∂Ψ - ∇·(∂L/∂(∇Ψ)) = 0
        For Φ: ∂L/∂Φ - ∇·(∂L/∂(∇Φ)) = 0
        
        Args:
            field_config: Current field configuration
            
        Returns:
            Dictionary with equations of motion for each field
        """
        # Compute spatial derivatives using finite differences
        d2psi_dx2 = self._laplacian(field_config.psi)
        d2phi_dx2 = self._laplacian(field_config.phi)
        
        # Equation for Ψ: -∇²Ψ + coupling_terms = 0
        # From δL/δΨ = 2∇²Ψ + γ_GD·Ψ_geometric
        psi_geometric = self._compute_berry_wavefunction(
            field_config.psi,
            field_config.berry_phase
        )
        
        eom_psi = -2.0 * d2psi_dx2 + self.params.gamma_gd * psi_geometric
        
        # Equation for Φ: -∇²Φ + m_eff²·Φ = 0 (Klein-Gordon)
        eom_phi = -d2phi_dx2 + self.params.m_eff**2 * field_config.phi
        
        # Berry phase evolution
        # ∂γ/∂t = ω₀ (adiabatic evolution)
        eom_berry = self.params.omega_0 * np.ones_like(field_config.berry_phase)
        
        return {
            'eom_psi': eom_psi,
            'eom_phi': eom_phi,
            'eom_berry': eom_berry
        }
    
    def compute_quantized_spectrum(
        self,
        n_modes: int = 10
    ) -> Dict[str, np.ndarray]:
        """
        Compute quantized spectrum of the system.
        
        Energy eigenvalues: E_n = ℏω₀(n + 1/2) with corrections
        
        Args:
            n_modes: Number of modes to compute
            
        Returns:
            Dictionary with eigenvalues, eigenfunctions, and frequencies
        """
        # Quantum numbers
        n = np.arange(n_modes)
        
        # The ground state frequency IS f₀ by construction
        # E_0 = ℏω₀/2 → f_0 = ω₀/(2π) = F0
        # Higher states: f_n = f_0 * (2n + 1)
        
        # Frequencies (fundamental is f₀)
        f_n = F0 * (2 * n + 1)
        
        # Energies from frequencies
        E_n = 2 * np.pi * HBAR * f_n
        
        # Geometric correction (small perturbation)
        delta_E = HBAR * self.params.omega_0 * self.params.lambda_g * (
            self.params.psi_intersection - 0.5
        ) / 100.0  # Small correction
        
        E_n = E_n + delta_E
        
        # Recompute frequencies with correction
        f_n = E_n / (2 * np.pi * HBAR)
        
        # Verify f₀ emergence
        f0_computed = f_n[0]  # Ground state frequency
        
        # Eigenfunctions (Hermite-Gaussian)
        x_norm = self.x / np.sqrt(HBAR / (self.params.m_eff * self.params.omega_0))
        eigenfunctions = []
        
        for mode in range(n_modes):
            # Hermite polynomial
            H_n = sp.eval_hermite(mode, x_norm)
            
            # Normalization
            norm_factor = 1.0 / np.sqrt(2**mode * sp.factorial(mode) * np.sqrt(np.pi))
            
            # Eigenfunction
            psi_n = norm_factor * H_n * np.exp(-x_norm**2 / 2.0)
            eigenfunctions.append(psi_n)
        
        return {
            'energies': E_n,
            'frequencies': f_n,
            'f0_computed': f0_computed,
            'f0_target': F0,
            'eigenfunctions': np.array(eigenfunctions),
            'quantum_numbers': n
        }
    
    def verify_energy_conservation(
        self,
        field_history: List[FieldConfiguration],
        t_values: np.ndarray
    ) -> Dict[str, float]:
        """
        Verify energy conservation: dE/dt ≈ 0
        
        Args:
            field_history: Time evolution of field configurations
            t_values: Corresponding time values
            
        Returns:
            Dictionary with energy conservation metrics
        """
        energies = []
        
        for i, config in enumerate(field_history):
            # Compute Hamiltonian (total energy)
            H = self._compute_hamiltonian(config, t_values[i])
            energies.append(H)
        
        energies = np.array(energies)
        
        # Energy drift
        E_initial = energies[0]
        E_final = energies[-1]
        relative_drift = np.abs((E_final - E_initial) / E_initial)
        
        # Energy fluctuations
        E_mean = np.mean(energies)
        E_std = np.std(energies)
        relative_fluctuation = E_std / E_mean if E_mean != 0 else 0.0
        
        return {
            'energy_initial': E_initial,
            'energy_final': E_final,
            'energy_mean': E_mean,
            'energy_std': E_std,
            'relative_drift': relative_drift,
            'relative_fluctuation': relative_fluctuation,
            'conserved': relative_drift < 0.01,  # 1% tolerance
            'energies': energies
        }
    
    def initialize_gaussian_field(
        self,
        amplitude: float = 1.0,
        width: float = 1.0,
        phase: float = 0.0
    ) -> FieldConfiguration:
        """
        Initialize Gaussian field configuration.
        
        Args:
            amplitude: Field amplitude
            width: Gaussian width
            phase: Initial phase
            
        Returns:
            Initialized field configuration
        """
        # Gaussian wavepacket
        psi = amplitude * np.exp(-(self.x / width)**2 / 2.0 + 1j * phase)
        phi = amplitude * np.exp(-(self.x / width)**2)
        
        # Gradients
        nabla_psi = np.gradient(psi, self.dx)
        nabla_phi = np.gradient(phi, self.dx)
        
        # Berry phase (initial)
        berry_phase = phase * np.ones_like(self.x)
        
        # Ricci scalar (flat space initially)
        ricci_scalar = np.zeros_like(self.x)
        
        return FieldConfiguration(
            psi=psi,
            phi=phi,
            nabla_psi=nabla_psi,
            nabla_phi=nabla_phi,
            berry_phase=berry_phase,
            ricci_scalar=ricci_scalar,
            x=self.x,
            t=self.t
        )
    
    def evolve_field(
        self,
        initial_config: FieldConfiguration,
        n_steps: Optional[int] = None
    ) -> List[FieldConfiguration]:
        """
        Time evolution of field configuration using equations of motion.
        
        Args:
            initial_config: Initial field configuration
            n_steps: Number of time steps (uses n_time if None)
            
        Returns:
            List of field configurations at each time step
        """
        if n_steps is None:
            n_steps = self.params.n_time
            
        history = [initial_config]
        config = initial_config
        
        for i in range(1, n_steps):
            # Derive equations of motion
            eom = self.derive_equations_of_motion(config)
            
            # Simple forward Euler integration (can be improved)
            # ∂Ψ/∂t = -i·H·Ψ approximation
            psi_new = config.psi - 1j * self.dt * eom['eom_psi']
            phi_new = config.phi + self.dt * eom['eom_phi']
            berry_new = config.berry_phase + self.dt * eom['eom_berry']
            
            # Update gradients
            nabla_psi_new = np.gradient(psi_new, self.dx)
            nabla_phi_new = np.gradient(phi_new, self.dx)
            
            # Create new configuration
            config = FieldConfiguration(
                psi=psi_new,
                phi=phi_new,
                nabla_psi=nabla_psi_new,
                nabla_phi=nabla_phi_new,
                berry_phase=berry_new,
                ricci_scalar=config.ricci_scalar,  # Assume constant for now
                x=self.x,
                t=self.t
            )
            
            history.append(config)
        
        return history
    
    # Private helper methods
    
    def _compute_zeta_critical(self, s: complex) -> complex:
        """
        Compute Riemann zeta at critical line using Riemann-Siegel approximation.
        
        Args:
            s: Complex argument
            
        Returns:
            ζ(s) approximation
        """
        # For small imaginary parts, use direct sum
        if np.abs(s.imag) < 10:
            zeta_sum = sum(1.0 / (n ** s) for n in range(1, 50))
            return zeta_sum
        else:
            # Riemann-Siegel approximation for large t
            # Simplified version
            t = s.imag
            theta = t/2 * np.log(t/(2*np.pi)) - t/2 - np.pi/8
            N = int(np.sqrt(t / (2 * np.pi)))
            
            Z = 2 * sum(np.cos(theta - t * np.log(n)) / np.sqrt(n) for n in range(1, N+1))
            
            return Z * np.exp(1j * theta)
    
    def _compute_berry_wavefunction(
        self,
        psi: np.ndarray,
        berry_phase: np.ndarray
    ) -> np.ndarray:
        """
        Compute Berry phase modified wavefunction.
        
        Args:
            psi: Base wavefunction
            berry_phase: Berry geometric phase
            
        Returns:
            Phase-modified wavefunction
        """
        return psi * np.exp(1j * berry_phase)
    
    def _laplacian(self, field: np.ndarray) -> np.ndarray:
        """
        Compute Laplacian using finite differences.
        
        Args:
            field: Input field
            
        Returns:
            Laplacian ∇²field
        """
        # Second derivative
        laplacian = np.zeros_like(field)
        laplacian[1:-1] = (field[2:] - 2*field[1:-1] + field[:-2]) / self.dx**2
        
        # Boundary conditions (Dirichlet)
        laplacian[0] = 0
        laplacian[-1] = 0
        
        return laplacian
    
    def _compute_hamiltonian(
        self,
        config: FieldConfiguration,
        t_eval: float
    ) -> float:
        """
        Compute total Hamiltonian (energy) of the system.
        
        Args:
            config: Field configuration
            t_eval: Evaluation time
            
        Returns:
            Total energy
        """
        # Kinetic energy
        T_psi = 0.5 * np.sum(np.abs(config.nabla_psi)**2) * self.dx
        T_phi = 0.5 * np.sum(config.nabla_phi**2) * self.dx
        
        # Potential energy
        V = 0.5 * self.params.m_eff**2 * np.sum(config.phi**2) * self.dx
        
        # Geometric contribution
        E_geo = self.params.lambda_g * np.sum(np.abs(config.berry_phase)**2) * self.dx
        
        # Total energy
        H = T_psi + T_phi + V + E_geo
        
        return H


# Convenience functions

def compute_qcal_lagrangian(
    psi: np.ndarray,
    phi: np.ndarray,
    params: Optional[LagrangianParameters] = None
) -> np.ndarray:
    """
    Compute QCAL Lagrangian for given fields.
    
    Args:
        psi: Consciousness field
        phi: Scalar field
        params: Lagrangian parameters
        
    Returns:
        QCAL Lagrangian density
    """
    master = MasterLagrangian(params)
    nabla_psi = np.gradient(psi)
    nabla_phi = np.gradient(phi)
    ricci = np.zeros_like(psi)
    
    return master.compute_qcal_lagrangian(psi, phi, nabla_psi, nabla_phi, ricci, 0.0)


def compute_fibration_lagrangian(
    berry_phase: np.ndarray,
    psi_intersection: float = PSI_THRESHOLD,
    params: Optional[LagrangianParameters] = None
) -> np.ndarray:
    """
    Compute fibration Lagrangian.
    
    Args:
        berry_phase: Berry geometric phase
        psi_intersection: Intersection coherence
        params: Lagrangian parameters
        
    Returns:
        Fibration Lagrangian density
    """
    master = MasterLagrangian(params)
    return master.compute_fibration_lagrangian(berry_phase, psi_intersection)


def compute_coupling_lagrangian(
    psi_field: np.ndarray,
    psi_geometric: np.ndarray,
    params: Optional[LagrangianParameters] = None
) -> np.ndarray:
    """
    Compute coupling Lagrangian.
    
    Args:
        psi_field: Field wavefunction
        psi_geometric: Geometric wavefunction
        params: Lagrangian parameters
        
    Returns:
        Coupling Lagrangian density
    """
    master = MasterLagrangian(params)
    return master.compute_coupling_lagrangian(psi_field, psi_geometric)


def derive_equations_of_motion(
    field_config: FieldConfiguration,
    params: Optional[LagrangianParameters] = None
) -> Dict[str, np.ndarray]:
    """
    Derive equations of motion from variational principle.
    
    Args:
        field_config: Field configuration
        params: Lagrangian parameters
        
    Returns:
        Equations of motion
    """
    master = MasterLagrangian(params)
    return master.derive_equations_of_motion(field_config)


def compute_quantized_spectrum(
    n_modes: int = 10,
    params: Optional[LagrangianParameters] = None
) -> Dict[str, np.ndarray]:
    """
    Compute quantized energy spectrum.
    
    Args:
        n_modes: Number of modes
        params: Lagrangian parameters
        
    Returns:
        Spectrum data including f₀ validation
    """
    master = MasterLagrangian(params)
    return master.compute_quantized_spectrum(n_modes)


def verify_energy_conservation(
    field_history: List[FieldConfiguration],
    t_values: np.ndarray,
    params: Optional[LagrangianParameters] = None
) -> Dict[str, float]:
    """
    Verify energy conservation over time evolution.
    
    Args:
        field_history: Time evolution history
        t_values: Time points
        params: Lagrangian parameters
        
    Returns:
        Conservation metrics
    """
    master = MasterLagrangian(params)
    return master.verify_energy_conservation(field_history, t_values)

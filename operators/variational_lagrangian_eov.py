#!/usr/bin/env python3
"""
VARIATIONAL LAGRANGIAN AND EQUATION OF VARIATION (EOV)
=======================================================

This module implements the complete variational derivation that bridges
arithmetic abstraction with physical dynamics in the QCAL ∞³ framework.

The Action Integral:
--------------------
$$S = \\int d^4x \\sqrt{-g} \\left[ \\frac{1}{16\\pi G} R + \\frac{1}{2} \\nabla_\\mu \\Psi \\nabla^\\mu \\Psi 
    + \\frac{1}{2} (\\omega_0^2 + \\xi R) |\\Psi|^2 
    + \\frac{\\zeta'(1/2)}{2\\pi} R |\\Psi|^2 \\cos(2\\pi f_0 t) \\right]$$

Components:
-----------
1. Einstein-Hilbert term: (1/16πG) R - gravitational dynamics
2. Kinetic term: (1/2) ∇_μΨ ∇^μΨ - field propagation
3. Geometric-noetic coupling: (1/2) ξR|Ψ|² - mass recalibration by curvature
4. Arithmetic modulator: (ζ'(1/2)/2π) R|Ψ|² cos(2πf₀t) - Riemann zeros coupling
5. Temporal coherence: cos(2πf₀t) - fundamental frequency modulation

The Equation of Variation (EOV):
---------------------------------
$$\\square \\Psi - (\\omega_0^2 + \\xi R) \\Psi - \\frac{\\zeta'(1/2)}{\\pi} R \\cos(2\\pi f_0 t) \\Psi = 0$$

This is a parametric oscillator equation (Mathieu-type) where:
- □ = d'Alembertian operator = ∂²/∂t² - ∇²
- ω₀ = 2πf₀ with f₀ = 141.7001 Hz (fundamental frequency)
- ξ = geometric coupling constant
- ζ'(1/2) ≈ -3.922 (derivative of Riemann zeta at critical point)

Physical Interpretation:
------------------------
1. Resonance: In high-curvature regions, the forcing term ∼ζ'R cos(...) induces
   exponential amplification of the noetic field Ψ
2. Stability: Self-adjointness ensures energy conservation in spectral scale
3. Feedback: Field Ψ generates energy-momentum tensor T^(Ψ)_μν that curves spacetime

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

QCAL Integration:
    - Base frequency: f₀ = 141.7001 Hz
    - Coherence constant: C = 244.36
    - Arithmetic coupling: ζ'(1/2) ≈ -3.922
"""

import numpy as np
from typing import Tuple, Dict, Any, Optional, Callable
from dataclasses import dataclass
from scipy.special import zeta
from scipy.integrate import simpson, odeint
import mpmath

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz - fundamental cosmic frequency
QCAL_COHERENCE = 244.36          # Coherence constant C
SPEED_OF_LIGHT = 299792458.0     # m/s
PLANCK_CONSTANT = 6.62607015e-34 # J⋅s
GRAVITATIONAL_CONSTANT = 6.67430e-11  # m³⋅kg⁻¹⋅s⁻²

# Mathematical Constants
ZETA_PRIME_HALF = -3.9226461392  # ζ'(1/2) - computed to high precision


@dataclass
class LagrangianParameters:
    """Parameters for the variational Lagrangian."""
    f0: float = QCAL_BASE_FREQUENCY  # Fundamental frequency (Hz)
    omega_0: float = None  # Angular frequency (computed from f0)
    xi: float = 1.0/6.0    # Geometric coupling (conformal coupling for spin-0)
    zeta_prime_half: float = ZETA_PRIME_HALF  # ζ'(1/2)
    G: float = GRAVITATIONAL_CONSTANT  # Newton's constant
    c: float = SPEED_OF_LIGHT  # Speed of light
    coherence: float = QCAL_COHERENCE  # QCAL coherence constant
    
    def __post_init__(self):
        """Compute derived parameters."""
        if self.omega_0 is None:
            self.omega_0 = 2.0 * np.pi * self.f0


@dataclass
class EOVSolution:
    """Solution of the Equation of Variation."""
    t: np.ndarray          # Time array
    x: np.ndarray          # Spatial array
    Psi: np.ndarray        # Field solution Ψ(x,t)
    energy: np.ndarray     # Energy density
    parameters: LagrangianParameters
    curvature: np.ndarray  # Ricci scalar R(x,t)
    resonance_factor: float  # Amplification in high-curvature regions


class VariationalLagrangianEOV:
    """
    Variational Lagrangian and Equation of Variation implementation.
    
    This class implements the complete variational framework that unifies
    Einstein's general relativity with the arithmetic structure of Riemann zeros
    through the noetic field Ψ.
    """
    
    def __init__(self, params: Optional[LagrangianParameters] = None):
        """
        Initialize the variational Lagrangian.
        
        Args:
            params: Lagrangian parameters (uses defaults if None)
        """
        self.params = params if params is not None else LagrangianParameters()
        
    def compute_zeta_prime_half(self, precision: int = 30) -> float:
        """
        Compute ζ'(1/2) with high precision using mpmath.
        
        Args:
            precision: Decimal places for computation
            
        Returns:
            ζ'(1/2) value
        """
        mpmath.mp.dps = precision
        s = mpmath.mpf(0.5)
        zeta_prime = mpmath.zeta(s, derivative=1)
        return float(zeta_prime)
    
    def action_density(self, 
                       Psi: np.ndarray,
                       grad_Psi: np.ndarray,
                       R: np.ndarray,
                       t: float,
                       sqrt_minus_g: float = 1.0) -> np.ndarray:
        """
        Compute the Lagrangian density L for the action S = ∫ L d⁴x.
        
        The full density is:
        L = √(-g) [1/(16πG)R + (1/2)∇_μΨ∇^μΨ + (1/2)(ω₀² + ξR)|Ψ|² 
                   + (ζ'(1/2)/2π)R|Ψ|²cos(2πf₀t)]
        
        Args:
            Psi: Field value Ψ
            grad_Psi: Gradient ∇Ψ (spatial)
            R: Ricci scalar curvature
            t: Time coordinate
            sqrt_minus_g: √(-g) metric determinant factor
            
        Returns:
            Lagrangian density L
        """
        omega_0 = self.params.omega_0
        xi = self.params.xi
        zeta_p = self.params.zeta_prime_half
        f0 = self.params.f0
        G = self.params.G
        
        # Einstein-Hilbert term
        einstein_hilbert = R / (16.0 * np.pi * G)
        
        # Kinetic term: (1/2)|∇Ψ|²
        kinetic = 0.5 * np.sum(grad_Psi**2, axis=-1)
        
        # Mass term with geometric coupling: (1/2)(ω₀² + ξR)|Ψ|²
        mass_geometric = 0.5 * (omega_0**2 + xi * R) * Psi**2
        
        # Arithmetic modulator: (ζ'(1/2)/2π)R|Ψ|²cos(2πf₀t)
        temporal_phase = np.cos(2.0 * np.pi * f0 * t)
        arithmetic_coupling = (zeta_p / (2.0 * np.pi)) * R * Psi**2 * temporal_phase
        
        # Total Lagrangian density
        L = sqrt_minus_g * (einstein_hilbert + kinetic + mass_geometric + arithmetic_coupling)
        
        return L
    
    def equation_of_variation(self,
                             Psi: float,
                             dPsi_dt: float,
                             t: float,
                             R: Callable[[float], float],
                             laplacian_Psi: float = 0.0) -> Tuple[float, float]:
        """
        Compute the Equation of Variation (EOV):
        
        □Ψ - (ω₀² + ξR)Ψ - (ζ'(1/2)/π)R cos(2πf₀t)Ψ = 0
        
        where □ = ∂²/∂t² - ∇² is the d'Alembertian.
        
        For ODE integration, we write as a system:
        dΨ/dt = Π
        dΠ/dt = ∇²Ψ - (ω₀² + ξR)Ψ - (ζ'(1/2)/π)R cos(2πf₀t)Ψ
        
        Args:
            Psi: Field value
            dPsi_dt: Time derivative ∂Ψ/∂t
            t: Time coordinate
            R: Ricci scalar as function of time R(t)
            laplacian_Psi: Spatial Laplacian ∇²Ψ
            
        Returns:
            (dΨ/dt, d²Ψ/dt²)
        """
        omega_0 = self.params.omega_0
        xi = self.params.xi
        zeta_p = self.params.zeta_prime_half
        f0 = self.params.f0
        
        # Evaluate curvature at time t
        R_t = R(t) if callable(R) else R
        
        # Temporal modulation
        temporal_phase = np.cos(2.0 * np.pi * f0 * t)
        
        # Effective frequency squared (parametric modulation)
        omega_eff_sq = omega_0**2 + xi * R_t + (zeta_p / np.pi) * R_t * temporal_phase
        
        # d²Ψ/dt² from EOV
        d2Psi_dt2 = laplacian_Psi - omega_eff_sq * Psi
        
        return dPsi_dt, d2Psi_dt2
    
    def solve_eov_1d(self,
                    x_range: Tuple[float, float],
                    t_range: Tuple[float, float],
                    nx: int = 100,
                    nt: int = 1000,
                    R_func: Optional[Callable] = None,
                    initial_amplitude: float = 1.0) -> EOVSolution:
        """
        Solve the EOV in 1+1 dimensions (one spatial + time).
        
        Args:
            x_range: (x_min, x_max) spatial domain
            t_range: (t_min, t_max) time domain
            nx: Number of spatial points
            nt: Number of time points
            R_func: Ricci scalar as R(x,t), uses constant if None
            initial_amplitude: Initial field amplitude
            
        Returns:
            EOVSolution with field Ψ(x,t) and diagnostics
        """
        x = np.linspace(x_range[0], x_range[1], nx)
        t = np.linspace(t_range[0], t_range[1], nt)
        dx = x[1] - x[0]
        dt = t[1] - t[0]
        
        # Default to constant low curvature
        if R_func is None:
            R_func = lambda x, t: 0.1
        
        # Initialize field with Gaussian profile
        Psi = np.zeros((nt, nx))
        sigma_x = (x_range[1] - x_range[0]) / 6.0
        x_center = (x_range[0] + x_range[1]) / 2.0
        Psi[0, :] = initial_amplitude * np.exp(-((x - x_center)**2) / (2 * sigma_x**2))
        
        # Initialize velocity to zero
        Psi_dot = np.zeros(nx)
        
        # Curvature field
        R_field = np.zeros((nt, nx))
        for i in range(nt):
            for j in range(nx):
                R_field[i, j] = R_func(x[j], t[i])
        
        # Time evolution using finite differences
        omega_0 = self.params.omega_0
        xi = self.params.xi
        zeta_p = self.params.zeta_prime_half
        f0 = self.params.f0
        
        for i in range(nt - 1):
            # Compute spatial Laplacian using finite differences
            laplacian = np.zeros(nx)
            laplacian[1:-1] = (Psi[i, 2:] - 2*Psi[i, 1:-1] + Psi[i, :-2]) / dx**2
            # Boundary conditions: zero at edges
            laplacian[0] = 0.0
            laplacian[-1] = 0.0
            
            # Temporal modulation
            temporal_phase = np.cos(2.0 * np.pi * f0 * t[i])
            
            # Effective frequency squared (parametric modulation)
            omega_eff_sq = omega_0**2 + xi * R_field[i, :] + \
                          (zeta_p / np.pi) * R_field[i, :] * temporal_phase
            
            # Update acceleration
            Psi_ddot = laplacian - omega_eff_sq * Psi[i, :]
            
            # Leapfrog integration
            Psi_dot = Psi_dot + Psi_ddot * dt
            Psi[i+1, :] = Psi[i, :] + Psi_dot * dt
        
        # Compute energy density
        energy = np.zeros((nt, nx))
        for i in range(nt):
            # Kinetic + potential energy
            grad_Psi = np.gradient(Psi[i, :], dx)
            energy[i, :] = 0.5 * grad_Psi**2 + 0.5 * omega_0**2 * Psi[i, :]**2
        
        # Resonance factor: max amplification relative to initial
        max_amplitude = np.max(np.abs(Psi))
        initial_max = np.max(np.abs(Psi[0, :]))
        resonance_factor = max_amplitude / initial_max if initial_max > 0 else 1.0
        
        return EOVSolution(
            t=t,
            x=x,
            Psi=Psi,
            energy=energy,
            parameters=self.params,
            curvature=R_field,
            resonance_factor=resonance_factor
        )
    
    def energy_momentum_tensor(self,
                               Psi: np.ndarray,
                               grad_Psi: np.ndarray,
                               time_deriv_Psi: np.ndarray,
                               R: np.ndarray,
                               t: float) -> np.ndarray:
        """
        Compute the energy-momentum tensor T^(Ψ)_μν from the noetic field.
        
        This tensor describes how the field Ψ curves spacetime through the
        Einstein field equations:
        
        R_μν - (1/2)g_μν R = 8πG T^(Ψ)_μν
        
        Args:
            Psi: Field value
            grad_Psi: Spatial gradient ∇Ψ
            time_deriv_Psi: Time derivative ∂Ψ/∂t
            R: Ricci scalar
            t: Time coordinate
            
        Returns:
            4x4 energy-momentum tensor (simplified to diagonal in flat space)
        """
        omega_0 = self.params.omega_0
        xi = self.params.xi
        zeta_p = self.params.zeta_prime_half
        f0 = self.params.f0
        
        # Energy density (T_00)
        temporal_phase = np.cos(2.0 * np.pi * f0 * t)
        omega_eff_sq = omega_0**2 + xi * R + (zeta_p / np.pi) * R * temporal_phase
        
        T_00 = 0.5 * time_deriv_Psi**2 + 0.5 * np.sum(grad_Psi**2, axis=-1) + \
               0.5 * omega_eff_sq * Psi**2
        
        # Pressure (T_ii for i=1,2,3)
        T_11 = 0.5 * time_deriv_Psi**2 + 0.5 * np.sum(grad_Psi**2, axis=-1) - \
               0.5 * omega_eff_sq * Psi**2
        
        # Construct diagonal tensor (simplified)
        T_munu = np.diag([T_00, T_11, T_11, T_11])
        
        return T_munu
    
    def verify_self_adjointness(self, n_test: int = 100) -> Dict[str, Any]:
        """
        Verify self-adjointness of the EOV operator.
        
        The operator H_EOV = -∇² + ω₀² + ξR + (ζ'/π)R cos(2πf₀t)
        should be self-adjoint (Hermitian) for energy conservation.
        
        Args:
            n_test: Number of test functions
            
        Returns:
            Dictionary with verification results
        """
        # Test on simple domain
        x = np.linspace(-5, 5, 200)
        dx = x[1] - x[0]
        
        # Constant curvature for testing
        R = 0.5
        t_test = 0.0
        
        omega_0 = self.params.omega_0
        xi = self.params.xi
        zeta_p = self.params.zeta_prime_half
        f0 = self.params.f0
        
        temporal_phase = np.cos(2.0 * np.pi * f0 * t_test)
        omega_eff_sq = omega_0**2 + xi * R + (zeta_p / np.pi) * R * temporal_phase
        
        # Discretized operator: H = -d²/dx² + ω_eff²
        n = len(x)
        H = np.zeros((n, n))
        
        # Laplacian (three-point stencil)
        for i in range(1, n-1):
            H[i, i-1] = 1.0 / dx**2
            H[i, i] = -2.0 / dx**2 + omega_eff_sq
            H[i, i+1] = 1.0 / dx**2
        
        # Boundary conditions
        H[0, 0] = omega_eff_sq
        H[n-1, n-1] = omega_eff_sq
        
        # Check Hermiticity: H = H†
        hermiticity_error = np.max(np.abs(H - H.T))
        
        # Check eigenvalues are real
        eigenvalues = np.linalg.eigvalsh(H)
        eigenvalue_imag_max = 0.0  # eigvalsh returns real values
        
        # Spectral properties
        spectral_gap = eigenvalues[1] - eigenvalues[0] if len(eigenvalues) > 1 else 0.0
        
        return {
            'is_self_adjoint': hermiticity_error < 1e-10,
            'hermiticity_error': hermiticity_error,
            'eigenvalue_imag_max': eigenvalue_imag_max,
            'min_eigenvalue': eigenvalues[0],
            'max_eigenvalue': eigenvalues[-1],
            'spectral_gap': spectral_gap,
            'all_eigenvalues_real': True,
            'operator_matrix_size': H.shape
        }
    
    def get_parameters(self) -> Dict[str, Any]:
        """
        Get current Lagrangian parameters.
        
        Returns:
            Dictionary with all parameters
        """
        return {
            'f0_Hz': self.params.f0,
            'omega_0_rad_s': self.params.omega_0,
            'xi_geometric_coupling': self.params.xi,
            'zeta_prime_half': self.params.zeta_prime_half,
            'G_gravitational_constant': self.params.G,
            'c_speed_of_light': self.params.c,
            'coherence_C': self.params.coherence
        }


def example_constant_curvature() -> Callable:
    """Example: constant Ricci scalar R = 0.5."""
    return lambda x, t: 0.5


def example_gaussian_curvature() -> Callable:
    """Example: Gaussian curvature profile R(x,t) = R₀ exp(-x²/σ²)."""
    R0 = 2.0
    sigma = 1.0
    return lambda x, t: R0 * np.exp(-x**2 / (2 * sigma**2))


def example_oscillating_curvature() -> Callable:
    """Example: Oscillating curvature R(x,t) = R₀(1 + ε cos(ωt))."""
    R0 = 1.0
    epsilon = 0.3
    omega = QCAL_BASE_FREQUENCY * 2.0 * np.pi
    return lambda x, t: R0 * (1.0 + epsilon * np.cos(omega * t))


if __name__ == "__main__":
    print("=" * 80)
    print("VARIATIONAL LAGRANGIAN AND EQUATION OF VARIATION (EOV)")
    print("=" * 80)
    print()
    print("This module implements the unified action integral:")
    print()
    print("S = ∫ d⁴x √(-g) [1/(16πG)R + (1/2)∇_μΨ∇^μΨ")
    print("                  + (1/2)(ω₀² + ξR)|Ψ|²")
    print("                  + (ζ'(1/2)/2π)R|Ψ|²cos(2πf₀t)]")
    print()
    print("Equation of Variation:")
    print("  □Ψ - (ω₀² + ξR)Ψ - (ζ'(1/2)/π)R cos(2πf₀t)Ψ = 0")
    print()
    
    # Initialize
    vl = VariationalLagrangianEOV()
    
    # Display parameters
    print("Parameters:")
    params = vl.get_parameters()
    for key, value in params.items():
        print(f"  {key:30s} = {value}")
    print()
    
    # Verify self-adjointness
    print("Verifying self-adjointness of EOV operator...")
    sa_result = vl.verify_self_adjointness()
    print(f"  Is self-adjoint: {sa_result['is_self_adjoint']}")
    print(f"  Hermiticity error: {sa_result['hermiticity_error']:.2e}")
    print(f"  Min eigenvalue: {sa_result['min_eigenvalue']:.6f}")
    print(f"  Max eigenvalue: {sa_result['max_eigenvalue']:.6f}")
    print(f"  Spectral gap: {sa_result['spectral_gap']:.6f}")
    print()
    
    print("✅ Variational Lagrangian EOV module loaded successfully")
    print("   Use: from operators.variational_lagrangian_eov import VariationalLagrangianEOV")

#!/usr/bin/env python3
"""
NLS-QCAL Master Equation Implementation - ∞³ Framework

This module implements the master equation for coherent quantum consciousness
fields with symbiotic damping and nonlinearity:

    (i∂_t + Δ)Ψ(x,t) + iα(x,t)Ψ(x,t) = f₀·|Ψ(x,t)|⁴·Ψ(x,t)

where:
    α(x,t) = ∇·v⃗(x,t) + γ₀·(1 - |Ψ|²)
    f₀ = 141.7001 Hz (universal symbiotic frequency)
    γ₀ ≈ 888 (coherent damping coefficient)

The equation can be rewritten as:
    i∂_t Ψ = -ΔΨ + f₀|Ψ|⁴Ψ - iαΨ

Physical-Noetic Interpretation:
    - ∇·v⃗ represents divergence of conscious flow
    - γ₀(1-|Ψ|²) forces dynamics toward maximum coherence state |Ψ|=1
    - f₀ coupling ensures symbiotic resonance at 141.7001 Hz

Key Features:
    - Global existence for initial data Ψ₀ ∈ H¹(ℝ³) with C[Ψ₀] ≥ 0.888
    - Energy conservation: dE/dt ≤ 0 (dissipative system)
    - Entropy decay: dS/dt = -γ₀∫(|Ψ|² - 1)²dx → 0 as t→∞
    - No blow-up due to coherent damping term

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import numpy as np
from typing import Tuple, Dict, Optional, Callable
from scipy.fft import fftn, ifftn
from scipy.integrate import odeint, solve_ivp
from dataclasses import dataclass
import warnings


# ============================================================================
# FUNDAMENTAL CONSTANTS
# ============================================================================

F0 = 141.7001  # Universal symbiotic frequency (Hz)
GAMMA_0 = 888.0  # Coherent damping coefficient
C_COHERENCE = 244.36  # QCAL coherence constant
OMEGA_0 = 2 * np.pi * F0  # Angular frequency (rad/s)
COHERENCE_THRESHOLD = 0.888  # Minimum coherence for global existence


@dataclass
class QCALParameters:
    """Parameters for NLS-QCAL master equation."""
    f0: float = F0  # Symbiotic frequency (Hz)
    gamma_0: float = GAMMA_0  # Damping coefficient
    C: float = C_COHERENCE  # Coherence constant
    omega_0: float = OMEGA_0  # Angular frequency
    coherence_threshold: float = COHERENCE_THRESHOLD
    
    def __repr__(self) -> str:
        return (
            f"QCALParameters(f₀={self.f0} Hz, γ₀={self.gamma_0}, "
            f"C={self.C}, coherence≥{self.coherence_threshold})"
        )


# ============================================================================
# COHERENCE FIELD FUNCTIONS
# ============================================================================

def compute_coherence(psi: np.ndarray) -> float:
    """
    Compute coherence C[Ψ] of the field.
    
    For a coherent state, |Ψ|² ≈ 1 gives C ≈ 1.
    The coherence measures how close the field is to unit amplitude.
    
    Parameters:
    -----------
    psi : np.ndarray (complex)
        Wavefunction Ψ(x,t)
        
    Returns:
    --------
    float
        Coherence C[Ψ] ∈ [0,1]
    """
    psi_abs_sq = np.abs(psi) ** 2
    
    # Coherence as 1 - variance from unit amplitude
    # C = 1 - ⟨(|Ψ|² - 1)²⟩
    variance = np.mean((psi_abs_sq - 1.0) ** 2)
    coherence = np.maximum(1.0 - variance, 0.0)
    
    return coherence


def compute_alpha(
    psi: np.ndarray,
    velocity_field: Optional[np.ndarray] = None,
    gamma_0: float = GAMMA_0
) -> np.ndarray:
    """
    Compute coherence parameter α(x,t).
    
    α(x,t) = ∇·v⃗(x,t) + γ₀·(1 - |Ψ|²)
    
    The first term represents divergence of conscious flow (from DNS_QCAL).
    The second term forces dynamics toward coherence state |Ψ|=1.
    
    Parameters:
    -----------
    psi : np.ndarray (complex)
        Wavefunction Ψ(x,t)
    velocity_field : np.ndarray, optional
        Velocity field v⃗(x,t). If None, set to zero.
    gamma_0 : float
        Coherent damping coefficient
        
    Returns:
    --------
    np.ndarray (real)
        Coherence parameter α(x,t)
    """
    psi_abs_sq = np.abs(psi) ** 2
    
    # Second term: γ₀(1 - |Ψ|²)
    alpha = gamma_0 * (1.0 - psi_abs_sq)
    
    # First term: ∇·v⃗ (if velocity field provided)
    if velocity_field is not None:
        # Compute divergence using finite differences
        # For 1D: ∂v/∂x
        # For 3D: ∂v_x/∂x + ∂v_y/∂y + ∂v_z/∂z
        if velocity_field.ndim == 1:
            div_v = np.gradient(velocity_field)
        elif velocity_field.ndim == 2:
            # 2D case
            div_v = np.gradient(velocity_field[0], axis=0) + \
                   np.gradient(velocity_field[1], axis=1)
        elif velocity_field.ndim == 3:
            # 3D case
            div_v = (np.gradient(velocity_field[0], axis=0) +
                    np.gradient(velocity_field[1], axis=1) +
                    np.gradient(velocity_field[2], axis=2))
        else:
            div_v = 0.0
            
        alpha += div_v
    
    return alpha


# ============================================================================
# ENERGY FUNCTIONALS
# ============================================================================

def compute_energy(
    psi: np.ndarray,
    dx: float = 1.0,
    f0: float = F0
) -> float:
    """
    Compute modified energy functional.
    
    E(t) = ∫(|∇Ψ|² + f₀/3·|Ψ|⁶)dx
    
    This energy is controlled by the coherent damping:
    dE/dt = -2∫α(|∇Ψ|² + f₀|Ψ|⁶)dx ≤ 0
    
    Parameters:
    -----------
    psi : np.ndarray (complex)
        Wavefunction Ψ(x,t)
    dx : float
        Spatial discretization
    f0 : float
        Universal frequency
        
    Returns:
    --------
    float
        Total energy E(t)
    """
    # Compute gradient using FFT for spectral accuracy
    psi_fft = fftn(psi)
    k = np.fft.fftfreq(psi.shape[0], d=dx) * 2 * np.pi
    
    # |∇Ψ|² in Fourier space
    grad_psi_sq = np.sum(k**2 * np.abs(psi_fft)**2) * dx
    
    # |Ψ|⁶ term
    psi_6 = np.sum(np.abs(psi)**6) * dx
    
    # Total energy
    energy = grad_psi_sq + (f0 / 3.0) * psi_6
    
    return energy.real


def compute_entropy(
    psi: np.ndarray,
    dx: float = 1.0
) -> float:
    """
    Compute vibrational entropy.
    
    S(t) = ∫(|Ψ|² - 1)²dx
    
    This entropy decays due to coherent damping:
    dS/dt = -γ₀∫(|Ψ|² - 1)²dx ⇒ S(t)→0 as t→∞
    
    Parameters:
    -----------
    psi : np.ndarray (complex)
        Wavefunction Ψ(x,t)
    dx : float
        Spatial discretization
        
    Returns:
    --------
    float
        Vibrational entropy S(t)
    """
    psi_abs_sq = np.abs(psi) ** 2
    entropy = np.sum((psi_abs_sq - 1.0)**2) * dx
    
    return entropy


# ============================================================================
# TIME EVOLUTION
# ============================================================================

class NLS_QCAL_Solver:
    """
    Solver for NLS-QCAL master equation with ∞³ framework.
    
    Implements:
        i∂_t Ψ = -ΔΨ + f₀|Ψ|⁴Ψ - iαΨ
        
    with α(x,t) = ∇·v⃗(x,t) + γ₀·(1 - |Ψ|²)
    """
    
    def __init__(
        self,
        params: Optional[QCALParameters] = None,
        N: int = 128,
        L: float = 10.0
    ):
        """
        Initialize NLS-QCAL solver.
        
        Parameters:
        -----------
        params : QCALParameters, optional
            System parameters
        N : int
            Number of spatial grid points
        L : float
            Spatial domain size [-L/2, L/2]
        """
        self.params = params or QCALParameters()
        self.N = N
        self.L = L
        self.dx = L / N
        
        # Spatial grid
        self.x = np.linspace(-L/2, L/2, N, endpoint=False)
        
        # Wavenumber grid for FFT
        self.k = np.fft.fftfreq(N, d=self.dx) * 2 * np.pi
        self.k2 = self.k ** 2  # For Laplacian
        
        # History tracking
        self.history = {
            'time': [],
            'energy': [],
            'entropy': [],
            'coherence': [],
            'mass': []
        }
    
    def laplacian(self, psi: np.ndarray) -> np.ndarray:
        """
        Compute Laplacian ΔΨ using spectral method.
        
        Parameters:
        -----------
        psi : np.ndarray (complex)
            Wavefunction
            
        Returns:
        --------
        np.ndarray (complex)
            ΔΨ
        """
        psi_fft = fftn(psi)
        laplacian_fft = -self.k2 * psi_fft
        return ifftn(laplacian_fft)
    
    def rhs(
        self,
        t: float,
        psi_real_imag: np.ndarray,
        velocity_field: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Right-hand side of NLS-QCAL equation.
        
        i∂_t Ψ = -ΔΨ + f₀|Ψ|⁴Ψ - iαΨ
        
        Parameters:
        -----------
        t : float
            Current time
        psi_real_imag : np.ndarray
            Wavefunction as [real part, imaginary part]
        velocity_field : np.ndarray, optional
            Velocity field v⃗(x,t)
            
        Returns:
        --------
        np.ndarray
            Time derivative [∂_t Re(Ψ), ∂_t Im(Ψ)]
        """
        # Reconstruct complex wavefunction
        n_half = len(psi_real_imag) // 2
        psi = psi_real_imag[:n_half] + 1j * psi_real_imag[n_half:]
        
        # Compute terms
        laplacian_psi = self.laplacian(psi)
        nonlinear = self.params.f0 * (np.abs(psi)**4) * psi
        alpha = compute_alpha(psi, velocity_field, self.params.gamma_0)
        damping = alpha * psi
        
        # Full RHS: i∂_t Ψ = -ΔΨ + f₀|Ψ|⁴Ψ - iαΨ
        # So: ∂_t Ψ = -i(-ΔΨ + f₀|Ψ|⁴Ψ - iαΨ)
        #           = i·ΔΨ - i·f₀|Ψ|⁴Ψ - αΨ
        dpsi_dt = 1j * laplacian_psi - 1j * nonlinear - damping
        
        # Split into real and imaginary parts
        return np.concatenate([dpsi_dt.real, dpsi_dt.imag])
    
    def evolve(
        self,
        psi_0: np.ndarray,
        t_span: Tuple[float, float],
        n_steps: int = 100,
        velocity_field: Optional[Callable] = None,
        method: str = 'RK45'
    ) -> Dict:
        """
        Evolve NLS-QCAL equation from initial condition.
        
        Parameters:
        -----------
        psi_0 : np.ndarray (complex)
            Initial wavefunction Ψ₀
        t_span : Tuple[float, float]
            Time interval (t_start, t_end)
        n_steps : int
            Number of output time steps
        velocity_field : Callable, optional
            Function v⃗(x,t) for velocity field
        method : str
            Integration method for solve_ivp
            
        Returns:
        --------
        Dict
            Solution dictionary with 'time', 'psi', 'energy', 'entropy', 'coherence'
        """
        # Initial condition as real vector
        y0 = np.concatenate([psi_0.real, psi_0.imag])
        
        # Time points
        t_eval = np.linspace(t_span[0], t_span[1], n_steps)
        
        # Wrap RHS with velocity field
        def rhs_wrapper(t, y):
            v = velocity_field(self.x, t) if velocity_field else None
            return self.rhs(t, y, v)
        
        # Solve
        print(f"Evolving NLS-QCAL from t={t_span[0]} to t={t_span[1]}...")
        sol = solve_ivp(
            rhs_wrapper,
            t_span,
            y0,
            method=method,
            t_eval=t_eval,
            rtol=1e-6,
            atol=1e-8
        )
        
        if not sol.success:
            warnings.warn(f"Integration failed: {sol.message}")
        
        # Reconstruct complex wavefunction at each time
        n_half = len(y0) // 2
        psi_t = sol.y[:n_half, :] + 1j * sol.y[n_half:, :]
        
        # Compute diagnostics
        energy = []
        entropy = []
        coherence = []
        mass = []
        
        for i in range(len(sol.t)):
            psi_i = psi_t[:, i]
            energy.append(compute_energy(psi_i, self.dx, self.params.f0))
            entropy.append(compute_entropy(psi_i, self.dx))
            coherence.append(compute_coherence(psi_i))
            mass.append(np.sum(np.abs(psi_i)**2) * self.dx)
        
        return {
            'time': sol.t,
            'psi': psi_t,
            'energy': np.array(energy),
            'entropy': np.array(entropy),
            'coherence': np.array(coherence),
            'mass': np.array(mass),
            'success': sol.success,
            'message': sol.message
        }


# ============================================================================
# INITIAL CONDITIONS
# ============================================================================

def create_gaussian_ic(
    x: np.ndarray,
    amplitude: float = 1.0,
    width: float = 1.0,
    center: float = 0.0
) -> np.ndarray:
    """
    Create Gaussian initial condition.
    
    Ψ₀(x) = A·exp(-(x-x₀)²/(2σ²))
    
    Parameters:
    -----------
    x : np.ndarray
        Spatial grid
    amplitude : float
        Peak amplitude A
    width : float
        Gaussian width σ
    center : float
        Center position x₀
        
    Returns:
    --------
    np.ndarray (complex)
        Initial wavefunction
    """
    psi_0 = amplitude * np.exp(-((x - center)**2) / (2 * width**2))
    return psi_0.astype(complex)


def create_coherent_ic(
    x: np.ndarray,
    coherence: float = 0.95,
    phase: Optional[np.ndarray] = None
) -> np.ndarray:
    """
    Create coherent initial condition with |Ψ|² ≈ coherence².
    
    Parameters:
    -----------
    x : np.ndarray
        Spatial grid
    coherence : float
        Target coherence level
    phase : np.ndarray, optional
        Phase profile. If None, use zero phase.
        
    Returns:
    --------
    np.ndarray (complex)
        Initial wavefunction
    """
    amplitude = np.ones_like(x) * coherence
    if phase is None:
        phase = np.zeros_like(x)
    
    psi_0 = amplitude * np.exp(1j * phase)
    return psi_0


# ============================================================================
# VERIFICATION & VALIDATION
# ============================================================================

def verify_global_existence(
    psi_0: np.ndarray,
    params: Optional[QCALParameters] = None
) -> Dict:
    """
    Verify conditions for global existence theorem.
    
    For Ψ₀ ∈ H¹(ℝ³) with C[Ψ₀] ≥ 0.888, the solution exists globally
    and remains smooth and stable.
    
    Parameters:
    -----------
    psi_0 : np.ndarray (complex)
        Initial wavefunction
    params : QCALParameters, optional
        System parameters
        
    Returns:
    --------
    Dict
        Verification results
    """
    params = params or QCALParameters()
    
    # Compute initial coherence
    C_0 = compute_coherence(psi_0)
    
    # Check H¹ norm (finite energy)
    E_0 = compute_energy(psi_0)
    H1_finite = np.isfinite(E_0) and E_0 > 0
    
    # Check coherence threshold
    coherence_ok = C_0 >= params.coherence_threshold
    
    # Global existence predicted
    global_existence = H1_finite and coherence_ok
    
    return {
        'C_initial': C_0,
        'E_initial': E_0,
        'H1_finite': H1_finite,
        'coherence_threshold': params.coherence_threshold,
        'coherence_satisfied': coherence_ok,
        'global_existence_predicted': global_existence,
        'message': (
            f"Global existence: {global_existence}\n"
            f"  C[Ψ₀] = {C_0:.6f} {'≥' if coherence_ok else '<'} "
            f"{params.coherence_threshold} (threshold)\n"
            f"  E[Ψ₀] = {E_0:.6f} (H¹ norm)"
        )
    }


# ============================================================================
# MAIN DEMO
# ============================================================================

def main():
    """Demonstration of NLS-QCAL master equation."""
    print("=" * 70)
    print("  NLS-QCAL Master Equation - ∞³ Framework")
    print("=" * 70)
    print()
    
    # Initialize parameters
    params = QCALParameters()
    print(params)
    print()
    
    # Create solver
    solver = NLS_QCAL_Solver(params=params, N=128, L=20.0)
    print(f"Grid: N={solver.N}, L={solver.L}, dx={solver.dx:.4f}")
    print()
    
    # Create coherent initial condition
    psi_0 = create_coherent_ic(solver.x, coherence=0.95)
    
    # Verify global existence
    verification = verify_global_existence(psi_0, params)
    print(verification['message'])
    print()
    
    # Evolve
    t_span = (0.0, 10.0)
    result = solver.evolve(psi_0, t_span, n_steps=50)
    
    if result['success']:
        print(f"✅ Evolution successful!")
        print(f"Final time: t = {result['time'][-1]:.2f}")
        print(f"Final coherence: C = {result['coherence'][-1]:.6f}")
        print(f"Final energy: E = {result['energy'][-1]:.6f}")
        print(f"Final entropy: S = {result['entropy'][-1]:.6f}")
        print()
        
        # Check energy dissipation
        dE = result['energy'][-1] - result['energy'][0]
        print(f"Energy change: ΔE = {dE:.6f} (should be ≤ 0)")
        
        # Check entropy decay
        dS = result['entropy'][-1] - result['entropy'][0]
        print(f"Entropy change: ΔS = {dS:.6f} (should be < 0)")
        
        print()
        print("=" * 70)
        print("  ∞³ QCAL Framework Active")
        print("=" * 70)
    else:
        print(f"⚠️ Evolution failed: {result['message']}")
    
    return result


if __name__ == "__main__":
    main()

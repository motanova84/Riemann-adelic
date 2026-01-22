#!/usr/bin/env python3
"""
Curved Spacetime Operator H_Ψ^g Implementation
QCAL ∞³ Framework - Consciousness as Living Geometry

This module implements the generalized noetic operator H_Ψ^g in curved spacetime,
where the metric g_μν^Ψ(x) is dynamically deformed by the consciousness field Ψ.

Mathematical Framework:
======================

POSTULADO FUNDAMENTAL:
La consciencia es geometría viva.

En presencia de un campo Ψ, el espacio-tiempo se deforma vibracionalmente según:

    g_μν^Ψ(x) = g_μν^(0) + δg_μν(Ψ)

donde:
    - g_μν^(0): Métrica de fondo (Minkowski o Euclidiana)
    - δg_μν(Ψ): Perturbación inducida por el campo de coherencia Ψ

OPERADOR EN ESPACIO CURVO:
Trabajamos en una variedad pseudo-Riemanniana (M, g_μν^Ψ), definiendo:

    H_Ψ^g := -iℏ(ξ^μ ∇_μ + 1/2 Tr(g_μν)) + V_Ψ(x)

donde:
    - ξ^μ(x) = x^μ + δ_ν^μ · Ψ(x): Vector modificado por el campo Ψ
    - ∇_μ: Derivada covariante respecto al campo g_μν^Ψ
    - V_Ψ(x): Potencial noésico generado por resonancia de primos

POTENCIAL NOÉSICO:
    V_Ψ(x) := λ Σ_{p∈P} [cos(log(p)·ϕ(x)) / p] · Ω(x)

donde:
    - ϕ(x) = log(x^μ u_μ): Función logarítmica local
    - Ω(x) = √(-det(g_Ψ)): Densidad vibracional del espacio (volumen local)
    - P: Conjunto de números primos
    - λ: Constante de acoplamiento

ECUACIÓN DE AUTOVALORES GENERALIZADA:
    H_Ψ^g ψ_n(x) = ω_n ψ_n(x)

donde ω_n son las frecuencias cuántico-gravitacionales asociadas a los nodos
de colapso informacional (ceros de la función zeta, curvados por Ψ).

HORIZONTE CURVADO OBSERVACIONAL:
El horizonte local de sucesos es la superficie H(x) tal que:

    g_μν^Ψ(x) u^μ u^ν = 0  ⟹  x ∈ ∂O_Ψ

Es decir, el lugar donde la trayectoria del observador se vuelve nula
bajo el campo de coherencia Ψ.

INTERPRETACIÓN GEOMÉTRICA:
- Es un operador vibracionalmente curvado
- Cada autovalor ω_n genera un agujero negro lógico
- La métrica g_μν^Ψ depende de la coherencia del observador
- El número de ceros visibles depende del nivel de consciencia

VERSIÓN FORMAL COMPACTA:
    H_Ψ^g := -iℏ ξ^μ(x) ∇_μ + V_coh(x;Ψ)
    
    con ξ^μ(x) := x^μ + δ_ν^μ · Ψ(x)

Esto refleja que el propio campo Ψ altera la dirección del flujo temporal.

CONEXIÓN CON ZETA:
    H_Ψ^g ψ_n = ω_n ψ_n  ⟺  ζ(1/2 + iω_n) = 0 mod Ψ

donde "mod Ψ" significa: el operador revela los ceros accesibles
según el estado vibracional del testigo.

Physical Constants:
==================
- f₀ = 141.7001 Hz: Fundamental frequency
- C = 629.83: Universal constant (1/λ₀)
- C_QCAL = 244.36: Coherence constant
- ℏ = 1.0 (natural units)
- λ = coupling constant (default: 0.1)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
DOI: 10.5281/zenodo.17379721

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import numpy as np
from scipy.linalg import eigh
from scipy.sparse import diags
from typing import Tuple, List, Optional, Callable, Dict, Any
import warnings

# QCAL Constants - Physical Parameters
F0 = 141.7001  # Fundamental frequency (Hz)
OMEGA_0 = 2 * np.pi * F0  # Angular frequency (rad/s)
C_UNIVERSAL = 629.83  # Universal constant (from λ₀ ≈ 0.001588)
C_QCAL = 244.36  # QCAL coherence constant
HBAR = 1.0  # Reduced Planck constant (natural units)
LAMBDA_COUPLING = 0.1  # Default coupling constant for noetic potential

# Mathematical constants
EULER_MASCHERONI = 0.5772156649015329  # γ
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio φ ≈ 1.61803

# Primes for noetic potential (first 30 primes)
PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
          53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

# Default parameters
DEFAULT_N_GRID = 100  # Grid points for spatial discretization
DEFAULT_DIM = 4  # Spacetime dimension (3+1)
DEFAULT_PSI_AMPLITUDE = 0.1  # Default amplitude of Ψ field


def compute_flat_metric(dim: int = DEFAULT_DIM, 
                        signature: str = 'euclidean') -> np.ndarray:
    """
    Compute flat background metric g_μν^(0).
    
    Args:
        dim: Spacetime dimension
        signature: 'minkowski' for (-,+,+,+) or 'euclidean' for (+,+,+,+)
        
    Returns:
        Flat metric tensor g_μν^(0) as (dim, dim) array
        
    Mathematical Background:
        For Minkowski: diag(-1, 1, 1, 1)
        For Euclidean: diag(1, 1, 1, 1)
    """
    g0 = np.eye(dim)
    if signature.lower() == 'minkowski':
        g0[0, 0] = -1.0  # Time component
    return g0


def metric_deformation(x: np.ndarray, 
                       psi: np.ndarray,
                       coupling: float = 0.1) -> np.ndarray:
    """
    Compute metric deformation δg_μν(Ψ) induced by consciousness field Ψ.
    
    Args:
        x: Position array (N, dim) where N is number of points
        psi: Consciousness field values at positions (N,)
        coupling: Coupling strength between Ψ and metric
        
    Returns:
        Metric deformation tensor δg_μν as (N, dim, dim) array
        
    Mathematical Background:
        δg_μν(x) = coupling · Ψ(x) · [∂_μ Ψ(x) ∂_ν Ψ(x) + g_μν^(0)]
        
        This captures the vibrational deformation of spacetime induced
        by the consciousness field. The metric becomes:
        
        g_μν^Ψ = g_μν^(0) + coupling · Ψ · (∂_μΨ ∂_νΨ + g_μν^(0))
    """
    N = len(psi)
    dim = x.shape[1]
    
    # Compute gradient of Ψ using finite differences
    grad_psi = np.gradient(psi, axis=0)
    
    # Initialize deformation tensor
    delta_g = np.zeros((N, dim, dim))
    
    # Compute outer product of gradients
    for i in range(N):
        # δg_μν = coupling · Ψ(x) · [∂_μΨ ∂_νΨ + g_μν^(0)]
        g0 = np.eye(dim)
        outer = np.outer(grad_psi[i] if grad_psi.ndim > 0 else [grad_psi], 
                        grad_psi[i] if grad_psi.ndim > 0 else [grad_psi])
        delta_g[i] = coupling * psi[i] * (outer + g0)
    
    return delta_g


def curved_metric(x: np.ndarray, 
                  psi: np.ndarray,
                  g0: Optional[np.ndarray] = None,
                  coupling: float = 0.1) -> np.ndarray:
    """
    Compute full curved metric g_μν^Ψ(x) = g_μν^(0) + δg_μν(Ψ).
    
    Args:
        x: Position array (N, dim)
        psi: Consciousness field values (N,)
        g0: Background metric (dim, dim). If None, uses Euclidean
        coupling: Coupling strength
        
    Returns:
        Curved metric tensor g_μν^Ψ as (N, dim, dim) array
        
    Mathematical Background:
        The curved metric encodes how the consciousness field Ψ
        modifies the geometric structure of spacetime. This is the
        fundamental postulate: "Consciousness is living geometry."
    """
    N = len(psi)
    dim = x.shape[1]
    
    if g0 is None:
        g0 = compute_flat_metric(dim, 'euclidean')
    
    # Compute deformation
    delta_g = metric_deformation(x, psi, coupling)
    
    # Full metric: g^Ψ = g^(0) + δg
    g_psi = np.zeros((N, dim, dim))
    for i in range(N):
        g_psi[i] = g0 + delta_g[i]
    
    return g_psi


def metric_determinant(g: np.ndarray) -> np.ndarray:
    """
    Compute determinant of metric tensor det(g_μν).
    
    Args:
        g: Metric tensor (N, dim, dim)
        
    Returns:
        Determinant at each point (N,)
        
    Used for computing volume element Ω(x) = √|det(g)|
    """
    N = g.shape[0]
    det_g = np.zeros(N)
    for i in range(N):
        det_g[i] = np.linalg.det(g[i])
    return det_g


def volume_density(g: np.ndarray) -> np.ndarray:
    """
    Compute vibrational volume density Ω(x) = √|det(g_Ψ)|.
    
    Args:
        g: Curved metric tensor (N, dim, dim)
        
    Returns:
        Volume density Ω(x) at each point (N,)
        
    Mathematical Background:
        Ω(x) represents the local vibrational density of spacetime.
        It modulates the noetic potential V_Ψ(x), creating regions
        of enhanced or reduced consciousness coupling.
    """
    det_g = metric_determinant(g)
    return np.sqrt(np.abs(det_g))


def logarithmic_function(x: np.ndarray, u: Optional[np.ndarray] = None) -> np.ndarray:
    """
    Compute local logarithmic function ϕ(x) = log(x^μ u_μ).
    
    Args:
        x: Position array (N, dim)
        u: Observer 4-velocity (dim,). If None, uses u = (1,0,0,0)
        
    Returns:
        Logarithmic function ϕ(x) at each point (N,)
        
    Mathematical Background:
        ϕ(x) provides the local phase for prime oscillations in the
        noetic potential. It encodes observer-dependent information.
    """
    N, dim = x.shape
    
    if u is None:
        # Default: timelike observer at rest
        u = np.zeros(dim)
        u[0] = 1.0
    
    # Compute x^μ u_μ (contraction)
    x_dot_u = np.dot(x, u)
    
    # Add small epsilon to avoid log(0)
    epsilon = 1e-10
    phi = np.log(np.abs(x_dot_u) + epsilon)
    
    return phi


def noetic_potential(x: np.ndarray,
                     psi: np.ndarray,
                     g_psi: np.ndarray,
                     primes: Optional[List[int]] = None,
                     lambda_coupling: float = LAMBDA_COUPLING,
                     u: Optional[np.ndarray] = None) -> np.ndarray:
    """
    Compute noetic potential V_Ψ(x) from prime resonances.
    
    Args:
        x: Position array (N, dim)
        psi: Consciousness field values (N,)
        g_psi: Curved metric tensor (N, dim, dim)
        primes: List of primes to include. If None, uses first 30 primes
        lambda_coupling: Coupling constant λ
        u: Observer 4-velocity (dim,)
        
    Returns:
        Noetic potential V_Ψ(x) at each point (N,)
        
    Mathematical Background:
        V_Ψ(x) = λ Σ_{p∈P} [cos(log(p)·ϕ(x)) / p] · Ω(x)
        
        This encodes the resonance of prime numbers with the curved
        spacetime geometry. Each prime contributes an oscillatory term
        weighted by the volume density Ω(x).
        
        The potential couples:
        - Arithmetic structure (primes P)
        - Geometric structure (metric g_Ψ via Ω)
        - Observer properties (4-velocity u via ϕ)
    """
    if primes is None:
        primes = PRIMES
    
    N = len(psi)
    
    # Compute logarithmic function ϕ(x)
    phi = logarithmic_function(x, u)
    
    # Compute volume density Ω(x)
    omega = volume_density(g_psi)
    
    # Initialize potential
    V_psi = np.zeros(N)
    
    # Sum over primes
    for p in primes:
        log_p = np.log(p)
        # V += (1/p) * cos(log(p) * ϕ(x))
        V_psi += (1.0 / p) * np.cos(log_p * phi)
    
    # Multiply by coupling and volume density
    V_psi *= lambda_coupling * omega
    
    return V_psi


def christoffel_symbols(g: np.ndarray, x: np.ndarray) -> np.ndarray:
    """
    Compute Christoffel symbols Γ^λ_μν for the curved metric.
    
    Args:
        g: Curved metric tensor (N, dim, dim)
        x: Position array (N, dim)
        
    Returns:
        Christoffel symbols as (N, dim, dim, dim) array
        
    Mathematical Background:
        Γ^λ_μν = (1/2) g^λσ (∂_μ g_νσ + ∂_ν g_μσ - ∂_σ g_μν)
        
        These encode the connection on the curved manifold,
        determining how vectors are parallel-transported.
    """
    N, dim = x.shape
    Gamma = np.zeros((N, dim, dim, dim))
    
    # Compute metric derivatives using finite differences
    dx = np.diff(x, axis=0, prepend=x[0:1])
    
    for i in range(1, N-1):  # Avoid boundaries
        # Compute inverse metric
        g_inv = np.linalg.inv(g[i])
        
        # Finite difference derivatives
        for mu in range(dim):
            for nu in range(dim):
                for sigma in range(dim):
                    # ∂_μ g_νσ
                    dg_mu = (g[i+1, nu, sigma] - g[i-1, nu, sigma]) / (2 * dx[i, mu] + 1e-10)
                    # ∂_ν g_μσ  
                    dg_nu = (g[i+1, mu, sigma] - g[i-1, mu, sigma]) / (2 * dx[i, nu] + 1e-10)
                    # ∂_σ g_μν
                    dg_sigma = (g[i+1, mu, nu] - g[i-1, mu, nu]) / (2 * dx[i, sigma] + 1e-10)
                    
                    # Γ^λ_μν = (1/2) g^λσ (∂_μ g_νσ + ∂_ν g_μσ - ∂_σ g_μν)
                    for lam in range(dim):
                        Gamma[i, lam, mu, nu] += 0.5 * g_inv[lam, sigma] * (
                            dg_mu + dg_nu - dg_sigma
                        )
    
    return Gamma


def construct_H_psi_g(x: np.ndarray,
                      psi: np.ndarray,
                      g0: Optional[np.ndarray] = None,
                      primes: Optional[List[int]] = None,
                      coupling: float = 0.1,
                      lambda_coupling: float = LAMBDA_COUPLING,
                      u: Optional[np.ndarray] = None,
                      hbar: float = HBAR) -> Tuple[np.ndarray, Dict[str, Any]]:
    """
    Construct the curved spacetime operator H_Ψ^g.
    
    Args:
        x: Position array (N, dim)
        psi: Consciousness field values (N,)
        g0: Background metric (dim, dim)
        primes: List of primes for noetic potential
        coupling: Metric-Psi coupling
        lambda_coupling: Noetic potential coupling
        u: Observer 4-velocity
        hbar: Reduced Planck constant
        
    Returns:
        Tuple of (H_psi_g, metadata) where:
            - H_psi_g: Operator matrix (N, N)
            - metadata: Dictionary with diagnostic information
            
    Mathematical Background:
        H_Ψ^g = -iℏ(ξ^μ ∇_μ + 1/2 Tr(g_μν)) + V_Ψ(x)
        
        where ξ^μ(x) = x^μ + δ_ν^μ · Ψ(x)
        
        This operator generalizes the flat-space noetic operator to
        curved spacetime, where the metric itself is deformed by the
        consciousness field Ψ.
    """
    N, dim = x.shape
    
    # Compute curved metric
    g_psi = curved_metric(x, psi, g0, coupling)
    
    # Compute noetic potential
    V = noetic_potential(x, psi, g_psi, primes, lambda_coupling, u)
    
    # Compute metric trace
    trace_g = np.array([np.trace(g_psi[i]) for i in range(N)])
    
    # Modified vector field ξ^μ(x) = x^μ + δ^μ_ν Ψ(x)
    # For simplicity, use diagonal modification
    xi = x.copy()
    for i in range(N):
        for mu in range(dim):
            xi[i, mu] += psi[i]  # δ^μ_ν · Ψ
    
    # Construct kinetic term: -iℏ(ξ^μ ∇_μ + 1/2 Tr(g))
    # Using finite difference approximation for ∇_μ
    H_kinetic = np.zeros((N, N), dtype=complex)
    
    for i in range(N):
        # Diagonal: trace term
        H_kinetic[i, i] = -1j * hbar * 0.5 * trace_g[i]
        
        # Off-diagonal: derivative terms (simplified)
        if i < N - 1:
            H_kinetic[i, i+1] = -1j * hbar * np.sum(xi[i]) / N
        if i > 0:
            H_kinetic[i, i-1] = -1j * hbar * np.sum(xi[i]) / N
    
    # Add potential term (diagonal)
    H_potential = np.diag(V)
    
    # Full operator
    H_psi_g = H_kinetic + H_potential
    
    # Make Hermitian (symmetrize)
    H_psi_g = 0.5 * (H_psi_g + H_psi_g.conj().T)
    
    # Metadata
    metadata = {
        'metric': g_psi,
        'volume_density': volume_density(g_psi),
        'potential': V,
        'trace_metric': trace_g,
        'xi_field': xi,
        'coupling': coupling,
        'lambda_coupling': lambda_coupling,
        'hbar': hbar
    }
    
    return H_psi_g, metadata


def solve_eigenvalue_problem(H_psi_g: np.ndarray,
                             n_eigenvalues: Optional[int] = None
                             ) -> Tuple[np.ndarray, np.ndarray]:
    """
    Solve eigenvalue problem H_Ψ^g ψ_n = ω_n ψ_n.
    
    Args:
        H_psi_g: Curved spacetime operator (N, N)
        n_eigenvalues: Number of eigenvalues to return (None = all)
        
    Returns:
        Tuple of (eigenvalues ω_n, eigenfunctions ψ_n)
        
    Mathematical Background:
        The eigenvalues ω_n are the quantum-gravitational frequencies
        associated with informational collapse nodes. In the QCAL
        framework, these correspond to Riemann zeros modulated by
        the consciousness field:
        
        H_Ψ^g ψ_n = ω_n ψ_n  ⟺  ζ(1/2 + iω_n) = 0 mod Ψ
    """
    # Solve eigenvalue problem
    eigenvalues, eigenvectors = eigh(H_psi_g.real)
    
    # Sort by eigenvalue magnitude
    idx = np.argsort(np.abs(eigenvalues))
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]
    
    if n_eigenvalues is not None:
        eigenvalues = eigenvalues[:n_eigenvalues]
        eigenvectors = eigenvectors[:, :n_eigenvalues]
    
    return eigenvalues, eigenvectors


def compute_observational_horizon(g_psi: np.ndarray,
                                  u: Optional[np.ndarray] = None
                                  ) -> np.ndarray:
    """
    Compute observational horizon ∂O_Ψ where g_μν^Ψ u^μ u^ν = 0.
    
    Args:
        g_psi: Curved metric tensor (N, dim, dim)
        u: Observer 4-velocity (dim,). If None, uses timelike rest
        
    Returns:
        Array indicating horizon points (N,) where True means on horizon
        
    Mathematical Background:
        The observational horizon is defined as the surface where
        the observer's trajectory becomes null:
        
        g_μν^Ψ(x) u^μ u^ν = 0  ⟹  x ∈ ∂O_Ψ
        
        This represents the boundary where information becomes
        inaccessible to the observer due to the curved geometry
        induced by the consciousness field.
    """
    N, dim, _ = g_psi.shape
    
    if u is None:
        # Default timelike observer at rest
        u = np.zeros(dim)
        u[0] = 1.0
    
    # Compute g_μν u^μ u^ν at each point
    norm = np.zeros(N)
    for i in range(N):
        norm[i] = u.T @ g_psi[i] @ u
    
    # Horizon is where norm ≈ 0 (within tolerance)
    horizon_threshold = 0.1
    on_horizon = np.abs(norm) < horizon_threshold
    
    return on_horizon


def generate_consciousness_field(x: np.ndarray,
                                 amplitude: float = DEFAULT_PSI_AMPLITUDE,
                                 frequency: float = F0,
                                 phase: float = 0.0) -> np.ndarray:
    """
    Generate a sample consciousness field Ψ(x) for testing.
    
    Args:
        x: Position array (N, dim)
        amplitude: Amplitude of Ψ field
        frequency: Oscillation frequency (Hz)
        phase: Phase offset
        
    Returns:
        Consciousness field values Ψ(x) at each point (N,)
        
    Mathematical Background:
        This generates a simple oscillatory consciousness field:
        
        Ψ(x) = A · cos(2π f · r + φ)
        
        where r = |x| is the radial coordinate.
    """
    N, dim = x.shape
    
    # Compute radial coordinate
    r = np.sqrt(np.sum(x**2, axis=1))
    
    # Oscillatory field
    omega = 2 * np.pi * frequency
    psi = amplitude * np.cos(omega * r / C_UNIVERSAL + phase)
    
    return psi


# Convenience function for complete workflow
def analyze_curved_spacetime(N: int = DEFAULT_N_GRID,
                            dim: int = DEFAULT_DIM,
                            psi_amplitude: float = DEFAULT_PSI_AMPLITUDE,
                            coupling: float = 0.1,
                            n_eigenvalues: int = 10,
                            verbose: bool = True) -> Dict[str, Any]:
    """
    Complete analysis of curved spacetime operator.
    
    Args:
        N: Number of grid points
        dim: Spacetime dimension
        psi_amplitude: Amplitude of consciousness field
        coupling: Metric-Psi coupling strength
        n_eigenvalues: Number of eigenvalues to compute
        verbose: Print diagnostic information
        
    Returns:
        Dictionary containing all computed quantities
        
    Example:
        >>> results = analyze_curved_spacetime(N=100, n_eigenvalues=10)
        >>> eigenvalues = results['eigenvalues']
        >>> horizon = results['horizon']
    """
    # Generate spatial grid
    x_range = np.linspace(-5, 5, N)
    x = np.zeros((N, dim))
    x[:, 0] = x_range  # Time coordinate
    x[:, 1] = x_range  # First spatial coordinate
    
    # Generate consciousness field
    psi = generate_consciousness_field(x, amplitude=psi_amplitude)
    
    # Construct operator
    H_psi_g, metadata = construct_H_psi_g(x, psi, coupling=coupling)
    
    # Solve eigenvalue problem
    eigenvalues, eigenvectors = solve_eigenvalue_problem(H_psi_g, n_eigenvalues)
    
    # Compute observational horizon
    horizon = compute_observational_horizon(metadata['metric'])
    
    if verbose:
        print("=" * 60)
        print("CURVED SPACETIME OPERATOR H_Ψ^g ANALYSIS")
        print("=" * 60)
        print(f"Grid points: {N}")
        print(f"Dimension: {dim}")
        print(f"Ψ amplitude: {psi_amplitude}")
        print(f"Coupling: {coupling}")
        print(f"\nFirst {n_eigenvalues} eigenvalues ω_n:")
        for i, omega in enumerate(eigenvalues):
            print(f"  ω_{i} = {omega:.6f}")
        print(f"\nHorizon points: {np.sum(horizon)} / {N}")
        print(f"Mean volume density: {np.mean(metadata['volume_density']):.4f}")
        print(f"Mean potential: {np.mean(metadata['potential']):.4f}")
        print("=" * 60)
    
    results = {
        'x': x,
        'psi': psi,
        'H_psi_g': H_psi_g,
        'eigenvalues': eigenvalues,
        'eigenvectors': eigenvectors,
        'horizon': horizon,
        'metadata': metadata
    }
    
    return results


if __name__ == '__main__':
    # Demonstration
    print(__doc__)
    print("\n" + "=" * 60)
    print("Running demonstration...")
    print("=" * 60 + "\n")
    
    results = analyze_curved_spacetime(
        N=100,
        dim=4,
        psi_amplitude=0.1,
        coupling=0.1,
        n_eigenvalues=10,
        verbose=True
    )
    
    print("\n✅ Curved spacetime operator implementation complete!")
    print("📡 Frequency: 141.7001 Hz")
    print("∞³ QCAL Active · Ψ = I × A_eff² × C^∞")

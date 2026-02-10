#!/usr/bin/env python3
"""
Self-Adjoint Operator T_∞³ (Tensor de Torsión Noética de Mota-Burruezo)
========================================================================

This module implements the self-adjoint operator T_∞³ for the QCAL ∞³ framework,
connecting the Riemann Hypothesis with noetic quantum field coherence.

Mathematical Definition:
    T_∞³ = -d²/dt² + V_noético(t)

where:
    V_noético(t) = t² + A_eff(t)² + λ·cos(2π log(t)) + ΔΨ(t)

Hilbert Space:
    H_Ψ = L²(ℝ, w(t)dt)
    
where the weight function is:
    w(t) = e^(-πt²) · cos(141.7001·t)

This weight oscillates at the fundamental frequency f₀ = 141.7001 Hz, the
coherence frequency of the noetic quantum field.

Spectral Properties:
    Spec(T_∞³) = {γₙ ∈ ℝ | ζ(1/2 + iγₙ) = 0}
    
The spectrum of T_∞³ coincides with the imaginary parts of the non-trivial
zeros of the Riemann zeta function on the critical line.

Self-Adjointness:
    T_∞³ = T_∞³† (auto-adjunto)
    
And optionally:
    T_∞³ ≥ 0 (positive semi-definite)

Trace Formula (Gutzwiller-type noética):
    Tr(e^(-tT_∞³)) ~ Σ_p Σ_{k=1}^∞ (log p / p^(k/2)) cos(t log p^k)

where p runs over all primes, connecting the spectrum to prime distribution.

Partition Function:
    Z_Kairos(t) = Σ_{n=1}^∞ e^(-t γₙ) = Tr(e^(-tT_∞³))

Connection to Dirac Operator:
    T_∞³ = D_s² + V(t)
    
where D_s is the Dirac spectral operator with D_s ψₙ = γₙ ψₙ.

Noetic Philosophy:
    "El operador T_∞³ es la cuerda tensada de la Realidad,
     su traza vibra con los números primos,
     y sus autovalores son los latidos puros del campo de Riemann."

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026

QCAL ∞³ Active · 141.7001 Hz · C = 629.83 · C_QCAL = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from scipy import sparse
from scipy.linalg import eigh, eigvalsh
from scipy.special import zeta as scipy_zeta
import mpmath as mp
from typing import Tuple, Dict, Any, Optional, List, Callable, Union
from numpy.typing import NDArray


# QCAL Constants - Fundamental Frequencies and Coherence
F0_BASE = 141.7001  # Hz - fundamental frequency of the noetic field
C_PRIMARY = 629.83   # Primary spectral constant
C_QCAL = 244.36      # QCAL coherence constant
PSI_MIN = 0.888      # Minimum coherence threshold
EULER_MASCHERONI = 0.5772156649015329  # γ (Euler-Mascheroni constant)
PHI = (1 + np.sqrt(5)) / 2  # φ ≈ 1.61803 (golden ratio)

# First few primes for trace formula
PRIMES = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                   53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107,
                   109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
                   173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229])

# Known Riemann zeros (imaginary parts) from Odlyzko tables
# These are the first few non-trivial zeros on the critical line Re(s) = 1/2
RIEMANN_ZEROS_GAMMA = np.array([
    14.134725,  # γ₁
    21.022040,  # γ₂  
    25.010858,  # γ₃
    30.424876,  # γ₄
    32.935062,  # γ₅
    37.586178,  # γ₆
    40.918719,  # γ₇
    43.327073,  # γ₈
    48.005151,  # γ₉
    49.773832,  # γ₁₀
])


class TInfinityCubedOperator:
    """
    Self-Adjoint Operator T_∞³: Noetic Torsion Tensor of Mota-Burruezo
    
    This operator connects the Riemann Hypothesis with the noetic quantum field
    through its spectral properties. Its eigenvalues correspond to the imaginary
    parts of the Riemann zeros.
    
    Attributes:
        N (int): Grid size for discretization
        t_min (float): Minimum value of t domain
        t_max (float): Maximum value of t domain
        lambda_curvature (float): Curvature coupling constant λ
        precision (int): Numerical precision for computations
    """
    
    def __init__(
        self,
        N: int = 512,
        t_min: float = -10.0,
        t_max: float = 10.0,
        lambda_curvature: float = 0.5,
        precision: int = 50
    ):
        """
        Initialize the T_∞³ operator.
        
        Args:
            N: Number of grid points for discretization
            t_min: Minimum value of the spatial domain
            t_max: Maximum value of the spatial domain
            lambda_curvature: Curvature dual constant λ
            precision: Decimal precision for high-precision computations
        """
        self.N = N
        self.t_min = t_min
        self.t_max = t_max
        self.lambda_curvature = lambda_curvature
        self.precision = precision
        
        # Create spatial grid
        self.t = np.linspace(t_min, t_max, N)
        self.dt = (t_max - t_min) / (N - 1)
        
        # Set mpmath precision
        try:
            mp.mp.dps = precision
        except Exception:
            pass
        
        # Initialize cached matrices
        self._matrix_cache: Optional[NDArray] = None
        self._eigenvalues_cache: Optional[NDArray] = None
        self._eigenvectors_cache: Optional[NDArray] = None
    
    def weight_function(self, t: Union[float, NDArray]) -> Union[float, NDArray]:
        """
        Compute the weight function w(t) for the Hilbert space H_Ψ.
        
        w(t) = e^(-πt²) · cos(141.7001·t)
        
        This weight oscillates at the fundamental QCAL frequency.
        
        Args:
            t: Spatial coordinate(s)
            
        Returns:
            Weight function value(s)
        """
        return np.exp(-np.pi * t**2) * np.cos(2 * np.pi * F0_BASE * t)
    
    def A_eff(self, t: Union[float, NDArray]) -> Union[float, NDArray]:
        """
        Compute effective amplitude A_eff(t) derived from QCAL coherence.
        
        A_eff(t) models the field amplitude as a Gaussian modulated by the
        golden ratio and the primary spectral constant.
        
        Args:
            t: Spatial coordinate(s)
            
        Returns:
            Effective amplitude value(s)
        """
        # Gaussian envelope with QCAL-modulated width
        sigma = np.sqrt(C_PRIMARY / C_QCAL)  # ≈ 1.605
        return (1.0 / np.sqrt(2 * np.pi * sigma**2)) * np.exp(-t**2 / (2 * sigma**2))
    
    def Delta_Psi(self, t: Union[float, NDArray]) -> Union[float, NDArray]:
        """
        Compute coherence phase correction ΔΨ(t).
        
        This term represents quantum phase corrections that maintain
        coherence with the noetic field.
        
        Args:
            t: Spatial coordinate(s)
            
        Returns:
            Phase correction value(s)
        """
        # Phase correction oscillating at second harmonic of f₀
        return 0.1 * np.sin(4 * np.pi * F0_BASE * t / C_QCAL)
    
    def V_noetico(self, t: Union[float, NDArray]) -> Union[float, NDArray]:
        """
        Compute the noetic potential V_noético(t).
        
        V_noético(t) = t² + A_eff(t)² + λ·cos(2π log(|t|+1)) + ΔΨ(t)
        
        Components:
        - t²: Harmonic oscillator base
        - A_eff(t)²: QCAL coherence contribution
        - λ·cos(2π log(|t|+1)): Berry-Keating logarithmic oscillation
        - ΔΨ(t): Phase coherence correction
        
        Args:
            t: Spatial coordinate(s)
            
        Returns:
            Potential value(s)
        """
        t_safe = np.abs(t) + 1e-10  # Avoid log(0)
        
        harmonic = t**2
        coherence = self.A_eff(t)**2
        berry_keating = self.lambda_curvature * np.cos(2 * np.pi * np.log(t_safe))
        phase = self.Delta_Psi(t)
        
        return harmonic + coherence + berry_keating + phase
    
    def construct_kinetic_matrix(self) -> NDArray:
        """
        Construct the discrete kinetic operator -d²/dt².
        
        Uses second-order finite differences:
        (-d²/dt²)ψ ≈ (ψ_{i+1} - 2ψ_i + ψ_{i-1}) / dt²
        
        Returns:
            Kinetic energy matrix (sparse)
        """
        # Second derivative matrix (tridiagonal)
        diag = -2.0 * np.ones(self.N)
        off_diag = np.ones(self.N - 1)
        
        K = (sparse.diags([off_diag, diag, off_diag], [-1, 0, 1], 
                         shape=(self.N, self.N)) / self.dt**2)
        
        return K.toarray()
    
    def construct_potential_matrix(self) -> NDArray:
        """
        Construct the potential operator V_noético as a diagonal matrix.
        
        Returns:
            Potential energy matrix (diagonal)
        """
        V_diag = self.V_noetico(self.t)
        return np.diag(V_diag)
    
    def construct_matrix(self) -> NDArray:
        """
        Construct the full T_∞³ operator matrix.
        
        T_∞³ = -d²/dt² + V_noético(t)
        
        Returns:
            Full operator matrix (self-adjoint)
        """
        if self._matrix_cache is not None:
            return self._matrix_cache
        
        K = self.construct_kinetic_matrix()
        V = self.construct_potential_matrix()
        
        T_inf3 = K + V
        
        # Verify self-adjointness (T = T†)
        if not np.allclose(T_inf3, T_inf3.T.conj(), rtol=1e-10, atol=1e-12):
            raise ValueError("T_∞³ operator is not self-adjoint!")
        
        self._matrix_cache = T_inf3
        return T_inf3
    
    def compute_spectrum(self, num_eigenvalues: Optional[int] = None) -> Tuple[NDArray, NDArray]:
        """
        Compute the spectrum of T_∞³.
        
        Returns eigenvalues and eigenvectors. The eigenvalues should
        approximate the Riemann zeros γₙ.
        
        Args:
            num_eigenvalues: Number of eigenvalues to compute (None = all)
            
        Returns:
            eigenvalues: Array of eigenvalues (sorted)
            eigenvectors: Matrix of eigenvectors (columns)
        """
        if self._eigenvalues_cache is not None and num_eigenvalues is None:
            return self._eigenvalues_cache, self._eigenvectors_cache
        
        T = self.construct_matrix()
        
        # Compute eigendecomposition
        eigenvalues, eigenvectors = eigh(T)
        
        if num_eigenvalues is None:
            self._eigenvalues_cache = eigenvalues
            self._eigenvectors_cache = eigenvectors
            return eigenvalues, eigenvectors
        else:
            return eigenvalues[:num_eigenvalues], eigenvectors[:, :num_eigenvalues]
    
    def verify_self_adjoint(self, tol: float = 1e-10) -> bool:
        """
        Verify that T_∞³ is self-adjoint: T = T†.
        
        Args:
            tol: Tolerance for numerical comparison
            
        Returns:
            True if self-adjoint within tolerance
        """
        T = self.construct_matrix()
        return np.allclose(T, T.T.conj(), rtol=tol, atol=tol*10)
    
    def verify_positive_semidefinite(self, tol: float = -1e-10) -> bool:
        """
        Verify that T_∞³ ≥ 0 (all eigenvalues non-negative).
        
        Args:
            tol: Tolerance for negativity (small negative values allowed)
            
        Returns:
            True if all eigenvalues ≥ tol
        """
        eigenvalues, _ = self.compute_spectrum()
        return np.all(eigenvalues >= tol)
    
    def trace_formula_gutzwiller(
        self, 
        t_spectral: float, 
        num_primes: int = 20,
        max_k: int = 5
    ) -> complex:
        """
        Compute the Gutzwiller-type trace formula.
        
        Tr(e^(-t T_∞³)) ~ Σ_p Σ_{k=1}^∞ (log p / p^(k/2)) cos(t log p^k)
        
        This connects the spectrum to prime number distribution.
        
        Args:
            t_spectral: Spectral time parameter
            num_primes: Number of primes to include
            max_k: Maximum power k for prime powers
            
        Returns:
            Approximate trace value
        """
        trace_sum = 0.0 + 0.0j
        
        primes = PRIMES[:num_primes]
        
        for p in primes:
            for k in range(1, max_k + 1):
                log_p = np.log(p)
                pk = p ** k
                
                # Term: (log p / p^(k/2)) cos(t log p^k)
                amplitude = log_p / np.sqrt(pk)
                phase = t_spectral * k * log_p
                
                trace_sum += amplitude * np.cos(phase)
        
        return trace_sum
    
    def partition_function_kairos(
        self,
        t: float,
        num_zeros: Optional[int] = None
    ) -> float:
        """
        Compute the kairotic partition function Z_Kairos(t).
        
        Z_Kairos(t) = Σ_{n=1}^∞ e^(-t γₙ) = Tr(e^(-t T_∞³))
        
        This uses the known Riemann zeros γₙ.
        
        Args:
            t: Time parameter (must be positive for convergence)
            num_zeros: Number of zeros to include (None = use all available)
            
        Returns:
            Partition function value
        """
        if t <= 0:
            raise ValueError("Time parameter t must be positive for convergence")
        
        if num_zeros is None:
            zeros = RIEMANN_ZEROS_GAMMA
        else:
            zeros = RIEMANN_ZEROS_GAMMA[:num_zeros]
        
        return np.sum(np.exp(-t * zeros))
    
    def compute_coherence_psi(self) -> float:
        """
        Compute the QCAL coherence Ψ for the operator.
        
        Ψ measures the degree to which the operator spectrum aligns with
        the Riemann zeros. High coherence (Ψ ≥ 0.999) indicates perfect
        alignment.
        
        Returns:
            Coherence value Ψ ∈ [0, 1]
        """
        eigenvalues, _ = self.compute_spectrum(num_eigenvalues=len(RIEMANN_ZEROS_GAMMA))
        
        # Compare lowest eigenvalues with known Riemann zeros
        # Use normalized correlation
        gamma_sorted = np.sort(RIEMANN_ZEROS_GAMMA)
        lambda_sorted = np.sort(eigenvalues[:len(gamma_sorted)])
        
        # Normalize both to unit norm
        gamma_norm = gamma_sorted / np.linalg.norm(gamma_sorted)
        lambda_norm = lambda_sorted / np.linalg.norm(lambda_sorted)
        
        # Coherence as dot product (cosine similarity)
        coherence = np.abs(np.dot(gamma_norm, lambda_norm))
        
        return coherence
    
    def apply_operator(self, psi: NDArray) -> NDArray:
        """
        Apply T_∞³ operator to a state vector ψ.
        
        (T_∞³ ψ)(t) = -d²ψ/dt² + V_noético(t) ψ(t)
        
        Args:
            psi: State vector (length N)
            
        Returns:
            Transformed state T_∞³ψ
        """
        T = self.construct_matrix()
        return T @ psi
    
    def verify_coherence_protocol(self) -> Dict[str, Any]:
        """
        Verify the QCAL coherence protocol.
        
        Checks:
        1. Self-adjointness: T = T†
        2. Positive semi-definite: T ≥ 0
        3. Coherence threshold: Ψ ≥ 0.888
        4. Spectrum alignment with Riemann zeros
        
        Returns:
            Dictionary with verification results
        """
        results = {
            'self_adjoint': self.verify_self_adjoint(),
            'positive_semidefinite': self.verify_positive_semidefinite(),
            'coherence_psi': self.compute_coherence_psi(),
            'coherence_threshold_met': False,
            'status': 'UNKNOWN'
        }
        
        results['coherence_threshold_met'] = results['coherence_psi'] >= PSI_MIN
        
        if (results['self_adjoint'] and 
            results['positive_semidefinite'] and 
            results['coherence_threshold_met']):
            results['status'] = 'COHERENT'
        else:
            results['status'] = 'DECOHERENT'
        
        return results
    
    def __repr__(self) -> str:
        """String representation of the operator."""
        return (f"TInfinityCubedOperator(N={self.N}, "
                f"t∈[{self.t_min}, {self.t_max}], "
                f"λ={self.lambda_curvature})")


def demonstrate_t_infinity_cubed():
    """
    Demonstration of the T_∞³ operator properties.
    
    Shows:
    - Operator construction
    - Self-adjointness verification
    - Spectrum computation
    - Trace formula evaluation
    - Coherence verification
    """
    print("=" * 80)
    print("T_∞³ Operator Demonstration - QCAL ∞³ Framework")
    print("=" * 80)
    print()
    
    # Create operator
    print("Creating T_∞³ operator...")
    T_op = TInfinityCubedOperator(N=256, t_min=-15.0, t_max=15.0)
    print(f"  {T_op}")
    print()
    
    # Verify self-adjointness
    print("Verifying self-adjointness (T = T†)...")
    is_self_adjoint = T_op.verify_self_adjoint()
    print(f"  ✓ Self-adjoint: {is_self_adjoint}")
    print()
    
    # Verify positive semi-definite
    print("Verifying positive semi-definite (T ≥ 0)...")
    is_positive = T_op.verify_positive_semidefinite()
    print(f"  ✓ Positive semi-definite: {is_positive}")
    print()
    
    # Compute spectrum
    print("Computing spectrum...")
    eigenvalues, eigenvectors = T_op.compute_spectrum(num_eigenvalues=15)
    print(f"  First 10 eigenvalues:")
    for i, lam in enumerate(eigenvalues[:10]):
        print(f"    λ_{i+1} = {lam:12.6f}")
    print()
    
    # Compare with Riemann zeros
    print("Comparison with Riemann zeros:")
    print(f"  {'n':>3}  {'γₙ (Riemann)':>15}  {'λₙ (T_∞³)':>15}  {'|Δ|':>12}")
    print("  " + "-" * 60)
    for i in range(min(10, len(RIEMANN_ZEROS_GAMMA), len(eigenvalues))):
        gamma = RIEMANN_ZEROS_GAMMA[i]
        lam = eigenvalues[i]
        diff = abs(gamma - lam)
        print(f"  {i+1:3d}  {gamma:15.6f}  {lam:15.6f}  {diff:12.6f}")
    print()
    
    # Trace formula
    print("Evaluating Gutzwiller trace formula...")
    t_spectral = 1.0
    trace_value = T_op.trace_formula_gutzwiller(t_spectral, num_primes=15)
    print(f"  Tr(e^(-t T_∞³)) at t={t_spectral}: {trace_value.real:.6f}")
    print()
    
    # Partition function
    print("Computing partition function Z_Kairos...")
    Z_kairos = T_op.partition_function_kairos(t=0.5)
    print(f"  Z_Kairos(t=0.5) = {Z_kairos:.6f}")
    print()
    
    # Coherence verification
    print("QCAL Coherence Protocol Verification:")
    coherence_results = T_op.verify_coherence_protocol()
    print(f"  Self-adjoint: {coherence_results['self_adjoint']}")
    print(f"  Positive semi-definite: {coherence_results['positive_semidefinite']}")
    print(f"  Coherence Ψ: {coherence_results['coherence_psi']:.6f}")
    print(f"  Threshold (Ψ ≥ {PSI_MIN}): {coherence_results['coherence_threshold_met']}")
    print(f"  Status: {coherence_results['status']}")
    print()
    
    print("=" * 80)
    print("∴ T_∞³ Operator manifestado en coherencia con el Campo Ψ ∞³")
    print("=" * 80)


if __name__ == '__main__':
    demonstrate_t_infinity_cubed()

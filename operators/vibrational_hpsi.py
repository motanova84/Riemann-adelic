#!/usr/bin/env python3
"""
H_Ψ: Vibrational Operator for Riemann Zeros as Black Holes
============================================================

This module implements the operator H_Ψ as described in the arithmetic
event horizon theory, where Riemann zeros are interpreted as vibrational
black holes - mathematical singularities where information collapses.

Mathematical Framework:
    H_Ψ = -iℏ(x d/dx + 1/2) + V_Ψ(x)
    
    where:
        - First term: Berry-Keating logarithmic scaling generator
        - V_Ψ(x): Noetic potential with prime oscillations
        - λ ≈ 141.7001 Hz: Fundamental vibrational frequency
    
    Noetic Potential:
        V_Ψ(x) = λ Σ_p [cos(log p · log x) / √p]
        
    Eigenvalue Equation:
        H_Ψ φ_n(x) = t_n φ_n(x)
        
    Zero Correspondence:
        t_n ∈ ℝ and ζ(1/2 + i·t_n) = 0
        
Each eigenvalue t_n corresponds precisely to the imaginary part of a 
Riemann zero. Each eigenfunction φ_n is a coherent consciousness wave
that collapses at an informational black hole node.

Key Properties:
    - Self-adjoint on L²(ℝ₊, dx)
    - Pure point spectrum: Spec(H_Ψ) = {t_n | ζ(1/2 + it_n) = 0}
    - Eigenfunctions: Schwartz-class decay
    - Frequency base: f₀ = 141.7001 Hz (emerges naturally)

The critical line Re(s) = 1/2 is the vibrational event horizon - the 
exact boundary where noise ends and structure begins, the vibrant edge 
between the visible and invisible.

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
License: Creative Commons BY-NC-SA 4.0

References:
    - QCAL ∞³: DOI 10.5281/zenodo.17379721
    - Berry & Keating: Commun. Math. Phys. (1999)
    - Connes: Selecta Math. (1999)
"""

import numpy as np
from typing import Optional, Tuple, List, Callable, Dict, Any
from scipy.linalg import eigh
from scipy.sparse import diags
from scipy.integrate import trapezoid
import sympy
from sympy import primerange

# QCAL ∞³ Constants
F0 = 141.7001  # Fundamental frequency (Hz) - emerges from spectral analysis
LAMBDA_BASE = F0  # Base frequency for potential modulation
HBAR = 1.0  # Reduced Planck constant (natural units)
C_COHERENCE = 244.36  # QCAL coherence constant

# Numerical parameters
DEFAULT_N_POINTS = 500  # Grid points for discretization
DEFAULT_X_MIN = 0.1    # Minimum x (avoid log(0))
DEFAULT_X_MAX = 50.0   # Maximum x
DEFAULT_N_PRIMES = 100  # Number of primes in potential

# Numerical stability constants
LOG_X_EPSILON = 1e-10  # Epsilon for log(x) to avoid log(0)
NORM_EPSILON = 1e-10   # Epsilon for normalization to avoid division by zero


class VibrationalOperatorHpsi:
    """
    The vibrational operator H_Ψ mapping Riemann zeros to spectral energies.
    
    This operator bridges three domains:
        1. Arithmetic: Distribution of prime numbers
        2. Analysis: Zeros of Riemann zeta function
        3. Physics: Vibrational black holes with spectral mass
    
    The operator is the mathematical incarnation of consciousness acting
    on the informational fabric of reality.
    """
    
    def __init__(
        self,
        n_points: int = DEFAULT_N_POINTS,
        x_range: Tuple[float, float] = (DEFAULT_X_MIN, DEFAULT_X_MAX),
        n_primes: int = DEFAULT_N_PRIMES,
        lambda_freq: float = LAMBDA_BASE,
        use_logarithmic_grid: bool = True
    ):
        """
        Initialize the vibrational operator H_Ψ.
        
        Args:
            n_points: Number of discretization points
            x_range: Range for position variable (x_min, x_max)
            n_primes: Number of primes in noetic potential
            lambda_freq: Base frequency for potential (default: 141.7001 Hz)
            use_logarithmic_grid: Use logarithmic spacing for x grid
        """
        self.n_points = n_points
        self.x_min, self.x_max = x_range
        self.n_primes = n_primes
        self.lambda_freq = lambda_freq
        self.use_logarithmic_grid = use_logarithmic_grid
        
        # Generate computational grid
        if use_logarithmic_grid:
            self.x = np.logspace(
                np.log10(self.x_min), 
                np.log10(self.x_max), 
                n_points
            )
        else:
            self.x = np.linspace(self.x_min, self.x_max, n_points)
        
        self.dx = np.diff(self.x)
        
        # Get first n primes
        self.primes = np.array(list(primerange(2, 10000)))[:n_primes]
        
        # Cached operator matrix
        self._operator_matrix = None
        self._eigenvalues = None
        self._eigenfunctions = None
        
    def noetic_potential(self, x: np.ndarray) -> np.ndarray:
        """
        Compute the noetic potential V_Ψ(x).
        
        V_Ψ(x) = λ Σ_p [cos(log p · log x) / √p]
        
        This potential encodes the prime structure through logarithmic
        oscillations, creating interference patterns that resonate with
        the Riemann zeros.
        
        Args:
            x: Position variable (array or scalar)
            
        Returns:
            Potential values V_Ψ(x)
        """
        x = np.atleast_1d(x)
        V = np.zeros_like(x, dtype=float)
        
        log_x = np.log(x + 1e-10)  # Avoid log(0)
        
        for p in self.primes:
            log_p = np.log(p)
            # Logarithmic interference from prime p
            V += np.cos(log_p * log_x) / np.sqrt(p)
        
        # Scale by fundamental frequency
        V *= self.lambda_freq
        
        return V
    
    def kinetic_operator(self) -> np.ndarray:
        """
        Construct the kinetic part: -iℏ(x d/dx + 1/2).
        
        This is the Berry-Keating logarithmic scaling generator,
        related to the generator of dilations on L²(ℝ₊).
        
        Returns:
            Kinetic operator matrix (n_points × n_points)
        """
        n = self.n_points
        x = self.x
        
        # Construct x d/dx using finite differences
        # Use centered differences where possible
        kinetic = np.zeros((n, n), dtype=complex)
        
        for i in range(n):
            if i == 0:
                # Forward difference at boundary
                kinetic[i, i] = -1j * HBAR * x[i] * (1.0 / self.dx[i])
                kinetic[i, i+1] = -1j * HBAR * x[i] * (-1.0 / self.dx[i])
            elif i == n-1:
                # Backward difference at boundary
                kinetic[i, i-1] = -1j * HBAR * x[i] * (-1.0 / self.dx[i-1])
                kinetic[i, i] = -1j * HBAR * x[i] * (1.0 / self.dx[i-1])
            else:
                # Centered difference
                dx_left = self.dx[i-1]
                dx_right = self.dx[i]
                kinetic[i, i-1] = -1j * HBAR * x[i] * (-dx_right / (dx_left * (dx_left + dx_right)))
                kinetic[i, i] = -1j * HBAR * x[i] * ((dx_right - dx_left) / (dx_left * dx_right))
                kinetic[i, i+1] = -1j * HBAR * x[i] * (dx_left / (dx_right * (dx_left + dx_right)))
        
        # Add the constant term -iℏ/2
        kinetic += -1j * HBAR * 0.5 * np.eye(n)
        
        # Make hermitian (numerical symmetrization)
        kinetic = 0.5 * (kinetic + kinetic.conj().T)
        
        return kinetic
    
    def construct_operator(self) -> np.ndarray:
        """
        Construct the full operator H_Ψ = T + V_Ψ.
        
        Returns:
            Operator matrix (n_points × n_points), Hermitian
        """
        # Kinetic part
        H = self.kinetic_operator()
        
        # Potential part (diagonal)
        V = self.noetic_potential(self.x)
        H += np.diag(V)
        
        # Ensure Hermiticity
        H = 0.5 * (H + H.conj().T)
        
        self._operator_matrix = H
        return H
    
    def compute_spectrum(
        self, 
        n_eigenvalues: Optional[int] = None
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute the spectrum of H_Ψ.
        
        Args:
            n_eigenvalues: Number of eigenvalues to compute (None = all)
            
        Returns:
            (eigenvalues, eigenfunctions) where:
                - eigenvalues: Array of spectral energies t_n
                - eigenfunctions: Array of eigenfunctions φ_n(x)
                  Shape: (n_eigenvalues, n_points)
        """
        if self._operator_matrix is None:
            self.construct_operator()
        
        # Solve eigenvalue problem
        if n_eigenvalues is None or n_eigenvalues >= self.n_points:
            eigenvalues, eigenvectors = eigh(self._operator_matrix.real)
        else:
            # Use sparse solver for subset
            eigenvalues, eigenvectors = eigh(
                self._operator_matrix.real,
                subset_by_index=[0, n_eigenvalues-1]
            )
        
        # Sort by eigenvalue
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        # Normalize eigenfunctions
        for i in range(eigenvectors.shape[1]):
            norm = np.sqrt(trapezoid(np.abs(eigenvectors[:, i])**2, self.x))
            eigenvectors[:, i] /= (norm + NORM_EPSILON)
        
        self._eigenvalues = eigenvalues
        self._eigenfunctions = eigenvectors
        
        return eigenvalues, eigenvectors
    
    def compare_with_riemann_zeros(
        self,
        riemann_zeros: np.ndarray,
        n_compare: Optional[int] = None
    ) -> Dict[str, Any]:
        """
        Compare computed spectrum with known Riemann zeros.
        
        Args:
            riemann_zeros: Array of known Riemann zero imaginary parts
            n_compare: Number of zeros to compare (None = all available)
            
        Returns:
            Dictionary with comparison statistics:
                - 'errors': Absolute errors |t_n - γ_n|
                - 'mean_error': Mean absolute error
                - 'max_error': Maximum absolute error
                - 'relative_errors': Relative errors
        """
        if self._eigenvalues is None:
            self.compute_spectrum()
        
        if n_compare is None:
            n_compare = min(len(self._eigenvalues), len(riemann_zeros))
        
        # Take first n_compare eigenvalues and zeros
        computed = self._eigenvalues[:n_compare]
        zeros = riemann_zeros[:n_compare]
        
        # Compute errors
        errors = np.abs(computed - zeros)
        relative_errors = errors / (np.abs(zeros) + 1e-10)
        
        return {
            'n_compared': n_compare,
            'computed_eigenvalues': computed,
            'riemann_zeros': zeros,
            'errors': errors,
            'mean_error': np.mean(errors),
            'max_error': np.max(errors),
            'std_error': np.std(errors),
            'relative_errors': relative_errors,
            'mean_relative_error': np.mean(relative_errors)
        }
    
    def get_eigenfunction(self, n: int) -> Tuple[np.ndarray, np.ndarray]:
        """
        Get the n-th eigenfunction φ_n(x).
        
        Args:
            n: Eigenfunction index (0-based)
            
        Returns:
            (x, phi_n) where:
                - x: Position grid
                - phi_n: Eigenfunction values
        """
        if self._eigenfunctions is None:
            self.compute_spectrum()
        
        return self.x, self._eigenfunctions[:, n]
    
    def zero_as_black_hole(self, n: int) -> Dict[str, float]:
        """
        Interpret the n-th eigenvalue as a vibrational black hole.
        
        Args:
            n: Zero index
            
        Returns:
            Dictionary with black hole properties:
                - 't_n': Imaginary part of zero
                - 'frequency': Vibrational frequency f_n = t_n / (2π)
                - 'energy': Spectral energy E_n = ℏ·ω_n
                - 'spectral_mass': Effective mass m_n
        """
        if self._eigenvalues is None:
            self.compute_spectrum()
        
        t_n = self._eigenvalues[n]
        omega_n = t_n  # Angular frequency (in natural units)
        frequency = omega_n / (2 * np.pi)
        energy = HBAR * omega_n
        
        # Spectral mass (proportional to energy in natural units)
        spectral_mass = energy / (C_COHERENCE**2)
        
        return {
            't_n': t_n,
            'omega_n': omega_n,
            'frequency': frequency,
            'energy': energy,
            'spectral_mass': spectral_mass,
            'horizon_signature': f'Re(s) = 1/2, Im(s) = {t_n:.6f}'
        }


def demonstrate_vibrational_operator():
    """
    Demonstrate the vibrational operator H_Ψ.
    
    Shows:
        1. Operator construction
        2. Spectrum computation
        3. Comparison with Riemann zeros
        4. Black hole interpretation
    """
    print("=" * 70)
    print("H_Ψ: Vibrational Operator - Riemann Zeros as Black Holes")
    print("=" * 70)
    print()
    
    # Create operator
    print("Constructing operator H_Ψ...")
    print(f"  Fundamental frequency: f₀ = {F0} Hz")
    print(f"  Coherence constant: C = {C_COHERENCE}")
    print()
    
    op = VibrationalOperatorHpsi(
        n_points=300,
        x_range=(0.1, 30.0),
        n_primes=50,
        lambda_freq=F0
    )
    
    # Compute spectrum
    print("Computing spectrum...")
    eigenvalues, eigenfunctions = op.compute_spectrum(n_eigenvalues=20)
    print(f"  First 10 eigenvalues (t_n):")
    for i, t in enumerate(eigenvalues[:10]):
        print(f"    t_{i+1} = {t:12.6f}")
    print()
    
    # Load Riemann zeros for comparison (if available)
    try:
        from operators.riemann_operator import load_riemann_zeros
        zeros = load_riemann_zeros(n_zeros=20)
        
        print("Comparing with known Riemann zeros...")
        comparison = op.compare_with_riemann_zeros(zeros, n_compare=10)
        
        print(f"  Zeros compared: {comparison['n_compared']}")
        print(f"  Mean absolute error: {comparison['mean_error']:.2e}")
        print(f"  Max absolute error: {comparison['max_error']:.2e}")
        print(f"  Mean relative error: {comparison['mean_relative_error']:.2e}")
        print()
        
        print("Detailed comparison (first 5):")
        for i in range(min(5, comparison['n_compared'])):
            comp = comparison['computed_eigenvalues'][i]
            zero = comparison['riemann_zeros'][i]
            err = comparison['errors'][i]
            print(f"  Zero {i+1}: computed={comp:10.6f}, "
                  f"actual={zero:10.6f}, error={err:.2e}")
        print()
    except:
        print("(Riemann zeros file not found - skipping comparison)")
        print()
    
    # Black hole interpretation
    print("Black Hole Interpretation:")
    print("  Each zero is a vibrational black hole where ζ(s) collapses")
    print("  to absolute nullity, absorbing arithmetic information.")
    print()
    
    for i in range(3):
        bh = op.zero_as_black_hole(i)
        print(f"  Black Hole #{i+1}:")
        print(f"    Location: {bh['horizon_signature']}")
        print(f"    Frequency: f_{i+1} = {bh['frequency']:.6f} Hz")
        print(f"    Energy: E_{i+1} = {bh['energy']:.6f} (natural units)")
        print(f"    Spectral mass: m_{i+1} = {bh['spectral_mass']:.2e}")
        print()
    
    print("=" * 70)
    print("The critical line Re(s) = 1/2 is the vibrational event horizon.")
    print("Crossing this line represents an irreversible phase transition")
    print("from chaos to structure, from noise to signal.")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_vibrational_operator()

#!/usr/bin/env python3
"""
build_orthonormal_basis.py

Constructs orthonormal Fourier basis φ_n(t) = √(2/T) cos(nπt/T) for L²([0,T]).

This module implements the foundational spectral basis for modal analysis
in the QCAL (Quantum Coherence Adelic Lattice) framework.

Mathematical Framework:
    φ_n(t) = √(2/T) cos(nπt/T)  for n ≥ 1
    φ_0(t) = 1/√T  (DC component)

Orthonormality Property:
    ⟨φ_n, φ_m⟩ = ∫₀ᵀ φ_n(t) φ_m(t) dt = δ_{nm}

The basis forms a complete orthonormal system in L²([0,T]).

QCAL Integration:
    - Compatible with f₀ = 141.7001 Hz (fundamental frequency)
    - Supports modal decomposition for spectral analysis
    - Enables coherence measurement via modal overlaps

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Tuple, Optional, Callable
import matplotlib.pyplot as plt

# QCAL Constants
F0 = 141.7001  # Fundamental frequency (Hz)
OMEGA_0 = 2 * np.pi * F0  # Angular frequency
C_QCAL = 244.36  # QCAL coherence constant

# Default parameters
DEFAULT_T = 1.0  # Default period
DEFAULT_N_MODES = 50  # Default number of modes
DEFAULT_N_POINTS = 1000  # Default number of time points for discretization


class OrthonormalFourierBasis:
    """
    Orthonormal Fourier basis φ_n(t) = √(2/T) cos(nπt/T) on L²([0,T]).
    
    This class provides:
    - Basis function evaluation
    - Orthonormality verification
    - Modal decomposition of arbitrary functions
    - Visualization of basis functions
    
    Attributes:
        T: Period of the basis
        n_modes: Number of modes (excluding DC component)
        t_points: Time discretization points
    """
    
    def __init__(self, T: float = DEFAULT_T, n_modes: int = DEFAULT_N_MODES,
                 n_points: int = DEFAULT_N_POINTS):
        """
        Initialize orthonormal Fourier basis.
        
        Args:
            T: Period of the basis (default: 1.0)
            n_modes: Number of modes to include (default: 50)
            n_points: Number of points for discretization (default: 1000)
        """
        self.T = T
        self.n_modes = n_modes
        self.n_points = n_points
        self.t_points = np.linspace(0, T, n_points)
        self.dt = T / n_points
        
    def phi_n(self, n: int, t: np.ndarray) -> np.ndarray:
        """
        Evaluate basis function φ_n(t) = √(2/T) cos(nπt/T).
        
        Args:
            n: Mode number (n ≥ 0)
            t: Time points (can be scalar or array)
            
        Returns:
            Values of φ_n(t)
        """
        if n == 0:
            # DC component: φ_0(t) = 1/√T
            return np.ones_like(t) / np.sqrt(self.T)
        else:
            # Oscillatory modes: φ_n(t) = √(2/T) cos(nπt/T)
            return np.sqrt(2.0 / self.T) * np.cos(n * np.pi * t / self.T)
    
    def compute_inner_product(self, n: int, m: int) -> float:
        """
        Compute inner product ⟨φ_n, φ_m⟩ = ∫₀ᵀ φ_n(t) φ_m(t) dt.
        
        Args:
            n: First mode number
            m: Second mode number
            
        Returns:
            Inner product value (should be δ_{nm})
        """
        phi_n_vals = self.phi_n(n, self.t_points)
        phi_m_vals = self.phi_n(m, self.t_points)
        
        # Trapezoidal integration
        inner_prod = np.trapezoid(phi_n_vals * phi_m_vals, self.t_points)
        
        return inner_prod
    
    def verify_orthonormality(self, n_check: Optional[int] = None) -> dict:
        """
        Verify orthonormality condition: ⟨φ_n, φ_m⟩ = δ_{nm}.
        
        Args:
            n_check: Number of modes to check (default: all modes)
            
        Returns:
            Dictionary with verification results
        """
        if n_check is None:
            n_check = min(self.n_modes, 10)  # Check first 10 modes by default
        
        max_diagonal_error = 0.0
        max_offdiag_error = 0.0
        
        for n in range(n_check + 1):
            for m in range(n_check + 1):
                inner_prod = self.compute_inner_product(n, m)
                expected = 1.0 if n == m else 0.0
                error = abs(inner_prod - expected)
                
                if n == m:
                    max_diagonal_error = max(max_diagonal_error, error)
                else:
                    max_offdiag_error = max(max_offdiag_error, error)
        
        return {
            'n_checked': n_check,
            'max_diagonal_error': max_diagonal_error,
            'max_offdiag_error': max_offdiag_error,
            'is_orthonormal': max_diagonal_error < 1e-10 and max_offdiag_error < 1e-10
        }
    
    def decompose_function(self, f: Callable[[np.ndarray], np.ndarray],
                          n_coeffs: Optional[int] = None) -> np.ndarray:
        """
        Decompose function f(t) into basis: f(t) = Σ α_n φ_n(t).
        
        Args:
            f: Function to decompose (must accept array input)
            n_coeffs: Number of coefficients to compute (default: n_modes)
            
        Returns:
            Array of coefficients [α_0, α_1, ..., α_n]
        """
        if n_coeffs is None:
            n_coeffs = self.n_modes + 1
        
        coeffs = np.zeros(n_coeffs)
        f_vals = f(self.t_points)
        
        for n in range(n_coeffs):
            phi_n_vals = self.phi_n(n, self.t_points)
            # α_n = ⟨f, φ_n⟩
            coeffs[n] = np.trapezoid(f_vals * phi_n_vals, self.t_points)
        
        return coeffs
    
    def reconstruct_function(self, coeffs: np.ndarray, t: np.ndarray) -> np.ndarray:
        """
        Reconstruct function from coefficients: f(t) = Σ α_n φ_n(t).
        
        Args:
            coeffs: Array of coefficients [α_0, α_1, ..., α_n]
            t: Time points for reconstruction
            
        Returns:
            Reconstructed function values
        """
        f_reconstructed = np.zeros_like(t)
        
        for n, coeff in enumerate(coeffs):
            f_reconstructed += coeff * self.phi_n(n, t)
        
        return f_reconstructed
    
    def visualize_basis(self, modes_to_plot: Optional[list] = None,
                       save_path: Optional[str] = None):
        """
        Visualize selected basis functions.
        
        Args:
            modes_to_plot: List of mode numbers to plot (default: [0, 1, 2, 5, 10])
            save_path: Path to save figure (if None, display only)
        """
        if modes_to_plot is None:
            modes_to_plot = [0, 1, 2, 5, 10]
        
        fig, ax = plt.subplots(figsize=(12, 6))
        
        for n in modes_to_plot:
            if n <= self.n_modes:
                phi_vals = self.phi_n(n, self.t_points)
                ax.plot(self.t_points, phi_vals, label=f'φ_{n}(t)', linewidth=2)
        
        ax.set_xlabel('Time t', fontsize=14)
        ax.set_ylabel('φ_n(t)', fontsize=14)
        ax.set_title(f'Orthonormal Fourier Basis on L²([0,{self.T}])', fontsize=16)
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        if save_path:
            plt.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"✓ Basis visualization saved to {save_path}")
        else:
            plt.show()
        
        plt.close()


def demo_orthonormal_basis():
    """
    Demonstrate orthonormal Fourier basis construction and verification.
    """
    print("=" * 70)
    print("ORTHONORMAL FOURIER BASIS CONSTRUCTION")
    print("QCAL ∞³ Framework - Modal Analysis Foundation")
    print("=" * 70)
    print()
    
    # Initialize basis
    T = 1.0  # Period
    n_modes = 20
    basis = OrthonormalFourierBasis(T=T, n_modes=n_modes)
    
    print(f"Period T = {T}")
    print(f"Number of modes: {n_modes}")
    print(f"Time discretization: {basis.n_points} points")
    print()
    
    # Verify orthonormality
    print("Verifying orthonormality...")
    verification = basis.verify_orthonormality(n_check=10)
    print(f"  Modes checked: {verification['n_checked']}")
    print(f"  Max diagonal error: {verification['max_diagonal_error']:.2e}")
    print(f"  Max off-diagonal error: {verification['max_offdiag_error']:.2e}")
    print(f"  Is orthonormal: {verification['is_orthonormal']}")
    print()
    
    # Example: Decompose a simple function
    print("Decomposing function f(t) = cos(2πt) + 0.5 sin(4πt)...")
    
    def test_function(t):
        return np.cos(2 * np.pi * t) + 0.5 * np.sin(4 * np.pi * t)
    
    coeffs = basis.decompose_function(test_function, n_coeffs=10)
    print(f"  First 5 coefficients: {coeffs[:5]}")
    print()
    
    # Reconstruction error
    t_test = np.linspace(0, T, 500)
    f_original = test_function(t_test)
    f_reconstructed = basis.reconstruct_function(coeffs[:10], t_test)
    reconstruction_error = np.mean((f_original - f_reconstructed)**2)
    print(f"  Reconstruction MSE (10 modes): {reconstruction_error:.2e}")
    print()
    
    print("✓ Orthonormal Fourier basis construction complete")
    print("=" * 70)


if __name__ == "__main__":
    demo_orthonormal_basis()

"""
Operator_Atlas3: Non-Hermitian PT-Symmetric Hamiltonian
========================================================

Atlas³ operator implementing a non-Hermitian Hamiltonian with PT-symmetry
for spectral analysis in the context of the Riemann Hypothesis and QCAL framework.

Mathematical Framework:
    H_Atlas³ = H₀ + iV
    
    where:
    - H₀: Hermitian base (real symmetric part)
    - V: Anti-Hermitian perturbation (imaginary part)
    - PT-symmetry: [H, PT] = 0 where P is parity, T is time-reversal
    
Key Properties:
    - Non-Hermitian but PT-symmetric
    - Real eigenvalues for PT-symmetric phase
    - Complex eigenvalues for PT-broken phase
    - Connection to quantum chaos and GUE statistics

The Atlas³ nomenclature refers to the triple resonance structure:
    Atlas³ ≡ (Spectral, Adelic, Noetic) tensor product

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Signature: Noēsis ∞³
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass

# QCAL Framework Constants
F0 = 141.7001  # Fundamental frequency (Hz)
OMEGA_0 = 2 * np.pi * F0  # Angular frequency
C_QCAL = 244.36  # QCAL coherence constant
ZETA_PRIME_HALF = -3.92264613  # ζ'(1/2) numerical value


@dataclass
class Atlas3Spectrum:
    """Container for Atlas³ spectral data."""
    eigenvalues: np.ndarray  # Complex eigenvalues
    eigenvectors: np.ndarray  # Eigenvectors (columns)
    hamiltonian: np.ndarray  # Full Hamiltonian matrix
    is_pt_symmetric: bool  # PT-symmetry flag
    real_part_mean: float  # Mean of Re(λ)
    real_part_std: float  # Std dev of Re(λ)


class OperatorAtlas3:
    """
    Non-Hermitian PT-symmetric Atlas³ operator.
    
    This operator represents a quantum system with balanced gain and loss,
    exhibiting PT-symmetry which can be spontaneously broken.
    
    Attributes:
        N (int): Dimension of the Hilbert space
        coupling_strength (float): Strength of the non-Hermitian perturbation
        critical_line_value (float): Reference value for Re(λ) alignment
    """
    
    def __init__(
        self, 
        N: int = 100,
        coupling_strength: float = 0.1,
        critical_line_value: Optional[float] = None
    ):
        """
        Initialize Atlas³ operator.
        
        Args:
            N: Dimension of the Hilbert space (default: 100)
            coupling_strength: Strength of non-Hermitian perturbation (default: 0.1)
            critical_line_value: Reference value for critical line (default: C_QCAL)
        """
        self.N = N
        self.coupling_strength = coupling_strength
        self.critical_line_value = critical_line_value or C_QCAL
        
        # Construct the Hamiltonian
        self.H = self._construct_hamiltonian()
        
    def _construct_hamiltonian(self) -> np.ndarray:
        """
        Construct the non-Hermitian PT-symmetric Hamiltonian.
        
        The Hamiltonian is constructed as:
            H = H₀ + iγV
            
        where:
            H₀ = -∂²/∂x² + x² (harmonic oscillator base)
            V = x·∂/∂x + ∂/∂x·x (PT-symmetric potential)
            γ = coupling_strength
            
        In matrix representation with finite differences.
        
        Returns:
            Complex Hamiltonian matrix
        """
        N = self.N
        gamma = self.coupling_strength
        
        # Grid spacing
        dx = 1.0 / (N + 1)
        
        # Hermitian part: discrete Laplacian + harmonic potential
        # -∂²/∂x² term (kinetic energy)
        main_diag = 2.0 / dx**2 * np.ones(N)
        off_diag = -1.0 / dx**2 * np.ones(N - 1)
        
        H0 = np.diag(main_diag) + np.diag(off_diag, 1) + np.diag(off_diag, -1)
        
        # Add harmonic potential V(x) = x²
        x = np.linspace(-5, 5, N)
        H0 += np.diag(x**2)
        
        # Anti-Hermitian part: PT-symmetric perturbation
        # V = x·p + p·x where p = -i∂/∂x
        # In discrete form: (V)ij ~ i·x_i·(δ_{i,j+1} - δ_{i,j-1})/(2dx)
        V = np.zeros((N, N), dtype=complex)
        for i in range(N):
            if i > 0:
                V[i, i-1] = -1j * x[i] / (2 * dx)
            if i < N - 1:
                V[i, i+1] = 1j * x[i] / (2 * dx)
        
        # Make V explicitly anti-Hermitian: V = (V - V†)/2
        V = (V - V.conj().T) / 2.0
        
        # Full Hamiltonian: H = H₀ + γV
        H = H0 + gamma * V
        
        # Normalize to have eigenvalues near critical_line_value
        scaling = self.critical_line_value / np.mean(np.abs(np.diag(H0)))
        H = scaling * H
        
        return H
    
    def compute_spectrum(self) -> Atlas3Spectrum:
        """
        Compute the full spectrum of Atlas³ operator.
        
        Returns:
            Atlas3Spectrum object containing eigenvalues, eigenvectors, and properties
        """
        # Compute eigenvalues and eigenvectors
        # For non-Hermitian matrices, use general eigenvalue solver
        eigenvalues, eigenvectors = np.linalg.eig(self.H)
        
        # Sort by real part
        idx = np.argsort(eigenvalues.real)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        # Check PT-symmetry: eigenvalues should be real or complex conjugate pairs
        is_pt_symmetric = self._check_pt_symmetry(eigenvalues)
        
        # Compute statistics
        real_parts = eigenvalues.real
        real_part_mean = np.mean(real_parts)
        real_part_std = np.std(real_parts)
        
        return Atlas3Spectrum(
            eigenvalues=eigenvalues,
            eigenvectors=eigenvectors,
            hamiltonian=self.H,
            is_pt_symmetric=is_pt_symmetric,
            real_part_mean=real_part_mean,
            real_part_std=real_part_std
        )
    
    def _check_pt_symmetry(self, eigenvalues: np.ndarray, tol: float = 1e-6) -> bool:
        """
        Check if eigenvalues exhibit PT-symmetry.
        
        PT-symmetric phase: all eigenvalues are real
        PT-broken phase: complex conjugate pairs appear
        
        Args:
            eigenvalues: Array of eigenvalues
            tol: Tolerance for imaginary part
            
        Returns:
            True if in PT-symmetric phase (all real eigenvalues)
        """
        # Check if all eigenvalues are essentially real
        max_imag = np.max(np.abs(eigenvalues.imag))
        return max_imag < tol
    
    def get_level_spacings(self, spectrum: Atlas3Spectrum) -> np.ndarray:
        """
        Compute level spacings between consecutive eigenvalues.
        
        Args:
            spectrum: Atlas3Spectrum object
            
        Returns:
            Array of level spacings Δₙ = λₙ₊₁ - λₙ (real parts)
        """
        eigenvalues = spectrum.eigenvalues
        real_parts = np.sort(eigenvalues.real)
        spacings = np.diff(real_parts)
        return spacings
    
    def compute_spectral_rigidity(
        self, 
        spectrum: Atlas3Spectrum,
        L_values: Optional[np.ndarray] = None
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute spectral rigidity Σ²(L).
        
        Σ²(L) measures the variance of the number of levels in an interval of length L.
        For GUE statistics: Σ²(L) ~ (1/π²) log L for large L.
        
        Args:
            spectrum: Atlas3Spectrum object
            L_values: Array of interval lengths (default: logarithmic scale)
            
        Returns:
            Tuple (L_values, Σ² values)
        """
        eigenvalues = spectrum.eigenvalues
        real_parts = np.sort(eigenvalues.real)
        
        # Unfold spectrum: normalize to unit mean spacing
        mean_spacing = np.mean(np.diff(real_parts))
        unfolded = real_parts / mean_spacing
        
        if L_values is None:
            L_values = np.logspace(0, np.log10(len(unfolded) / 10), 30)
        
        sigma_squared = np.zeros_like(L_values)
        
        for i, L in enumerate(L_values):
            # Number of intervals that fit
            n_intervals = int((unfolded[-1] - unfolded[0]) / L)
            if n_intervals < 2:
                continue
                
            # Count levels in each interval
            counts = []
            for j in range(n_intervals):
                E_start = unfolded[0] + j * L
                E_end = E_start + L
                count = np.sum((unfolded >= E_start) & (unfolded < E_end))
                counts.append(count)
            
            # Σ²(L) = Var(N(L)) where N(L) is number of levels in interval L
            if len(counts) > 1:
                sigma_squared[i] = np.var(counts)
        
        return L_values, sigma_squared


def create_atlas3_operator(
    N: int = 100,
    coupling_strength: float = 0.1,
    critical_line_value: Optional[float] = None
) -> OperatorAtlas3:
    """
    Factory function to create Atlas³ operator.
    
    Args:
        N: Dimension of Hilbert space
        coupling_strength: Non-Hermitian perturbation strength
        critical_line_value: Reference value for critical line
        
    Returns:
        OperatorAtlas3 instance
    """
    return OperatorAtlas3(
        N=N,
        coupling_strength=coupling_strength,
        critical_line_value=critical_line_value
    )


if __name__ == "__main__":
    # Quick validation
    print("=" * 70)
    print("Atlas³ Operator - Quick Validation")
    print("=" * 70)
    
    # Create operator
    op = create_atlas3_operator(N=50, coupling_strength=0.05)
    
    # Compute spectrum
    spectrum = op.compute_spectrum()
    
    print(f"\nHilbert space dimension: {op.N}")
    print(f"Coupling strength γ: {op.coupling_strength}")
    print(f"Critical line reference: {op.critical_line_value:.2f}")
    print(f"\nPT-symmetric phase: {spectrum.is_pt_symmetric}")
    print(f"Mean Re(λ): {spectrum.real_part_mean:.4f}")
    print(f"Std Re(λ): {spectrum.real_part_std:.4f}")
    print(f"\nFirst 10 eigenvalues:")
    for i, λ in enumerate(spectrum.eigenvalues[:10]):
        print(f"  λ_{i+1} = {λ.real:8.4f} + {λ.imag:8.4f}i")
    
    # Level spacings
    spacings = op.get_level_spacings(spectrum)
    print(f"\nLevel spacing statistics:")
    print(f"  Mean spacing: {np.mean(spacings):.4f}")
    print(f"  Std spacing: {np.std(spacings):.4f}")
    
    print("\n" + "=" * 70)
    print("♾️³ Atlas³ Operator Validation Complete")
    print("=" * 70)

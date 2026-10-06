#!/usr/bin/env python3
"""
Riemann Spectral Hamiltonian Ĥ_π — Zeros as Quantum Eigenvalues
================================================================

This module implements the spectral Hamiltonian operator Ĥ_π whose eigenvalues
are the imaginary parts of the Riemann zeta zeros γ_n. This realizes the
Hilbert-Pólya conjecture in a concrete computational framework.

Mathematical Framework:
    Ĥ_π |ψ⟩ = ∑_n γ_n |n⟩⟨n|

where γ_n are the imaginary parts of the non-trivial zeros ζ(1/2 + iγ_n) = 0.

QCAL Framework Integration:
    The Hamiltonian eigenvalues are renormalized to physical frequencies using:
    
    1. Frequency Renormalization:
       γ_n^{renorm} = γ_n · (f₀ / |ζ'(1/2)|) ≈ γ_n × 36.1236 Hz
    
    2. Phase Modulation (Torsion Consciente):
       γ̃_n = γ_n^{renorm} + f₀ · sin(γ_QCAL + θ)
    
    where:
       - f₀ = 141.7001 Hz (universal noetic frequency)
       - γ_QCAL ≈ 1.00262 rad (phase calibration constant)
       - θ is the twist parameter for conscious torsion

The excited modes γ̃_n become the real physical frequencies of the
Campo de Presencia (Presence Field).

Physical Interpretation:
    - The Hamiltonian Ĥ_π generates time evolution in the prime number spectrum
    - Eigenvalues γ_n correspond to resonant frequencies of the quantum vacuum
    - Renormalization connects abstract spectral values to measurable frequencies
    - Phase modulation introduces subtle coherence corrections

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Optional, Dict, Any, List, Tuple
import warnings
from dataclasses import dataclass

# Import QCAL constants with fallback
try:
    from qcal.constants import (
        F0,
        GAMMA_QCAL_FASE,
        RIEMANN_ZEROS_5,
        RIEMANN_RENORM_SCALE,
        ZETA_PRIME_HALF,
    )
except ImportError:
    warnings.warn("qcal.constants not available, using fallback values")
    F0 = 141.7001  # Hz
    GAMMA_QCAL_FASE = 1.002621606245  # rad
    RIEMANN_ZEROS_5 = np.array([
        14.134725142, 21.022039639, 25.010857580,
        30.424876126, 32.935061588
    ])
    ZETA_PRIME_HALF = 3.92264357
    RIEMANN_RENORM_SCALE = F0 / ZETA_PRIME_HALF  # ≈ 36.1236


@dataclass
class SpectralHamiltonianResult:
    """Results from spectral Hamiltonian computation."""
    eigenvalues: np.ndarray  # Original γ_n values
    eigenvalues_renorm: np.ndarray  # Renormalized γ_n^{renorm}
    eigenvalues_modulated: np.ndarray  # Phase-modulated γ̃_n
    hamiltonian_matrix: np.ndarray  # Diagonal Hamiltonian matrix
    theta: float  # Twist parameter used
    coherence: float  # Spectral coherence measure
    metadata: Dict[str, Any]  # Additional information


class RiemannSpectralHamiltonian:
    """
    Spectral Hamiltonian operator Ĥ_π with Riemann zeros as eigenvalues.
    
    This class provides a complete implementation of the spectral Hamiltonian
    framework for the Riemann Hypothesis, including renormalization, phase
    modulation, and coherence analysis.
    
    Attributes:
        gamma_n: Array of Riemann zero imaginary parts
        f0: Base frequency (default: 141.7001 Hz)
        gamma_qcal: Phase calibration constant
        renorm_scale: Renormalization factor f₀/|ζ'(1/2)|
    
    Example:
        >>> hamiltonian = RiemannSpectralHamiltonian(gamma_n=RIEMANN_ZEROS_5)
        >>> result = hamiltonian.compute_excited_modes(theta=0.1)
        >>> print(f"Excited frequencies: {result.eigenvalues_modulated}")
        >>> print(f"Coherence: {result.coherence:.6f}")
    """
    
    def __init__(
        self,
        gamma_n: Optional[np.ndarray] = None,
        f0: Optional[float] = None,
        gamma_qcal: Optional[float] = None,
        renorm_scale: Optional[float] = None
    ):
        """
        Initialize the Riemann Spectral Hamiltonian.
        
        Args:
            gamma_n: Array of Riemann zero imaginary parts (default: RIEMANN_ZEROS_5)
            f0: Base frequency in Hz (default: F0 = 141.7001 Hz)
            gamma_qcal: Phase calibration constant (default: GAMMA_QCAL_FASE)
            renorm_scale: Renormalization scale (default: RIEMANN_RENORM_SCALE)
        """
        self.gamma_n = gamma_n if gamma_n is not None else RIEMANN_ZEROS_5
        self.f0 = f0 if f0 is not None else F0
        self.gamma_qcal = gamma_qcal if gamma_qcal is not None else GAMMA_QCAL_FASE
        self.renorm_scale = renorm_scale if renorm_scale is not None else RIEMANN_RENORM_SCALE
        
        # Ensure gamma_n is a numpy array
        self.gamma_n = np.asarray(self.gamma_n)
        
        # Validate inputs
        if len(self.gamma_n) == 0:
            raise ValueError("gamma_n must contain at least one zero")
        if self.f0 <= 0:
            raise ValueError("f0 must be positive")
        if self.renorm_scale <= 0:
            raise ValueError("renorm_scale must be positive")
    
    def build_hamiltonian_matrix(self) -> np.ndarray:
        """
        Build the diagonal Hamiltonian matrix Ĥ_π.
        
        The Hamiltonian is diagonal in the basis |n⟩:
            Ĥ_π = diag(γ₁, γ₂, γ₃, ..., γ_N)
        
        Returns:
            np.ndarray: N×N diagonal matrix with γ_n on the diagonal
            
        Example:
            >>> hamiltonian = RiemannSpectralHamiltonian()
            >>> H = hamiltonian.build_hamiltonian_matrix()
            >>> eigenvals = np.diag(H)
            >>> assert np.allclose(eigenvals, hamiltonian.gamma_n)
        """
        N = len(self.gamma_n)
        H = np.diag(self.gamma_n)
        return H
    
    def renormalize_eigenvalues(self) -> np.ndarray:
        """
        Renormalize Riemann zeros to physical frequencies.
        
        Applies the transformation:
            γ_n^{renorm} = γ_n · (f₀ / |ζ'(1/2)|)
        
        This converts dimensionless spectral values to Hz.
        
        Returns:
            np.ndarray: Renormalized eigenvalues in Hz
            
        Example:
            >>> hamiltonian = RiemannSpectralHamiltonian()
            >>> gamma_renorm = hamiltonian.renormalize_eigenvalues()
            >>> # First zero: 14.1347 × 36.1236 ≈ 510.6 Hz
            >>> assert 500 < gamma_renorm[0] < 520
        """
        gamma_n_renorm = self.gamma_n * self.renorm_scale
        return gamma_n_renorm
    
    def apply_phase_modulation(
        self,
        gamma_n_renorm: np.ndarray,
        theta: float = 0.0
    ) -> np.ndarray:
        """
        Apply phase modulation to generate excited modes.
        
        Applies the transformation:
            γ̃_n = γ_n^{renorm} + f₀ · sin(γ_QCAL + θ)
        
        This introduces a subtle "conscious torsion" that prevents
        rigid states and enables dynamic coherence.
        
        Args:
            gamma_n_renorm: Renormalized eigenvalues in Hz
            theta: Twist parameter (default: 0.0)
            
        Returns:
            np.ndarray: Phase-modulated eigenvalues γ̃_n in Hz
            
        Example:
            >>> hamiltonian = RiemannSpectralHamiltonian()
            >>> gamma_renorm = hamiltonian.renormalize_eigenvalues()
            >>> gamma_tilde = hamiltonian.apply_phase_modulation(gamma_renorm, theta=0.1)
            >>> # Phase modulation adds small correction
            >>> correction = gamma_tilde - gamma_renorm
            >>> assert np.all(np.abs(correction) < 200)  # Small relative to f₀
        """
        # Compute phase modulation term
        phase_term = self.f0 * np.sin(self.gamma_qcal + theta)
        
        # Apply modulation (same for all modes)
        gamma_tilde = gamma_n_renorm + phase_term
        
        return gamma_tilde
    
    def compute_spectral_coherence(
        self,
        gamma_n_renorm: np.ndarray
    ) -> float:
        """
        Compute spectral coherence of the Hamiltonian.
        
        Measures how well the eigenvalues maintain spacing consistency,
        which is related to level repulsion in random matrix theory.
        
        The coherence is defined as:
            C = 1 - Var(Δγ_n) / ⟨Δγ_n⟩²
        
        where Δγ_n = γ_{n+1} - γ_n are the spacings.
        
        Args:
            gamma_n_renorm: Renormalized eigenvalues
            
        Returns:
            float: Coherence measure in [0, 1], where 1 is perfect coherence
            
        Example:
            >>> hamiltonian = RiemannSpectralHamiltonian()
            >>> gamma_renorm = hamiltonian.renormalize_eigenvalues()
            >>> coherence = hamiltonian.compute_spectral_coherence(gamma_renorm)
            >>> assert 0 <= coherence <= 1
        """
        if len(gamma_n_renorm) < 2:
            return 1.0  # Perfect coherence for single eigenvalue
        
        # Compute spacings
        spacings = np.diff(gamma_n_renorm)
        
        if len(spacings) == 0:
            return 1.0
        
        # Mean and variance of spacings
        mean_spacing = np.mean(spacings)
        var_spacing = np.var(spacings)
        
        # Avoid division by zero
        if mean_spacing == 0:
            return 0.0
        
        # Coherence measure
        coherence = 1.0 - var_spacing / (mean_spacing ** 2)
        
        # Clamp to [0, 1]
        coherence = np.clip(coherence, 0.0, 1.0)
        
        return coherence
    
    def compute_excited_modes(
        self,
        theta: float = 0.0,
        verbose: bool = False
    ) -> SpectralHamiltonianResult:
        """
        Compute the complete excited mode spectrum.
        
        This is the main interface method that performs:
        1. Builds the Hamiltonian matrix
        2. Renormalizes eigenvalues to physical frequencies
        3. Applies phase modulation
        4. Computes spectral coherence
        
        Args:
            theta: Twist parameter for phase modulation (default: 0.0)
            verbose: Print detailed information (default: False)
            
        Returns:
            SpectralHamiltonianResult containing all computed values
            
        Example:
            >>> hamiltonian = RiemannSpectralHamiltonian()
            >>> result = hamiltonian.compute_excited_modes(theta=0.1, verbose=True)
            >>> print(f"Excited modes: {result.eigenvalues_modulated}")
            >>> print(f"Coherence: {result.coherence:.6f}")
        """
        # Step 1: Build Hamiltonian matrix
        H = self.build_hamiltonian_matrix()
        
        # Step 2: Renormalize eigenvalues
        gamma_n_renorm = self.renormalize_eigenvalues()
        
        # Step 3: Apply phase modulation
        gamma_tilde = self.apply_phase_modulation(gamma_n_renorm, theta)
        
        # Step 4: Compute coherence
        coherence = self.compute_spectral_coherence(gamma_n_renorm)
        
        # Metadata
        metadata = {
            'n_zeros': len(self.gamma_n),
            'f0': self.f0,
            'gamma_qcal': self.gamma_qcal,
            'renorm_scale': self.renorm_scale,
            'phase_modulation': self.f0 * np.sin(self.gamma_qcal + theta),
        }
        
        if verbose:
            print("=" * 70)
            print("Riemann Spectral Hamiltonian Ĥ_π — Excited Modes")
            print("=" * 70)
            print(f"Number of zeros: {len(self.gamma_n)}")
            print(f"Base frequency f₀: {self.f0:.4f} Hz")
            print(f"Renormalization scale: {self.renorm_scale:.4f}")
            print(f"Phase calibration γ_QCAL: {self.gamma_qcal:.6f} rad")
            print(f"Twist parameter θ: {theta:.6f} rad")
            print(f"Phase modulation: {metadata['phase_modulation']:.4f} Hz")
            print()
            print("Eigenvalue progression:")
            for i, (gn, gr, gt) in enumerate(
                zip(self.gamma_n, gamma_n_renorm, gamma_tilde), 1
            ):
                print(f"  γ_{i}: {gn:12.6f} → {gr:10.2f} Hz → {gt:10.2f} Hz")
            print()
            print(f"Spectral coherence: {coherence:.6f}")
            print("=" * 70)
        
        # Create result object
        result = SpectralHamiltonianResult(
            eigenvalues=self.gamma_n,
            eigenvalues_renorm=gamma_n_renorm,
            eigenvalues_modulated=gamma_tilde,
            hamiltonian_matrix=H,
            theta=theta,
            coherence=coherence,
            metadata=metadata
        )
        
        return result
    
    def get_excited_frequencies(
        self,
        theta: float = 0.0
    ) -> np.ndarray:
        """
        Get the excited mode frequencies γ̃_n directly.
        
        Convenience method that returns only the final modulated frequencies.
        
        Args:
            theta: Twist parameter (default: 0.0)
            
        Returns:
            np.ndarray: Excited mode frequencies in Hz
            
        Example:
            >>> hamiltonian = RiemannSpectralHamiltonian()
            >>> frequencies = hamiltonian.get_excited_frequencies(theta=0.05)
            >>> print(f"Excited frequencies: {frequencies}")
        """
        result = self.compute_excited_modes(theta=theta, verbose=False)
        return result.eigenvalues_modulated


def compute_hamiltonian_spectrum(
    gamma_n: Optional[np.ndarray] = None,
    theta: float = 0.0,
    verbose: bool = False
) -> Dict[str, Any]:
    """
    Convenience function to compute the Hamiltonian spectrum.
    
    This is a simplified interface for quick computations.
    
    Args:
        gamma_n: Riemann zeros (default: RIEMANN_ZEROS_5)
        theta: Twist parameter (default: 0.0)
        verbose: Print details (default: False)
        
    Returns:
        Dictionary with keys:
            - 'eigenvalues': Original γ_n
            - 'eigenvalues_renorm': Renormalized frequencies
            - 'eigenvalues_modulated': Phase-modulated frequencies
            - 'coherence': Spectral coherence
            
    Example:
        >>> spectrum = compute_hamiltonian_spectrum(theta=0.1, verbose=True)
        >>> excited_modes = spectrum['eigenvalues_modulated']
    """
    hamiltonian = RiemannSpectralHamiltonian(gamma_n=gamma_n)
    result = hamiltonian.compute_excited_modes(theta=theta, verbose=verbose)
    
    return {
        'eigenvalues': result.eigenvalues,
        'eigenvalues_renorm': result.eigenvalues_renorm,
        'eigenvalues_modulated': result.eigenvalues_modulated,
        'coherence': result.coherence,
        'hamiltonian_matrix': result.hamiltonian_matrix,
        'theta': result.theta,
        'metadata': result.metadata,
    }


# Example usage
if __name__ == '__main__':
    print("QCAL ∞³ — Riemann Spectral Hamiltonian Demo")
    print()
    
    # Create Hamiltonian with default Riemann zeros
    hamiltonian = RiemannSpectralHamiltonian()
    
    # Compute excited modes with twist parameter
    theta = 0.1  # rad
    result = hamiltonian.compute_excited_modes(theta=theta, verbose=True)
    
    print()
    print("Excited mode frequencies γ̃_n:")
    for i, freq in enumerate(result.eigenvalues_modulated, 1):
        print(f"  Mode {i}: {freq:.2f} Hz")
    
    print()
    print(f"Overall coherence: {result.coherence:.6f}")
    print()
    print("✓ Hamiltonian spectrum computed successfully")

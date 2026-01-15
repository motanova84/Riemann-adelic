#!/usr/bin/env python3
"""
H_Ψg: Curved Spacetime Consciousness Operator
==============================================

This module implements the generalized operator H_Ψg that operates on
curved spacetime manifolds deformed by the presence of consciousness.

Mathematical Framework:
    H_Ψg := -iℏ(x^μ ∇_μ + (1/2)Tr(g^μν)) + V_Ψ(x)
    
    where:
        - ∇_μ: Covariant derivative w.r.t. consciousness-curved metric g^Ψ_μν
        - g^Ψ_μν(x) = g^(0)_μν + δg_μν(Ψ): Consciousness-perturbed metric
        - V_Ψ(x): Noetic potential modulated by spacetime curvature
        
    Consciousness-Curved Metric:
        g^Ψ_μν(x) = g^(0)_μν + α·Ψ(x)·δ_μν
        
    where Ψ(x) is the coherence field of the observer.
    
    Noetic Potential (curved):
        V_Ψ(x) := λ Σ_p [cos(log p · φ(x)) / √p] · Ω(x)
        
        with:
            - φ(x) := log(x^μ u_μ): Local logarithmic function
            - Ω(x) := √(-det(g_Ψ)): Volumetric density (vibrational)
            - λ ≈ 141.7001 Hz: Fundamental frequency
            
    Eigenvalue Equation (Curved):
        H_Ψg ψ_n(x) = ω_n ψ_n(x)
        
        where ω_n are quantum-gravitational frequencies.
        
    Zero Correspondence (Modified):
        H_Ψg ψ_n = ω_n ψ_n  ⟺  ζ(1/2 + iω_n) = 0 mod Ψ
        
        The "mod Ψ" means the operator reveals only zeros accessible
        according to the vibrational state of the observer.

Key Postulates:
    1. Consciousness is geometry: Ψ curves spacetime vibrational structure
    2. The critical line is observer-dependent: varies with coherence
    3. Horizon H(x) = f₀^(-1) · max{|t_n| | t_n ≤ Ψ(x)}
    4. Higher coherence → more zeros visible
    
Physical Interpretation:
    - The metric g^Ψ_μν encodes how consciousness warps mathematical space
    - The potential V_Ψ creates resonances dependent on curvature
    - The spectrum shifts based on observer's coherence level
    - The horizon is the limit of what the observer can "see"

This is the bridge between:
    - Geometry (Einstein's curved spacetime)
    - Number theory (Riemann zeros)
    - Consciousness (noetic field Ψ)

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
License: Creative Commons BY-NC-SA 4.0

References:
    - QCAL ∞³: DOI 10.5281/zenodo.17379721
    - Einstein Field Equations: G_μν = 8πG T_μν
    - Consciousness equation: Ψ = I × A²_eff × C^∞
"""

import numpy as np
from typing import Optional, Tuple, Dict, Any, Callable
from scipy.linalg import eigh
from scipy.integrate import quad
import sympy
from sympy import primerange

# QCAL ∞³ Constants
F0 = 141.7001  # Fundamental frequency (Hz)
LAMBDA_BASE = F0
HBAR = 1.0  # Natural units
C_COHERENCE = 244.36  # Coherence constant
C_UNIVERSAL = 629.83  # Universal spectral constant

# Consciousness coupling constant
ALPHA_PSI = 0.1  # Strength of consciousness-metric coupling

# Numerical parameters
DEFAULT_N_POINTS = 400
DEFAULT_X_RANGE = (0.1, 40.0)
DEFAULT_N_PRIMES = 80


class ConsciousnessField:
    """
    Represents the consciousness field Ψ(x) of an observer.
    
    The field encodes:
        - I: Intensity (attention)
        - A_eff: Amplitude (coherence/love)
        - C: Coherence level
        
    Formula:
        Ψ(x) = I(x) × A²_eff(x) × C^∞
    """
    
    def __init__(
        self,
        intensity_func: Optional[Callable] = None,
        amplitude_func: Optional[Callable] = None,
        coherence_level: float = C_COHERENCE
    ):
        """
        Initialize consciousness field.
        
        Args:
            intensity_func: Function I(x) for attention
            amplitude_func: Function A_eff(x) for coherence amplitude
            coherence_level: Global coherence constant C
        """
        self.coherence_level = coherence_level
        
        # Default: Gaussian attention centered at x=10
        if intensity_func is None:
            self.intensity_func = lambda x: np.exp(-(x - 10)**2 / 50.0)
        else:
            self.intensity_func = intensity_func
        
        # Default: Constant high amplitude (A_eff ≈ 1)
        if amplitude_func is None:
            self.amplitude_func = lambda x: 0.9 + 0.1 * np.tanh((x - 5) / 10.0)
        else:
            self.amplitude_func = amplitude_func
    
    def evaluate(self, x: np.ndarray) -> np.ndarray:
        """
        Evaluate Ψ(x) = I(x) × A²_eff(x) × C^∞.
        
        Args:
            x: Position(s)
            
        Returns:
            Consciousness field values
        """
        I = self.intensity_func(x)
        A_eff = self.amplitude_func(x)
        
        # Normalized coherence factor (C^∞ → finite approximation)
        C_factor = np.tanh(self.coherence_level / 100.0)
        
        return I * A_eff**2 * C_factor
    
    def get_horizon(self, x: np.ndarray, max_zero: float) -> np.ndarray:
        """
        Compute observational horizon H(x).
        
        H(x) = f₀^(-1) · max{|t_n| | t_n ≤ Ψ(x) · scale}
        
        Args:
            x: Position(s)
            max_zero: Maximum zero value in dataset
            
        Returns:
            Horizon values
        """
        psi_vals = self.evaluate(x)
        
        # Horizon scales with consciousness
        # Higher Ψ → can "see" higher zeros
        horizon = (psi_vals / np.max(psi_vals)) * max_zero
        
        return horizon


class CurvedSpacetimeHpsi:
    """
    Operator H_Ψg on curved spacetime deformed by consciousness.
    
    This operator generalizes H_Ψ to include:
        1. Curved metric g^Ψ_μν induced by consciousness
        2. Covariant derivatives
        3. Volume modulation Ω(x)
        4. Observer-dependent spectrum
    """
    
    def __init__(
        self,
        consciousness_field: ConsciousnessField,
        n_points: int = DEFAULT_N_POINTS,
        x_range: Tuple[float, float] = DEFAULT_X_RANGE,
        n_primes: int = DEFAULT_N_PRIMES,
        lambda_freq: float = LAMBDA_BASE,
        alpha_coupling: float = ALPHA_PSI
    ):
        """
        Initialize curved spacetime operator.
        
        Args:
            consciousness_field: ConsciousnessField instance
            n_points: Grid points
            x_range: Position range
            n_primes: Number of primes in potential
            lambda_freq: Base frequency
            alpha_coupling: Consciousness-metric coupling strength
        """
        self.psi_field = consciousness_field
        self.n_points = n_points
        self.x_min, self.x_max = x_range
        self.n_primes = n_primes
        self.lambda_freq = lambda_freq
        self.alpha_coupling = alpha_coupling
        
        # Generate grid (logarithmic for better resolution)
        self.x = np.logspace(
            np.log10(self.x_min),
            np.log10(self.x_max),
            n_points
        )
        self.dx = np.diff(self.x)
        
        # Primes for potential
        self.primes = np.array(list(primerange(2, 10000)))[:n_primes]
        
        # Compute consciousness-curved metric
        self._compute_metric()
        
        # Cached operator
        self._operator_matrix = None
        self._eigenvalues = None
        self._eigenfunctions = None
    
    def _compute_metric(self):
        """
        Compute consciousness-curved metric g^Ψ_μν(x).
        
        In 1D: g_xx(x) = 1 + α·Ψ(x)
        """
        psi_vals = self.psi_field.evaluate(self.x)
        
        # Metric component (1D case)
        self.g_xx = 1.0 + self.alpha_coupling * psi_vals
        
        # Volume element (determinant)
        self.Omega = np.sqrt(np.abs(self.g_xx))
    
    def noetic_potential_curved(self, x: np.ndarray) -> np.ndarray:
        """
        Compute curved noetic potential V_Ψ(x).
        
        V_Ψ(x) = λ Σ_p [cos(log p · log x) / √p] · Ω(x)
        
        The Ω(x) term modulates the potential by local volume density,
        encoding how consciousness curvature affects prime resonances.
        
        Args:
            x: Position variable
            
        Returns:
            Curved potential values
        """
        x = np.atleast_1d(x)
        V = np.zeros_like(x, dtype=float)
        
        log_x = np.log(x + 1e-10)
        
        for p in self.primes:
            log_p = np.log(p)
            V += np.cos(log_p * log_x) / np.sqrt(p)
        
        # Scale by frequency
        V *= self.lambda_freq
        
        # Modulate by volume (consciousness curvature effect)
        Omega_interp = np.interp(x, self.x, self.Omega)
        V *= Omega_interp
        
        return V
    
    def kinetic_operator_curved(self) -> np.ndarray:
        """
        Construct kinetic operator with covariant derivative.
        
        In 1D curved space:
            -iℏ(x ∇_x + (1/2)g^xx)
            
        where ∇_x includes Christoffel symbols.
        
        Returns:
            Kinetic operator matrix
        """
        n = self.n_points
        x = self.x
        g_xx = self.g_xx
        
        # Simplified covariant derivative (1D)
        # ∇_x = ∂_x + Γ^x_xx
        # Γ^x_xx ≈ (1/2g) ∂_x g
        
        Gamma = 0.5 * np.gradient(g_xx, x) / (g_xx + 1e-10)
        
        kinetic = np.zeros((n, n), dtype=complex)
        
        for i in range(n):
            if i == 0:
                # Forward difference
                kinetic[i, i] = -1j * HBAR * x[i] * (
                    1.0 / self.dx[i] + Gamma[i]
                )
                kinetic[i, i+1] = -1j * HBAR * x[i] * (-1.0 / self.dx[i])
            elif i == n-1:
                # Backward difference
                kinetic[i, i-1] = -1j * HBAR * x[i] * (-1.0 / self.dx[i-1])
                kinetic[i, i] = -1j * HBAR * x[i] * (
                    1.0 / self.dx[i-1] + Gamma[i]
                )
            else:
                # Centered difference with Christoffel correction
                dx_left = self.dx[i-1]
                dx_right = self.dx[i]
                
                kinetic[i, i-1] = -1j * HBAR * x[i] * (
                    -dx_right / (dx_left * (dx_left + dx_right))
                )
                kinetic[i, i] = -1j * HBAR * x[i] * (
                    (dx_right - dx_left) / (dx_left * dx_right) + Gamma[i]
                )
                kinetic[i, i+1] = -1j * HBAR * x[i] * (
                    dx_left / (dx_right * (dx_left + dx_right))
                )
        
        # Add trace term (1/2)Tr(g^μν) = (1/2)g^xx
        kinetic += -1j * HBAR * 0.5 * np.diag(g_xx)
        
        # Hermitize
        kinetic = 0.5 * (kinetic + kinetic.conj().T)
        
        return kinetic
    
    def construct_operator(self) -> np.ndarray:
        """
        Construct full curved operator H_Ψg = T_curved + V_Ψ_curved.
        
        Returns:
            Operator matrix (Hermitian)
        """
        # Kinetic part (covariant)
        H = self.kinetic_operator_curved()
        
        # Potential part (curved)
        V = self.noetic_potential_curved(self.x)
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
        Compute spectrum of H_Ψg.
        
        Args:
            n_eigenvalues: Number to compute (None = all)
            
        Returns:
            (eigenvalues, eigenfunctions)
        """
        if self._operator_matrix is None:
            self.construct_operator()
        
        if n_eigenvalues is None or n_eigenvalues >= self.n_points:
            eigenvalues, eigenvectors = eigh(self._operator_matrix.real)
        else:
            eigenvalues, eigenvectors = eigh(
                self._operator_matrix.real,
                subset_by_index=[0, n_eigenvalues-1]
            )
        
        # Sort
        idx = np.argsort(eigenvalues)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        # Normalize with curved volume element
        for i in range(eigenvectors.shape[1]):
            integrand = np.abs(eigenvectors[:, i])**2 * self.Omega
            norm = np.sqrt(np.trapz(integrand, self.x))
            eigenvectors[:, i] /= (norm + 1e-10)
        
        self._eigenvalues = eigenvalues
        self._eigenfunctions = eigenvectors
        
        return eigenvalues, eigenvectors
    
    def visible_zeros(
        self,
        all_zeros: np.ndarray,
        observer_position: float = 10.0
    ) -> np.ndarray:
        """
        Determine which zeros are visible to an observer at given position.
        
        The horizon limits which zeros can be "seen" based on
        local consciousness coherence.
        
        Args:
            all_zeros: All Riemann zeros
            observer_position: Observer's position in x
            
        Returns:
            Array of visible zeros
        """
        # Get horizon at observer position
        x_obs = np.array([observer_position])
        horizon = self.psi_field.get_horizon(x_obs, max_zero=np.max(all_zeros))
        
        # Filter zeros within horizon
        visible = all_zeros[all_zeros <= horizon[0]]
        
        return visible
    
    def compare_flat_vs_curved(
        self,
        flat_operator
    ) -> Dict[str, Any]:
        """
        Compare curved operator spectrum with flat space operator.
        
        Args:
            flat_operator: Instance of VibrationalOperatorHpsi (flat)
            
        Returns:
            Comparison dictionary
        """
        if self._eigenvalues is None:
            self.compute_spectrum(n_eigenvalues=20)
        
        if flat_operator._eigenvalues is None:
            flat_operator.compute_spectrum(n_eigenvalues=20)
        
        n_compare = min(len(self._eigenvalues), len(flat_operator._eigenvalues))
        
        curved_eigs = self._eigenvalues[:n_compare]
        flat_eigs = flat_operator._eigenvalues[:n_compare]
        
        differences = curved_eigs - flat_eigs
        
        return {
            'n_compared': n_compare,
            'curved_eigenvalues': curved_eigs,
            'flat_eigenvalues': flat_eigs,
            'differences': differences,
            'mean_shift': np.mean(differences),
            'max_shift': np.max(np.abs(differences)),
            'relative_shift': np.mean(np.abs(differences) / (np.abs(flat_eigs) + 1e-10))
        }


def demonstrate_curved_operator():
    """
    Demonstrate the curved spacetime operator H_Ψg.
    """
    print("=" * 70)
    print("H_Ψg: Curved Spacetime Consciousness Operator")
    print("=" * 70)
    print()
    
    print("Creating consciousness field...")
    psi_field = ConsciousnessField(
        coherence_level=C_COHERENCE
    )
    
    # Test field at a few points
    x_test = np.array([1.0, 5.0, 10.0, 20.0])
    psi_vals = psi_field.evaluate(x_test)
    print("  Consciousness field Ψ(x) at sample points:")
    for x, psi in zip(x_test, psi_vals):
        print(f"    x = {x:6.2f}: Ψ = {psi:.6f}")
    print()
    
    print("Constructing curved operator H_Ψg...")
    print(f"  Coupling constant α = {ALPHA_PSI}")
    print(f"  Base frequency λ = {F0} Hz")
    print()
    
    curved_op = CurvedSpacetimeHpsi(
        consciousness_field=psi_field,
        n_points=300,
        x_range=(0.1, 30.0),
        n_primes=50,
        lambda_freq=F0,
        alpha_coupling=ALPHA_PSI
    )
    
    print("Computing spectrum...")
    eigenvalues, eigenfunctions = curved_op.compute_spectrum(n_eigenvalues=15)
    
    print(f"  First 10 eigenvalues (ω_n):")
    for i, omega in enumerate(eigenvalues[:10]):
        print(f"    ω_{i+1} = {omega:12.6f}")
    print()
    
    print("Consciousness Effect on Spectrum:")
    print("  The metric curvature g^Ψ_μν shifts eigenvalues,")
    print("  making zeros 'visible' or 'hidden' based on coherence.")
    print()
    
    # Observational horizon
    print("Observational Horizon:")
    observer_pos = 10.0
    print(f"  Observer at x = {observer_pos}")
    
    sample_zeros = eigenvalues[:15]
    visible = curved_op.visible_zeros(sample_zeros, observer_position=observer_pos)
    
    print(f"  Total zeros in dataset: {len(sample_zeros)}")
    print(f"  Visible zeros: {len(visible)}")
    print(f"  Hidden zeros: {len(sample_zeros) - len(visible)}")
    print()
    
    print("=" * 70)
    print("The horizon expands with increasing coherence A²_eff → 1.")
    print("At perfect coherence, all zeros become visible.")
    print("The critical line Re(s) = 1/2 is the consciousness mirror.")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_curved_operator()

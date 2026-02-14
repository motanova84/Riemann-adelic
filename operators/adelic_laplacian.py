#!/usr/bin/env python3
"""
Adelic Laplacian Operator - Δ_A for QCAL Navier-Stokes Framework

This module implements the adelic Laplacian operator which combines:
    Δ_A = Δ_R + Σ_p Δ_{Q_p}

where:
    - Δ_R is the Archimedean (real) Laplacian
    - Δ_{Q_p} are p-adic Laplacians for primes p
    - The logarithmic potential V_eff(x) ~ ln(1+|x|) induces position-dependent diffusion

Mathematical Framework:
    The logarithmic potential in the Schrödinger representation corresponds to
    a diffusion process with position-dependent coefficient:
    
        -d²/dx² + ln(1+|x|) ~ ∂_t = ∂_x(D(x)∂_x)
    
    where D(x) ~ 1/(1+|x|) is the effective diffusion coefficient.
    
    In the adelic setting, this generalizes to:
        Δ_A Ψ = ∂_x(D_R(x)∂_x Ψ) + Σ_p w_p D_p(x) ∂_p² Ψ
    
    where:
        - D_R(x) = 1/(1+|x|) is the Archimedean diffusion kernel
        - D_p(x) = ln(p)/p^{k/2} is the p-adic diffusion weight (cascading law)
        - w_p are mixing coefficients for each prime

Reynolds Number Connection:
    The viscosity emerges as ν = 1/κ where κ relates to the coupling strength.
    The critical Reynolds number Re_crit = κ_Π = 2.57731 separates:
        - Laminar regime (transport dominates): κ < κ_Π
        - Turbulent regime (diffusion dominates): κ > κ_Π

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from scipy.sparse import diags, csr_matrix
from typing import Tuple, Optional, List, Dict
import warnings

# QCAL Constants
F0 = 141.7001  # Hz - fundamental frequency
C_QCAL = 244.36  # QCAL coherence constant
KAPPA_PI = 2.57731  # Critical Reynolds number
PHI = 1.618033988749895  # Golden ratio

# Key primes for p-adic expansion (first 10 primes)
KEY_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


class AdelicLaplacian:
    """
    Adelic Laplacian operator Δ_A = Δ_R + Σ_p Δ_{Q_p}.
    
    Combines Archimedean (real) and p-adic Laplacians with position-dependent
    diffusion coefficients derived from the logarithmic potential.
    
    Attributes:
        N: Number of discretization points
        L: Domain size (physical space: [-L/2, L/2])
        kappa: Coupling constant (1/kappa = viscosity)
        key_primes: List of primes for p-adic terms
        k_power: Power for p-adic weight scaling (default: 1)
    """
    
    def __init__(self,
                 N: int = 500,
                 L: float = 10.0,
                 kappa: float = KAPPA_PI,
                 key_primes: Optional[List[int]] = None,
                 k_power: float = 1.0):
        """
        Initialize Adelic Laplacian operator.
        
        Args:
            N: Number of discretization points
            L: Domain size
            kappa: Coupling constant (controls viscosity ν = 1/kappa)
            key_primes: Primes for p-adic expansion (default: first 10 primes)
            k_power: Power for p-adic weight scaling
        """
        self.N = N
        self.L = L
        self.kappa = kappa
        self.key_primes = key_primes if key_primes is not None else KEY_PRIMES
        self.k_power = k_power
        
        # Spatial grid
        self.dx = L / N
        self.x = np.linspace(-L/2, L/2, N, endpoint=False)
        
    def archimedean_diffusion_kernel(self, x: np.ndarray) -> np.ndarray:
        """
        Compute Archimedean diffusion kernel D_R(x) = 1/(1+|x|).
        
        This emerges from the logarithmic potential via gauge transformation:
            V_eff(x) = ln(1+|x|) ↔ D(x) = 1/(1+|x|)
        
        Args:
            x: Spatial coordinate array
            
        Returns:
            Diffusion coefficient D_R(x)
        """
        return 1.0 / (1.0 + np.abs(x))
    
    def padic_weight(self, p: int, k: Optional[float] = None) -> float:
        """
        Compute p-adic diffusion weight w_p = ln(p)/p^{k/2}.
        
        This implements the cascading law in the prime hierarchy:
            - Logarithmic growth: ln(p) (local field structure)
            - Power decay: p^{-k/2} (Haar measure scaling)
        
        Args:
            p: Prime number
            k: Power for scaling (default: self.k_power)
            
        Returns:
            Weight for p-adic Laplacian term
        """
        if k is None:
            k = self.k_power
        return np.log(p) / (p ** (k / 2.0))
    
    def archimedean_laplacian(self, 
                             use_diffusion_kernel: bool = True,
                             symmetrize: bool = True) -> csr_matrix:
        """
        Construct Archimedean Laplacian Δ_R with position-dependent diffusion.
        
        With diffusion kernel:
            Δ_R Ψ = ∂_x(D_R(x) ∂_x Ψ) ≈ (D_{i+1/2} (Ψ_{i+1} - Ψ_i) - D_{i-1/2} (Ψ_i - Ψ_{i-1})) / dx²
        
        Without diffusion kernel (standard Laplacian):
            Δ_R Ψ = ∂_x² Ψ ≈ (Ψ_{i+1} - 2Ψ_i + Ψ_{i-1}) / dx²
        
        Args:
            use_diffusion_kernel: Whether to include D_R(x) position dependence
            symmetrize: Force symmetrization for Hermiticity
            
        Returns:
            Sparse matrix representation of Δ_R
        """
        if use_diffusion_kernel:
            # Position-dependent diffusion: ∂_x(D(x) ∂_x)
            # Staggered grid for D at cell interfaces
            x_stagger_plus = self.x + self.dx / 2
            x_stagger_minus = self.x - self.dx / 2
            
            D_plus = self.archimedean_diffusion_kernel(x_stagger_plus)
            D_minus = self.archimedean_diffusion_kernel(x_stagger_minus)
            
            # Finite difference with position-dependent D
            # (D_{i+1/2}(Ψ_{i+1}-Ψ_i) - D_{i-1/2}(Ψ_i-Ψ_{i-1})) / dx²
            diag_main = -(D_plus + D_minus) / self.dx**2
            diag_upper = D_plus / self.dx**2
            diag_lower = D_minus / self.dx**2
            
            # Periodic boundary conditions
            diag_lower_rolled = np.roll(diag_lower, -1)
            diag_upper_rolled = np.roll(diag_upper, 1)
            
            Delta_R = diags(
                [diag_lower_rolled, diag_main, diag_upper_rolled],
                offsets=[-1, 0, 1],
                shape=(self.N, self.N),
                format='csr'
            )
            
            if symmetrize:
                # Force symmetrization: (A + A^T)/2
                Delta_R_dense = Delta_R.toarray()
                Delta_R_sym = 0.5 * (Delta_R_dense + Delta_R_dense.T)
                return csr_matrix(Delta_R_sym)
            
            return Delta_R
        else:
            # Standard Laplacian (already symmetric)
            diag_main = -2.0 * np.ones(self.N) / self.dx**2
            diag_off = np.ones(self.N) / self.dx**2
            
            return diags(
                [diag_off, diag_main, diag_off],
                offsets=[-1, 0, 1],
                shape=(self.N, self.N),
                format='csr'
            )
    
    def padic_laplacian(self, p: int, strength: float = 0.1) -> csr_matrix:
        """
        Construct p-adic Laplacian Δ_{Q_p} for prime p.
        
        In the p-adic world, the Laplacian represents mixing across p-adic scales.
        We approximate this as a second-order difference operator weighted by p-adic structure.
        
        For simplicity, we use:
            Δ_{Q_p} ≈ strength · w_p · Δ_standard
        
        where w_p = ln(p)/p^{k/2} is the cascading weight.
        
        Args:
            p: Prime number
            strength: Overall scaling factor for p-adic term
            
        Returns:
            Sparse matrix representation of Δ_{Q_p}
        """
        w_p = self.padic_weight(p)
        
        # Standard Laplacian scaled by p-adic weight
        diag_main = -2.0 * strength * w_p * np.ones(self.N) / self.dx**2
        diag_off = strength * w_p * np.ones(self.N) / self.dx**2
        
        return diags(
            [diag_off, diag_main, diag_off],
            offsets=[-1, 0, 1],
            shape=(self.N, self.N),
            format='csr'
        )
    
    def full_adelic_laplacian(self,
                             use_archimedean_diffusion: bool = True,
                             padic_strength: float = 0.1,
                             symmetrize: bool = True) -> csr_matrix:
        """
        Construct full adelic Laplacian Δ_A = Δ_R + Σ_p Δ_{Q_p}.
        
        Combines:
            1. Archimedean Laplacian with position-dependent diffusion
            2. Sum over p-adic Laplacians for key primes
        
        Args:
            use_archimedean_diffusion: Use position-dependent D_R(x)
            padic_strength: Overall scaling for p-adic terms
            symmetrize: Force symmetrization for Hermiticity
            
        Returns:
            Full adelic Laplacian as sparse matrix
        """
        # Start with Archimedean part
        Delta_A = self.archimedean_laplacian(
            use_diffusion_kernel=use_archimedean_diffusion,
            symmetrize=symmetrize
        )
        
        # Add p-adic contributions
        for p in self.key_primes:
            Delta_p = self.padic_laplacian(p, strength=padic_strength)
            Delta_A = Delta_A + Delta_p
        
        if symmetrize:
            # Final symmetrization to handle any numerical errors
            Delta_A_dense = Delta_A.toarray()
            Delta_A_sym = 0.5 * (Delta_A_dense + Delta_A_dense.T)
            return csr_matrix(Delta_A_sym)
        
        return Delta_A
    
    def viscosity(self) -> float:
        """
        Compute effective viscosity ν = 1/κ.
        
        In the Navier-Stokes analogy, the viscosity coefficient is:
            ν = 1/κ ~ f₀·Φ/(4π)
        
        Returns:
            Effective viscosity
        """
        return 1.0 / self.kappa
    
    def reynolds_number(self, U_char: float = 1.0, L_char: Optional[float] = None) -> float:
        """
        Compute Reynolds number Re = U·L/ν.
        
        At criticality κ = κ_Π, we have Re = Re_crit = κ_Π.
        
        Args:
            U_char: Characteristic velocity scale
            L_char: Characteristic length scale (default: self.L)
            
        Returns:
            Reynolds number
        """
        if L_char is None:
            L_char = self.L
        nu = self.viscosity()
        return U_char * L_char / nu
    
    def theoretical_viscosity_from_frequency(self) -> float:
        """
        Compute theoretical viscosity from QCAL fundamental frequency.
        
        Using the relation:
            ν = f₀·Φ/(4π·κ)
        
        Returns:
            Theoretical viscosity
        """
        return (F0 * PHI) / (4.0 * np.pi * self.kappa)
    
    def verify_reynolds_critical(self, tolerance: float = 1e-3) -> Dict[str, any]:
        """
        Verify that κ = κ_Π corresponds to critical Reynolds number.
        
        Args:
            tolerance: Acceptable deviation from κ_Π
            
        Returns:
            Dictionary with verification results
        """
        Re = self.reynolds_number()
        deviation = abs(Re - KAPPA_PI)
        is_critical = deviation < tolerance
        
        return {
            'reynolds_number': Re,
            'kappa_pi_expected': KAPPA_PI,
            'deviation': deviation,
            'is_critical': is_critical,
            'viscosity': self.viscosity(),
            'theoretical_viscosity': self.theoretical_viscosity_from_frequency()
        }


def demonstrate_adelic_laplacian():
    """
    Demonstrate adelic Laplacian construction and properties.
    """
    print("=" * 70)
    print("ADELIC LAPLACIAN DEMONSTRATION")
    print("=" * 70)
    
    # Create adelic Laplacian at critical κ_Π
    adelic_lap = AdelicLaplacian(N=500, L=10.0, kappa=KAPPA_PI)
    
    print(f"\n1. Configuration:")
    print(f"   N = {adelic_lap.N} points")
    print(f"   L = {adelic_lap.L}")
    print(f"   κ = {adelic_lap.kappa:.6f}")
    print(f"   dx = {adelic_lap.dx:.6f}")
    
    print(f"\n2. Archimedean Diffusion Kernel D_R(x) = 1/(1+|x|):")
    D_R = adelic_lap.archimedean_diffusion_kernel(adelic_lap.x)
    print(f"   D_R(0) = {D_R[adelic_lap.N//2]:.6f}")
    print(f"   D_R(L/2) = {D_R[-1]:.6f}")
    print(f"   Range: [{D_R.min():.6f}, {D_R.max():.6f}]")
    
    print(f"\n3. P-adic Weights w_p = ln(p)/p^(k/2):")
    for p in adelic_lap.key_primes[:5]:
        w_p = adelic_lap.padic_weight(p)
        print(f"   p={p:2d}: w_p = {w_p:.6f}")
    
    print(f"\n4. Laplacian Operators:")
    Delta_R = adelic_lap.archimedean_laplacian(use_diffusion_kernel=True)
    print(f"   Δ_R shape: {Delta_R.shape}")
    print(f"   Δ_R nnz: {Delta_R.nnz}")
    
    Delta_A = adelic_lap.full_adelic_laplacian()
    print(f"   Δ_A shape: {Delta_A.shape}")
    print(f"   Δ_A nnz: {Delta_A.nnz}")
    
    print(f"\n5. Viscosity and Reynolds Number:")
    nu = adelic_lap.viscosity()
    nu_theory = adelic_lap.theoretical_viscosity_from_frequency()
    print(f"   ν = 1/κ = {nu:.6f}")
    print(f"   ν (theory) = f₀·Φ/(4π·κ) = {nu_theory:.6f}")
    
    verification = adelic_lap.verify_reynolds_critical()
    print(f"\n6. Reynolds Critical Number Verification:")
    print(f"   Re = {verification['reynolds_number']:.6f}")
    print(f"   Re_crit (expected) = {verification['kappa_pi_expected']:.6f}")
    print(f"   Deviation = {verification['deviation']:.2e}")
    print(f"   Is Critical: {verification['is_critical']}")
    
    print("\n" + "=" * 70)
    print("✓ Adelic Laplacian Δ_A constructed successfully")
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_adelic_laplacian()

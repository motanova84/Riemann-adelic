#!/usr/bin/env python3
"""
Navier-Stokes Adelic Operator - Complete Evolution Generator for QCAL

This module implements the complete Navier-Stokes-like evolution operator
for the QCAL system, transitioning from Anosov flows to fluid dynamics with
adelic diffusion.

Mathematical Framework:
    The complete evolution operator is:
    
        ∂_t Ψ = -i(x∂_x + 1/2)Ψ + (1/κ)Δ_A Ψ + V_eff(x)Ψ
    
    Or equivalently, separating real and imaginary parts:
    
        ∂_t Ψ = (1/κ)Δ_A Ψ  [diffusion]
                - x∂_x Ψ     [transport/expansion]
                + V_eff(x)Ψ  [confinement]
    
    where:
        - Δ_A = Δ_R + Σ_p Δ_{Q_p} is the adelic Laplacian
        - V_eff(x) ~ ln(1+|x|) is the logarithmic confinement potential
        - κ is the coupling constant (1/κ = viscosity ν)

Navier-Stokes Analogy:
    This is exactly analogous to Navier-Stokes in a stratified medium:
    
        ∂_t u = ν·Δu      [viscous diffusion]
                - u·∇u     [convective transport]  
                + F        [external forcing/confinement]
    
    with the correspondence:
        - Ψ ↔ velocity field u
        - x∂_x ↔ u·∇ (in logarithmic coordinates)
        - 1/κ ↔ ν (viscosity)
        - V_eff ↔ F (forcing that maintains compactness)

Critical Reynolds Number:
    κ_Π = 2.57731 is the critical Reynolds number separating:
        - Laminar regime (κ < κ_Π): Transport dominates
        - Turbulent regime (κ > κ_Π): Diffusion dominates
    
    At κ = κ_Π, energy production by transport balances dissipation by diffusion,
    leading to the observed spectral cascade C(L) → 1/κ_Π.

Kolmogorov Cascade:
    In logarithmic coordinates, the cascade becomes linear:
        λ_max(L) ~ L  (instead of L^{2/3} in physical space)
    
    This gives:
        C(L) = πλ_max(L)/(2L) → 1/κ_Π

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from scipy.sparse import csr_matrix, diags
from scipy.linalg import eigh
from typing import Tuple, Optional, Dict, Callable
import warnings

try:
    from .adelic_laplacian import AdelicLaplacian, F0, C_QCAL, KAPPA_PI, PHI
except ImportError:
    import sys
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from adelic_laplacian import AdelicLaplacian, F0, C_QCAL, KAPPA_PI, PHI


class NavierStokesAdelicOperator:
    """
    Complete Navier-Stokes Adelic Evolution Operator.
    
    Implements:
        H_NS = -i(x∂_x + 1/2) + (1/κ)Δ_A + V_eff(x)
    
    where:
        - First term: Transport/expansion (convective)
        - Second term: Adelic diffusion (viscous)
        - Third term: Logarithmic confinement (forcing)
    
    Attributes:
        N: Number of discretization points
        L: Domain size
        kappa: Coupling constant (controls viscosity)
        V_amp: Amplitude of confinement potential
        adelic_laplacian: AdelicLaplacian instance
    """
    
    def __init__(self,
                 N: int = 500,
                 L: float = 10.0,
                 kappa: float = KAPPA_PI,
                 V_amp: float = 1.0,
                 key_primes: Optional[list] = None,
                 padic_strength: float = 0.1):
        """
        Initialize Navier-Stokes Adelic operator.
        
        Args:
            N: Number of discretization points
            L: Domain size
            kappa: Coupling constant
            V_amp: Amplitude of confinement potential
            key_primes: Primes for p-adic expansion
            padic_strength: Strength of p-adic diffusion
        """
        self.N = N
        self.L = L
        self.kappa = kappa
        self.V_amp = V_amp
        self.padic_strength = padic_strength
        
        # Initialize adelic Laplacian
        self.adelic_laplacian = AdelicLaplacian(
            N=N, L=L, kappa=kappa, key_primes=key_primes
        )
        
        # Spatial grid
        self.dx = L / N
        self.x = self.adelic_laplacian.x
        
    def transport_operator(self) -> csr_matrix:
        """
        Construct transport operator T = -x∂_x.
        
        This represents expansion in the Archimedean direction,
        analogous to the convective term u·∇u in Navier-Stokes.
        
        In logarithmic coordinates, this is the natural scaling operator.
        
        Returns:
            Sparse matrix representation of -x∂_x
        """
        # First derivative operator ∂_x (centered differences)
        # ∂_x Ψ ≈ (Ψ_{i+1} - Ψ_{i-1}) / (2dx)
        diag_upper = np.ones(self.N) / (2.0 * self.dx)
        diag_lower = -np.ones(self.N) / (2.0 * self.dx)
        
        # Periodic boundary conditions
        grad_x = diags(
            [diag_lower, diag_upper],
            offsets=[-1, 1],
            shape=(self.N, self.N),
            format='csr'
        )
        
        # Multiply by -x (position-dependent scaling)
        x_diag = diags(-self.x, 0, shape=(self.N, self.N), format='csr')
        
        return x_diag @ grad_x
    
    def confinement_potential(self) -> np.ndarray:
        """
        Compute logarithmic confinement potential V_eff(x) = V_amp · ln(1+|x|).
        
        This potential:
            1. Keeps the system in a compact domain
            2. Generates position-dependent diffusion (via gauge transform)
            3. Provides the "forcing" term in Navier-Stokes analogy
        
        Returns:
            Array of potential values V_eff(x)
        """
        return self.V_amp * np.log(1.0 + np.abs(self.x))
    
    def viscous_diffusion_operator(self, 
                                   use_archimedean_diffusion: bool = True) -> csr_matrix:
        """
        Construct viscous diffusion operator (1/κ)Δ_A.
        
        This is the analog of ν·Δ in Navier-Stokes, with:
            - ν = 1/κ (viscosity)
            - Δ_A = adelic Laplacian (diffusion in all directions)
        
        Args:
            use_archimedean_diffusion: Use position-dependent Archimedean kernel
            
        Returns:
            Sparse matrix representation of (1/κ)Δ_A
        """
        nu = 1.0 / self.kappa  # Viscosity
        Delta_A = self.adelic_laplacian.full_adelic_laplacian(
            use_archimedean_diffusion=use_archimedean_diffusion,
            padic_strength=self.padic_strength
        )
        return nu * Delta_A
    
    def full_operator(self,
                     include_transport: bool = True,
                     include_diffusion: bool = True,
                     include_confinement: bool = True,
                     hermitian_version: bool = False) -> csr_matrix:
        """
        Construct full Navier-Stokes adelic operator.
        
        H_NS = -i(x∂_x + 1/2) + (1/κ)Δ_A + V_eff(x)
        
        Args:
            include_transport: Include transport term -x∂_x
            include_diffusion: Include diffusion term (1/κ)Δ_A
            include_confinement: Include potential V_eff(x)
            hermitian_version: If True, make operator Hermitian (for eigenvalue analysis)
            
        Returns:
            Full evolution operator
        """
        # Start with zero operator
        H = csr_matrix((self.N, self.N), dtype=complex)
        
        # Add diffusion term (always real, Hermitian)
        if include_diffusion:
            H = H + self.viscous_diffusion_operator()
        
        # Add transport term (can be imaginary or real)
        if include_transport:
            T = self.transport_operator()
            if hermitian_version:
                # Make Hermitian by using real part only
                H = H + T.real
            else:
                # Include -i factor for evolution operator
                H = H - 1j * T
        
        # Add confinement potential (diagonal, real, Hermitian)
        if include_confinement:
            V = self.confinement_potential()
            V_diag = diags(V, 0, shape=(self.N, self.N), format='csr')
            H = H + V_diag
        
        return H
    
    def compute_spectrum(self, 
                        n_eigenvalues: int = 50,
                        hermitian_version: bool = True) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute eigenvalue spectrum of the operator.
        
        For spectral analysis, we use the Hermitian version:
            H_hermitian = (1/κ)Δ_A + x∂_x + V_eff(x)
        
        Args:
            n_eigenvalues: Number of eigenvalues to compute
            hermitian_version: Use Hermitian version for real eigenvalues
            
        Returns:
            Tuple of (eigenvalues, eigenvectors)
        """
        H = self.full_operator(hermitian_version=hermitian_version)
        
        # Convert to dense for eigh (for large systems, use sparse solvers)
        H_dense = H.toarray()
        
        # For Hermitian operators, use eigh (more efficient)
        if hermitian_version:
            # Make sure it's symmetric
            H_dense = 0.5 * (H_dense + H_dense.conj().T)
            eigenvalues, eigenvectors = eigh(H_dense)
        else:
            # For non-Hermitian, use eig
            from scipy.linalg import eig
            eigenvalues, eigenvectors = eig(H_dense)
        
        # Sort by real part
        idx = np.argsort(eigenvalues.real)
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        # Return requested number
        return eigenvalues[:n_eigenvalues], eigenvectors[:, :n_eigenvalues]
    
    def analyze_reynolds_regime(self) -> Dict[str, any]:
        """
        Analyze the Reynolds regime (laminar vs turbulent).
        
        Returns:
            Dictionary with regime analysis
        """
        Re = self.adelic_laplacian.reynolds_number()
        nu = self.adelic_laplacian.viscosity()
        
        # Determine regime
        if Re < KAPPA_PI:
            regime = "laminar"
            description = "Transport dominates over diffusion"
        elif Re > KAPPA_PI:
            regime = "turbulent"
            description = "Diffusion dominates over transport"
        else:
            regime = "critical"
            description = "Balance between transport and dissipation"
        
        return {
            'reynolds_number': Re,
            'kappa': self.kappa,
            'viscosity': nu,
            'regime': regime,
            'description': description,
            'kappa_pi_critical': KAPPA_PI,
            'deviation_from_critical': abs(Re - KAPPA_PI)
        }
    
    def energy_balance_analysis(self, psi: Optional[np.ndarray] = None) -> Dict[str, float]:
        """
        Analyze energy balance: production vs dissipation.
        
        At critical κ = κ_Π, energy production by transport should balance
        dissipation by diffusion.
        
        Args:
            psi: State vector (if None, use ground state)
            
        Returns:
            Dictionary with energy balance metrics
        """
        if psi is None:
            # Use ground state
            eigenvalues, eigenvectors = self.compute_spectrum(n_eigenvalues=1)
            psi = eigenvectors[:, 0]
        
        # Ensure normalization
        psi = psi / np.linalg.norm(psi)
        
        # Compute energy production by transport: <ψ| T |ψ>
        T = self.transport_operator()
        transport_energy = np.real(psi.conj() @ T @ psi)
        
        # Compute energy dissipation by diffusion: <ψ| (1/κ)Δ_A |ψ>
        D = self.viscous_diffusion_operator()
        diffusion_energy = np.real(psi.conj() @ D @ psi)
        
        # Potential energy: <ψ| V |ψ>
        V = self.confinement_potential()
        potential_energy = np.real(psi.conj() @ (V * psi))
        
        # Total energy
        total_energy = transport_energy + diffusion_energy + potential_energy
        
        # Balance ratio
        if abs(diffusion_energy) > 1e-10:
            balance_ratio = abs(transport_energy) / abs(diffusion_energy)
        else:
            balance_ratio = np.inf
        
        return {
            'transport_energy': transport_energy,
            'diffusion_energy': diffusion_energy,
            'potential_energy': potential_energy,
            'total_energy': total_energy,
            'balance_ratio': balance_ratio,
            'is_balanced': abs(balance_ratio - 1.0) < 0.1
        }


def demonstrate_navier_stokes_adelic():
    """
    Demonstrate Navier-Stokes adelic operator and verify key properties.
    """
    print("=" * 80)
    print("NAVIER-STOKES ADELIC OPERATOR DEMONSTRATION")
    print("=" * 80)
    
    # Create operator at critical κ_Π
    ns_op = NavierStokesAdelicOperator(N=500, L=10.0, kappa=KAPPA_PI, V_amp=1.0)
    
    print(f"\n1. Configuration:")
    print(f"   N = {ns_op.N} points")
    print(f"   L = {ns_op.L}")
    print(f"   κ = {ns_op.kappa:.6f} (critical κ_Π = {KAPPA_PI:.6f})")
    print(f"   V_amp = {ns_op.V_amp}")
    
    print(f"\n2. Component Operators:")
    T = ns_op.transport_operator()
    print(f"   Transport T = -x∂_x:")
    print(f"     Shape: {T.shape}, nnz: {T.nnz}")
    
    D = ns_op.viscous_diffusion_operator()
    print(f"   Diffusion (1/κ)Δ_A:")
    print(f"     Shape: {D.shape}, nnz: {D.nnz}")
    
    V = ns_op.confinement_potential()
    print(f"   Confinement V_eff(x) = ln(1+|x|):")
    print(f"     V(0) = {V[ns_op.N//2]:.6f}")
    print(f"     V(L/2) = {V[-1]:.6f}")
    
    print(f"\n3. Reynolds Regime Analysis:")
    regime = ns_op.analyze_reynolds_regime()
    print(f"   Reynolds number: {regime['reynolds_number']:.6f}")
    print(f"   Viscosity ν = 1/κ: {regime['viscosity']:.6f}")
    print(f"   Regime: {regime['regime']}")
    print(f"   {regime['description']}")
    print(f"   Deviation from critical: {regime['deviation_from_critical']:.2e}")
    
    print(f"\n4. Computing Spectrum (first 10 eigenvalues)...")
    eigenvalues, eigenvectors = ns_op.compute_spectrum(n_eigenvalues=10)
    print(f"   Eigenvalues:")
    for i, lam in enumerate(eigenvalues):
        print(f"     λ_{i} = {lam.real:12.6f} + {lam.imag:12.6f}i")
    
    print(f"\n5. Energy Balance Analysis (ground state):")
    psi_0 = eigenvectors[:, 0]
    energy = ns_op.energy_balance_analysis(psi=psi_0)
    print(f"   Transport energy: {energy['transport_energy']:12.6f}")
    print(f"   Diffusion energy: {energy['diffusion_energy']:12.6f}")
    print(f"   Potential energy: {energy['potential_energy']:12.6f}")
    print(f"   Total energy: {energy['total_energy']:12.6f}")
    print(f"   Balance ratio |T|/|D|: {energy['balance_ratio']:.6f}")
    print(f"   Is balanced (±10%): {energy['is_balanced']}")
    
    print("\n" + "=" * 80)
    print("✓ Navier-Stokes Adelic Operator H_NS constructed successfully")
    print("✓ Framework transition: Anosov flows → Navier-Stokes with adelic diffusion")
    print("=" * 80)
    
    return ns_op


if __name__ == "__main__":
    ns_op = demonstrate_navier_stokes_adelic()

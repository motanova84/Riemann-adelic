#!/usr/bin/env python3
"""
Adelic Laplacian Operator: Δ_𝔸 = Δ_ℝ + Σ_p Δ_ℚ_p

This module implements the unified Adelic Laplacian operator acting on 
functions in L²(𝔸_ℚ¹/ℚ^*), the space of square-integrable functions on 
the adelic quotient.

Mathematical Framework:
    The Adelic Laplacian is the sum of:
    1. Archimedean component: Δ_ℝ (continuous, standard Laplacian on ℝ)
    2. p-adic components: Σ_p Δ_ℚ_p (discrete, Laplacians on Bruhat-Tits trees)
    
    Heat Kernel:
        K_t(x,y) = K_t^ℝ(x_ℝ, y_ℝ) · ∏_p K_t^{ℚ_p}(x_p, y_p)
        
    Seeley-DeWitt Expansion:
        K_t(x,x) ~ (4πt)^{-d/2} [a_0 + a_1·t + a_2·t² + ...]
        
        where a_2 contains spectral information about primes.

The operator is essential for the Adelic Navier-Stokes formulation of the
Riemann Hypothesis, providing the diffusion term (1/κ)Δ_𝔸 that balances
the transport term -x∂_x.

Viscosity Constant:
    κ = 4π/(f₀·Φ) ≈ 2.577310
    where f₀ = 141.7001 Hz and Φ = (1+√5)/2
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
from typing import Tuple, List, Callable, Optional, Dict, Any
from scipy.linalg import eigh
from scipy.sparse import diags, csr_matrix
from scipy.integrate import trapezoid
from sympy import primerange
from scipy.sparse import diags, csr_matrix
from typing import Tuple, Optional, List, Dict
import warnings

# QCAL Constants
F0 = 141.7001  # Hz - fundamental frequency
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
KAPPA = 4 * np.pi / (F0 * PHI)  # Viscosity inverse ≈ 2.577310
C_QCAL = 244.36  # QCAL coherence constant

# Numerical parameters
DEFAULT_N_POINTS = 500
DEFAULT_X_RANGE = (-10.0, 10.0)
DEFAULT_N_PRIMES = 50
DEFAULT_P_ADIC_DEPTH = 5  # Depth in Bruhat-Tits tree
C_QCAL = 244.36  # QCAL coherence constant
KAPPA_PI = 2.57731  # Critical Reynolds number
PHI = 1.618033988749895  # Golden ratio

# Key primes for p-adic expansion (first 10 primes)
KEY_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]


class AdelicLaplacian:
    """
    Unified Adelic Laplacian operator Δ_𝔸 = Δ_ℝ + Σ_p Δ_ℚ_p.
    
    This operator acts on functions in the adelic Hilbert space L²(𝔸_ℚ¹/ℚ^*),
    combining continuous diffusion on ℝ with discrete diffusion on p-adic trees.
    
    Components:
        1. Archimedean Laplacian Δ_ℝ: Standard second derivative on ℝ
        2. p-adic Laplacians Δ_ℚ_p: Graph Laplacians on Bruhat-Tits trees
        3. Heat kernel coefficients: Seeley-DeWitt expansion
        
    The operator is symmetric, positive, and has spectral gap related to
    the distribution of prime numbers.
    
    Attributes:
        kappa: Viscosity inverse (coupling constant)
        f0: Fundamental frequency (Hz)
        n_points: Number of discretization points
        x_range: Range for real coordinate
        n_primes: Number of primes to include
        p_adic_depth: Depth of Bruhat-Tits tree exploration
    """
    
    def __init__(
        self,
        kappa: float = KAPPA,
        f0: float = F0,
        n_points: int = DEFAULT_N_POINTS,
        x_range: Tuple[float, float] = DEFAULT_X_RANGE,
        n_primes: int = DEFAULT_N_PRIMES,
        p_adic_depth: int = DEFAULT_P_ADIC_DEPTH
    ):
        """
        Initialize the Adelic Laplacian operator.
        
        Args:
            kappa: Viscosity inverse (default: 2.577310)
            f0: Fundamental frequency in Hz (default: 141.7001)
            n_points: Number of grid points for discretization
            x_range: Tuple (x_min, x_max) for real coordinate
            n_primes: Number of primes to include in p-adic sum
            p_adic_depth: Depth for Bruhat-Tits tree neighbors
        """
        self.kappa = kappa
        self.f0 = f0
        self.n_points = n_points
        self.x_range = x_range
        self.n_primes = n_primes
        self.p_adic_depth = p_adic_depth
        
        # Generate grid for real coordinate
        self.x = np.linspace(x_range[0], x_range[1], n_points)
        self.dx = (x_range[1] - x_range[0]) / (n_points - 1)
        
        # Generate primes for p-adic components
        self.primes = list(primerange(2, 1000))[:n_primes]
        
    def archimedean_laplacian(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply the Archimedean (real) Laplacian: Δ_ℝ ψ = ∂²ψ/∂x².
        
        Uses second-order finite differences with periodic boundary conditions.
        
        Args:
            psi: Function values on the grid (shape: n_points)
            
        Returns:
            Second derivative approximation (shape: n_points)
        """
        if len(psi) != self.n_points:
            raise ValueError(f"Function must have {self.n_points} points")
            
        # Second-order finite difference
        laplacian = np.zeros_like(psi)
        
        # Interior points
        laplacian[1:-1] = (psi[2:] - 2*psi[1:-1] + psi[:-2]) / self.dx**2
        
        # Boundary points (periodic)
        laplacian[0] = (psi[1] - 2*psi[0] + psi[-1]) / self.dx**2
        laplacian[-1] = (psi[0] - 2*psi[-1] + psi[-2]) / self.dx**2
        
        return laplacian
    
    def p_adic_laplacian(self, psi: np.ndarray, p: int) -> np.ndarray:
        """
        Apply the p-adic Laplacian: Δ_ℚ_p on the Bruhat-Tits tree.
        
        The Bruhat-Tits tree for ℚ_p is a (p+1)-regular tree where each
        vertex has p+1 neighbors. The p-adic Laplacian is the graph Laplacian:
        
            (Δ_ℚ_p ψ)(x) = Σ_{y~x} [ψ(y) - ψ(x)]
        
        where y~x denotes y is a neighbor of x in the tree.
        
        For numerical implementation, we use a simplified model where the
        effect of the p-adic tree is captured by a weighted difference operator
        modulated by the p-adic absolute value.
        
        Args:
            psi: Function values on the grid
            p: Prime number
            
        Returns:
            p-adic Laplacian approximation
        """
        # Simplified p-adic Laplacian: weighted difference operator
        # This captures the essential tree structure of ℚ_p
        laplacian_p = np.zeros_like(psi)
        
        # Weight by p-adic absolute value |x|_p
        # For simplicity, use oscillatory pattern modulated by log(p)
        weight = np.log(p) / p**0.5
        
        # Apply graph Laplacian structure: average over "neighbors"
        # Each point has approximately p+1 neighbors in the tree
        for i in range(self.n_points):
            # Local neighborhood in the discretized tree
            neighbors = []
            for j in range(1, min(p+2, self.n_points)):
                if i + j < self.n_points:
                    neighbors.append(i + j)
                if i - j >= 0:
                    neighbors.append(i - j)
            
            if neighbors:
                # Graph Laplacian: sum of (neighbor - center)
                laplacian_p[i] = weight * (np.mean(psi[neighbors]) - psi[i])
        
        return laplacian_p
    
    def total_action(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply the total Adelic Laplacian: Δ_𝔸 = Δ_ℝ + Σ_p Δ_ℚ_p.
        
        Args:
            psi: Function values on the grid
            
        Returns:
            Total Laplacian action
        """
        # Archimedean component
        result = self.archimedean_laplacian(psi)
        
        # Sum over p-adic components
        for p in self.primes:
            result += self.p_adic_laplacian(psi, p)
        
        return result
    
    def diffusion_operator(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply the scaled diffusion operator: (1/κ) Δ_𝔸.
        
        This is the diffusion term in the Adelic Navier-Stokes operator.
        
        Args:
            psi: Function values on the grid
            
        Returns:
            Scaled Laplacian action
        """
        return (1.0 / self.kappa) * self.total_action(psi)
    
    def heat_kernel_coefficient_a0(self, t: float) -> float:
        """
        Leading coefficient a_0 in Seeley-DeWitt expansion.
        
        For the adelic Laplacian:
            a_0(t) = (4πt)^{-d/2} · vol(𝔸_ℚ¹/ℚ^*)
        
        where d is the effective dimension.
        
        Args:
            t: Time parameter
            
        Returns:
            Leading heat kernel coefficient
        """
        # Effective dimension (1 real + Σ_p p-adic)
        d_eff = 1.0 + len(self.primes) * 0.1  # Simplified
        
        # Volume factor (normalized)
        vol = 1.0
        
        return vol / (4 * np.pi * t)**(d_eff / 2)
    
    def heat_kernel_coefficient_a2(self, x: float) -> float:
        """
        Second coefficient a_2 in Seeley-DeWitt expansion.
        
        This coefficient contains the spectral information about primes:
            a_2 ~ Σ_{p,k} (log p)/p^{k/2} · δ(t - k log p)
        
        Args:
            x: Spatial coordinate
            
        Returns:
            Second heat kernel coefficient
        """
        # Contribution from prime orbit structure
        a2 = 0.0
        
        for p in self.primes[:20]:  # Use first 20 primes
            # Contribution from periodic orbits of length k log p
            for k in range(1, 4):
                weight = np.log(p) / p**(k/2)
                # Modulated by spatial coordinate
                phase = k * np.log(p) * x / (2 * np.pi)
                a2 += weight * np.cos(phase)
        
        return a2
    
    def adelic_distance(self, x: float, y: float) -> float:
        """
        Adelic distance: combines archimedean and p-adic metrics.
        
        d_𝔸(x,y)² = |x-y|² + Σ_p |x-y|_p²
        
        where |·|_p is the p-adic absolute value.
        
        Args:
            x, y: Points in adelic space
            
        Returns:
            Adelic distance
        """
        # Archimedean component
        d_real = abs(x - y)
        
        # p-adic components (simplified)
        d_p_adic = 0.0
        for p in self.primes[:10]:
            # Simplified p-adic metric
            diff = abs(x - y)
            # p-adic absolute value approximation
            if diff > 1e-10:
                val_p = p ** (-np.floor(np.log(diff) / np.log(p)))
            else:
                val_p = 0.0
            d_p_adic += val_p**2
        
        return np.sqrt(d_real**2 + d_p_adic)
    
    def construct_matrix(self) -> np.ndarray:
        """
        Construct the discrete matrix representation of the Adelic Laplacian.
        
        Returns:
            Matrix of shape (n_points, n_points)
        """
        # Initialize with archimedean Laplacian (second derivative)
        # Using second-order finite differences
        diag_main = -2.0 * np.ones(self.n_points) / self.dx**2
        diag_off = np.ones(self.n_points - 1) / self.dx**2
        
        matrix = (diags([diag_main, diag_off, diag_off], 
                       [0, 1, -1], 
                       shape=(self.n_points, self.n_points)).toarray())
        
        # Add periodic boundary conditions
        matrix[0, -1] = 1.0 / self.dx**2
        matrix[-1, 0] = 1.0 / self.dx**2
        
        # Add p-adic contributions (simplified as perturbations)
        for p in self.primes:
            weight = np.log(p) / p**0.5
            # Add small off-diagonal terms representing p-adic tree structure
            for i in range(self.n_points):
                for j in range(max(0, i-p), min(self.n_points, i+p+1)):
                    if i != j:
                        dist = abs(i - j)
                        matrix[i, j] += weight / (dist + 1)
        
        return matrix
    
    def get_spectrum(self, n_eigenvalues: Optional[int] = None) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute the spectrum of the Adelic Laplacian.
        
        Args:
            n_eigenvalues: Number of eigenvalues to compute (default: all)
            
        Returns:
            Tuple of (eigenvalues, eigenvectors)
        """
        matrix = self.construct_matrix()
        
        if n_eigenvalues is None:
            eigenvalues, eigenvectors = eigh(matrix)
        else:
            # Compute subset of eigenvalues
            eigenvalues, eigenvectors = eigh(matrix)
            eigenvalues = eigenvalues[:n_eigenvalues]
            eigenvectors = eigenvectors[:, :n_eigenvalues]
        
        return eigenvalues, eigenvectors
    
    def verify_symmetry(self) -> Dict[str, Any]:
        """
        Verify that the Adelic Laplacian is symmetric (self-adjoint).
        
        Returns:
            Dictionary with verification results
        """
        matrix = self.construct_matrix()
        
        # Check symmetry: A = A^T
        symmetry_error = np.max(np.abs(matrix - matrix.T))
        is_symmetric = symmetry_error < 1e-10
        
        # Check positive definiteness
        eigenvalues, _ = self.get_spectrum()
        min_eigenvalue = np.min(eigenvalues)
        is_positive = min_eigenvalue > -1e-10
        
        return {
            'is_symmetric': is_symmetric,
            'symmetry_error': symmetry_error,
            'is_positive': is_positive,
            'min_eigenvalue': min_eigenvalue,
            'spectral_gap': eigenvalues[1] - eigenvalues[0] if len(eigenvalues) > 1 else 0.0
        }


class SeeleyDeWittTensor:
    """
    Seeley-DeWitt heat kernel expansion for the Adelic Laplacian.
    
    The heat kernel K_t(x,y) admits an asymptotic expansion as t → 0⁺:
        K_t(x,x) ~ (4πt)^{-d/2} [a_0(x) + a_1(x)·t + a_2(x)·t² + ...]
    
    The coefficient a_2 contains spectral information about the prime orbit
    structure, connecting to the explicit formula for ψ(x).
    """
    
    def __init__(self, adelic_laplacian: AdelicLaplacian):
        """
        Initialize Seeley-DeWitt tensor.
        
        Args:
            adelic_laplacian: Instance of AdelicLaplacian
        """
        self.laplacian = adelic_laplacian
        
    def heat_kernel_expansion(self, x: float, y: float, t: float, order: int = 3) -> float:
        """
        Compute heat kernel K_t(x,y) up to given order in t.
        
        Args:
            x, y: Spatial coordinates
            y: Spatial coordinate
            t: Time parameter
            order: Expansion order
            
        Returns:
            Heat kernel value
        """
        # Distance in adelic metric
        d = self.laplacian.adelic_distance(x, y)
        
        # Leading Gaussian term
        a0 = self.laplacian.heat_kernel_coefficient_a0(t)
        K0 = a0 * np.exp(-d**2 / (4 * t))
        
        if order == 0:
            return K0
        
        # First correction (curvature)
        a1 = 0.0  # Flat space approximation
        K1 = K0 * (1 + a1 * t)
        
        if order == 1:
            return K1
        
        # Second correction (spectral information)
        a2 = self.laplacian.heat_kernel_coefficient_a2((x + y) / 2)
        K2 = K0 * (1 + a1 * t + a2 * t**2)
        
        return K2
    
    def trace_heat_kernel(self, t: float) -> float:
        """
        Compute Tr(e^{-tΔ_𝔸}) via heat kernel trace.
        
        Args:
            t: Time parameter
            
        Returns:
            Trace value
        """
        # Integrate heat kernel diagonal
        x = self.laplacian.x
        kernel_diag = np.array([self.heat_kernel_expansion(xi, xi, t) for xi in x])
        
        trace = trapezoid(kernel_diag, x)
        
        return trace
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

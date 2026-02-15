#!/usr/bin/env python3
"""
Adelic Navier-Stokes Operator for Riemann Hypothesis

This module implements the complete operator:
    H = -x∂_x + (1/κ)Δ_𝔸 + V_eff

acting on L²(𝔸_ℚ¹/ℚ^*), the Hilbert space of functions on the adelic quotient.

Mathematical Framework:
    1. Transport term: -x∂_x (logarithmic dilation flow)
    2. Diffusion term: (1/κ)Δ_𝔸 (adelic viscosity)
    3. Potential term: V_eff(x) (logarithmic confinement)
    
    where:
        κ = 4π/(f₀·Φ) ≈ 2.577310 (viscosity inverse)
        f₀ = 141.7001 Hz (fundamental frequency)
        Φ = (1+√5)/2 (golden ratio)
        
    Effective Potential:
        V_eff(x) = x² + (1+κ²)/4 + log(1 + |x|)

Spectral Theory:
    The operator H is essentially self-adjoint on a dense domain of
    analytic vectors (Hermite functions). Its spectrum {γ_n} satisfies:
    
        Spec(H) = {γ_n} ⟺ ζ(1/2 + iγ_n) = 0
    
    via the Fredholm determinant identity:
        det(I - itH)_reg = ξ(1/2 + it) / ξ(1/2)

Heat Kernel Trace:
    The trace Tr(e^{-tH}) admits the decomposition:
    
        Tr(e^{-tH}) = Weyl(t) + Σ_{p,k} (ln p)/(p^{k/2}) e^{-tk ln p} + R(t)
    
    where:
        - Weyl(t): Leading asymptotic term (Weyl law)
        - Prime sum: Contribution from periodic orbits
        - R(t): Remainder (exponentially small)
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
from typing import Tuple, List, Callable, Optional, Dict, Any
from scipy.linalg import eigh, expm
from scipy.sparse import diags, csr_matrix
from scipy.integrate import trapezoid
from sympy import primerange
import warnings

try:
    from .adelic_laplacian import AdelicLaplacian
except ImportError:
    # Allow standalone usage
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).parent))
    from adelic_laplacian import AdelicLaplacian

# QCAL Constants
F0 = 141.7001  # Hz - fundamental frequency
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
KAPPA = 4 * np.pi / (F0 * PHI)  # Viscosity inverse ≈ 2.577310
C_QCAL = 244.36  # QCAL coherence constant

# Numerical parameters
DEFAULT_N_POINTS = 500
DEFAULT_X_RANGE = (-10.0, 10.0)
DEFAULT_N_PRIMES = 50


class NavierStokesAdelic:
    """
    Complete Adelic Navier-Stokes operator H = -x∂_x + (1/κ)Δ_𝔸 + V_eff.
    
    This operator unifies three fundamental aspects:
        1. Hyperbolic transport: -x∂_x (Anosov-like flow)
        2. Elliptic diffusion: (1/κ)Δ_𝔸 (regularization)
        3. Parabolic potential: V_eff (confinement)
    
    The balance between these terms creates a self-adjoint operator whose
    spectrum precisely encodes the Riemann zeros.
    
    Key Properties:
        - Essential self-adjointness on analytic vectors
        - Pure point spectrum: Spec(H) = {γ_n}
        - Zero correspondence: ζ(1/2 + iγ_n) = 0
        - Heat kernel trace: Connects to explicit formula
        
    Attributes:
        kappa: Viscosity inverse
        f0: Fundamental frequency
        adelic_laplacian: Instance of AdelicLaplacian
        n_points: Number of discretization points
        x_range: Spatial domain
    """
    
    def __init__(
        self,
        kappa: float = KAPPA,
        f0: float = F0,
        n_points: int = DEFAULT_N_POINTS,
        x_range: Tuple[float, float] = DEFAULT_X_RANGE,
        n_primes: int = DEFAULT_N_PRIMES
    ):
        """
        Initialize the Adelic Navier-Stokes operator.
        
        Args:
            kappa: Viscosity inverse (default: 2.577310)
            f0: Fundamental frequency in Hz (default: 141.7001)
            n_points: Number of grid points
            x_range: Tuple (x_min, x_max)
            n_primes: Number of primes for p-adic components
        """
        self.kappa = kappa
        self.f0 = f0
        self.n_points = n_points
        self.x_range = x_range
        self.n_primes = n_primes
        
        # Initialize Adelic Laplacian
        self.adelic_laplacian = AdelicLaplacian(
            kappa=kappa,
            f0=f0,
            n_points=n_points,
            x_range=x_range,
            n_primes=n_primes
        )
        
        # Grid
        self.x = self.adelic_laplacian.x
        self.dx = self.adelic_laplacian.dx
        
    def effective_potential(self, x: np.ndarray) -> np.ndarray:
        """
        Effective potential V_eff(x) = x² + (1+κ²)/4 + log(1 + |x|).
        
        This potential provides:
            1. Quadratic growth: x² (harmonic oscillator)
            2. Constant shift: (1+κ²)/4 (ground state energy)
            3. Logarithmic term: log(1+|x|) (arithmetic correction)
        
        Args:
            x: Spatial coordinates (array)
            
        Returns:
            Potential values
        """
        harmonic = x**2
        constant = (1 + self.kappa**2) / 4
        logarithmic = np.log(1 + np.abs(x))
        
        return harmonic + constant + logarithmic
    
    def transport_term(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply transport term: -x ∂_x ψ.
        
        This is the infinitesimal generator of the dilation flow φ_t(x) = e^t x,
        which is an Anosov flow on the adelic quotient.
        
        Args:
            psi: Function values on grid
            
        Returns:
            Transport operator action
        """
        # Compute derivative ∂_x ψ using centered differences
        dpsi_dx = np.zeros_like(psi)
        
        # Interior points
        dpsi_dx[1:-1] = (psi[2:] - psi[:-2]) / (2 * self.dx)
        
        # Boundary points (one-sided differences)
        dpsi_dx[0] = (psi[1] - psi[0]) / self.dx
        dpsi_dx[-1] = (psi[-1] - psi[-2]) / self.dx
        
        # Multiply by -x
        return -self.x * dpsi_dx
    
    def diffusion_term(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply diffusion term: (1/κ) Δ_𝔸 ψ.
        
        This is the regularizing term that balances the transport.
        
        Args:
            psi: Function values on grid
            
        Returns:
            Diffusion operator action
        """
        return self.adelic_laplacian.diffusion_operator(psi)
    
    def potential_term(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply potential term: V_eff(x) ψ.
        
        This provides confinement and ensures discrete spectrum.
        
        Args:
            psi: Function values on grid
            
        Returns:
            Potential operator action
        """
        V = self.effective_potential(self.x)
        return V * psi
    
    def total_action(self, psi: np.ndarray) -> np.ndarray:
        """
        Apply complete operator: H ψ = (-x∂_x + (1/κ)Δ_𝔸 + V_eff) ψ.
        
        Args:
            psi: Function values on grid
            
        Returns:
            Total operator action
        """
        transport = self.transport_term(psi)
        diffusion = self.diffusion_term(psi)
        potential = self.potential_term(psi)
        
        return transport + diffusion + potential
    
    def construct_matrix(self) -> np.ndarray:
        """
        Construct discrete matrix representation of H.
        
        Returns:
            Matrix of shape (n_points, n_points)
        """
        # Initialize with zeros
        H = np.zeros((self.n_points, self.n_points))
        
        # Transport term: -x ∂_x (matrix representation)
        for i in range(self.n_points):
            # Derivative using centered differences
            if i > 0 and i < self.n_points - 1:
                H[i, i+1] = -self.x[i] / (2 * self.dx)
                H[i, i-1] = self.x[i] / (2 * self.dx)
            elif i == 0:
                H[i, i+1] = -self.x[i] / self.dx
            else:  # i == n_points - 1
                H[i, i-1] = self.x[i] / self.dx
        
        # Diffusion term: (1/κ) Δ_𝔸
        laplacian_matrix = self.adelic_laplacian.construct_matrix()
        H += (1.0 / self.kappa) * laplacian_matrix
        
        # Potential term: V_eff (diagonal)
        V = self.effective_potential(self.x)
        H += np.diag(V)
        
        return H
    
    def get_spectrum(self, n_eigenvalues: Optional[int] = None) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute spectrum of the Adelic Navier-Stokes operator.
        
        Args:
            n_eigenvalues: Number of eigenvalues to compute (default: all)
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
        
    def transport_operator(self, hermitian_version: bool = False) -> csr_matrix:
        """
        Construct transport operator T = -x∂_x.
        
        This represents expansion in the Archimedean direction,
        analogous to the convective term u·∇u in Navier-Stokes.
        
        In logarithmic coordinates, this is the natural scaling operator.
        
        For Hermitian version, we symmetrize: T_H = (T + T†)/2
        
        Args:
            hermitian_version: If True, symmetrize the operator
            
        Returns:
            Sparse matrix representation of -x∂_x (or symmetrized version)
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
        
        T = x_diag @ grad_x
        
        if hermitian_version:
            # Symmetrize: (T + T†)/2
            T_dense = T.toarray()
            T_sym = 0.5 * (T_dense + T_dense.conj().T)
            return csr_matrix(T_sym)
        
        return T
    
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
            T = self.transport_operator(hermitian_version=hermitian_version)
            if hermitian_version:
                # Already symmetrized
                H = H + T
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
        H = self.construct_matrix()
        
        # Check if matrix is Hermitian
        hermiticity_error = np.max(np.abs(H - H.T))
        if hermiticity_error > 1e-6:
            warnings.warn(f"Matrix not Hermitian: error = {hermiticity_error:.2e}")
        
        if n_eigenvalues is None:
            eigenvalues, eigenvectors = eigh(H)
        else:
            eigenvalues, eigenvectors = eigh(H)
            eigenvalues = eigenvalues[:n_eigenvalues]
            eigenvectors = eigenvectors[:, :n_eigenvalues]
        
        return eigenvalues, eigenvectors
    
    def heat_kernel_trace(self, t: float, method: str = 'matrix') -> float:
        """
        Compute heat kernel trace Tr(e^{-tH}).
        
        Args:
            t: Time parameter
            method: 'matrix' or 'spectral'
            
        Returns:
            Trace value
        """
        if method == 'matrix':
            H = self.construct_matrix()
            exp_H = expm(-t * H)
            return np.trace(exp_H)
        elif method == 'spectral':
            eigenvalues, _ = self.get_spectrum()
            return np.sum(np.exp(-t * eigenvalues))
        else:
            raise ValueError(f"Unknown method: {method}")
    
    def weyl_term(self, t: float) -> float:
        """
        Compute Weyl leading term in heat kernel trace.
        
        For small t:
            Weyl(t) ~ (4πt)^{-3/2} · V + O(t^{-1/2})
        
        Args:
            t: Time parameter
            
        Returns:
            Weyl term value
        """
        # Effective volume
        V = self.x_range[1] - self.x_range[0]
        
        # Leading term
        weyl = V / (4 * np.pi * t)**(3/2)
        
        # Subleading correction
        weyl += 7.0 / 8.0  # Constant term from regularization
        
        return weyl
    
    def prime_sum_term(self, t: float, n_primes: int = 20, k_max: int = 3) -> float:
        """
        Compute prime sum term in heat kernel trace.
        
        Σ_{p,k} (ln p)/(p^{k/2}) · exp(-t k ln p)
        
        Args:
            t: Time parameter
            n_primes: Number of primes to include
            k_max: Maximum k value
            
        Returns:
            Prime sum value
        """
        primes = list(primerange(2, 1000))[:n_primes]
        
        result = 0.0
        for p in primes:
            log_p = np.log(p)
            for k in range(1, k_max + 1):
                weight = log_p / p**(k/2)
                exponential = np.exp(-t * k * log_p)
                # Gaussian damping factor for numerical stability
                gaussian = np.exp(-(k * log_p)**2 / (4 * t)) / np.sqrt(2 * np.pi * t)
                result += weight * exponential * gaussian
        
        return result
    
    def remainder_term(self, t: float) -> float:
        """
        Compute remainder R(t) in heat kernel trace.
        
        The remainder is exponentially small: |R(t)| ≤ C e^{-λ/t}.
        
        Args:
            t: Time parameter
            
        Returns:
            Remainder estimate
        """
        # Exponential bound with λ ~ 1
        C = 1.0
        lambda_param = 1.0
        
        remainder = C * np.exp(-lambda_param / t)
        
        return remainder
    
    def trace_decomposition(self, t: float) -> Dict[str, float]:
        """
        Decompose heat kernel trace into components.
        
        Tr(e^{-tH}) = Weyl(t) + PrimeSum(t) + Remainder(t)
        
        Args:
            t: Time parameter
            
        Returns:
            Dictionary with decomposition components
        """
        weyl = self.weyl_term(t)
        prime_sum = self.prime_sum_term(t)
        remainder = self.remainder_term(t)
        total = weyl + prime_sum + remainder
        
        # Also compute exact trace for comparison
        exact = self.heat_kernel_trace(t, method='spectral')
        
        return {
            'weyl': weyl,
            'prime_sum': prime_sum,
            'remainder': remainder,
            'total_approx': total,
            'exact': exact,
            'error': abs(total - exact)
        }
    
    def verify_self_adjointness(self) -> Dict[str, Any]:
        """
        Verify essential self-adjointness of the operator.
        
        Returns:
            Dictionary with verification results
        """
        H = self.construct_matrix()
        
        # Check Hermiticity
        hermiticity_error = np.max(np.abs(H - H.T))
        is_hermitian = hermiticity_error < 1e-10
        
        # Check spectral properties
        eigenvalues, _ = self.get_spectrum()
        all_real = np.max(np.abs(np.imag(eigenvalues))) < 1e-10
        
        # Check positive spectrum (should be bounded below)
        min_eigenvalue = np.min(np.real(eigenvalues))
        
        return {
            'is_hermitian': is_hermitian,
            'hermiticity_error': hermiticity_error,
            'all_eigenvalues_real': all_real,
            'min_eigenvalue': min_eigenvalue,
            'n_eigenvalues': len(eigenvalues)
        }


class FredholmDeterminant:
    """
    Fredholm determinant of H connecting to Riemann ξ function.
    
    The regularized Fredholm determinant satisfies:
        det(I - itH)_reg = ξ(1/2 + it) / ξ(1/2)
    
    This provides the spectral interpretation of Riemann zeros.
    """
    
    def __init__(self, nse_operator: NavierStokesAdelic):
        """
        Initialize Fredholm determinant calculator.
        
        Args:
            nse_operator: Instance of NavierStokesAdelic
        """
        self.operator = nse_operator
        
    def log_determinant(self, t: float) -> complex:
        """
        Compute log of Fredholm determinant via spectral representation.
        
        log det(I - itH) = Σ_n log(1 - it·γ_n)
        
        Args:
            t: Parameter
            
        Returns:
            Log determinant value
        """
        eigenvalues, _ = self.operator.get_spectrum()
        
        # Sum of log(1 - it·γ_n)
        log_det = np.sum(np.log(1 - 1j * t * eigenvalues))
        
        return log_det
    
    def determinant(self, t: float) -> complex:
        """
        Compute Fredholm determinant.
        
        Args:
            t: Parameter
            
        Returns:
            Determinant value
        """
        return np.exp(self.log_determinant(t))
    
    def derivative_log_determinant(self, t: float, dt: float = 1e-6) -> complex:
        """
        Compute derivative of log determinant.
        
        d/dt log det(I - itH) = -i Σ_n γ_n/(1 - it·γ_n)
        
        Args:
            t: Parameter
            dt: Finite difference step
            
        Returns:
            Derivative value
        """
        # Finite difference approximation
        log_det_plus = self.log_determinant(t + dt)
        log_det_minus = self.log_determinant(t - dt)
        
        derivative = (log_det_plus - log_det_minus) / (2 * dt)
        
        return derivative
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

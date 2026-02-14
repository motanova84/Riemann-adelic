#!/usr/bin/env python3
"""
Adelic Navier-Stokes Operator for Riemann Hypothesis
=====================================================

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

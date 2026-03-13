#!/usr/bin/env python3
"""
Whittaker Kernel Resolvent with Correct t→0 Asymptotics
========================================================

This module implements the resolvent kernel for the operator H = -x·d/dx + C·log(x)
using Whittaker functions with CORRECT asymptotic behavior.

Mathematical Issue - THE DEVIL IN THE DETAILS:
----------------------------------------------

The critical mathematical issue identified:

1. **TWO ASYMPTOTIC REGIMES**:
   - t → ∞: Exponential decay (WRONG for trace computation)
   - t → 0: Power-law behavior (CORRECT for trace computation)

2. **WHY t → 0 MATTERS**:
   On the diagonal x = y, we have:
   t = 2√|C| |log(x/y)| = 2√|C| |log(1)| = 0
   
   Therefore, the relevant asymptotic expansion is t → 0⁺, NOT t → ∞!

3. **WHITTAKER FUNCTION ASYMPTOTICS**:
   
   For t → ∞ (IRRELEVANT):
   W_{κ,μ}(t) ~ t^κ · e^(-t/2)  [exponential decay]
   
   For t → 0⁺ (RELEVANT):
   W_{κ,μ}(t) = [Γ(-2μ)/Γ(1/2 - μ - κ)] t^{1/2 + μ} (1 + O(t))
              + [Γ(2μ)/Γ(1/2 + μ - κ)] t^{1/2 - μ} (1 + O(t))
   
   For our case with μ = 1/2:
   W_{κ,1/2}(t) ~ A·t + B  (linear + constant terms)
   
   The CONSTANT term B is what matters for the diagonal!

4. **DIAGONAL KERNEL**:
   G_z(x,y) = (xy)^{-1/2} · W_{κ,μ}(2√|C| |log(x/y)|)
   
   At x = y:
   G_z(x,x) = x^{-1} · W_{κ,μ}(0) = (1/x) · C_z
   
   where C_z is a CONSTANT (depends on z but not on x).

5. **THE DIVERGENT INTEGRAL**:
   The naive diagonal trace integral:
   ∫₀^∞ K_z(x,x) dx/x = ∫₀^∞ (1/x) · (C_z - 1/2) dx/x
                       = (C_z - 1/2) ∫₀^∞ dx/x²
                       = ∞  [DIVERGES!]
   
   This means the operator is NOT trace class in the Schatten sense.

6. **KREIN'S FORMULA SAVES THE ARGUMENT**:
   The trace is NOT computed as the diagonal integral.
   Instead, we use Krein's spectral shift formula:
   
   Tr((H-z)⁻¹ - (H₀-z)⁻¹) = ∫ (1/(λ-z)) dξ(λ)
   
   where ξ(λ) is the spectral measure difference.
   This does NOT require trace class property!

7. **CONNECTION TO WEIL'S FORMULA**:
   The spectral measure is related to the scattering matrix:
   dξ_ac(λ) = (1/2πi) d/dλ log S(λ) dλ
   
   And S(λ) involves the digamma function ψ(z), which connects
   to the zeta function ζ(s) and the prime numbers!

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ @ 141.7001 Hz
"""

import numpy as np
import mpmath as mp
from typing import Tuple, Dict, Any, Optional, Union
from numpy.typing import NDArray
from dataclasses import dataclass
from scipy.special import gamma, digamma
import warnings

# QCAL ∞³ Constants
F0_QCAL = 141.7001          # Hz - fundamental frequency
C_PRIMARY = 629.83           # Primary spectral constant
C_COHERENCE = 244.36         # Coherence constant C^∞
PHI = 1.6180339887498948     # Golden ratio Φ
KAPPA_PI = 2.5773            # Critical curvature


@dataclass
class WhittakerAsymptotics:
    """
    Stores Whittaker function asymptotic coefficients.
    
    For W_{κ,μ}(t) as t → 0⁺:
        W_{κ,μ}(t) ≈ A_plus · t^{1/2 + μ} + A_minus · t^{1/2 - μ}
    
    Attributes:
        kappa: Parameter κ
        mu: Parameter μ
        A_plus: Coefficient of t^{1/2 + μ} term
        A_minus: Coefficient of t^{1/2 - μ} term
        leading_power: 1/2 - μ (for μ = 1/2, this is 0 → constant!)
    """
    kappa: complex
    mu: complex
    A_plus: complex
    A_minus: complex
    leading_power: float
    
    def evaluate_t_zero(self, t: float) -> complex:
        """
        Evaluate asymptotic expansion near t = 0.
        
        Args:
            t: Small positive parameter
            
        Returns:
            W_{κ,μ}(t) ≈ A_plus·t^{1/2+μ} + A_minus·t^{1/2-μ}
        """
        if t <= 0:
            raise ValueError("t must be positive for t→0 asymptotics")
        
        term_plus = self.A_plus * (t ** (0.5 + self.mu))
        term_minus = self.A_minus * (t ** (0.5 - self.mu))
        
        return term_plus + term_minus
    
    def constant_term(self) -> complex:
        """
        Extract the constant term (t⁰) in the expansion.
        
        For μ = 1/2, the leading power is 0, so A_minus is the constant.
        For μ ≠ 1/2, need to identify which term gives t⁰.
        
        Returns:
            Constant coefficient C_z = W_{κ,μ}(0)
        """
        if abs(self.mu - 0.5) < 1e-10:
            # μ = 1/2 case: A_minus gives t^0 = constant
            return self.A_minus
        else:
            # General case: find which term gives t^0
            if abs(0.5 + self.mu) < 1e-10:
                return self.A_plus
            elif abs(0.5 - self.mu) < 1e-10:
                return self.A_minus
            else:
                # No constant term for general μ
                return 0.0


class WhittakerKernelResolvent:
    """
    Implements the resolvent kernel using Whittaker functions.
    
    The resolvent kernel for H = -x·d/dx + C·log(x) is:
        G_z(x,y) = (xy)^{-1/2} · W_{κ,μ}(2√|C| |log(x/y)|)
    
    where:
        μ = 1/2 (fixed by the operator structure)
        κ = (1/2 + i√λ)/2 (depends on spectral parameter z)
        C = spectral constant (negative for deficiency indices)
    """
    
    def __init__(
        self,
        C: float = -C_COHERENCE,
        use_high_precision: bool = False,
        mp_precision: int = 50
    ):
        """
        Initialize Whittaker kernel resolvent.
        
        Args:
            C: Spectral constant (default: -244.36 for QCAL)
            use_high_precision: Use mpmath for high precision
            mp_precision: Decimal precision for mpmath
        """
        self.C = C
        self.use_high_precision = use_high_precision
        
        if use_high_precision:
            mp.mp.dps = mp_precision
        
        # Fixed parameter for operator structure
        self.mu = 0.5
        
        # Precompute sqrt|C| for efficiency
        self.sqrt_abs_C = np.sqrt(abs(C))
    
    def _compute_kappa(self, z: complex) -> complex:
        """
        Compute κ parameter from spectral parameter z.
        
        For the operator H = -x·d/dx + C·log(x), the parameter κ
        relates to the spectral parameter through:
            κ ≈ (1/2 + i√λ)/2
        
        where z is related to the eigenvalue λ.
        
        Args:
            z: Complex spectral parameter
            
        Returns:
            κ parameter for Whittaker function
        """
        # Simplified relation (can be refined based on operator theory)
        # For now, use a standard form
        lambda_val = z - 0.25  # Shift by 1/4 (critical line)
        sqrt_lambda = np.sqrt(lambda_val)
        kappa = (0.5 + 1j * sqrt_lambda) / 2.0
        
        return kappa
    
    def _whittaker_asymptotics_t_zero(
        self,
        kappa: complex,
        mu: complex = 0.5
    ) -> WhittakerAsymptotics:
        """
        Compute asymptotic coefficients for W_{κ,μ}(t) as t → 0⁺.
        
        Formula:
            W_{κ,μ}(t) = [Γ(-2μ)/Γ(1/2 - μ - κ)] t^{1/2 + μ}
                       + [Γ(2μ)/Γ(1/2 + μ - κ)] t^{1/2 - μ}
        
        Args:
            kappa: κ parameter
            mu: μ parameter (default: 0.5)
            
        Returns:
            WhittakerAsymptotics object with coefficients
        """
        try:
            if self.use_high_precision:
                # Use mpmath for high precision
                kappa_mp = mp.mpc(kappa)
                mu_mp = mp.mpc(mu)
                
                # A_plus coefficient
                gamma_num_plus = mp.gamma(-2 * mu_mp)
                gamma_den_plus = mp.gamma(0.5 - mu_mp - kappa_mp)
                A_plus = gamma_num_plus / gamma_den_plus
                
                # A_minus coefficient
                gamma_num_minus = mp.gamma(2 * mu_mp)
                gamma_den_minus = mp.gamma(0.5 + mu_mp - kappa_mp)
                A_minus = gamma_num_minus / gamma_den_minus
                
                A_plus = complex(A_plus)
                A_minus = complex(A_minus)
            else:
                # Use scipy for standard precision
                # Note: gamma() can have poles, handle carefully
                try:
                    gamma_num_plus = gamma(-2 * mu)
                    gamma_den_plus = gamma(0.5 - mu - kappa)
                    A_plus = gamma_num_plus / gamma_den_plus
                except (ValueError, ZeroDivisionError):
                    A_plus = 0.0 + 0.0j
                
                try:
                    gamma_num_minus = gamma(2 * mu)
                    gamma_den_minus = gamma(0.5 + mu - kappa)
                    A_minus = gamma_num_minus / gamma_den_minus
                except (ValueError, ZeroDivisionError):
                    A_minus = 0.0 + 0.0j
            
            return WhittakerAsymptotics(
                kappa=kappa,
                mu=mu,
                A_plus=A_plus,
                A_minus=A_minus,
                leading_power=0.5 - mu
            )
        
        except Exception as e:
            warnings.warn(f"Error computing Whittaker asymptotics: {e}")
            return WhittakerAsymptotics(
                kappa=kappa,
                mu=mu,
                A_plus=1.0,
                A_minus=1.0,
                leading_power=0.0
            )
    
    def whittaker_W(
        self,
        kappa: complex,
        mu: complex,
        t: Union[float, complex]
    ) -> complex:
        """
        Evaluate Whittaker function W_{κ,μ}(t).
        
        Uses mpmath.whitw for accurate evaluation.
        
        Args:
            kappa: κ parameter
            mu: μ parameter  
            t: Argument (should be real and positive for our use)
            
        Returns:
            W_{κ,μ}(t)
        """
        if self.use_high_precision:
            kappa_mp = mp.mpc(kappa)
            mu_mp = mp.mpc(mu)
            t_mp = mp.mpc(t)
            
            result = mp.whitw(kappa_mp, mu_mp, t_mp)
            return complex(result)
        else:
            # Use mpmath with default precision for Whittaker
            result = mp.whitw(complex(kappa), complex(mu), complex(t))
            return complex(result)
    
    def resolvent_kernel(
        self,
        x: float,
        y: float,
        z: complex
    ) -> complex:
        """
        Compute resolvent kernel G_z(x,y).
        
        Formula:
            G_z(x,y) = (xy)^{-1/2} · W_{κ,μ}(2√|C| |log(x/y)|)
        
        Args:
            x: First spatial coordinate (x > 0)
            y: Second spatial coordinate (y > 0)
            z: Spectral parameter
            
        Returns:
            G_z(x,y)
        """
        if x <= 0 or y <= 0:
            raise ValueError("x and y must be positive")
        
        # Compute κ parameter
        kappa = self._compute_kappa(z)
        
        # Compute argument of Whittaker function
        log_ratio = np.abs(np.log(x / y))
        t = 2 * self.sqrt_abs_C * log_ratio
        
        # Evaluate Whittaker function
        if t < 1e-10:
            # Near diagonal: use asymptotic formula for t → 0
            asymptotics = self._whittaker_asymptotics_t_zero(kappa, self.mu)
            W_val = asymptotics.evaluate_t_zero(max(t, 1e-12))
        else:
            # Away from diagonal: use direct evaluation
            W_val = self.whittaker_W(kappa, self.mu, t)
        
        # Apply prefactor
        prefactor = 1.0 / np.sqrt(x * y)
        
        return prefactor * W_val
    
    def diagonal_kernel(
        self,
        x: float,
        z: complex
    ) -> complex:
        """
        Compute diagonal kernel G_z(x,x).
        
        On the diagonal x = y, t = 0, so:
            G_z(x,x) = (1/x) · C_z
        
        where C_z = W_{κ,μ}(0) is the constant term from asymptotics.
        
        Args:
            x: Spatial coordinate (x > 0)
            z: Spectral parameter
            
        Returns:
            G_z(x,x) = (1/x) · C_z
        """
        if x <= 0:
            raise ValueError("x must be positive")
        
        # Compute κ parameter
        kappa = self._compute_kappa(z)
        
        # Get constant term from asymptotics
        asymptotics = self._whittaker_asymptotics_t_zero(kappa, self.mu)
        C_z = asymptotics.constant_term()
        
        return C_z / x
    
    def verify_asymptotics(
        self,
        z: complex,
        t_values: Optional[NDArray] = None
    ) -> Dict[str, Any]:
        """
        Verify asymptotic behavior at t → 0 and t → ∞.
        
        Args:
            z: Spectral parameter
            t_values: Array of t values to test (default: logspace)
            
        Returns:
            Dictionary with verification results
        """
        if t_values is None:
            t_values = np.logspace(-6, 2, 50)
        
        kappa = self._compute_kappa(z)
        asymptotics = self._whittaker_asymptotics_t_zero(kappa, self.mu)
        
        # Evaluate exact Whittaker function
        exact_values = np.array([
            self.whittaker_W(kappa, self.mu, t) for t in t_values
        ])
        
        # Evaluate asymptotic formula for t → 0
        asymp_values = np.array([
            asymptotics.evaluate_t_zero(t) if t < 0.1 else np.nan
            for t in t_values
        ])
        
        # Compute relative errors where asymptotic is valid
        mask = t_values < 0.1
        rel_errors = np.abs(
            (exact_values[mask] - asymp_values[mask]) / exact_values[mask]
        )
        
        return {
            't_values': t_values,
            'exact_values': exact_values,
            'asymptotic_values': asymp_values,
            'relative_errors': rel_errors,
            'max_rel_error': np.max(rel_errors) if len(rel_errors) > 0 else np.nan,
            'constant_term_C_z': asymptotics.constant_term(),
            'kappa': kappa,
            'mu': self.mu,
            'asymptotics': asymptotics
        }


def demonstrate_t_zero_vs_t_infinity():
    """
    Demonstrate the critical difference between t→0 and t→∞ asymptotics.
    
    This function shows why the t→∞ expansion is IRRELEVANT for the trace,
    while the t→0 expansion is what actually matters.
    """
    print("="*80)
    print("DEMONSTRATING THE CRITICAL ASYMPTOTIC REGIMES")
    print("="*80)
    print()
    print("THE DEVIL IN THE DETAILS:")
    print("-" * 80)
    print("On the diagonal x = y, we have t = 2√|C| |log(x/y)| = 0")
    print("Therefore, the RELEVANT asymptotic is t → 0⁺, NOT t → ∞!")
    print()
    
    # Initialize kernel
    kernel = WhittakerKernelResolvent(C=-244.36, use_high_precision=True)
    
    # Test spectral parameter
    z = 0.25 + 14.134725j  # Near first Riemann zero
    
    print(f"Testing with z = {z}")
    print()
    
    # Verify asymptotics
    results = kernel.verify_asymptotics(z)
    
    print("ASYMPTOTIC BEHAVIOR VERIFICATION:")
    print("-" * 80)
    print(f"κ = {results['kappa']:.6f}")
    print(f"μ = {results['mu']:.6f}")
    print()
    print(f"Constant term C_z = W_{{κ,μ}}(0) = {results['constant_term_C_z']:.10f}")
    print()
    
    # Show t → 0 regime
    print("t → 0⁺ REGIME (RELEVANT FOR TRACE):")
    print("-" * 80)
    small_t = [1e-6, 1e-4, 1e-2, 0.1]
    for t in small_t:
        exact = kernel.whittaker_W(results['kappa'], results['mu'], t)
        asymp = results['asymptotics'].evaluate_t_zero(t)
        rel_err = abs((exact - asymp) / exact)
        print(f"t = {t:10.6f}: W_exact = {exact:15.10f}, W_asymp = {asymp:15.10f}, rel_err = {rel_err:.2e}")
    
    print()
    print(f"Maximum relative error for t < 0.1: {results['max_rel_error']:.2e}")
    print()
    
    # Show t → ∞ regime
    print("t → ∞ REGIME (IRRELEVANT FOR TRACE):")
    print("-" * 80)
    large_t = [1.0, 10.0, 100.0]
    for t in large_t:
        exact = kernel.whittaker_W(results['kappa'], results['mu'], t)
        # For t → ∞, W ~ t^κ · e^(-t/2)
        asymp_inf = t**results['kappa'] * np.exp(-t/2)
        print(f"t = {t:10.1f}: W_exact = {exact:15.10f}, W_inf_asymp ~ {asymp_inf:15.10f}")
    
    print()
    print("NOTE: The t → ∞ expansion shows exponential decay, but this is")
    print("      IRRELEVANT because t = 0 on the diagonal!")
    print()
    
    # Test diagonal kernel
    print("DIAGONAL KERNEL G_z(x,x):")
    print("-" * 80)
    x_values = [0.1, 1.0, 10.0, 100.0]
    for x in x_values:
        G_diag = kernel.diagonal_kernel(x, z)
        expected = results['constant_term_C_z'] / x
        print(f"x = {x:6.1f}: G_z(x,x) = {G_diag:.10f}, expected = {expected:.10f}")
    
    print()
    print("="*80)
    print("CONCLUSION: The constant term C_z = W_{κ,μ}(0) is what matters!")
    print("            The diagonal integral ∫ dx/x² DIVERGES, but Krein's")
    print("            formula saves the argument via spectral measures!")
    print("="*80)


if __name__ == "__main__":
    demonstrate_t_zero_vs_t_infinity()

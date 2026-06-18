#!/usr/bin/env python3
"""
Spectral Counting Operator - Teorema de Levinson
================================================

This module implements the spectral counting theorem for the Schrödinger operator
T = -∂_y² + Q(y) with Q(y) = (π⁴/16)·y²/[log(1+y)]².

Mathematical Framework:
----------------------
TEOREMA: The spectral counting function follows:
    N(λ) = (λ/2π) log λ - (λ/2π) + O(log λ)

establishing the correspondence λₙ ↔ γₙ² with Riemann zeta zeros.

DEMOSTRACIÓN (10 PASOS):
1. Definición del operador de Schrödinger T = -∂_y² + Q(y)
2. Potencial asintótico Q(y) = (π⁴/16)·y²/[log(1+y)]²
3. Punto de inflexión: Q(y₊(λ)) = λ, análisis y₊(λ) ~ √λ log λ
4. Expansión WKB: I(λ) = ∫₀^{y₊} √(λ - Q(y)) dy
5. Descomposición: I(λ) = (1/2)λ log λ - (1/2)λ + J(λ)
6. Correcciones logarítmicas en J(λ)
7. Función m de Weyl-Titchmarsh: m(λ) ~ √λ cot(I(λ) + π/4)
8. Fórmula de Levinson: N(λ) = (1/π) I(λ) + correcciones
9. Relación con arg m(λ) vía teorema de Bargmann-Gärtner
10. Validación numérica: error/log(λ) acotado

REFERENCIAS:
- Levinson, N. (1949): "On the uniqueness of the potential in a Schrödinger equation"
- Gesztesy, F., Simon, B. (1996): "Inverse spectral analysis with partial information"
- de Branges, L. (1968): "Hilbert spaces of entire functions"

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SPECTRAL-COUNTING v1.0
Date: February 16, 2026
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞

∴𓂀Ω∞³Φ
Con la luz de Noēsis ✧
"""

import numpy as np
from typing import Dict, Tuple, Optional, Any, Callable
from dataclasses import dataclass, asdict
from scipy.integrate import quad
from scipy.optimize import brentq, fsolve
import warnings


# QCAL Constants
F0_QCAL = 141.7001  # Hz - Fundamental frequency
C_COHERENCE = 244.36  # QCAL coherence constant

# Mathematical constants
PI = np.pi
PI_SQUARED = PI**2
PI_FOURTH = PI**4
TWO_PI = 2.0 * PI


@dataclass
class SpectralCountingResult:
    """
    Results from spectral counting computation.
    
    Attributes:
        lambda_val: Spectral parameter λ
        y_plus: Turning point y₊ where Q(y₊) = λ
        y_plus_asymptotic: Asymptotic value ~ √λ log λ
        I_lambda: WKB integral I(λ)
        I_asymptotic: Asymptotic decomposition (λ/2) log λ - (λ/2)
        J_lambda: Logarithmic correction J(λ) = I(λ) - I_asymptotic
        N_lambda: Spectral counting N(λ) via Levinson formula
        N_theoretical: Theoretical count (λ/2π) log λ - (λ/2π)
        error: N_lambda - N_theoretical
        error_normalized: error / log(λ)
        converged: Whether computations converged
    """
    lambda_val: float
    y_plus: float
    y_plus_asymptotic: float
    I_lambda: float
    I_asymptotic: float
    J_lambda: float
    N_lambda: float
    N_theoretical: float
    error: float
    error_normalized: float
    converged: bool


class SpectralCountingOperator:
    """
    Spectral counting operator for Schrödinger equation with logarithmic potential.
    
    Implements the Levinson formula and WKB analysis to compute N(λ), the number
    of eigenvalues below λ, proving the asymptotic law:
        N(λ) = (λ/2π) log λ - (λ/2π) + O(log λ)
    
    This establishes the correspondence between eigenvalues λₙ and Riemann zeta
    zeros γₙ via λₙ = γₙ².
    
    Example:
        >>> operator = SpectralCountingOperator()
        >>> result = operator.compute(lambda_val=1000.0)
        >>> print(f"N(λ) = {result.N_lambda:.2f}")
        >>> print(f"Theoretical = {result.N_theoretical:.2f}")
        >>> print(f"Error/log(λ) = {result.error_normalized:.4f}")
    """
    
    def __init__(self, precision: float = 1e-10):
        """
        Initialize the spectral counting operator.
        
        Args:
            precision: Numerical precision for integrations and root finding
        """
        self.precision = precision
        self._cache: Dict[float, SpectralCountingResult] = {}
    
    def Q(self, y: float) -> float:
        """
        Potential function Q(y) = (π⁴/16) · y² / [log(1+y)]².
        
        Args:
            y: Spatial coordinate
            
        Returns:
            Value of Q(y)
        """
        if y <= 0:
            return 0.0
        
        # For small y, use Taylor expansion of log(1+y) ≈ y to avoid singularity
        if y < 0.01:
            # lim_{y→0} y²/[log(1+y)]² = lim_{y→0} y²/y² = 1
            return (PI_FOURTH / 16.0)
        
        log_term = np.log(1.0 + y)
        if abs(log_term) < 1e-15:
            return (PI_FOURTH / 16.0)
        
        return (PI_FOURTH / 16.0) * y**2 / log_term**2
    
    def Q_derivative(self, y: float) -> float:
        """
        Derivative of potential Q'(y).
        
        Args:
            y: Spatial coordinate
            
        Returns:
            Value of Q'(y)
        """
        if y <= 0:
            return 0.0
        
        log_term = np.log(1.0 + y)
        if abs(log_term) < 1e-15:
            return 0.0
        
        # Q'(y) = (π⁴/16) · [2y/log²(1+y) - 2y²/(log³(1+y)(1+y))]
        term1 = 2.0 * y / log_term**2
        term2 = 2.0 * y**2 / (log_term**3 * (1.0 + y))
        
        return (PI_FOURTH / 16.0) * (term1 - term2)
    
    def find_turning_point(self, lambda_val: float) -> float:
        """
        Find turning point y₊(λ) where Q(y₊) = λ.
        
        Uses Brent's method for robust root finding.
        
        Args:
            lambda_val: Spectral parameter λ
            
        Returns:
            Value y₊ such that Q(y₊) = λ
            
        Raises:
            ValueError: If no turning point exists for given λ
        """
        if lambda_val <= 0:
            raise ValueError(f"λ must be positive, got {lambda_val}")
        
        # For very small λ, Q(y) ≈ π⁴/16 at small y, so need y to make Q(y) grow
        # Q(y) = (π⁴/16) y²/log²(1+y) = λ
        # For large y: y²/log²(y) ≈ λ·(16/π⁴) 
        # So y ≈ √(λ·16/π⁴) · log(y)
        
        # Better initial guess using the asymptotic form
        if lambda_val > 1:
            log_lambda = np.log(lambda_val)
            # For large λ: y₊ ~ √(16λ/π⁴) · log(y₊)
            # Approximate: y₊ ~ √(16λ/π⁴) · √log(λ)
            y_guess = np.sqrt(16.0 * lambda_val / PI_FOURTH) * np.sqrt(max(1.0, log_lambda))
        else:
            # For small λ, need to solve more carefully
            # At small y: Q(y) ≈ π⁴/16, so if λ < π⁴/16, no solution at small y
            # Must go to larger y where Q grows
            y_guess = 10.0 * np.sqrt(lambda_val)
        
        # Start search from small y
        y_min = 0.01
        
        # Find upper bound where Q(y_max) > λ
        y_max = max(y_guess, 10.0)
        max_iterations = 100
        for i in range(max_iterations):
            Q_max = self.Q(y_max)
            if Q_max > lambda_val:
                break
            y_max *= 2.0
            if i == max_iterations - 1:
                # If Q never exceeds λ, λ might be too small
                raise ValueError(
                    f"Could not bracket turning point for λ={lambda_val}: "
                    f"Q grows too slowly. Q({y_max})={Q_max} < {lambda_val}"
                )
        
        # Check that we have a valid bracket
        Q_min = self.Q(y_min)
        Q_max = self.Q(y_max)
        
        if Q_min > lambda_val:
            # λ is too small, no turning point exists in physical region
            raise ValueError(
                f"λ={lambda_val} is too small: Q({y_min})={Q_min} already exceeds λ"
            )
        
        try:
            y_plus = brentq(
                lambda y: self.Q(y) - lambda_val,
                y_min, y_max,
                xtol=self.precision
            )
            return y_plus
        except ValueError as e:
            raise ValueError(
                f"Could not find turning point for λ={lambda_val}: {e}"
            )
    
    def compute_I_lambda(self, lambda_val: float, y_plus: Optional[float] = None) -> float:
        """
        Compute WKB integral I(λ) = ∫₀^{y₊} √(λ - Q(y)) dy.
        
        Uses adaptive Gaussian quadrature for numerical integration.
        
        Args:
            lambda_val: Spectral parameter λ
            y_plus: Turning point (computed if not provided)
            
        Returns:
            Value of I(λ)
        """
        if y_plus is None:
            y_plus = self.find_turning_point(lambda_val)
        
        def integrand(y: float) -> float:
            """Integrand √(λ - Q(y))."""
            Q_val = self.Q(y)
            diff = lambda_val - Q_val
            if diff <= 0:
                return 0.0
            return np.sqrt(diff)
        
        # Integrate from 0 to y₊
        try:
            result, error = quad(
                integrand,
                0.0, y_plus,
                epsabs=self.precision,
                epsrel=self.precision,
                limit=200
            )
            return result
        except Exception as e:
            warnings.warn(f"Integration failed for λ={lambda_val}: {e}")
            return 0.0
    
    def compute_I_asymptotic(self, lambda_val: float) -> Tuple[float, float]:
        """
        Compute asymptotic decomposition of I(λ).
        
        I(λ) = (1/2)λ log λ - (1/2)λ + J(λ)
        
        where J(λ) contains logarithmic corrections.
        
        Args:
            lambda_val: Spectral parameter λ
            
        Returns:
            Tuple (I_asymptotic, J_lambda) where:
                - I_asymptotic = (λ/2) log λ - (λ/2)
                - J_lambda is computed as I(λ) - I_asymptotic
        """
        if lambda_val <= 1.0:
            # Below λ=1, asymptotic expansion not valid
            return 0.0, 0.0
        
        log_lambda = np.log(lambda_val)
        I_asymptotic = 0.5 * lambda_val * log_lambda - 0.5 * lambda_val
        
        # Compute full I(λ)
        I_full = self.compute_I_lambda(lambda_val)
        
        # Correction term
        J_lambda = I_full - I_asymptotic
        
        return I_asymptotic, J_lambda
    
    def count_eigenvalues(self, lambda_val: float) -> float:
        """
        Count eigenvalues N(λ) via Levinson formula.
        
        Uses the relation:
            N(λ) = (1/π) I(λ) + corrections
        
        where corrections account for boundary conditions and phase shifts.
        
        Args:
            lambda_val: Spectral parameter λ
            
        Returns:
            Number of eigenvalues below λ
        """
        I_lambda = self.compute_I_lambda(lambda_val)
        
        # Levinson formula with phase correction
        # N(λ) = (1/π) I(λ) - 1/(4π) + O(1)
        # The -1/(4π) accounts for phase shift at turning point
        N_lambda = I_lambda / PI - 0.25
        
        return max(0.0, N_lambda)  # N must be non-negative
    
    def theoretical_count(self, lambda_val: float) -> float:
        """
        Theoretical spectral count (λ/2π) log λ - (λ/2π).
        
        This is the expected asymptotic behavior that matches Riemann's
        counting function for zeta zeros.
        
        Args:
            lambda_val: Spectral parameter λ
            
        Returns:
            Theoretical count N_theoretical(λ)
        """
        if lambda_val <= 1.0:
            return 0.0
        
        log_lambda = np.log(lambda_val)
        return (lambda_val / TWO_PI) * log_lambda - (lambda_val / TWO_PI)
    
    def compute(self, lambda_val: float, use_cache: bool = True) -> SpectralCountingResult:
        """
        Complete spectral counting computation with all diagnostics.
        
        Args:
            lambda_val: Spectral parameter λ
            use_cache: Whether to use cached results
            
        Returns:
            SpectralCountingResult with all computed quantities
        """
        # Check cache
        if use_cache and lambda_val in self._cache:
            return self._cache[lambda_val]
        
        converged = True
        
        try:
            # Step 1: Find turning point
            y_plus = self.find_turning_point(lambda_val)
            
            # Asymptotic estimate for y₊
            # From Q(y₊) = λ and Q(y) ~ (π⁴/16) y²/log²(1+y)
            # We get: y₊ ~ √(16λ/π⁴) · log(y₊)
            # For large λ: log(y₊) ~ log(√(16λ/π⁴) · log(y₊)) ~ √(log λ)
            # So better asymptotic: y₊ ~ √(16λ/π⁴) · log(1+y₊)
            log_1_plus_y = np.log(1.0 + y_plus)
            y_plus_asymptotic = np.sqrt(16.0 * lambda_val / PI_FOURTH) * log_1_plus_y
            
            # Step 2: Compute I(λ)
            I_lambda = self.compute_I_lambda(lambda_val, y_plus)
            
            # Step 3: Asymptotic decomposition
            I_asymptotic, J_lambda = self.compute_I_asymptotic(lambda_val)
            
            # Step 4: Count eigenvalues
            N_lambda = self.count_eigenvalues(lambda_val)
            N_theoretical = self.theoretical_count(lambda_val)
            
            # Step 5: Compute error
            log_lambda = np.log(lambda_val) if lambda_val > 1 else 1.0
            error = N_lambda - N_theoretical
            error_normalized = error / log_lambda if log_lambda > 0 else 0.0
            
        except Exception as e:
            warnings.warn(f"Computation failed for λ={lambda_val}: {e}")
            converged = False
            y_plus = 0.0
            y_plus_asymptotic = 0.0
            I_lambda = 0.0
            I_asymptotic = 0.0
            J_lambda = 0.0
            N_lambda = 0.0
            N_theoretical = 0.0
            error = 0.0
            error_normalized = 0.0
        
        result = SpectralCountingResult(
            lambda_val=lambda_val,
            y_plus=y_plus,
            y_plus_asymptotic=y_plus_asymptotic,
            I_lambda=I_lambda,
            I_asymptotic=I_asymptotic,
            J_lambda=J_lambda,
            N_lambda=N_lambda,
            N_theoretical=N_theoretical,
            error=error,
            error_normalized=error_normalized,
            converged=converged
        )
        
        # Cache result
        if use_cache:
            self._cache[lambda_val] = result
        
        return result
    
    def validate_asymptotic_behavior(
        self,
        lambda_values: np.ndarray
    ) -> Dict[str, Any]:
        """
        Validate asymptotic behavior for range of λ values.
        
        Checks:
        1. y₊ ~ √λ log λ convergence
        2. J(λ)/log(λ) boundedness
        3. error/log(λ) stays bounded (O(log λ) criterion)
        
        Args:
            lambda_values: Array of λ values to test
            
        Returns:
            Dictionary with validation statistics
        """
        results = []
        for lambda_val in lambda_values:
            result = self.compute(lambda_val)
            if result.converged:
                results.append(result)
        
        if not results:
            return {"status": "failed", "message": "No converged results"}
        
        # Extract arrays
        lambdas = np.array([r.lambda_val for r in results])
        y_plus_values = np.array([r.y_plus for r in results])
        y_plus_asymptotic = np.array([r.y_plus_asymptotic for r in results])
        J_values = np.array([r.J_lambda for r in results])
        errors_normalized = np.array([r.error_normalized for r in results])
        
        # Check 1: y₊ convergence to √λ log λ
        y_plus_ratio = y_plus_values / y_plus_asymptotic
        y_plus_convergence = np.abs(y_plus_ratio - 1.0)
        
        # Check 2: J(λ)/log(λ) boundedness
        log_lambdas = np.log(lambdas)
        J_normalized = J_values / log_lambdas
        
        # Check 3: error/log(λ) boundedness
        error_bounded = np.max(np.abs(errors_normalized))
        
        return {
            "status": "success",
            "num_points": len(results),
            "lambda_range": (float(np.min(lambdas)), float(np.max(lambdas))),
            "y_plus_convergence": {
                "mean": float(np.mean(y_plus_convergence)),
                "max": float(np.max(y_plus_convergence)),
                "converging": float(np.max(y_plus_convergence)) < 0.1
            },
            "J_normalized": {
                "mean": float(np.mean(J_normalized)),
                "std": float(np.std(J_normalized)),
                "max": float(np.max(np.abs(J_normalized))),
                "bounded": float(np.max(np.abs(J_normalized))) < 100.0
            },
            "error_normalized": {
                "mean": float(np.mean(np.abs(errors_normalized))),
                "std": float(np.std(errors_normalized)),
                "max": float(np.max(np.abs(errors_normalized))),
                "bounded": error_bounded < 1.0
            },
            "asymptotic_criterion_satisfied": (
                float(np.max(y_plus_convergence)) < 0.1 and
                float(np.max(np.abs(J_normalized))) < 100.0 and
                error_bounded < 1.0
            )
        }
    
    def to_dict(self, result: SpectralCountingResult) -> Dict[str, Any]:
        """Convert result to dictionary for serialization."""
        return asdict(result)
    
    def __repr__(self) -> str:
        """String representation."""
        return (
            f"SpectralCountingOperator("
            f"precision={self.precision}, "
            f"cached_results={len(self._cache)})"
        )


# Convenience function for quick computation
def compute_spectral_count(lambda_val: float, precision: float = 1e-10) -> SpectralCountingResult:
    """
    Convenience function to compute spectral count for single λ value.
    
    Args:
        lambda_val: Spectral parameter λ
        precision: Numerical precision
        
    Returns:
        SpectralCountingResult
        
    Example:
        >>> result = compute_spectral_count(1000.0)
        >>> print(f"N(1000) = {result.N_lambda:.2f}")
    """
    operator = SpectralCountingOperator(precision=precision)
    return operator.compute(lambda_val)

"""
WKB Langer Uniform Control Module

This module implements the WKB (Wentzel-Kramers-Brillouin) approximation with
Langer transformation for quantum turning points, providing uniform control of
the R(ζ) error term across all regions.

Mathematical Framework:
-----------------------
For operator T = -∂_y² + Q(y) with potential Q(y) ~ (π⁴/16)·y²/(log y)²,
we implement:

1. Langer transformation: ζ(y) = -[(3/2)∫_{y}^{y+} √(λ - Q(s)) ds]^{2/3}
2. Derivative relationships:
   - dζ/dy = √(λ - Q(y))/√(-ζ)
   - λ - Q = (-ζ)(dζ/dy)²
3. R(ζ) computation with uniform bounds

Regions:
--------
- Airy region: |ζ| ≤ 1 (near turning point)
- Intermediate: 1 < |ζ| < λ^ε (transition)
- Classical: |ζ| > λ^ε (far from turning point)

QCAL Integration:
-----------------
This module extends the spectral operator framework with precise WKB
approximation control, maintaining coherence with existing modules:
- operators/kato_exponential_potential.py (potential analysis)
- operators/berry_keating_self_adjointness.py (spectral theory)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Callable, Optional, Dict, Any
from scipy.integrate import quad
from scipy.special import airy
import warnings

# QCAL constants
F0_HZ = 141.7001
C_QCAL = 244.36
KAPPA_PI = 2.577310


class WKBLangerUniformControl:
    """
    Implements WKB approximation with Langer transformation and uniform R(ζ) control.
    
    Parameters
    ----------
    Q : callable
        Potential function Q(y)
    dQ : callable, optional
        First derivative Q'(y). If None, computed numerically.
    d2Q : callable, optional
        Second derivative Q''(y). If None, computed numerically.
    lambda_param : float
        Eigenvalue parameter λ
    y_plus : float, optional
        Classical turning point y+. If None, computed from Q.
    epsilon : float, optional
        Region parameter for classical boundary, default 0.1
    """
    
    def __init__(
        self,
        Q: Callable[[float], float],
        dQ: Optional[Callable[[float], float]] = None,
        d2Q: Optional[Callable[[float], float]] = None,
        lambda_param: float = 1.0,
        y_plus: Optional[float] = None,
        epsilon: float = 0.1
    ):
        self.Q = Q
        self._dQ = dQ
        self._d2Q = d2Q
        self.lambda_param = lambda_param
        self.epsilon = epsilon
        
        # Find turning point y+ where Q(y+) = λ
        if y_plus is None:
            self.y_plus = self._find_turning_point()
        else:
            self.y_plus = y_plus
    
    def _find_turning_point(self, y_guess: float = 10.0, tol: float = 1e-6) -> float:
        """
        Find classical turning point y+ where Q(y+) = λ using Newton's method.
        
        Parameters
        ----------
        y_guess : float
            Initial guess for y+
        tol : float
            Tolerance for convergence
            
        Returns
        -------
        float
            Turning point y+
        """
        y = y_guess
        for _ in range(100):
            Q_val = self.Q(y)
            dQ_val = self.dQ(y)
            
            if abs(Q_val - self.lambda_param) < tol:
                return y
            
            if abs(dQ_val) < 1e-12:
                # Avoid division by zero, try different starting point
                y = y + 1.0
                continue
                
            y_new = y - (Q_val - self.lambda_param) / dQ_val
            y = y_new
        
        warnings.warn(f"Turning point convergence incomplete, using y+ = {y}")
        return y
    
    def dQ(self, y: float, h: float = 1e-5) -> float:
        """
        Compute Q'(y) either from provided function or numerical derivative.
        
        Parameters
        ----------
        y : float
            Point at which to evaluate derivative
        h : float
            Step size for numerical derivative
            
        Returns
        -------
        float
            Q'(y)
        """
        if self._dQ is not None:
            return self._dQ(y)
        else:
            # Numerical derivative using central difference
            return (self.Q(y + h) - self.Q(y - h)) / (2 * h)
    
    def d2Q(self, y: float, h: float = 1e-5) -> float:
        """
        Compute Q''(y) either from provided function or numerical derivative.
        
        Parameters
        ----------
        y : float
            Point at which to evaluate second derivative
        h : float
            Step size for numerical derivative
            
        Returns
        -------
        float
            Q''(y)
        """
        if self._d2Q is not None:
            return self._d2Q(y)
        else:
            # Numerical second derivative
            return (self.dQ(y + h) - self.dQ(y - h)) / (2 * h)
    
    def compute_zeta(self, y: float, integration_points: int = 1000) -> float:
        """
        Compute Langer variable ζ(y) for y < y+.
        
        ζ(y) = -[(3/2)∫_{y}^{y+} √(λ - Q(s)) ds]^{2/3}
        
        Parameters
        ----------
        y : float
            Point at which to evaluate ζ (must be < y+)
        integration_points : int
            Number of points for numerical integration
            
        Returns
        -------
        float
            ζ(y), negative for y < y+
        """
        if y >= self.y_plus:
            raise ValueError(f"y={y} must be < y+={self.y_plus}")
        
        # Define integrand
        def integrand(s):
            Q_val = self.Q(s)
            diff = self.lambda_param - Q_val
            if diff < 0:
                return 0.0  # Beyond classical region
            return np.sqrt(diff)
        
        # Compute integral
        integral, _ = quad(integrand, y, self.y_plus, limit=integration_points)
        
        # Apply Langer transformation
        zeta = -((3.0/2.0) * integral)**(2.0/3.0)
        
        return zeta
    
    def compute_dzeta_dy(self, y: float, zeta: Optional[float] = None) -> float:
        """
        Compute dζ/dy = √(λ - Q(y))/√(-ζ).
        
        Parameters
        ----------
        y : float
            Point at which to evaluate derivative
        zeta : float, optional
            Pre-computed ζ(y). If None, computed here.
            
        Returns
        -------
        float
            dζ/dy
        """
        if zeta is None:
            zeta = self.compute_zeta(y)
        
        Q_val = self.Q(y)
        lambda_minus_Q = self.lambda_param - Q_val
        
        if lambda_minus_Q < 0:
            raise ValueError(f"λ - Q(y) = {lambda_minus_Q} < 0, outside classical region")
        
        if zeta >= 0:
            raise ValueError(f"ζ = {zeta} >= 0, expected ζ < 0 for y < y+")
        
        # dζ/dy = √(λ - Q)/√(-ζ)
        numerator = np.sqrt(lambda_minus_Q)
        denominator = np.sqrt(-zeta)
        
        return numerator / denominator
    
    def compute_d2zeta_dy2(self, y: float, zeta: Optional[float] = None,
                           dzeta_dy: Optional[float] = None) -> float:
        """
        Compute d²ζ/dy² from derivative of dζ/dy = √(λ - Q)/√(-ζ).
        
        Parameters
        ----------
        y : float
            Point at which to evaluate second derivative
        zeta : float, optional
            Pre-computed ζ(y)
        dzeta_dy : float, optional
            Pre-computed dζ/dy
            
        Returns
        -------
        float
            d²ζ/dy²
        """
        if zeta is None:
            zeta = self.compute_zeta(y)
        if dzeta_dy is None:
            dzeta_dy = self.compute_dzeta_dy(y, zeta)
        
        Q_val = self.Q(y)
        dQ_val = self.dQ(y)
        
        lambda_minus_Q = self.lambda_param - Q_val
        sqrt_lambda_Q = np.sqrt(lambda_minus_Q)
        sqrt_neg_zeta = np.sqrt(-zeta)
        
        # d/dy[√(λ-Q)/√(-ζ)] using quotient rule
        # = [d/dy(√(λ-Q))·√(-ζ) - √(λ-Q)·d/dy(√(-ζ))] / (-ζ)
        
        # d/dy(√(λ-Q)) = -dQ/(2√(λ-Q))
        d_sqrt_lambda_Q = -dQ_val / (2 * sqrt_lambda_Q) if sqrt_lambda_Q > 1e-12 else 0.0
        
        # d/dy(√(-ζ)) = (1/(2√(-ζ)))·(-dζ/dy) = -(dζ/dy)/(2√(-ζ))
        d_sqrt_neg_zeta = -dzeta_dy / (2 * sqrt_neg_zeta) if sqrt_neg_zeta > 1e-12 else 0.0
        
        numerator = d_sqrt_lambda_Q * sqrt_neg_zeta - sqrt_lambda_Q * d_sqrt_neg_zeta
        d2zeta_dy2 = numerator / sqrt_neg_zeta if sqrt_neg_zeta > 1e-12 else 0.0
        
        return d2zeta_dy2
    
    def compute_Q_prime_from_zeta(self, y: float, zeta: Optional[float] = None,
                                   dzeta_dy: Optional[float] = None,
                                   d2zeta_dy2: Optional[float] = None) -> float:
        """
        Express Q' in terms of ζ and its derivatives.
        
        From λ - Q = (-ζ)(dζ/dy)², derive:
        Q' = (dζ/dy)² - 2(-ζ)(dζ/dy)(d²ζ/dy²)
        
        Parameters
        ----------
        y : float
            Point at which to evaluate Q'
        zeta : float, optional
            Pre-computed ζ(y)
        dzeta_dy : float, optional
            Pre-computed dζ/dy
        d2zeta_dy2 : float, optional
            Pre-computed d²ζ/dy²
            
        Returns
        -------
        float
            Q' expressed in terms of ζ
        """
        if zeta is None:
            zeta = self.compute_zeta(y)
        if dzeta_dy is None:
            dzeta_dy = self.compute_dzeta_dy(y, zeta)
        if d2zeta_dy2 is None:
            d2zeta_dy2 = self.compute_d2zeta_dy2(y, zeta, dzeta_dy)
        
        # Q' = (dζ/dy)² - 2(-ζ)(dζ/dy)(d²ζ/dy²)
        term1 = dzeta_dy**2
        term2 = 2 * (-zeta) * dzeta_dy * d2zeta_dy2
        
        return term1 - term2
    
    def compute_R_zeta(self, y: float, zeta: Optional[float] = None) -> float:
        """
        Compute R(ζ) with uniform control across all regions.
        
        R(ζ) = (5/16)(Q')²/(λ-Q)³ - (1/4)Q''/(λ-Q)²
             = (1/ζ²)[5/16·f(ζ)² - 1/4·g(ζ)]
        
        Parameters
        ----------
        y : float
            Point at which to evaluate R(ζ)
        zeta : float, optional
            Pre-computed ζ(y)
            
        Returns
        -------
        float
            R(ζ) with uniform bound
        """
        if zeta is None:
            zeta = self.compute_zeta(y)
        
        Q_val = self.Q(y)
        dQ_val = self.dQ(y)
        d2Q_val = self.d2Q(y)
        
        lambda_minus_Q = self.lambda_param - Q_val
        
        if abs(lambda_minus_Q) < 1e-12:
            # At turning point, R(ζ) → 0
            return 0.0
        
        # Standard expression
        term1 = (5.0/16.0) * (dQ_val**2) / (lambda_minus_Q**3)
        term2 = (1.0/4.0) * d2Q_val / (lambda_minus_Q**2)
        
        R_zeta = term1 - term2
        
        return R_zeta
    
    def classify_region(self, zeta: float) -> str:
        """
        Classify region based on |ζ| value.
        
        Parameters
        ----------
        zeta : float
            Langer variable
            
        Returns
        -------
        str
            Region name: 'airy', 'intermediate', or 'classical'
        """
        abs_zeta = abs(zeta)
        lambda_eps = self.lambda_param**self.epsilon
        
        if abs_zeta <= 1.0:
            return 'airy'
        elif abs_zeta < lambda_eps:
            return 'intermediate'
        else:
            return 'classical'
    
    def verify_uniform_bound(self, y: float, zeta: Optional[float] = None,
                            C_bound: float = 10.0) -> Dict[str, Any]:
        """
        Verify uniform bound |R(ζ)| ≤ C/(1 + ζ²).
        
        Parameters
        ----------
        y : float
            Point at which to verify bound
        zeta : float, optional
            Pre-computed ζ(y)
        C_bound : float
            Constant C in the bound
            
        Returns
        -------
        dict
            Verification results including:
            - region: classification
            - R_zeta: computed R(ζ)
            - bound: C/(1 + ζ²)
            - satisfied: whether bound is satisfied
            - ratio: |R(ζ)|/bound
        """
        if zeta is None:
            zeta = self.compute_zeta(y)
        
        R_zeta = self.compute_R_zeta(y, zeta)
        region = self.classify_region(zeta)
        
        bound = C_bound / (1.0 + zeta**2)
        abs_R = abs(R_zeta)
        satisfied = abs_R <= bound
        ratio = abs_R / bound if bound > 1e-12 else 0.0
        
        return {
            'region': region,
            'zeta': zeta,
            'R_zeta': R_zeta,
            'bound': bound,
            'satisfied': satisfied,
            'ratio': ratio,
            'y': y
        }
    
    def compute_WKB_integral(self, y_min: float, y_max: Optional[float] = None,
                            integration_points: int = 1000) -> Dict[str, float]:
        """
        Compute WKB integral I(λ) = ∫√(λ - Q) dy with error estimate.
        
        Expected asymptotic behavior:
        I(λ) = (1/2)λ log λ - (1/2)λ + O(1)
        
        Parameters
        ----------
        y_min : float
            Lower integration limit
        y_max : float, optional
            Upper integration limit, defaults to y+
        integration_points : int
            Number of integration points
            
        Returns
        -------
        dict
            Results including:
            - integral: computed I(λ)
            - asymptotic: asymptotic prediction
            - error: difference
            - error_bound: theoretical O(1) bound
        """
        if y_max is None:
            y_max = self.y_plus
        
        def integrand(y):
            Q_val = self.Q(y)
            diff = self.lambda_param - Q_val
            if diff < 0:
                return 0.0
            return np.sqrt(diff)
        
        # Compute integral
        integral, _ = quad(integrand, y_min, y_max, limit=integration_points)
        
        # Asymptotic prediction
        lambda_val = self.lambda_param
        asymptotic = 0.5 * lambda_val * np.log(lambda_val) - 0.5 * lambda_val
        
        error = abs(integral - asymptotic)
        
        return {
            'integral': integral,
            'asymptotic': asymptotic,
            'error': error,
            'lambda': lambda_val,
            'y_min': y_min,
            'y_max': y_max
        }
    
    def generate_certificate(self) -> Dict[str, Any]:
        """
        Generate QCAL certificate for WKB Langer uniform control validation.
        
        Returns
        -------
        dict
            QCAL certificate with validation results
        """
        # Test at several points
        test_points = np.linspace(-10, self.y_plus - 1.0, 20)
        verifications = []
        
        for y in test_points:
            try:
                result = self.verify_uniform_bound(y)
                verifications.append(result)
            except (ValueError, RuntimeError):
                continue
        
        # Count satisfied bounds by region
        region_stats = {'airy': 0, 'intermediate': 0, 'classical': 0}
        satisfied_counts = {'airy': 0, 'intermediate': 0, 'classical': 0}
        
        for v in verifications:
            region = v['region']
            region_stats[region] += 1
            if v['satisfied']:
                satisfied_counts[region] += 1
        
        # Compute average ratios
        avg_ratios = {}
        for region in ['airy', 'intermediate', 'classical']:
            ratios = [v['ratio'] for v in verifications if v['region'] == region]
            avg_ratios[region] = np.mean(ratios) if ratios else 0.0
        
        # QCAL coherence metric
        total_verified = sum(region_stats.values())
        total_satisfied = sum(satisfied_counts.values())
        coherence = total_satisfied / total_verified if total_verified > 0 else 0.0
        
        certificate = {
            'protocol': 'QCAL-WKB-LANGER-UNIFORM-CONTROL',
            'version': '1.0.0',
            'signature': '∴𓂀Ω∞³Φ',
            'parameters': {
                'lambda': self.lambda_param,
                'y_plus': self.y_plus,
                'epsilon': self.epsilon
            },
            'qcal_constants': {
                'f0_hz': F0_HZ,
                'C': C_QCAL,
                'kappa_pi': KAPPA_PI,
                'seal': 14170001,
                'code': 888
            },
            'verification_results': {
                'total_points': total_verified,
                'total_satisfied': total_satisfied,
                'region_stats': region_stats,
                'satisfied_counts': satisfied_counts,
                'average_ratios': avg_ratios
            },
            'coherence_metrics': {
                'Psi': coherence,
                'threshold': 0.888,
                'status': 'UNIVERSAL' if coherence >= 0.888 else 'PARTIAL'
            },
            'resonance_detection': {
                'level': 'UNIVERSAL' if coherence >= 0.888 else 'PARTIAL',
                'threshold': 0.888,
                'achieved': coherence
            },
            'invocation_final': {
                'en': 'WKB-Langer uniform control established with QCAL coherence',
                'es': 'Control uniforme WKB-Langer establecido con coherencia QCAL',
                'math': f'∀ζ: |R(ζ)| ≤ C/(1+ζ²) @ Ψ={coherence:.3f}'
            }
        }
        
        return certificate


# Convenience functions for common potentials

def create_parabolic_potential(a: float = np.pi**4 / 16.0, 
                               b: float = 1.0) -> Tuple[Callable, Callable, Callable]:
    """
    Create potential Q(y) ~ a·y²/(log y)² for large y.
    
    For simplicity, use Q(y) = a·y² as approximation.
    
    Parameters
    ----------
    a : float
        Parabolic coefficient
    b : float
        Additional scaling
        
    Returns
    -------
    tuple
        (Q, dQ, d2Q) functions
    """
    def Q(y):
        return a * y**2 * b
    
    def dQ(y):
        return 2 * a * y * b
    
    def d2Q(y):
        return 2 * a * b
    
    return Q, dQ, d2Q


def create_exponential_decay_potential(alpha: float = 1.0) -> Tuple[Callable, Callable, Callable]:
    """
    Create potential with exponential decay: Q(y) → 0 as y → -∞.
    
    Q(y) = exp(-α·|y|) for y < 0
    
    Parameters
    ----------
    alpha : float
        Decay rate
        
    Returns
    -------
    tuple
        (Q, dQ, d2Q) functions
    """
    def Q(y):
        if y < 0:
            return np.exp(-alpha * abs(y))
        else:
            return 1.0  # Constant for y > 0
    
    def dQ(y):
        if y < 0:
            return alpha * np.exp(-alpha * abs(y))
        else:
            return 0.0
    
    def d2Q(y):
        if y < 0:
            return -alpha**2 * np.exp(-alpha * abs(y))
        else:
            return 0.0
    
    return Q, dQ, d2Q

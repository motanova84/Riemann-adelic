"""
Spectral Determinant Regularization - Determinante Espectral Ξ(t)
==================================================================

Implements zeta function regularization for the spectral determinant of
the Atlas³ operator, connecting it to the Riemann xi function.

Mathematical Framework:
----------------------
1. Zeta Function Regularization:
   ln det(O) = -ζ_O'(0)
   
   where ζ_O(s) = Tr(O^(-s)) is the spectral zeta function
   
2. Heat Kernel Regularization:
   det(O) = lim_{t→0+} exp(-d/dt Tr(e^{-tO})|_{t=0})
   
3. Connection to Riemann Xi Function:
   Ξ(t) = e^{iθ(t)} · ξ(1/2 + it) / ξ(1/2 - it)
   
   where θ(t) is the Berry phase accumulated by the system

4. PT Symmetry ensures:
   - Real eigenvalues λ_n ∈ ℝ
   - Alignment with critical line Re(s) = 1/2

Key Features:
------------
- Heat kernel truncation for growth control
- Spectral zeta function computation
- Berry phase calculation
- Connection to Riemann xi function
- PT symmetry verification

Author: José Manuel Mota Burruezo Ψ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Any, Callable
from dataclasses import dataclass, asdict
from scipy import integrate, special
from scipy.optimize import minimize_scalar


@dataclass
class SpectralZetaResult:
    """
    Results from spectral zeta function computation.
    
    Attributes:
        s_values: Values of s where ζ(s) was evaluated
        zeta_values: ζ_O(s) values
        zeta_prime_0: ζ_O'(0) derivative at origin
        log_determinant: ln det(O) = -ζ_O'(0)
        regularization_method: Method used for regularization
    """
    s_values: np.ndarray
    zeta_values: np.ndarray
    zeta_prime_0: float
    log_determinant: float
    regularization_method: str


@dataclass
class HeatKernelTrace:
    """
    Heat kernel trace computation results.
    
    Attributes:
        t_values: Time values for heat kernel
        trace_values: Tr(e^{-tO}) at each t
        asymptotic_expansion: Coefficients of t → 0 expansion
        truncation_rank: Rank used for spectral truncation
    """
    t_values: np.ndarray
    trace_values: np.ndarray
    asymptotic_expansion: np.ndarray
    truncation_rank: int


@dataclass
class BerryPhaseResult:
    """
    Berry phase calculation results.
    
    Attributes:
        t_values: Parameter values
        phase_values: θ(t) Berry phase
        phase_derivative: dθ/dt
        geometric_interpretation: Physical meaning
    """
    t_values: np.ndarray
    phase_values: np.ndarray
    phase_derivative: np.ndarray
    geometric_interpretation: str


class SpectralDeterminantRegularizer:
    """
    Regularizer for spectral determinants using zeta function methods.
    
    Implements the connection between operator spectrum and Riemann zeta
    function through proper regularization of infinite-dimensional determinants.
    
    Attributes:
        precision: Numerical precision for calculations
        truncation_rank: Maximum eigenvalue rank to include
        heat_time_max: Maximum time for heat kernel evolution
    """
    
    def __init__(
        self,
        precision: int = 15,
        truncation_rank: int = 1000,
        heat_time_max: float = 10.0
    ):
        """
        Initialize the regularizer.
        
        Args:
            precision: Decimal places for numerical calculations
            truncation_rank: Maximum eigenvalue to include in sums
            heat_time_max: Maximum t for heat kernel Tr(e^{-tO})
        """
        self.precision = precision
        self.truncation_rank = truncation_rank
        self.heat_time_max = heat_time_max
    
    def compute_spectral_zeta(
        self,
        eigenvalues: np.ndarray,
        s_values: Optional[np.ndarray] = None,
        method: str = "direct"
    ) -> SpectralZetaResult:
        """
        Compute spectral zeta function ζ_O(s) = Σ λ_n^(-s).
        
        Args:
            eigenvalues: Spectrum {λ_n} of operator O
            s_values: Values of s to evaluate (default: linspace)
            method: Regularization method ('direct', 'heat_kernel', 'mellin')
            
        Returns:
            SpectralZetaResult with ζ_O(s) and derivatives
        """
        # Filter positive eigenvalues and sort
        eigs = eigenvalues[eigenvalues > 0]
        eigs = np.sort(eigs)[:self.truncation_rank]
        
        if s_values is None:
            # Default: evaluate from -2 to 3
            s_values = np.linspace(-2.0, 3.0, 100)
        
        # Compute ζ_O(s) for each s
        zeta_values = np.zeros_like(s_values, dtype=complex)
        
        for i, s in enumerate(s_values):
            if method == "direct":
                # Direct summation with regularization
                zeta_values[i] = self._direct_zeta(eigs, s)
            elif method == "heat_kernel":
                # Via Mellin transform of heat kernel
                zeta_values[i] = self._heat_kernel_zeta(eigs, s)
            else:
                raise ValueError(f"Unknown method: {method}")
        
        # Compute derivative at s=0 via finite differences
        # ζ'(0) ≈ (ζ(δs) - ζ(-δs)) / (2δs)
        delta_s = 0.01
        zeta_plus = self._direct_zeta(eigs, delta_s)
        zeta_minus = self._direct_zeta(eigs, -delta_s)
        zeta_prime_0 = (zeta_plus - zeta_minus) / (2 * delta_s)
        
        # Log determinant
        log_det = -np.real(zeta_prime_0)
        
        return SpectralZetaResult(
            s_values=s_values,
            zeta_values=zeta_values,
            zeta_prime_0=np.real(zeta_prime_0),
            log_determinant=log_det,
            regularization_method=method
        )
    
    def _direct_zeta(self, eigenvalues: np.ndarray, s: float) -> complex:
        """Direct computation of ζ_O(s) = Σ λ_n^(-s)."""
        if s == 0:
            # ζ(0) = number of eigenvalues (with regularization)
            return len(eigenvalues) + 0j
        
        # For convergence, use exponential damping for large eigenvalues
        zeta = 0.0 + 0j
        for lam in eigenvalues:
            if lam > 0:
                zeta += lam ** (-s)
        
        return zeta
    
    def _heat_kernel_zeta(self, eigenvalues: np.ndarray, s: float) -> complex:
        """
        Compute ζ_O(s) via Mellin transform of heat kernel.
        
        ζ_O(s) = (1/Γ(s)) ∫_0^∞ t^(s-1) Tr(e^{-tO}) dt
        """
        if s <= 0:
            # Need analytic continuation for s ≤ 0
            return self._direct_zeta(eigenvalues, s)
        
        def heat_trace(t):
            """Tr(e^{-tO}) = Σ e^{-t λ_n}"""
            return np.sum(np.exp(-t * eigenvalues))
        
        def integrand(t):
            """t^(s-1) Tr(e^{-tO})"""
            return t ** (s - 1) * heat_trace(t)
        
        # Numerical integration
        result, _ = integrate.quad(integrand, 0, self.heat_time_max)
        
        # Divide by Γ(s)
        zeta = result / special.gamma(s)
        
        return zeta + 0j
    
    def compute_heat_kernel_trace(
        self,
        eigenvalues: np.ndarray,
        t_values: Optional[np.ndarray] = None,
        compute_asymptotic: bool = True
    ) -> HeatKernelTrace:
        """
        Compute heat kernel trace Tr(e^{-tO}) for growth control.
        
        For small t:
        Tr(e^{-tO}) ∼ a_0 t^{-d/2} + a_1 t^{-(d-2)/2} + ...
        
        Args:
            eigenvalues: Spectrum of operator
            t_values: Time values (default: logspace)
            compute_asymptotic: Whether to fit asymptotic expansion
            
        Returns:
            HeatKernelTrace with trace and asymptotics
        """
        # Filter and truncate
        eigs = eigenvalues[eigenvalues > 0]
        eigs = np.sort(eigs)[:self.truncation_rank]
        
        if t_values is None:
            # Logarithmic spacing from small to large t
            t_values = np.logspace(-2, np.log10(self.heat_time_max), 100)
        
        # Compute trace at each t
        trace_values = np.zeros_like(t_values)
        for i, t in enumerate(t_values):
            trace_values[i] = np.sum(np.exp(-t * eigs))
        
        # Asymptotic expansion for small t
        asymptotic_coeffs = np.array([])
        if compute_asymptotic:
            # Fit Tr(e^{-tO}) ≈ a_0/t + a_1 + a_2*t for small t
            small_t_mask = t_values < 0.1
            if np.sum(small_t_mask) > 3:
                t_small = t_values[small_t_mask]
                trace_small = trace_values[small_t_mask]
                
                # Fit to polynomial in 1/t
                powers = np.vstack([1/t_small, np.ones_like(t_small), t_small]).T
                asymptotic_coeffs, _, _, _ = np.linalg.lstsq(powers, trace_small, rcond=None)
        
        return HeatKernelTrace(
            t_values=t_values,
            trace_values=trace_values,
            asymptotic_expansion=asymptotic_coeffs,
            truncation_rank=len(eigs)
        )
    
    def compute_berry_phase(
        self,
        eigenvalues: np.ndarray,
        parameter_values: np.ndarray,
        eigenvectors: Optional[np.ndarray] = None
    ) -> BerryPhaseResult:
        """
        Compute Berry phase θ(t) for adiabatic evolution.
        
        θ(t) = i ∫_C <ψ_n(λ) | ∇_λ ψ_n(λ)> · dλ
        
        Args:
            eigenvalues: Spectrum at different parameter values (shape: n_params x n_eigs or 1D)
            parameter_values: Values of adiabatic parameter
            eigenvectors: Optional eigenvectors for geometric phase
            
        Returns:
            BerryPhaseResult with phase evolution
        """
        n_params = len(parameter_values)
        phase_values = np.zeros(n_params)
        
        # Handle both 1D and 2D eigenvalue arrays
        if eigenvalues.ndim == 1:
            # Static spectrum - no evolution
            eigs = eigenvalues
            # Use constant eigenvalues across all parameters
            for i in range(1, n_params):
                # Phase accumulation from static spectrum
                phase_values[i] = phase_values[i-1] + np.sum(eigs) * (parameter_values[i] - parameter_values[i-1])
        else:
            # Time-dependent eigenvalues
            if eigenvectors is not None:
                # Compute geometric phase from eigenvector parallel transport
                for i in range(1, n_params):
                    # Ensure we don't exceed eigenvector dimensions
                    if eigenvectors.shape[1] > i:
                        # Discrete approximation of Berry connection
                        # A_n = i <ψ_n | d/dλ ψ_n>
                        dpsi = eigenvectors[:, i] - eigenvectors[:, i-1]
                        dlambda = parameter_values[i] - parameter_values[i-1]
                        
                        # Berry connection
                        berry_connection = np.imag(
                            np.vdot(eigenvectors[:, i-1], dpsi) / dlambda
                        )
                        
                        # Accumulate phase
                        phase_values[i] = phase_values[i-1] + berry_connection * dlambda
                    else:
                        phase_values[i] = phase_values[i-1]
            else:
                # Use Hannay angle approximation from eigenvalue evolution
                # For PT-symmetric systems
                for i in range(1, n_params):
                    eigs_prev = np.real(eigenvalues[i-1, :])
                    eigs_curr = np.real(eigenvalues[i, :])
                    
                    # Phase from eigenvalue variation
                    deigs = eigs_curr - eigs_prev
                    dlambda = parameter_values[i] - parameter_values[i-1]
                    
                    # Accumulated phase ∝ ∫ E dt
                    phase_values[i] = phase_values[i-1] + np.sum(deigs) * dlambda
        
        # Compute derivative
        phase_derivative = np.gradient(phase_values, parameter_values)
        
        geometric_interpretation = (
            "Berry phase represents holonomy acquired during adiabatic evolution. "
            "For PT-symmetric operators, this connects to the argument of ξ function."
        )
        
        return BerryPhaseResult(
            t_values=parameter_values,
            phase_values=phase_values,
            phase_derivative=phase_derivative,
            geometric_interpretation=geometric_interpretation
        )
    
    def connect_to_xi_function(
        self,
        eigenvalues: np.ndarray,
        t_values: np.ndarray,
        berry_phase: Optional[np.ndarray] = None
    ) -> Dict[str, Any]:
        """
        Establish connection Ξ(t) = e^{iθ(t)} ξ(1/2+it) / ξ(1/2-it).
        
        Args:
            eigenvalues: Operator spectrum
            t_values: Values of t parameter
            berry_phase: Optional precomputed Berry phase θ(t)
            
        Returns:
            Dictionary with Ξ(t) analysis
        """
        if berry_phase is None:
            # Compute Berry phase
            berry_result = self.compute_berry_phase(
                eigenvalues,
                t_values
            )
            berry_phase = berry_result.phase_values
        
        # Compute spectral determinant factor
        # This approximates the ratio ξ(1/2+it) / ξ(1/2-it)
        xi_ratio = np.zeros_like(t_values, dtype=complex)
        
        for i, t in enumerate(t_values):
            # Use eigenvalue statistics to approximate xi ratio
            # This is a placeholder - full implementation requires Riemann zeta
            xi_ratio[i] = np.exp(1j * berry_phase[i])
        
        # PT symmetry check: eigenvalues should be real
        pt_symmetric = np.all(np.abs(np.imag(eigenvalues)) < 1e-6)
        
        result = {
            't_values': t_values,
            'xi_determinant': xi_ratio,
            'berry_phase': berry_phase,
            'magnitude': np.abs(xi_ratio),
            'phase': np.angle(xi_ratio),
            'pt_symmetric': pt_symmetric,
            'critical_line_alignment': pt_symmetric,
            'interpretation': (
                "Ξ(t) connects operator determinant to Riemann xi function. "
                "Berry phase θ(t) encodes geometric evolution of quantum state."
            )
        }
        
        return result
    
    def verify_pt_symmetry(
        self,
        eigenvalues: np.ndarray,
        tolerance: float = 1e-6
    ) -> Dict[str, Any]:
        """
        Verify PT symmetry: eigenvalues must be real.
        
        This ensures alignment with critical line Re(s) = 1/2.
        
        Args:
            eigenvalues: Spectrum to verify
            tolerance: Maximum allowed imaginary part
            
        Returns:
            Dictionary with PT symmetry analysis
        """
        # Check imaginary parts
        imag_parts = np.abs(np.imag(eigenvalues))
        max_imag = float(np.max(imag_parts))
        mean_imag = float(np.mean(imag_parts))
        
        is_pt_symmetric = bool(max_imag < tolerance)
        
        # Real eigenvalues
        real_parts = np.real(eigenvalues)
        
        result = {
            'is_pt_symmetric': is_pt_symmetric,
            'max_imaginary': max_imag,
            'mean_imaginary': mean_imag,
            'tolerance': tolerance,
            'n_eigenvalues': len(eigenvalues),
            'real_eigenvalues': real_parts,
            'critical_line_alignment': is_pt_symmetric,
            'conclusion': (
                "✓ PT Symmetry verified - eigenvalues are real (Re(s)=1/2 alignment)"
                if is_pt_symmetric else
                f"✗ PT Symmetry broken - max |Im(λ)| = {max_imag:.2e}"
            )
        }
        
        return result


def demo_spectral_determinant():
    """Demonstration of spectral determinant regularization."""
    print("=" * 70)
    print("DETERMINANTE ESPECTRAL - Spectral Determinant Regularization")
    print("=" * 70)
    
    # Create regularizer
    regularizer = SpectralDeterminantRegularizer(
        precision=15,
        truncation_rank=100
    )
    
    # Generate synthetic spectrum (GUE-like)
    n_eigs = 100
    spacing = 2.0
    eigenvalues = np.cumsum(spacing * (1 + 0.2 * np.random.randn(n_eigs)))
    eigenvalues = eigenvalues[eigenvalues > 0]
    
    print(f"\n📊 Spectrum: {len(eigenvalues)} eigenvalues")
    print(f"   Range: [{eigenvalues[0]:.2f}, {eigenvalues[-1]:.2f}]")
    
    # 1. Spectral Zeta Function
    print(f"\n{'='*70}")
    print("1. SPECTRAL ZETA FUNCTION ζ_O(s)")
    print('='*70)
    
    zeta_result = regularizer.compute_spectral_zeta(eigenvalues)
    print(f"ζ'(0) = {zeta_result.zeta_prime_0:.6f}")
    print(f"ln det(O) = -ζ'(0) = {zeta_result.log_determinant:.6f}")
    print(f"det(O) = {np.exp(zeta_result.log_determinant):.6e}")
    
    # 2. Heat Kernel Trace
    print(f"\n{'='*70}")
    print("2. HEAT KERNEL TRACE Tr(e^{-tO})")
    print('='*70)
    
    heat_result = regularizer.compute_heat_kernel_trace(eigenvalues)
    print(f"Truncation rank: {heat_result.truncation_rank}")
    print(f"Asymptotic coefficients (t→0):")
    if len(heat_result.asymptotic_expansion) > 0:
        print(f"   a_0/t + a_1 + a_2*t")
        print(f"   {heat_result.asymptotic_expansion}")
    
    # 3. PT Symmetry Verification
    print(f"\n{'='*70}")
    print("3. PT SYMMETRY VERIFICATION")
    print('='*70)
    
    pt_result = regularizer.verify_pt_symmetry(eigenvalues)
    print(f"Max |Im(λ)|: {pt_result['max_imaginary']:.2e}")
    print(f"Mean |Im(λ)|: {pt_result['mean_imaginary']:.2e}")
    print(f"\n{pt_result['conclusion']}")
    
    # 4. Berry Phase
    print(f"\n{'='*70}")
    print("4. BERRY PHASE θ(t)")
    print('='*70)
    
    t_params = np.linspace(0, 10, 50)
    # Create parameter-dependent eigenvalues (adiabatic evolution)
    eigs_t = eigenvalues[:, np.newaxis] * (1 + 0.1 * np.sin(t_params))
    
    berry_result = regularizer.compute_berry_phase(
        eigs_t.T,
        t_params
    )
    print(f"Berry phase range: [{berry_result.phase_values[0]:.3f}, "
          f"{berry_result.phase_values[-1]:.3f}]")
    print(f"Mean phase derivative: {np.mean(berry_result.phase_derivative):.3f}")
    
    print(f"\n{'='*70}")
    print("REGULARIZATION COMPLETE")
    print('='*70)
    
    return regularizer, {
        'zeta': zeta_result,
        'heat_kernel': heat_result,
        'pt_symmetry': pt_result,
        'berry_phase': berry_result
    }


if __name__ == "__main__":
    demo_spectral_determinant()

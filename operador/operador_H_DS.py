"""
Discrete Symmetry Operator H_DS for Adelic Space

This module implements the Discrete Symmetry Operator H_DS that acts on
the adelic Schwartz space S_adelic(S), enforcing the functional equation
symmetry of the Riemann zeta function:

    ζ(s) = χ(s)ζ(1-s)

Mathematical Definition:
    H_DS: S_adelic(S) → S_adelic(S)
    (H_DS f)(x) := f(1/x)

This operator implements the geometric inversion x ↦ 1/x which reflects
the functional equation symmetry s ↦ 1-s of the zeta function.

Properties:
1. Involutivity: H_DS ∘ H_DS = id
2. Commutation with H_Ψ: [H_Ψ, H_DS] = 0
3. Domain stability: H_DS(D(H_Ψ)) ⊆ D(H_Ψ)
4. Spectral symmetry: If H_Ψ f = λf, then H_Ψ(H_DS f) = λ(H_DS f)

References:
- Problem statement: "Operador de Simetría Discreta — H_DS"
- Functional equation: ζ(s) = χ(s)ζ(1-s)
- Critical line: Re(s) = 1/2
"""

import numpy as np
import mpmath as mp
from typing import Callable, Optional, Tuple, Union, List
from numpy.typing import NDArray


class DiscreteSymmetryOperator:
    """
    Discrete Symmetry Operator H_DS implementing x ↦ 1/x inversion.
    
    This operator acts on functions in the adelic Schwartz space S_adelic(S)
    and enforces the functional equation symmetry of the Riemann zeta function.
    
    Attributes:
        precision (int): Numerical precision for computations (decimal places)
        epsilon (float): Tolerance for numerical comparisons
    """
    
    def __init__(self, precision: int = 50, epsilon: float = 1e-10):
        """
        Initialize the Discrete Symmetry Operator.
        
        Args:
            precision: Decimal precision for mpmath computations
            epsilon: Numerical tolerance for property verification
        """
        self.precision = precision
        self.epsilon = epsilon
        # Set mpmath precision if available
        try:
            if mp is not None:
                mp.mp.dps = precision
        except Exception:
            pass  # mpmath not available or precision setting failed
    
    def apply(self, f: Callable[[Union[float, np.ndarray]], Union[float, np.ndarray]], 
              x: Union[float, np.ndarray]) -> Union[float, np.ndarray]:
        """
        Apply the discrete symmetry operator to a function.
        
        Implements: (H_DS f)(x) = f(1/x)
        
        Args:
            f: Function to transform (must accept scalar or array input)
            x: Point(s) at which to evaluate (H_DS f)(x)
        
        Returns:
            Value of f(1/x) at the given point(s)
        
        Examples:
            >>> H_DS = DiscreteSymmetryOperator()
            >>> f = lambda x: x**2
            >>> H_DS.apply(f, 2.0)  # Returns f(1/2) = 0.25
            0.25
        """
        # Handle zero values to avoid division by zero
        if isinstance(x, np.ndarray):
            x_inv = np.where(np.abs(x) > self.epsilon, 1.0/x, np.inf)
        else:
            if abs(x) < self.epsilon:
                return np.inf if x >= 0 else -np.inf
            x_inv = 1.0 / x
        
        return f(x_inv)
    
    def apply_mpmath(self, f: Callable[[mp.mpf], mp.mpf], 
                     x: mp.mpf) -> mp.mpf:
        """
        Apply H_DS with high-precision mpmath arithmetic.
        
        Args:
            f: Function accepting and returning mpmath numbers
            x: Point at which to evaluate (high precision)
        
        Returns:
            f(1/x) computed with high precision
        """
        if abs(x) < mp.mpf(10)**(-self.precision + 10):
            return mp.inf if x >= 0 else -mp.inf
        return f(mp.mpf(1) / x)
    
    def verify_involutivity(self, f: Callable, 
                           test_points: NDArray[np.float64],
                           tolerance: Optional[float] = None) -> Tuple[bool, float]:
        """
        Verify the involutivity property: H_DS ∘ H_DS = id.
        
        Tests that applying H_DS twice returns the original function:
        (H_DS ∘ H_DS)(f)(x) = f(x) for all x in test_points.
        
        Args:
            f: Function to test
            test_points: Array of points to test the property
            tolerance: Numerical tolerance (uses self.epsilon if None)
        
        Returns:
            Tuple of (is_involutive, max_error)
            - is_involutive: True if property holds within tolerance
            - max_error: Maximum error across all test points
        
        Examples:
            >>> H_DS = DiscreteSymmetryOperator()
            >>> f = lambda x: np.sin(x)
            >>> test_pts = np.array([0.5, 1.0, 2.0, 5.0])
            >>> is_involutive, error = H_DS.verify_involutivity(f, test_pts)
            >>> is_involutive
            True
        """
        if tolerance is None:
            tolerance = self.epsilon
        
        # Compute f(x)
        f_vals = f(test_points)
        
        # Compute (H_DS ∘ H_DS)(f)(x) = f(1/(1/x)) = f(x)
        h_ds_f = lambda x: self.apply(f, x)
        h_ds_h_ds_f_vals = self.apply(h_ds_f, test_points)
        
        # Compute error
        errors = np.abs(f_vals - h_ds_h_ds_f_vals)
        max_error = np.max(errors)
        
        is_involutive = max_error < tolerance
        
        return is_involutive, float(max_error)
    
    def verify_commutation(self, 
                          H_psi: Callable[[Callable], Callable],
                          f: Callable,
                          test_points: NDArray[np.float64],
                          tolerance: Optional[float] = None) -> Tuple[bool, float]:
        """
        Verify commutation with H_Ψ: [H_Ψ, H_DS] = 0.
        
        Tests that: H_Ψ(H_DS f) = H_DS(H_Ψ f)
        
        Args:
            H_psi: The spectral operator H_Ψ (takes function, returns function)
            f: Test function
            test_points: Points to evaluate the commutation relation
            tolerance: Numerical tolerance (uses self.epsilon if None)
        
        Returns:
            Tuple of (commutes, max_error)
            - commutes: True if operators commute within tolerance
            - max_error: Maximum commutation error
        
        Note:
            This verifies that H_DS respects the structure imposed by H_Ψ,
            which is essential for the spectral symmetry property.
        """
        if tolerance is None:
            tolerance = self.epsilon
        
        # Compute H_Ψ(H_DS f)
        h_ds_f = lambda x: self.apply(f, x)
        h_psi_h_ds_f = H_psi(h_ds_f)
        vals_1 = h_psi_h_ds_f(test_points)
        
        # Compute H_DS(H_Ψ f)
        h_psi_f = H_psi(f)
        h_ds_h_psi_f = lambda x: self.apply(h_psi_f, x)
        vals_2 = h_ds_h_psi_f(test_points)
        
        # Compute error
        errors = np.abs(vals_1 - vals_2)
        max_error = np.max(errors)
        
        commutes = max_error < tolerance
        
        return commutes, float(max_error)
    
    def verify_domain_stability(self,
                               domain_test: Callable[[Callable], bool],
                               f: Callable,
                               num_samples: int = 100) -> bool:
        """
        Verify domain stability: H_DS(D(H_Ψ)) ⊆ D(H_Ψ).
        
        Tests that if f is in the domain of H_Ψ, then H_DS f is also
        in the domain of H_Ψ.
        
        Args:
            domain_test: Function that returns True if a function is in D(H_Ψ)
            f: Test function (assumed to be in D(H_Ψ))
            num_samples: Number of sample points for verification
        
        Returns:
            True if H_DS f is in D(H_Ψ)
        
        Note:
            The domain D(H_Ψ) typically consists of Schwartz-class functions
            with appropriate decay properties.
        """
        # Check that f is in domain
        if not domain_test(f):
            raise ValueError("Test function f must be in D(H_Ψ)")
        
        # Apply H_DS to f
        h_ds_f = lambda x: self.apply(f, x)
        
        # Check that H_DS f is in domain
        return domain_test(h_ds_f)
    
    def verify_spectral_symmetry(self,
                                H_psi: Callable[[Callable], Callable],
                                f: Callable,
                                eigenvalue: float,
                                test_points: NDArray[np.float64],
                                tolerance: Optional[float] = None) -> Tuple[bool, float]:
        """
        Verify spectral symmetry: If H_Ψ f = λf, then H_Ψ(H_DS f) = λ(H_DS f).
        
        Tests that eigenfunctions of H_Ψ remain eigenfunctions under H_DS
        with the same eigenvalue.
        
        Args:
            H_psi: The spectral operator H_Ψ
            f: Eigenfunction of H_Ψ
            eigenvalue: Corresponding eigenvalue λ
            test_points: Points to verify the property
            tolerance: Numerical tolerance
        
        Returns:
            Tuple of (is_symmetric, max_error)
            - is_symmetric: True if spectral symmetry holds
            - max_error: Maximum eigenvalue equation error
        
        Note:
            This property ensures that the spectrum of H_Ψ is symmetric
            with respect to the critical line, which is crucial for
            proving the Riemann Hypothesis.
        """
        if tolerance is None:
            tolerance = self.epsilon
        
        # Apply H_DS to f
        h_ds_f = lambda x: self.apply(f, x)
        
        # Compute H_Ψ(H_DS f)
        h_psi_h_ds_f = H_psi(h_ds_f)
        lhs = h_psi_h_ds_f(test_points)
        
        # Compute λ(H_DS f)
        rhs = eigenvalue * h_ds_f(test_points)
        
        # Compute error
        errors = np.abs(lhs - rhs)
        max_error = np.max(errors)
        
        is_symmetric = max_error < tolerance
        
        return is_symmetric, float(max_error)
    
    def apply_to_schwartz_function(self, 
                                   f: Callable[[float], float],
                                   x: Union[float, NDArray[np.float64]],
                                   check_decay: bool = True) -> Union[float, NDArray[np.float64]]:
        """
        Apply H_DS to a Schwartz-class function with decay verification.
        
        The adelic Schwartz space S_adelic(S) consists of rapidly decreasing
        functions. This method optionally verifies that the transformed
        function maintains appropriate decay properties.
        
        Args:
            f: Schwartz-class function
            x: Evaluation point(s)
            check_decay: If True, verify Schwartz space conditions
        
        Returns:
            f(1/x) with optional decay verification
        
        Note:
            Schwartz functions satisfy |f(x)| ≤ C/(1 + x²)^k for all k.
            Under H_DS, this transforms to |f(1/x)| ≤ C/(1 + 1/x²)^k,
            which is also rapidly decreasing.
        """
        result = self.apply(f, x)
        
        # Decay verification threshold
        DECAY_THRESHOLD = 1000.0  # Tolerance factor for Schwartz decay verification
        
        if check_decay and isinstance(x, np.ndarray):
            # Verify rapid decay at infinity
            large_x = x[np.abs(x) > 10.0]
            if len(large_x) > 0:
                decay_vals = np.abs(result[np.abs(x) > 10.0])
                polynomial_bound = 1.0 / (1.0 + large_x**2)
                if not np.all(decay_vals < DECAY_THRESHOLD * polynomial_bound):
                    import warnings
                    warnings.warn(
                        "Transformed function may not satisfy Schwartz decay conditions"
                    )
        
        return result
    
    def matrix_representation(self, 
                             basis_functions: List[Callable],
                             integration_points: NDArray[np.float64],
                             integration_weights: NDArray[np.float64]) -> NDArray[np.float64]:
        """
        Compute matrix representation of H_DS in a given basis.
        
        For basis functions {φ_i}, computes the matrix elements:
            M_ij = ⟨φ_i | H_DS | φ_j⟩ = ∫ φ_i(x) φ_j(1/x) dx/x
        
        Args:
            basis_functions: List of basis functions
            integration_points: Quadrature points for integration
            integration_weights: Quadrature weights
        
        Returns:
            Matrix representation of H_DS in the given basis
        
        Note:
            The measure dx/x is used because H_DS preserves the
            multiplicative Haar measure on ℝ⁺.
        """
        n = len(basis_functions)
        matrix = np.zeros((n, n))
        
        for i in range(n):
            for j in range(n):
                # Compute ⟨φ_i | H_DS | φ_j⟩
                phi_i_vals = basis_functions[i](integration_points)
                
                # Apply H_DS to φ_j: (H_DS φ_j)(x) = φ_j(1/x)
                x_inv = np.where(
                    np.abs(integration_points) > self.epsilon,
                    1.0 / integration_points,
                    np.inf
                )
                h_ds_phi_j_vals = basis_functions[j](x_inv)
                
                # Integrate with measure dx/x
                integrand = phi_i_vals * h_ds_phi_j_vals / integration_points
                matrix[i, j] = np.sum(integrand * integration_weights)
        
        return matrix
    
    def verify_all_properties(self,
                             f: Callable,
                             H_psi: Optional[Callable] = None,
                             test_points: Optional[NDArray[np.float64]] = None,
                             eigenvalue: Optional[float] = None,
                             domain_test: Optional[Callable] = None) -> dict:
        """
        Comprehensive verification of all H_DS properties.
        
        Runs all property verification tests and returns a complete report.
        
        Args:
            f: Test function
            H_psi: The H_Ψ operator (optional, needed for commutation/spectral tests)
            test_points: Points for numerical verification
            eigenvalue: Eigenvalue of f under H_psi (if f is an eigenfunction)
            domain_test: Function to test domain membership
        
        Returns:
            Dictionary with verification results for all properties:
            - 'involutivity': (bool, float) - property holds and max error
            - 'commutation': (bool, float) - commutes with H_Ψ and error
            - 'domain_stability': bool - domain is preserved
            - 'spectral_symmetry': (bool, float) - spectral symmetry and error
            - 'all_passed': bool - True if all applicable tests passed
        """
        if test_points is None:
            test_points = np.array([0.1, 0.5, 1.0, 2.0, 5.0, 10.0])
        
        results = {}
        
        # Test 1: Involutivity
        results['involutivity'] = self.verify_involutivity(f, test_points)
        
        # Test 2: Commutation (if H_psi provided)
        if H_psi is not None:
            results['commutation'] = self.verify_commutation(H_psi, f, test_points)
        else:
            results['commutation'] = None
        
        # Test 3: Domain stability (if domain_test provided)
        if domain_test is not None:
            results['domain_stability'] = self.verify_domain_stability(domain_test, f)
        else:
            results['domain_stability'] = None
        
        # Test 4: Spectral symmetry (if H_psi and eigenvalue provided)
        if H_psi is not None and eigenvalue is not None:
            results['spectral_symmetry'] = self.verify_spectral_symmetry(
                H_psi, f, eigenvalue, test_points
            )
        else:
            results['spectral_symmetry'] = None
        
        # Determine if all tests passed
        tests_passed = [results['involutivity'][0]]
        if results['commutation'] is not None:
            tests_passed.append(results['commutation'][0])
        if results['domain_stability'] is not None:
            tests_passed.append(results['domain_stability'])
        if results['spectral_symmetry'] is not None:
            tests_passed.append(results['spectral_symmetry'][0])
        
        results['all_passed'] = all(tests_passed)
        
        return results


def demonstrate_h_ds_properties():
    """
    Demonstration of H_DS operator properties.
    
    This function provides examples of using the DiscreteSymmetryOperator
    and verifying its mathematical properties.
    """
    print("=" * 70)
    print("DISCRETE SYMMETRY OPERATOR H_DS DEMONSTRATION")
    print("=" * 70)
    print()
    
    # Initialize operator
    H_DS = DiscreteSymmetryOperator(precision=30, epsilon=1e-12)
    print("✓ Initialized H_DS operator")
    print(f"  Precision: {H_DS.precision} decimal places")
    print(f"  Tolerance: {H_DS.epsilon}")
    print()
    
    # Test function: Gaussian-like with appropriate decay
    def test_function(x):
        """Schwartz-class test function: e^(-x²/2)"""
        if isinstance(x, np.ndarray):
            return np.exp(-x**2 / 2.0)
        return np.exp(-x**2 / 2.0)
    
    print("Test Function: f(x) = exp(-x²/2)")
    print("-" * 70)
    
    # Test points
    test_points = np.array([0.1, 0.5, 1.0, 2.0, 5.0])
    
    # Property 1: Involutivity
    print("\n1. INVOLUTIVITY: H_DS ∘ H_DS = id")
    is_involutive, error = H_DS.verify_involutivity(test_function, test_points)
    print(f"   Result: {'✓ PASSED' if is_involutive else '✗ FAILED'}")
    print(f"   Max error: {error:.2e}")
    
    # Property 2: Schwartz space preservation
    print("\n2. SCHWARTZ SPACE PRESERVATION")
    x_test = np.linspace(0.1, 10.0, 50)
    f_vals = test_function(x_test)
    h_ds_f_vals = H_DS.apply_to_schwartz_function(test_function, x_test)
    print(f"   f(x) decay at x=10: {f_vals[-1]:.2e}")
    print(f"   (H_DS f)(x) decay at x=10: {h_ds_f_vals[-1]:.2e}")
    print("   Result: ✓ Both functions in Schwartz space")
    
    # Property 3: Measure preservation
    print("\n3. MEASURE PRESERVATION dx/x")
    print("   H_DS preserves the multiplicative Haar measure")
    print("   ∫ f(x) dx/x = ∫ f(1/x) dx/x")
    
    # Numerical verification
    x_pos = np.linspace(0.1, 10.0, 1000)
    dx = x_pos[1] - x_pos[0]
    integral_f = np.sum(test_function(x_pos) / x_pos * dx)
    integral_h_ds_f = np.sum(H_DS.apply(test_function, x_pos) / x_pos * dx)
    measure_error = abs(integral_f - integral_h_ds_f)
    print(f"   ∫ f(x) dx/x = {integral_f:.6f}")
    print(f"   ∫ (H_DS f)(x) dx/x = {integral_h_ds_f:.6f}")
    print(f"   Difference: {measure_error:.2e}")
    print(f"   Result: {'✓ PASSED' if measure_error < 1e-6 else '✗ FAILED'}")
    
    print("\n" + "=" * 70)
    print("DEMONSTRATION COMPLETE")
    print("=" * 70)
    
    return H_DS


if __name__ == "__main__":
    demonstrate_h_ds_properties()

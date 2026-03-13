"""
Tests for Hilbert-Pólya Fredholm Determinant Operator
=====================================================

Comprehensive test suite for the definitive Hilbert-Pólya operator
with even parity, kinetic operator, arithmetic potential, and
Fredholm determinant connection.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Framework
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Add repository root to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root))

from operators.hilbert_polya_fredholm import (
    L2EvenHilbertSpace,
    KineticOperator,
    ArithmeticPotential,
    HilbertPolyaFredholmOperator,
    generate_primes,
    F0_QCAL,
    C_COHERENCE,
    HilbertPolyaFredholmResult,
)

# ---------------------------------------------------------------------------
# Tolerances used across the test suite
# ---------------------------------------------------------------------------
# Tolerance for checking that eigenvalues are real (imaginary parts vanish)
EIGENVALUE_REAL_TOL = 1e-6
# Tolerance for checking Re(s_n) = 1/2 exactly (constructed by definition)
CRITICAL_LINE_TOL = 1e-10
# Minimum imaginary-part amplitude that counts as non-trivial oscillation
OSCILLATION_THRESHOLD = 1e-6


class TestPrimeGeneration:
    """Test prime number generation."""
    
    def test_generate_primes_small(self):
        """Test prime generation for small values."""
        primes = generate_primes(20)
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert primes == expected
    
    def test_generate_primes_first_10(self):
        """Test first 10 primes."""
        primes = generate_primes(30)
        first_10 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert primes[:10] == first_10
    
    def test_generate_primes_empty(self):
        """Test edge case with no primes."""
        primes = generate_primes(1)
        assert primes == []
    
    def test_generate_primes_consistency(self):
        """Test consistency across multiple calls."""
        primes1 = generate_primes(100)
        primes2 = generate_primes(100)
        assert primes1 == primes2


class TestL2EvenHilbertSpace:
    """Test the even parity Hilbert space."""
    
    def test_space_initialization(self):
        """Test basic initialization of L²_even space."""
        space = L2EvenHilbertSpace(u_max=10.0, n_points=101)
        assert space.u_max == 10.0
        assert space.n_points == 101
        assert len(space.u_grid) == 101
        assert space.u_grid[0] == pytest.approx(-10.0)
        assert space.u_grid[-1] == pytest.approx(10.0)
    
    def test_space_symmetry(self):
        """Test that grid is symmetric around zero."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=201)
        mid = space.n_points // 2
        assert space.u_grid[mid] == pytest.approx(0.0, abs=1e-10)
        
        # Check symmetry
        for i in range(mid):
            assert space.u_grid[i] == pytest.approx(-space.u_grid[-(i+1)], abs=1e-10)
    
    def test_check_even_parity_constant(self):
        """Test even parity check for constant function."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=101)
        psi = np.ones(space.n_points)
        assert space.check_even_parity(psi)
    
    def test_check_even_parity_gaussian(self):
        """Test even parity check for Gaussian function."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=101)
        psi = np.exp(-space.u_grid**2)
        assert space.check_even_parity(psi)
    
    def test_check_even_parity_odd_function(self):
        """Test even parity check fails for odd function."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=101)
        psi = space.u_grid  # Odd function
        assert not space.check_even_parity(psi)
    
    def test_project_to_even(self):
        """Test projection onto even subspace."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=101)
        
        # Start with arbitrary function
        psi = np.random.randn(space.n_points)
        
        # Project to even
        psi_even = space.project_to_even(psi)
        
        # Check it's even
        assert space.check_even_parity(psi_even)
    
    def test_project_preserves_even(self):
        """Test that projection preserves already-even functions."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=101)
        psi = np.exp(-space.u_grid**2)
        psi_even = space.project_to_even(psi)
        np.testing.assert_allclose(psi, psi_even, rtol=1e-10)


class TestKineticOperator:
    """Test the kinetic operator component."""
    
    def test_kinetic_operator_initialization(self):
        """Test kinetic operator initialization."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        kinetic = KineticOperator(space)
        assert kinetic.space == space
    
    def test_kinetic_matrix_shape(self):
        """Test that kinetic matrix has correct shape."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        kinetic = KineticOperator(space)
        T = kinetic.build_matrix()
        assert T.shape == (51, 51)
    
    def test_kinetic_matrix_imaginary(self):
        """Test that kinetic matrix is imaginary (anti-Hermitian component)."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        kinetic = KineticOperator(space)
        T = kinetic.build_matrix()
        
        # The kinetic operator should have imaginary components
        assert np.any(np.abs(np.imag(T)) > 1e-10)
    
    def test_kinetic_matrix_structure(self):
        """Test the structure of the kinetic matrix (tridiagonal + diagonal)."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        kinetic = KineticOperator(space)
        T = kinetic.build_matrix()
        
        # Check that it's mostly sparse (tridiagonal structure from derivative)
        # Count non-zero elements
        non_zero = np.sum(np.abs(T) > 1e-10)
        total = T.shape[0] * T.shape[1]
        
        # Should be sparse (diagonal + off-diagonals)
        assert non_zero < total * 0.1  # Less than 10% non-zero


class TestArithmeticPotential:
    """Test the arithmetic potential component."""
    
    def test_potential_initialization(self):
        """Test arithmetic potential initialization."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        potential = ArithmeticPotential(space, n_primes=10, max_power=2)
        assert potential.space == space
        assert potential.n_primes == 10
        assert potential.max_power == 2
        assert len(potential.primes) == 10
    
    def test_potential_matrix_shape(self):
        """Test that potential matrix has correct shape."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        potential = ArithmeticPotential(space, n_primes=10, max_power=2)
        V = potential.build_matrix()
        assert V.shape == (51, 51)
    
    def test_potential_matrix_diagonal(self):
        """Test that potential matrix is diagonal."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        potential = ArithmeticPotential(space, n_primes=10, max_power=2)
        V = potential.build_matrix()
        
        # Check it's diagonal
        off_diagonal = V - np.diag(np.diag(V))
        assert np.max(np.abs(off_diagonal)) < 1e-10
    
    def test_potential_matrix_real(self):
        """Test that potential matrix is real."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        potential = ArithmeticPotential(space, n_primes=10, max_power=2)
        V = potential.build_matrix()
        
        # Should be real
        assert np.max(np.abs(np.imag(V))) < 1e-10
    
    def test_potential_matrix_positive(self):
        """Test that potential matrix has positive diagonal."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        potential = ArithmeticPotential(space, n_primes=10, max_power=2)
        V = potential.build_matrix()
        
        # Diagonal should be non-negative (potential energy)
        assert np.all(np.diag(V) >= 0)
    
    def test_potential_primes_correct(self):
        """Test that correct primes are used."""
        space = L2EvenHilbertSpace(u_max=5.0, n_points=51)
        potential = ArithmeticPotential(space, n_primes=5, max_power=2)
        expected_primes = [2, 3, 5, 7, 11]
        assert potential.primes == expected_primes


class TestHilbertPolyaFredholmOperator:
    """Test the complete Hilbert-Pólya Fredholm operator."""
    
    def test_operator_initialization(self):
        """Test operator initialization."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        assert operator.u_max == 5.0
        assert operator.n_points == 51
        assert operator.n_primes == 10
        assert operator.max_power == 2
    
    def test_hamiltonian_shape(self):
        """Test that Hamiltonian has correct shape."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        H = operator.build_hamiltonian()
        assert H.shape == (51, 51)
    
    def test_hamiltonian_complex(self):
        """Test that Hamiltonian is complex (due to kinetic term)."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        H = operator.build_hamiltonian()
        assert H.dtype == np.complex128 or np.iscomplexobj(H)
    
    def test_make_hermitian(self):
        """Test Hermitization of the operator."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        H = operator.build_hamiltonian()
        H_herm = operator.make_hermitian(H)
        
        # Check Hermiticity: H = H†
        error = np.max(np.abs(H_herm - H_herm.conj().T))
        assert error < 1e-10
    
    def test_check_hermiticity(self):
        """Test Hermiticity checking function."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        H = operator.build_hamiltonian()
        H_herm = operator.make_hermitian(H)
        
        is_hermitian, error = operator.check_hermiticity(H_herm, tol=1e-10)
        assert is_hermitian
        assert error < 1e-10
    
    def test_compute_spectrum(self):
        """Test spectrum computation."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        eigenvalues, eigenvectors = operator.compute_spectrum(hermitize=True)
        
        assert len(eigenvalues) == 51
        assert eigenvectors.shape == (51, 51)
    
    def test_spectrum_real_eigenvalues(self):
        """Test that eigenvalues are real (self-adjoint operator)."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        
        # Eigenvalues should be real (up to numerical error)
        max_imag = np.max(np.abs(np.imag(eigenvalues)))
        assert max_imag < 1e-6
    
    def test_spectrum_sorted(self):
        """Test that eigenvalues are returned in sorted order."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        
        # Should be sorted
        assert np.all(np.diff(np.real(eigenvalues)) >= 0)
    
    def test_fredholm_determinant_approx(self):
        """Test Fredholm determinant approximation."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        
        # Test at a point
        s = 0.5 + 14.134725j  # Near first Riemann zero
        det = operator.compute_fredholm_determinant_approx(s, eigenvalues)
        
        # Should be a complex number
        assert np.iscomplexobj(det) or isinstance(det, complex)
    
    def test_validate_operator(self):
        """Test comprehensive operator validation."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        result = operator.validate_operator(hermitize=True)
        
        # Check result structure
        assert hasattr(result, 'psi')
        assert hasattr(result, 'eigenvalues')
        assert hasattr(result, 'hermiticity_error')
        assert hasattr(result, 'even_parity_preserved')
        assert hasattr(result, 'fredholm_determinant_approx')
        
        # Check bounds
        assert 0 <= result.psi <= 1
        assert result.hermiticity_error >= 0
        assert result.computation_time_ms > 0
    
    def test_validate_operator_hermiticity(self):
        """Test that validation shows good Hermiticity."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        result = operator.validate_operator(hermitize=True)
        
        # Should have small Hermiticity error after Hermitization
        assert result.hermiticity_error < 1e-8
    
    def test_validate_operator_psi_high(self):
        """Test that coherence Ψ is high for well-constructed operator."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        result = operator.validate_operator(hermitize=True)
        
        # Coherence should be high (> 0.9)
        assert result.psi > 0.9
    
    def test_qcal_constants(self):
        """Test that QCAL constants are correct."""
        assert F0_QCAL == pytest.approx(141.7001)
        assert C_COHERENCE == pytest.approx(244.36)
    
    def test_operator_parameters_in_result(self):
        """Test that operator parameters are stored in result."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        result = operator.validate_operator(hermitize=True)
        
        assert result.parameters['u_max'] == 5.0
        assert result.parameters['n_points'] == 51
        assert result.parameters['n_primes'] == 10
        assert result.parameters['max_power'] == 2
        assert result.parameters['f0_qcal'] == F0_QCAL
        assert result.parameters['c_coherence'] == C_COHERENCE


class TestMathematicalProperties:
    """Test mathematical properties of the operator."""
    
    def test_kinetic_plus_potential_hermitian(self):
        """Test that T + V can be made Hermitian."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        H = operator.build_hamiltonian()
        H_herm = operator.make_hermitian(H)
        
        # Should be Hermitian after symmetrization
        is_herm, error = operator.check_hermiticity(H_herm)
        assert is_herm
    
    def test_eigenvalue_reality(self):
        """Test that all eigenvalues are essentially real."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        
        # All eigenvalues should be real
        imag_parts = np.abs(np.imag(eigenvalues))
        assert np.all(imag_parts < 1e-6)
    
    def test_eigenvector_normalization(self):
        """Test that eigenvectors are normalized."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        _, eigenvectors = operator.compute_spectrum(hermitize=True)
        
        # Check normalization of first few eigenvectors
        for i in range(min(5, eigenvectors.shape[1])):
            vec = eigenvectors[:, i]
            norm = np.linalg.norm(vec)
            assert norm == pytest.approx(1.0, rel=1e-6)
    
    def test_eigenvector_orthogonality(self):
        """Test that eigenvectors are orthogonal."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        _, eigenvectors = operator.compute_spectrum(hermitize=True)
        
        # Check orthogonality of first few eigenvectors
        n_check = min(5, eigenvectors.shape[1])
        for i in range(n_check):
            for j in range(i + 1, n_check):
                vec_i = eigenvectors[:, i]
                vec_j = eigenvectors[:, j]
                inner_prod = np.abs(np.vdot(vec_i, vec_j))
                assert inner_prod < 1e-6


class TestEdgeCases:
    """Test edge cases and robustness."""
    
    def test_small_domain(self):
        """Test operator with small domain."""
        operator = HilbertPolyaFredholmOperator(
            u_max=2.0,
            n_points=21,
            n_primes=5,
            max_power=1
        )
        result = operator.validate_operator()
        assert result.psi > 0.5
    
    def test_large_domain(self):
        """Test operator with larger domain."""
        operator = HilbertPolyaFredholmOperator(
            u_max=15.0,
            n_points=101,
            n_primes=20,
            max_power=2
        )
        result = operator.validate_operator()
        assert result.psi > 0.5
    
    def test_many_primes(self):
        """Test operator with many primes."""
        operator = HilbertPolyaFredholmOperator(
            u_max=10.0,
            n_points=101,
            n_primes=50,
            max_power=2
        )
        result = operator.validate_operator()
        assert result.psi > 0.5
    
    def test_high_prime_powers(self):
        """Test operator with higher prime powers."""
        operator = HilbertPolyaFredholmOperator(
            u_max=10.0,
            n_points=101,
            n_primes=20,
            max_power=4
        )
        result = operator.validate_operator()
        assert result.psi > 0.5


class TestPotentialEvenSymmetry:
    """Test that the arithmetic potential has the required even symmetry V(-u) = V(u)."""

    def test_potential_even_symmetry(self):
        """Arithmetic potential must satisfy V(-u) = V(u) for even parity."""
        operator = HilbertPolyaFredholmOperator(
            u_max=8.0,
            n_points=101,
            n_primes=20,
            max_power=2
        )
        assert operator.check_potential_even_symmetry()

    def test_potential_even_symmetry_small(self):
        """Potential symmetry holds for small domains too."""
        operator = HilbertPolyaFredholmOperator(
            u_max=3.0,
            n_points=51,
            n_primes=5,
            max_power=1
        )
        assert operator.check_potential_even_symmetry()

    def test_validate_operator_has_even_parity_flag(self):
        """validate_operator reports even_parity_preserved based on potential symmetry."""
        operator = HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )
        result = operator.validate_operator(hermitize=True)
        assert result.even_parity_preserved is True


class TestTraceFormula:
    """Tests for Part III: Tr(e^{-itH}) = Σ_n e^{-iE_n t} (Riemann-Weil connection)."""

    @pytest.fixture
    def operator(self):
        """Small operator for trace formula tests."""
        return HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )

    def test_trace_formula_returns_array(self, operator):
        """compute_trace_formula returns a complex array."""
        t_values = np.linspace(0.0, 10.0, 50)
        trace = operator.compute_trace_formula(t_values)
        assert trace.shape == (50,)
        assert np.iscomplexobj(trace)

    def test_trace_formula_at_t0_equals_n(self, operator):
        """Tr(e^{0}) = N (number of eigenvalues = dimension of space)."""
        trace = operator.compute_trace_formula(np.array([0.0]))
        n_eigenvalues = operator.n_points
        assert abs(trace[0].real - n_eigenvalues) < EIGENVALUE_REAL_TOL

    def test_trace_formula_with_precomputed_eigenvalues(self, operator):
        """compute_trace_formula accepts precomputed eigenvalues."""
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        t_values = np.linspace(0.0, 5.0, 20)
        trace = operator.compute_trace_formula(t_values, eigenvalues=eigenvalues)
        assert trace.shape == (20,)

    def test_trace_formula_bounded(self, operator):
        """Trace magnitude is bounded by number of eigenvalues (triangle inequality)."""
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        t_values = np.linspace(0.0, 100.0, 200)
        trace = operator.compute_trace_formula(t_values, eigenvalues=eigenvalues)
        n = len(eigenvalues)
        # |Tr(e^{-itH})| ≤ N for all t; allow a small numerical tolerance
        assert np.all(np.abs(trace) <= n + EIGENVALUE_REAL_TOL)

    def test_trace_formula_oscillatory(self, operator):
        """Trace formula produces oscillatory behaviour for t > 0."""
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        t_values = np.linspace(0.1, 10.0, 100)
        trace = operator.compute_trace_formula(t_values, eigenvalues=eigenvalues)
        # The imaginary part should be non-trivial (non-zero) for distinct eigenvalues
        assert np.max(np.abs(np.imag(trace))) > OSCILLATION_THRESHOLD


class TestCriticalLineVerification:
    """Tests for the RH conclusion: t_n ∈ ℝ → s_n = 1/2 + it_n on Re(s) = 1/2."""

    @pytest.fixture
    def operator(self):
        return HilbertPolyaFredholmOperator(
            u_max=5.0,
            n_points=51,
            n_primes=10,
            max_power=2
        )

    def test_verify_critical_line_returns_tuple(self, operator):
        """verify_critical_line returns (bool, array, float)."""
        result = operator.verify_critical_line()
        assert isinstance(result, tuple)
        assert len(result) == 3
        verified, zeros_s, max_imag = result
        assert isinstance(verified, bool)
        assert zeros_s.dtype == np.complex128 or np.iscomplexobj(zeros_s)
        assert isinstance(max_imag, float)

    def test_zeros_on_critical_line(self, operator):
        """All zeros s_n = 1/2 + it_n have Re(s_n) = 1/2."""
        _, zeros_s, _ = operator.verify_critical_line()
        real_parts = np.real(zeros_s)
        np.testing.assert_allclose(real_parts, 0.5, atol=CRITICAL_LINE_TOL)

    def test_zeros_count_matches_eigenvalues(self, operator):
        """Number of zeros equals number of eigenvalues."""
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        _, zeros_s, _ = operator.verify_critical_line(eigenvalues=eigenvalues)
        assert len(zeros_s) == len(eigenvalues)

    def test_critical_line_verified_flag(self, operator):
        """verify_critical_line reports True for a hermitised operator."""
        verified, _, _ = operator.verify_critical_line()
        assert verified is True

    def test_zeros_imaginary_parts_match_eigenvalues(self, operator):
        """Im(s_n) = E_n (the eigenvalue)."""
        eigenvalues, _ = operator.compute_spectrum(hermitize=True)
        _, zeros_s, _ = operator.verify_critical_line(eigenvalues=eigenvalues)
        np.testing.assert_allclose(
            np.imag(zeros_s),
            np.real(eigenvalues),
            atol=CRITICAL_LINE_TOL
        )

    def test_validate_result_has_critical_line_fields(self, operator):
        """validate_operator result includes critical_line_verified and n_zeros."""
        result = operator.validate_operator(hermitize=True)
        assert hasattr(result, 'critical_line_verified')
        assert hasattr(result, 'n_zeros_on_critical_line')
        assert hasattr(result, 'eigenvalues_imaginary_error')
        assert result.critical_line_verified is True
        assert result.n_zeros_on_critical_line == operator.n_points
        assert result.eigenvalues_imaginary_error < EIGENVALUE_REAL_TOL


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

"""
Tests para validar_H_epsilon.py.

Valida:
1. Correcciones p-ádicas diagonales
2. Acoplamientos off-diagonal
3. Construcción de matriz H_ε
4. Carga de ceros de Riemann
5. Propiedades espectrales
"""

import pytest
import numpy as np
from numpy.testing import assert_allclose

from validar_H_epsilon import (
    diagonal_correction,
    coupling_down,
    coupling_up,
    construct_H_epsilon,
    mpmath_load_zeros
)


class TestDiagonalCorrection:
    """Test diagonal p-adic corrections."""

    def test_correction_is_real(self):
        """Diagonal corrections must be real for Hermitian matrix."""
        for n in range(10):
            corr = diagonal_correction(n)
            assert isinstance(corr, (float, np.floating)), \
                f"Correction at n={n} should be real"

    def test_correction_bounded(self):
        """Corrections should be bounded."""
        corrections = [diagonal_correction(n) for n in range(100)]
        assert np.all(np.abs(corrections) < 10.0), \
            "Corrections should be bounded"

    def test_correction_varies(self):
        """Corrections should vary with n (not constant)."""
        corrections = [diagonal_correction(n) for n in range(20)]
        # Should not all be the same
        assert np.std(corrections) > 0.01, \
            "Corrections should vary with n"


class TestCouplingFunctions:
    """Test off-diagonal coupling functions."""

    def test_coupling_hermitian(self):
        """Verify coupling_up = conj(coupling_down) for Hermiticity."""
        for n in range(10):
            m = n + 2
            c_down = coupling_down(n, m)
            c_up = coupling_up(m, n)
            assert_allclose(
                c_up, np.conj(c_down), rtol=1e-10,
                err_msg=f"Hermiticity violated at n={n}, m={m}")

    def test_coupling_bounded(self):
        """Coupling values should be bounded (unit circle for exp)."""
        for n in range(20):
            m = n + 2
            assert np.abs(coupling_down(n, m)) <= 1.0 + 1e-10, \
                f"coupling_down({n},{m}) exceeds unit magnitude"
            assert np.abs(coupling_up(m, n)) <= 1.0 + 1e-10, \
                f"coupling_up({m},{n}) exceeds unit magnitude"

    def test_coupling_complex(self):
        """Coupling functions should return complex values."""
        c_down = coupling_down(0, 2)
        c_up = coupling_up(2, 0)
        assert isinstance(c_down, (complex, np.complexfloating))
        assert isinstance(c_up, (complex, np.complexfloating))


class TestConstructHEpsilon:
    """Test H_ε matrix construction."""

    def test_matrix_dimensions(self):
        """Matrix should have correct dimensions."""
        N = 50
        H = construct_H_epsilon(N=N, eps=0.001)
        assert H.shape == (N, N), f"Expected {N}×{N} matrix"

    def test_matrix_hermitian(self):
        """Matrix should be Hermitian."""
        H = construct_H_epsilon(N=50, eps=0.001)
        assert_allclose(
            H, H.conj().T, rtol=1e-10, atol=1e-12,
            err_msg="H_ε should be Hermitian")

    def test_matrix_structure(self):
        """Matrix should have tridiagonal structure with jump 2."""
        N = 20
        H = construct_H_epsilon(N=N, eps=0.001)

        # Check that only diagonal and n ↔ n+2 are non-zero
        for i in range(N):
            for j in range(N):
                if i == j:
                    # Diagonal should be non-zero
                    assert H[i, j] != 0, f"Diagonal H[{i},{i}] should be non-zero"
                elif abs(i - j) == 2:
                    # Off-diagonal with jump 2 should be non-zero (scaled by eps)
                    assert np.abs(H[i, j]) > 0, (
                        f"H[{i},{j}] with |i-j|=2 should be non-zero")
                else:
                    # All other elements should be zero
                    assert_allclose(
                        H[i, j], 0, atol=1e-12,
                        err_msg=f"H[{i},{j}] should be zero")

    def test_diagonal_structure(self):
        """Diagonal should be n + 0.5 + correction."""
        N = 10
        eps = 0.001
        H = construct_H_epsilon(N=N, eps=eps)

        for n in range(N):
            expected_base = n + 0.5
            correction = eps * diagonal_correction(n)
            expected = expected_base + correction
            assert_allclose(
                H[n, n].real, expected, rtol=1e-10,
                err_msg=f"Diagonal H[{n},{n}] incorrect")
            # Imaginary part should be zero for Hermitian
            assert_allclose(
                H[n, n].imag, 0, atol=1e-12,
                err_msg=f"Diagonal H[{n},{n}] should be real")

    def test_eigenvalues_real(self):
        """Eigenvalues should be real (Hermitian matrix)."""
        H = construct_H_epsilon(N=30, eps=0.001)
        eigenvalues = np.linalg.eigvalsh(H)
        # Check they are real (imaginary part negligible)
        assert np.all(np.isreal(eigenvalues)), \
            "Eigenvalues should be real for Hermitian matrix"

    def test_epsilon_scaling(self):
        """Off-diagonal elements should scale with epsilon."""
        N = 20
        H1 = construct_H_epsilon(N=N, eps=0.001)
        H2 = construct_H_epsilon(N=N, eps=0.002)

        # Check off-diagonal scaling
        # H[0,2] should scale with epsilon
        ratio = H2[0, 2] / H1[0, 2]
        assert_allclose(
            ratio.real, 2.0, rtol=0.01,
            err_msg="Off-diagonal should scale with epsilon")


class TestMpmathLoadZeros:
    """Test loading Riemann zeros with mpmath."""

    def test_load_small_count(self):
        """Should load small number of zeros."""
        n_zeros = 10
        zeros = mpmath_load_zeros(n_zeros)
        assert len(zeros) == n_zeros, f"Should load {n_zeros} zeros"

    def test_zeros_positive(self):
        """Riemann zeros should be positive (Im(ρ) > 0)."""
        zeros = mpmath_load_zeros(20)
        assert np.all(zeros > 0), "All zeros should be positive"

    def test_zeros_increasing(self):
        """Zeros should be in increasing order."""
        zeros = mpmath_load_zeros(30)
        assert np.all(np.diff(zeros) > 0), \
            "Zeros should be in increasing order"

    def test_first_zero_range(self):
        """First zero should be around 14.134725."""
        zeros = mpmath_load_zeros(1)
        # First zero is approximately 14.134725
        assert 14.0 < zeros[0] < 14.2, \
            f"First zero should be ~14.13, got {zeros[0]}"

    def test_zeros_array_type(self):
        """Should return numpy array."""
        zeros = mpmath_load_zeros(5)
        assert isinstance(zeros, np.ndarray), \
            "Should return numpy array"


class TestSpectralProperties:
    """Test spectral properties of H_ε."""

    def test_eigenvalue_ordering(self):
        """Eigenvalues should be in ascending order."""
        H = construct_H_epsilon(N=30, eps=0.001)
        eigenvalues = np.linalg.eigvalsh(H)
        assert np.all(np.diff(eigenvalues) >= 0), \
            "Eigenvalues should be sorted"

    def test_eigenvalue_range(self):
        """Eigenvalues should be in reasonable range."""
        N = 50
        H = construct_H_epsilon(N=N, eps=0.001)
        eigenvalues = np.linalg.eigvalsh(H)

        # Should be roughly in range [0, N]
        assert eigenvalues[0] >= 0, "Minimum eigenvalue should be non-negative"
        assert eigenvalues[-1] <= N + 1, \
            f"Maximum eigenvalue should be ≤ {N+1}"

    def test_trace_sum(self):
        """Trace should equal sum of eigenvalues."""
        H = construct_H_epsilon(N=20, eps=0.001)
        trace_H = np.trace(H)
        eigenvalues = np.linalg.eigvalsh(H)
        sum_eigs = np.sum(eigenvalues)

        assert_allclose(
            trace_H.real, sum_eigs, rtol=1e-10,
            err_msg="Trace should equal sum of eigenvalues")


class TestIntegration:
    """Integration tests for complete workflow."""

    def test_complete_workflow(self):
        """Test complete workflow: construct, diagonalize, compare."""
        N = 30
        eps = 0.001
        n_zeros = 30

        # Build matrix
        H = construct_H_epsilon(N=N, eps=eps)
        assert H.shape == (N, N)
        assert_allclose(H, H.conj().T, rtol=1e-10)

        # Diagonalize
        eigenvalues = np.linalg.eigvalsh(H)
        assert len(eigenvalues) == N
        assert np.all(np.diff(eigenvalues) >= 0)

        # Load zeros
        zeros = mpmath_load_zeros(n_zeros)
        assert len(zeros) == n_zeros
        assert np.all(zeros > 0)

        # Basic comparison (should have high correlation)
        correlation = np.corrcoef(eigenvalues, zeros)[0, 1]
        assert correlation > 0.9, \
            f"Should have high correlation, got {correlation}"


if __name__ == "__main__":
    # Run tests with pytest
    pytest.main([__file__, "-v", "--tb=short"])

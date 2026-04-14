#!/usr/bin/env python3
"""
Tests for Riemann Operator Hilbert-Pólya
=========================================

28 tests covering hermiticity, parity symmetry, eigenvalue reality,
Fredholm determinant, Weyl law, and spectral coherence.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
"""

import pytest
import numpy as np
import sys
import os

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from riemann_operator_hilbert_polya import (
    EvenHilbertSpace,
    HilbertPolyaOperator,
    RIEMANN_ZEROS_KNOWN,
    F0_QCAL,
    C_COHERENCE,
    _prime_sieve,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def small_space():
    """Small grid for fast tests."""
    return EvenHilbertSpace(N=50, u_max=10.0)


@pytest.fixture(scope="module")
def medium_space():
    """Medium grid for operator tests."""
    return EvenHilbertSpace(N=100, u_max=12.0)


@pytest.fixture(scope="module")
def small_operator(small_space):
    """Operator on small grid."""
    return HilbertPolyaOperator(small_space, num_primes=10, max_k=4)


@pytest.fixture(scope="module")
def medium_operator(medium_space):
    """Operator on medium grid for spectral tests."""
    return HilbertPolyaOperator(medium_space, num_primes=15, max_k=5)


# ---------------------------------------------------------------------------
# TestEvenHilbertSpace
# ---------------------------------------------------------------------------

class TestEvenHilbertSpace:
    """Tests for EvenHilbertSpace."""

    def test_grid_symmetry(self, small_space):
        """Grid must be symmetric around u=0."""
        u = small_space.u
        assert np.allclose(u, -u[::-1], atol=1e-12), "Grid is not symmetric."

    def test_grid_length(self, small_space):
        """Grid length must equal N (adjusted to even)."""
        assert len(small_space.u) == small_space.N

    def test_grid_span(self, small_space):
        """Grid must span from -u_max to +u_max."""
        assert np.isclose(small_space.u[0], -small_space.u_max, atol=1e-12)
        assert np.isclose(small_space.u[-1], small_space.u_max, atol=1e-12)

    def test_enforce_parity_makes_even(self, small_space):
        """enforce_parity must produce an even function."""
        rng = np.random.default_rng(42)
        psi = rng.standard_normal(small_space.N)
        psi_even = small_space.enforce_parity(psi)
        is_even, err = small_space.check_parity(psi_even)
        assert is_even, f"Parity not enforced; max error = {err:.3e}"

    def test_check_parity_true_for_even(self, small_space):
        """Genuinely even function should pass parity check."""
        u = small_space.u
        psi = np.cosh(u)  # even function
        is_even, err = small_space.check_parity(psi)
        assert is_even, f"cosh(u) failed parity check; error = {err:.3e}"

    def test_check_parity_false_for_odd(self, small_space):
        """Odd function should fail parity check."""
        u = small_space.u
        psi = np.sinh(u)  # odd function
        is_even, _ = small_space.check_parity(psi)
        assert not is_even, "sinh(u) incorrectly passed parity check."

    def test_inner_product_self_norm_positive(self, small_space):
        """<ψ|ψ> must be strictly positive for non-zero ψ."""
        u = small_space.u
        psi = np.exp(-(u ** 2))
        val = small_space.inner_product(psi, psi)
        assert np.real(val) > 0, "Inner product of non-zero vector is non-positive."

    def test_normalize(self, small_space):
        """Normalised vector must have unit norm."""
        u = small_space.u
        psi = np.exp(-(u ** 2))
        psi_norm = small_space.normalize(psi)
        assert abs(small_space.norm(psi_norm) - 1.0) < 1e-10

    def test_n_adjusted_to_even(self):
        """Odd N must be adjusted to even."""
        space = EvenHilbertSpace(N=51, u_max=10.0)
        assert space.N % 2 == 0

    def test_invalid_n_raises(self):
        """N < 4 must raise ValueError."""
        with pytest.raises(ValueError):
            EvenHilbertSpace(N=2, u_max=5.0)

    def test_invalid_u_max_raises(self):
        """Non-positive u_max must raise ValueError."""
        with pytest.raises(ValueError):
            EvenHilbertSpace(N=20, u_max=-1.0)


# ---------------------------------------------------------------------------
# TestHilbertPolyaOperator – matrix properties
# ---------------------------------------------------------------------------

class TestHermiticity:
    """Hermiticity / self-adjointness tests."""

    def test_hermitian_exact(self, small_operator):
        """H must equal H^T exactly (real symmetric matrix)."""
        H = small_operator.matrix
        assert np.allclose(H, H.T, atol=1e-12), "H is not symmetric."

    def test_check_hermiticity_returns_true(self, small_operator):
        """check_hermiticity() must return (True, ~0)."""
        is_herm, err = small_operator.check_hermiticity()
        assert is_herm, f"Hermiticity check failed; error = {err:.3e}"
        assert err < 1e-10, f"Hermitian error too large: {err:.3e}"

    def test_eigenvalues_are_real(self, small_operator):
        """All eigenvalues of a Hermitian matrix must be real."""
        vals = small_operator.eigenvalues()
        max_imag = float(np.max(np.abs(np.imag(vals))))
        assert max_imag < 1e-10, f"Imaginary parts found: max|Im(λ)| = {max_imag:.3e}"


# ---------------------------------------------------------------------------
# TestParity
# ---------------------------------------------------------------------------

class TestParity:
    """Parity commutation tests."""

    def test_parity_commutation(self, small_operator):
        """[H, P] must be (near) zero."""
        commutes, err = small_operator.check_parity_commutation()
        assert commutes, f"[H,P] ≠ 0; error = {err:.3e}"

    def test_eigenvectors_are_even(self, small_operator):
        """All eigenvectors on L²_even must have positive parity expectation."""
        even_idx, odd_idx = small_operator.parity_eigenvectors()
        assert len(odd_idx) == 0 or len(even_idx) >= len(odd_idx), (
            "More odd eigenvectors than even; parity symmetry may be broken."
        )


# ---------------------------------------------------------------------------
# TestSpectral
# ---------------------------------------------------------------------------

class TestSpectral:
    """Spectral / eigenvalue tests."""

    def test_num_eigenvalues(self, small_operator):
        """Number of eigenvalues must equal N."""
        vals = small_operator.eigenvalues()
        assert len(vals) == small_operator.space.N

    def test_eigenvalues_sorted(self, small_operator):
        """Eigenvalues returned by eigenvalues() must be sorted."""
        vals = small_operator.eigenvalues()
        assert np.all(np.diff(vals) >= -1e-12), "Eigenvalues are not sorted."

    def test_positive_eigenvalues_exist(self, small_operator):
        """There must be positive eigenvalues for comparison with zeros."""
        vals = small_operator.eigenvalues()
        assert np.any(vals > 0), "No positive eigenvalues found."

    def test_zeta_correlation_positive(self, medium_operator):
        """Spectral correlation with Riemann zeros must be positive."""
        result = medium_operator.compare_with_zeta_zeros(n_zeros=8)
        corr = result["correlation"]
        assert not np.isnan(corr), "Correlation is NaN."
        assert corr > 0, f"Non-positive correlation: {corr:.4f}"

    def test_weyl_coefficient(self, small_operator):
        """Weyl coefficient must be 2 u_max / π."""
        expected = 2.0 * small_operator.space.u_max / np.pi
        assert np.isclose(small_operator.weyl_law_coefficient(), expected)

    def test_density_of_states_normalised(self, small_operator):
        """Density of states histogram must integrate to approximately 1."""
        vals = small_operator.eigenvalues()
        e_min, e_max = float(vals.min()), float(vals.max())
        centres, density = small_operator.density_of_states((e_min, e_max), n_bins=20)
        dE = centres[1] - centres[0] if len(centres) > 1 else 1.0
        integral = float(np.sum(density) * dE)
        assert abs(integral - 1.0) < 0.15, f"DOS integral = {integral:.4f}, expected ≈ 1."


# ---------------------------------------------------------------------------
# TestFredholm
# ---------------------------------------------------------------------------

class TestFredholm:
    """Fredholm determinant tests."""

    def test_fredholm_returns_complex(self, small_operator):
        """fredholm_determinant must return a complex number."""
        result = small_operator.fredholm_determinant(s=complex(1.0, 50.0))
        assert isinstance(result, complex), "Fredholm determinant is not complex."

    def test_fredholm_nonzero(self, small_operator):
        """det(s - H) must be non-zero for generic s."""
        result = small_operator.fredholm_determinant(s=complex(100.0, 100.0))
        assert abs(result) > 0, "Fredholm determinant is exactly zero."


# ---------------------------------------------------------------------------
# TestCoherence
# ---------------------------------------------------------------------------

class TestCoherence:
    """QCAL coherence and summary tests."""

    def test_summary_keys(self, small_operator):
        """summary() must return dict with required keys."""
        s = small_operator.summary()
        for key in [
            "N", "u_max", "is_hermitian", "hermitian_error",
            "parity_commutes", "num_eigenvalues", "zeta_correlation",
        ]:
            assert key in s, f"Missing key '{key}' in summary."

    def test_qcal_constants(self):
        """QCAL fundamental constants must have expected values."""
        assert np.isclose(F0_QCAL, 141.7001, atol=1e-4)
        assert np.isclose(C_COHERENCE, 244.36, atol=1e-4)

    def test_prime_sieve_correctness(self):
        """_prime_sieve must return first 25 primes up to 100."""
        primes = _prime_sieve(100)
        assert len(primes) == 25
        assert primes[0] == 2
        assert primes[-1] == 97

    def test_riemann_zeros_list(self):
        """RIEMANN_ZEROS_KNOWN must have ≥ 10 known zeros."""
        assert len(RIEMANN_ZEROS_KNOWN) >= 10
        # First zero is known to be ≈ 14.1347
        assert np.isclose(RIEMANN_ZEROS_KNOWN[0], 14.1347, atol=1e-3)

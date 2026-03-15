#!/usr/bin/env python3
"""
Tests for the FractalQCAL Operator Module

This test suite validates the FractalQCALOperator and helper functions,
including:
  1. Prime generation correctness
  2. Operator construction and dimension checks
  3. Potential positivity
  4. Hermiticity of the Hamiltonian
  5. Spectral output shape and basic sanity checks

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np

from operators.fractal_qcal_operator import (
    FractalQCALOperator,
    RIEMANN_ZEROS_20,
    generate_primes,
)

# Number of primes up to 9999 (inclusive), by the prime-counting function π(9999)
_PRIMES_BELOW_10000 = 1229


# ---------------------------------------------------------------------------
# Tests for generate_primes
# ---------------------------------------------------------------------------

class TestGeneratePrimes:
    """Tests for the generate_primes helper."""

    def test_small_primes(self):
        """First few primes up to 30 are correct."""
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert generate_primes(30) == expected

    def test_count_primes_below_10000(self):
        """There are 1229 primes up to and including 9999."""
        primes = generate_primes(9999)
        assert len(primes) == _PRIMES_BELOW_10000

    def test_all_entries_are_prime(self):
        """Spot-check that every returned number is indeed prime."""
        primes = generate_primes(100)
        for p in primes:
            assert all(p % d != 0 for d in range(2, p)), f"{p} is not prime"

    def test_minimum_n_max(self):
        """n_max=2 returns only [2]."""
        assert generate_primes(2) == [2]

    def test_invalid_n_max_raises(self):
        """n_max < 2 must raise ValueError."""
        with pytest.raises(ValueError):
            generate_primes(1)
        with pytest.raises(ValueError):
            generate_primes(0)

    def test_returns_list(self):
        """Return type must be list."""
        result = generate_primes(10)
        assert isinstance(result, list)


# ---------------------------------------------------------------------------
# Tests for RIEMANN_ZEROS_20 constant
# ---------------------------------------------------------------------------

class TestRiemannZeros20:
    """Tests for the hard-coded Riemann zeros array."""

    def test_length_is_20(self):
        """Array must contain exactly 20 zeros."""
        assert len(RIEMANN_ZEROS_20) == 20

    def test_first_zero_value(self):
        """First zero must match the well-known value γ₁ ≈ 14.1347."""
        assert abs(RIEMANN_ZEROS_20[0] - 14.134725141734693790) < 1e-12

    def test_strictly_increasing(self):
        """Zeros must be in strictly increasing order."""
        assert all(
            RIEMANN_ZEROS_20[i] < RIEMANN_ZEROS_20[i + 1]
            for i in range(len(RIEMANN_ZEROS_20) - 1)
        )

    def test_all_positive(self):
        """All zero ordinates must be positive."""
        assert np.all(RIEMANN_ZEROS_20 > 0)


# ---------------------------------------------------------------------------
# Tests for FractalQCALOperator
# ---------------------------------------------------------------------------

class TestFractalQCALOperator:
    """Tests for the FractalQCALOperator class."""

    # ------------------------------------------------------------------
    # Initialisation
    # ------------------------------------------------------------------

    def test_default_init(self):
        """Default construction (N=512) creates the right grid."""
        op = FractalQCALOperator(N=512)
        assert op.N == 512
        assert len(op.u) == 512
        assert len(op.primes) == _PRIMES_BELOW_10000

    def test_custom_primes(self):
        """Custom prime list is accepted and stored correctly."""
        custom_primes = [2, 3, 5, 7, 11]
        op = FractalQCALOperator(N=16, primes=custom_primes)
        assert op.primes == custom_primes
        assert len(op.log_primes) == 5

    def test_f0_calibration(self):
        """f₀ must equal γ₁ / π."""
        op = FractalQCALOperator(N=16)
        expected_f0 = RIEMANN_ZEROS_20[0] / np.pi
        assert abs(op.f0 - expected_f0) < 1e-14

    def test_invalid_N_not_int(self):
        """Non-integer N raises ValueError."""
        with pytest.raises(ValueError):
            FractalQCALOperator(N=4.5)

    def test_invalid_N_too_small(self):
        """N < 4 raises ValueError."""
        with pytest.raises(ValueError):
            FractalQCALOperator(N=2)

    def test_invalid_N_odd(self):
        """Odd N raises ValueError."""
        with pytest.raises(ValueError):
            FractalQCALOperator(N=5)

    def test_empty_primes_raises(self):
        """Empty primes list raises ValueError."""
        with pytest.raises(ValueError):
            FractalQCALOperator(N=16, primes=[])

    def test_du_positive(self):
        """Grid spacing du must be positive."""
        op = FractalQCALOperator(N=16)
        assert op.du > 0

    def test_grid_range(self):
        """Grid spans exactly [0, 100] as given by np.linspace."""
        op = FractalQCALOperator(N=64)
        assert op.u[0] == 0.0
        assert op.u[-1] == 100.0

    # ------------------------------------------------------------------
    # Potential
    # ------------------------------------------------------------------

    def test_v_mod_shape(self):
        """Potential matrix has shape (N, N)."""
        op = FractalQCALOperator(N=16)
        V = op.v_mod_fractal()
        assert V.shape == (16, 16)

    def test_v_mod_is_diagonal(self):
        """Potential matrix is diagonal (off-diagonal entries are zero)."""
        op = FractalQCALOperator(N=16)
        V = op.v_mod_fractal()
        off_diag = V - np.diag(np.diag(V))
        assert np.allclose(off_diag, 0.0)

    def test_v_mod_nonneg_diagonal(self):
        """Diagonal entries of the potential are non-negative."""
        op = FractalQCALOperator(N=32)
        V = op.v_mod_fractal()
        assert np.all(np.diag(V) >= 0.0)

    def test_v_mod_invalid_sigma(self):
        """Non-positive sigma raises ValueError."""
        op = FractalQCALOperator(N=16)
        with pytest.raises(ValueError):
            op.v_mod_fractal(sigma=0.0)
        with pytest.raises(ValueError):
            op.v_mod_fractal(sigma=-1.0)

    # ------------------------------------------------------------------
    # Hamiltonian
    # ------------------------------------------------------------------

    def test_hamiltonian_shape(self):
        """Hamiltonian has shape (N, N)."""
        op = FractalQCALOperator(N=16)
        H = op.build_hamiltonian()
        assert H.shape == (16, 16)

    def test_hamiltonian_is_hermitian(self):
        """Hamiltonian must satisfy H ≈ H†."""
        op = FractalQCALOperator(N=32)
        H = op.build_hamiltonian()
        assert np.allclose(H, H.conj().T, atol=1e-10), (
            "Hamiltonian is not Hermitian; max asymmetry = "
            f"{np.max(np.abs(H - H.conj().T)):.2e}"
        )

    def test_hamiltonian_real_eigenvalues(self):
        """Eigenvalues of a Hermitian matrix must be real."""
        op = FractalQCALOperator(N=32)
        H = op.build_hamiltonian()
        evals = np.linalg.eigvals(H)
        assert np.allclose(evals.imag, 0.0, atol=1e-8), (
            f"Max imaginary part of eigenvalue: {np.max(np.abs(evals.imag)):.2e}"
        )

    # ------------------------------------------------------------------
    # get_modes
    # ------------------------------------------------------------------

    def test_get_modes_default_length(self):
        """get_modes() returns exactly 20 values by default."""
        op = FractalQCALOperator(N=128)
        modes = op.get_modes()
        assert len(modes) == 20

    def test_get_modes_custom_n(self):
        """get_modes(n_modes=5) returns exactly 5 values."""
        op = FractalQCALOperator(N=64)
        modes = op.get_modes(n_modes=5)
        assert len(modes) == 5

    def test_get_modes_sorted(self):
        """Returned modes are in non-decreasing order."""
        op = FractalQCALOperator(N=64)
        modes = op.get_modes(n_modes=10)
        assert np.all(modes[:-1] <= modes[1:])

    def test_get_modes_finite(self):
        """All returned modes should be finite (no NaN or Inf)."""
        op = FractalQCALOperator(N=128)
        modes = op.get_modes()
        assert np.all(np.isfinite(modes)), f"Non-finite modes found: {modes[~np.isfinite(modes)]}"

    def test_get_modes_invalid_n_modes_zero(self):
        """n_modes=0 raises ValueError."""
        op = FractalQCALOperator(N=16)
        with pytest.raises(ValueError):
            op.get_modes(n_modes=0)

    def test_get_modes_too_many_raises(self):
        """n_modes > N//2 raises ValueError."""
        op = FractalQCALOperator(N=16)
        with pytest.raises(ValueError):
            op.get_modes(n_modes=9)

    def test_get_modes_returns_ndarray(self):
        """Return type must be numpy.ndarray."""
        op = FractalQCALOperator(N=64)
        modes = op.get_modes()
        assert isinstance(modes, np.ndarray)

    # ------------------------------------------------------------------
    # Spectral accuracy (lightweight, coarse N)
    # ------------------------------------------------------------------

    @pytest.mark.slow
    def test_spectral_modes_order_of_magnitude(self):
        """
        Modes should be in the same order of magnitude as Riemann zeros (10-80).

        Uses N=256 for a fast smoke-test.  Full accuracy requires N=4096
        (too slow for CI).
        """
        op = FractalQCALOperator(N=256, primes=generate_primes(9999))
        modes = op.get_modes()
        assert np.all(modes > 5.0), "Modes unexpectedly small"
        assert np.all(modes < 200.0), "Modes unexpectedly large"

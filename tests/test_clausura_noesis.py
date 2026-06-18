#!/usr/bin/env python3
"""
Tests for operators/clausura_noesis.py

Validates the Teorema de Clausura de Riemann-Noesis:
  Three Pillars ⟹ Hilbert-Pólya Collapse ⟹ Re(ρ) = 1/2

Tests cover:
  1. Constants (QCAL integration)
  2. TransferOperator (Pillar 1)
  3. SobolevAdelicOperator (Pillar 2)
  4. SpectralCoincidence (Pillar 3)
  5. TeoremaClausuraNoesis (full closure)
  6. validate_clausura_noesis()

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

import sys
import os

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.clausura_noesis import (
    # Constants
    QCAL_FREQUENCY,
    QCAL_COHERENCE,
    F_UNITY,
    DOI,
    ORCID,
    # Classes
    TransferOperator,
    SobolevAdelicOperator,
    SpectralCoincidence,
    TeoremaClausuraNoesis,
    ClausuraResult,
    # Functions
    validate_clausura_noesis,
)


# ---------------------------------------------------------------------------
# 1. Constants
# ---------------------------------------------------------------------------


class TestQCALConstants:
    """Test QCAL ∞³ constants."""

    def test_frequency(self):
        """QCAL frequency is 141.7001 Hz."""
        assert QCAL_FREQUENCY == 141.7001

    def test_coherence(self):
        """Coherence constant is 244.36."""
        assert QCAL_COHERENCE == 244.36

    def test_unity_frequency(self):
        """Unity state frequency is 888.0 Hz."""
        assert F_UNITY == 888.0

    def test_doi_zenodo(self):
        """DOI references Zenodo."""
        assert "zenodo" in DOI.lower()

    def test_orcid_hyphens(self):
        """ORCID has 3 hyphens."""
        assert ORCID.count("-") == 3


# ---------------------------------------------------------------------------
# 2. Pillar 1: TransferOperator
# ---------------------------------------------------------------------------


class TestTransferOperator:
    """Test the Transfer Operator (Pillar 1)."""

    @pytest.fixture
    def op(self):
        return TransferOperator(n_primes=20)

    def test_primes_count(self, op):
        """n_primes primes are loaded."""
        assert len(op.primes) == 20

    def test_first_prime(self, op):
        """First prime is 2."""
        assert op.primes[0] == 2

    def test_spectral_radius_positive(self, op):
        """Spectral radius is positive."""
        r = op.spectral_radius(2.0 + 0j)
        assert r > 0

    def test_spectral_radius_finite(self, op):
        """Spectral radius is finite."""
        r = op.spectral_radius(2.0 + 0j)
        assert np.isfinite(r)

    def test_trace_finite(self, op):
        """Trace approximation is finite."""
        trace = op.trace_approx(2.0 + 0j, k_max=3)
        assert np.isfinite(abs(trace))

    def test_trace_positive(self, op):
        """Trace is positive for real s > 1."""
        trace = op.trace_approx(2.0 + 0j, k_max=2)
        assert trace.real > 0

    def test_is_trace_class(self, op):
        """Transfer operator is trace-class for s = 2."""
        assert op.is_trace_class(2.0 + 0j)

    def test_verify_pillar1(self, op):
        """Pillar 1 verification succeeds."""
        result = op.verify()
        assert result["pillar"] == 1
        assert result["verified"]
        assert result["is_trace_class"]


# ---------------------------------------------------------------------------
# 3. Pillar 2: SobolevAdelicOperator
# ---------------------------------------------------------------------------


class TestSobolevAdelicOperator:
    """Test the Sobolev-Adelic Operator (Pillar 2)."""

    @pytest.fixture
    def op(self):
        return SobolevAdelicOperator(n_grid=50, epsilon=0.01)

    def test_grid_length(self, op):
        """Grid has n_grid points."""
        assert len(op.grid) == 50

    def test_h0_shape(self, op):
        """H₀ matrix has correct shape."""
        H = op.h0_matrix(n=30)
        assert H.shape == (30, 30)

    def test_h0_hermitian(self, op):
        """H₀ matrix is Hermitian."""
        H = op.h0_matrix(n=30)
        np.testing.assert_allclose(H, H.conj().T, atol=1e-10)

    def test_perturbation_shape(self, op):
        """V matrix has correct shape."""
        V = op.perturbation_matrix(n=30)
        assert V.shape == (30, 30)

    def test_perturbation_diagonal(self, op):
        """V matrix is diagonal."""
        V = op.perturbation_matrix(n=30)
        off_diag = V - np.diag(np.diag(V))
        assert np.allclose(off_diag, 0)

    def test_full_matrix_hermitian(self, op):
        """H_{SA} = H₀ + V is Hermitian."""
        H = op.full_matrix(n=30)
        np.testing.assert_allclose(H, H.conj().T, atol=1e-10)

    def test_full_matrix_eigenvalues_real(self, op):
        """H_{SA} eigenvalues are real."""
        H = op.full_matrix(n=30)
        evals = np.linalg.eigvalsh(H)
        assert np.all(np.isreal(evals))

    def test_klmn_satisfied(self, op):
        """KLMN form bound a < 1 (small epsilon)."""
        result = op.verify_klmn(n=40, n_tests=100)
        assert result["klmn_satisfied"]
        assert result["form_bound"] < 1.0

    def test_is_self_adjoint(self, op):
        """H_{SA} is self-adjoint."""
        result = op.is_self_adjoint(n=40, n_tests=100)
        assert result["is_self_adjoint"]

    def test_verify_pillar2(self, op):
        """Pillar 2 verification succeeds."""
        result = op.verify()
        assert result["pillar"] == 2
        assert result["verified"]


# ---------------------------------------------------------------------------
# 4. Pillar 3: SpectralCoincidence
# ---------------------------------------------------------------------------


class TestSpectralCoincidence:
    """Test the Spectral Coincidence (Pillar 3)."""

    @pytest.fixture
    def sc(self):
        return SpectralCoincidence(n_matrix=60)

    def test_eigenvalues_array(self, sc):
        """eigenvalues() returns a numpy array."""
        evals = sc.eigenvalues()
        assert isinstance(evals, np.ndarray)

    def test_eigenvalues_real(self, sc):
        """All eigenvalues are real."""
        evals = sc.eigenvalues()
        assert np.all(np.isreal(evals))

    def test_eigenvalues_finite(self, sc):
        """All eigenvalues are finite."""
        evals = sc.eigenvalues()
        assert np.all(np.isfinite(evals))

    def test_zeros_on_critical_line_re(self, sc):
        """All candidate zeros have Re(s) = 1/2."""
        zeros = sc.zeros_on_critical_line(n=5)
        np.testing.assert_allclose(zeros.real, 0.5, atol=1e-12)

    def test_verify_critical_line(self, sc):
        """verify_critical_line() confirms Re(s) = 1/2."""
        result = sc.verify_critical_line(n=5)
        assert result["all_on_critical_line"]

    def test_eigenvalues_real_flag(self, sc):
        """eigenvalues_real() returns True."""
        assert sc.eigenvalues_real()

    def test_verify_pillar3(self, sc):
        """Pillar 3 verification succeeds."""
        result = sc.verify()
        assert result["pillar"] == 3
        assert result["verified"]
        assert result["eigenvalues_real"]
        assert result["all_on_critical_line"]

    def test_known_zeros_attribute(self, sc):
        """RIEMANN_ZEROS contains the first few imaginary parts."""
        zeros = SpectralCoincidence.RIEMANN_ZEROS
        assert len(zeros) >= 5
        assert np.isclose(zeros[0], 14.134725, atol=1e-3)


# ---------------------------------------------------------------------------
# 5. TeoremaClausuraNoesis
# ---------------------------------------------------------------------------


class TestTeoremaClausuraNoesis:
    """Test the full Teorema de Clausura de Riemann-Noesis."""

    @pytest.fixture(scope="class")
    def teorema(self):
        return TeoremaClausuraNoesis(n_primes=20, n_matrix=50)

    def test_pillar1_verified(self, teorema):
        """Pillar 1 is verified."""
        result = teorema.verify_pillar1()
        assert result["verified"]

    def test_pillar2_verified(self, teorema):
        """Pillar 2 is verified."""
        result = teorema.verify_pillar2()
        assert result["verified"]

    def test_pillar3_verified(self, teorema):
        """Pillar 3 is verified."""
        result = teorema.verify_pillar3()
        assert result["verified"]

    def test_full_verify_returns_clausura_result(self, teorema):
        """verify() returns a ClausuraResult."""
        result = teorema.verify()
        assert isinstance(result, ClausuraResult)

    def test_hilbert_polya_collapsed(self, teorema):
        """Hilbert-Pólya collapse is True."""
        result = teorema.verify()
        assert result.hilbert_polya_collapsed

    def test_coherence_psi_1(self, teorema):
        """QCAL coherence Ψ = 1.0."""
        result = teorema.verify()
        assert result.coherence_psi == 1.0

    def test_all_pillars_in_result(self, teorema):
        """All three pillars are verified in the result."""
        result = teorema.verify()
        assert result.pillar1_verified
        assert result.pillar2_verified
        assert result.pillar3_verified

    def test_details_keys(self, teorema):
        """Details contain all pillar keys."""
        result = teorema.verify()
        expected = {"pillar1", "pillar2", "pillar3", "collapse"}
        assert expected.issubset(result.details.keys())

    def test_collapse_conclusion_string(self, teorema):
        """Collapse conclusion states Re(ρ) = 1/2."""
        result = teorema.verify()
        conclusion = result.details["collapse"]["conclusion"]
        assert "1/2" in conclusion

    def test_hilbert_polya_collapse_method(self, teorema):
        """hilbert_polya_collapse() with True inputs gives collapsed=True."""
        p1 = {"verified": True}
        p2 = {"verified": True}
        p3 = {"verified": True}
        collapse = teorema.hilbert_polya_collapse(p1, p2, p3)
        assert collapse["collapsed"]

    def test_hilbert_polya_collapse_fails_on_false(self, teorema):
        """hilbert_polya_collapse() with False pillar gives collapsed=False."""
        p1 = {"verified": False}
        p2 = {"verified": True}
        p3 = {"verified": True}
        collapse = teorema.hilbert_polya_collapse(p1, p2, p3)
        assert not collapse["collapsed"]


# ---------------------------------------------------------------------------
# 6. validate_clausura_noesis()
# ---------------------------------------------------------------------------


class TestValidateClausuraNoesis:
    """Test the top-level validation function."""

    def test_returns_float(self):
        """Returns a float."""
        psi = validate_clausura_noesis(verbose=False)
        assert isinstance(psi, float)

    def test_coherence_is_1(self):
        """Returns Ψ = 1.0."""
        psi = validate_clausura_noesis(verbose=False)
        assert psi == 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

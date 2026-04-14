#!/usr/bin/env python3
"""
Tests for Berry-Keating Symbiotic Operators
============================================

Validates both operators introduced by the QCAL symbiotic framework:

*   :class:`PAdicBerryKeatingOperator` —
    :math:`\\hat{S}\\psi(x) = \\Phi \\cdot \\int_{\\mathbb{Q}_p} \\chi_p(p^n x\\xi)\\psi(\\xi)\\,d\\mu_p(\\xi)`

*   :class:`SymbioticHamiltonian` —
    :math:`\\hat{H}_{symbio} = \\tfrac{1}{2}(x\\hat{p}+\\hat{p}x) + f_0`

Test coverage
-------------
1.  Module constants (Φ, f₀, C_QCAL)
2.  :class:`PAdicBerryKeatingOperator`
    a.  Initialisation
    b.  Matrix shape and dtype
    c.  Unitarity up to Φ factor
    d.  All singular values equal Φ/p^K
    e.  Character orthogonality
    f.  ``apply`` maps correct shape
    g.  Invalid prime raises ValueError
3.  :class:`SymbioticHamiltonian`
    a.  Initialisation
    b.  Hermitian matrix
    c.  Real eigenvalues
    d.  f₀ frequency shift present
    e.  Berry-Keating kinetic structure
    f.  Commutation relations
    g.  Spectrum sorted ascending
4.  Integration tests
    a.  BK structure preserved when f₀ = 0
    b.  Ŝ ⊗ I + I ⊗ Ĥ spectral coherence
5.  Full validation function

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import pytest
import numpy as np

from operators.berry_keating_symbiotic import (
    # Constants
    F0,
    C_QCAL,
    PHI,
    P_DEFAULT,
    K_DEFAULT,
    N_SYMB,
    # Classes
    PAdicBerryKeatingOperator,
    SymbioticHamiltonian,
    BerryKeatingSymbioticSystem,
    # Functions
    validate_berry_keating_symbiotic,
    _is_prime,
)


# ══════════════════════════════════════════════════════════════════════════════
#  Class 1 — Module constants
# ══════════════════════════════════════════════════════════════════════════════

class TestConstants:
    """Test fundamental QCAL constants exported by the module."""

    def test_f0_value(self):
        """Base frequency must be 141.7001 Hz (QCAL master frequency)."""
        assert abs(F0 - 141.7001) < 1e-4

    def test_c_qcal_value(self):
        """QCAL coherence constant must be 244.36."""
        assert abs(C_QCAL - 244.36) < 0.01

    def test_phi_value(self):
        """Golden ratio Φ must satisfy Φ² = Φ + 1."""
        assert abs(PHI**2 - PHI - 1) < 1e-12

    def test_phi_numerical(self):
        """Φ ≈ 1.6180339887."""
        assert abs(PHI - 1.6180339887) < 1e-9

    def test_p_default_is_prime(self):
        """Default prime P_DEFAULT must be a prime number."""
        assert _is_prime(P_DEFAULT)

    def test_k_default_positive(self):
        """Default depth K_DEFAULT must be positive."""
        assert K_DEFAULT >= 1


# ══════════════════════════════════════════════════════════════════════════════
#  Class 2 — PAdicBerryKeatingOperator
# ══════════════════════════════════════════════════════════════════════════════

class TestPAdicBerryKeatingOperator:
    """Tests for the p-adic Ŝ operator."""

    # ── initialisation ────────────────────────────────────────────────────────

    def test_default_initialization(self):
        """Default constructor must succeed with valid attributes."""
        op = PAdicBerryKeatingOperator()
        assert op.p == P_DEFAULT
        assert op.K == K_DEFAULT
        assert op.dim == P_DEFAULT ** K_DEFAULT
        assert isinstance(op.S, np.ndarray)

    def test_custom_parameters(self):
        """Constructor must accept custom p, K, n, phi."""
        op = PAdicBerryKeatingOperator(p=3, K=2, n=1, phi=1.5)
        assert op.p == 3
        assert op.K == 2
        assert op.dim == 9
        assert op.phi == 1.5

    def test_matrix_shape(self):
        """Operator matrix must be square with side p^K."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        assert op.S.shape == (8, 8)

    def test_matrix_dtype_complex(self):
        """Operator matrix must be complex."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        assert np.iscomplexobj(op.S)

    def test_invalid_prime_raises(self):
        """Composite number must raise ValueError."""
        with pytest.raises(ValueError):
            PAdicBerryKeatingOperator(p=4, K=2)

    def test_one_is_not_prime(self):
        """p=1 must raise ValueError."""
        with pytest.raises(ValueError):
            PAdicBerryKeatingOperator(p=1, K=2)

    def test_invalid_K_negative_raises(self):
        """Negative K must raise ValueError."""
        with pytest.raises(ValueError):
            PAdicBerryKeatingOperator(p=2, K=-1)

    def test_invalid_K_bool_raises(self):
        """Boolean K must raise ValueError."""
        with pytest.raises(ValueError):
            PAdicBerryKeatingOperator(p=2, K=True)

    def test_invalid_n_float_raises(self):
        """Float n must raise ValueError."""
        with pytest.raises(ValueError):
            PAdicBerryKeatingOperator(p=2, K=3, n=1.5)  # type: ignore

    def test_n_clamped_below_zero(self):
        """n < 0 is clamped to 0; operator still builds."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=-5)
        assert op.n == 0

    def test_n_clamped_above_K(self):
        """n > K is clamped to K; operator still builds."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=10)
        assert op.n == 3

    # ── unitarity ────────────────────────────────────────────────────────────

    def test_unitarity_up_to_phi(self):
        r"""S†S should have block structure: Φ²/p^K on connected entries."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        result = op.verify_unitarity_up_to_phi()
        assert result["verified"], (
            f"max_block_error={result['max_block_error']:.2e}"
        )

    def test_unitarity_prime_3(self):
        """Block-structure check for p=3, K=2."""
        op = PAdicBerryKeatingOperator(p=3, K=2, n=1)
        result = op.verify_unitarity_up_to_phi()
        assert result["verified"]

    def test_unitarity_different_n(self):
        """Block-structure must hold for various n values."""
        for n in [0, 1, 2]:
            op = PAdicBerryKeatingOperator(p=2, K=3, n=n)
            result = op.verify_unitarity_up_to_phi()
            assert result["verified"], f"Failed for n={n}"

    def test_unitarity_n0_is_diagonal(self):
        """For n=0 the block structure reduces to diagonal (standard DFT)."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=0)
        result = op.verify_unitarity_up_to_phi()
        assert result["verified"]
        # For n=0, period = p^K, so all blocks have size 1 (diagonal)
        S = op.S
        SdS = S.conj().T @ S
        off_diag = SdS - np.diag(np.diag(SdS))
        assert float(np.max(np.abs(off_diag))) < 1e-10

    # ── singular values ───────────────────────────────────────────────────────

    def test_golden_ratio_scaling(self):
        r"""Non-zero SVs must equal Φ/√(p^{K-n})."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        result = op.verify_golden_ratio_scaling()
        assert result["verified"], (
            f"max_sv_error={result['max_sv_error']:.2e}"
        )

    def test_singular_values_count(self):
        """Number of singular values must equal dim."""
        op = PAdicBerryKeatingOperator(p=2, K=4, n=1)
        sv = op.singular_values()
        assert len(sv) == op.dim

    def test_singular_values_nonzero_count(self):
        """Number of non-zero SVs must equal p^{K-n}."""
        for n in [0, 1, 2]:
            op = PAdicBerryKeatingOperator(p=2, K=3, n=n)
            sv = op.singular_values()
            n_nonzero = np.sum(sv > 1e-10)
            expected = 2 ** (3 - n)
            assert n_nonzero == expected, f"n={n}: got {n_nonzero}, expected {expected}"

    def test_singular_values_nonzero_all_equal(self):
        """All non-zero SVs should be equal to Φ/√(p^{K-n})."""
        op = PAdicBerryKeatingOperator(p=3, K=2, n=1)
        sv = op.singular_values()
        sv_sorted = np.sort(sv)[::-1]
        n_nonzero = 3 ** (2 - 1)  # p^{K-n} = 3
        expected_sv = PHI / np.sqrt(float(n_nonzero))
        assert np.allclose(sv_sorted[:n_nonzero], expected_sv, atol=1e-10)

    def test_singular_value_n0(self):
        """For n=0, all SVs equal Φ/√dim (standard DFT)."""
        op = PAdicBerryKeatingOperator(p=2, K=4, n=0)
        sv = op.singular_values()
        expected = PHI / np.sqrt(float(op.dim))
        assert np.allclose(sv, expected, atol=1e-10)

    # ── character orthogonality ───────────────────────────────────────────────

    def test_padic_character_orthogonality(self):
        """P-adic characters must form an orthonormal system."""
        op = PAdicBerryKeatingOperator(p=2, K=4, n=1)
        result = op.verify_padic_character_orthogonality()
        assert result["verified"], (
            f"max_ortho_error={result['max_ortho_error']:.2e}"
        )

    def test_character_orthogonality_prime_3(self):
        """Character orthogonality for p=3."""
        op = PAdicBerryKeatingOperator(p=3, K=2, n=1)
        result = op.verify_padic_character_orthogonality()
        assert result["verified"]

    # ── apply ────────────────────────────────────────────────────────────────

    def test_apply_shape(self):
        """apply() must return a vector of same length."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        psi = np.ones(op.dim, dtype=complex)
        result = op.apply(psi)
        assert result.shape == (op.dim,)

    def test_apply_wrong_shape_raises(self):
        """apply() must raise ValueError for wrong input shape."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        with pytest.raises(ValueError):
            op.apply(np.ones(op.dim + 1))

    def test_apply_linearity(self):
        """apply() must be linear: S(αψ + βφ) = αS(ψ) + βS(φ)."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        np.random.seed(42)
        psi = np.random.randn(op.dim) + 1j * np.random.randn(op.dim)
        phi = np.random.randn(op.dim) + 1j * np.random.randn(op.dim)
        alpha, beta = 2.0 + 1j, -1.5 + 0.5j
        lhs = op.apply(alpha * psi + beta * phi)
        rhs = alpha * op.apply(psi) + beta * op.apply(phi)
        assert np.allclose(lhs, rhs, atol=1e-12)

    def test_apply_norm_preservation(self):
        r"""For n=0, ‖Sψ‖ = (Φ/√dim) · ‖ψ‖ (all SVs equal Φ/√dim)."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=0)  # n=0: full-rank DFT
        np.random.seed(0)
        psi = np.random.randn(op.dim) + 1j * np.random.randn(op.dim)
        psi /= np.linalg.norm(psi)
        s_psi = op.apply(psi)
        # For n=0 all SVs = Φ/√dim → ||S psi|| = Φ/√dim for any unit psi
        expected_norm = PHI / np.sqrt(float(op.dim))
        assert abs(np.linalg.norm(s_psi) - expected_norm) < 1e-10


# ══════════════════════════════════════════════════════════════════════════════
#  Class 3 — SymbioticHamiltonian
# ══════════════════════════════════════════════════════════════════════════════

class TestSymbioticHamiltonian:
    """Tests for Ĥ_symbio = ½(xp̂ + p̂x) + f₀."""

    # ── initialisation ────────────────────────────────────────────────────────

    def test_default_initialization(self):
        """Default constructor must set correct attributes."""
        h = SymbioticHamiltonian()
        assert h.N == N_SYMB
        assert abs(h.f0 - F0) < 1e-6

    def test_custom_parameters(self):
        """Constructor must accept custom N, L, f0."""
        h = SymbioticHamiltonian(N=50, L=5.0, f0=100.0)
        assert h.N == 50
        assert h.L == 5.0
        assert h.f0 == 100.0

    def test_invalid_N_small_raises(self):
        """N < 4 must raise ValueError."""
        with pytest.raises(ValueError):
            SymbioticHamiltonian(N=3)

    def test_invalid_N_zero_raises(self):
        """N=0 must raise ValueError."""
        with pytest.raises(ValueError):
            SymbioticHamiltonian(N=0)

    def test_invalid_L_zero_raises(self):
        """L=0 must raise ValueError."""
        with pytest.raises(ValueError):
            SymbioticHamiltonian(N=50, L=0.0)

    def test_invalid_L_negative_raises(self):
        """Negative L must raise ValueError."""
        with pytest.raises(ValueError):
            SymbioticHamiltonian(N=50, L=-5.0)

    def test_grid_shape(self):
        """t and x grids must have length N."""
        h = SymbioticHamiltonian(N=100)
        assert len(h.t) == 100
        assert len(h.x) == 100

    def test_x_positive(self):
        """Physical grid x = exp(t) must be strictly positive."""
        h = SymbioticHamiltonian(N=100)
        assert np.all(h.x > 0)

    def test_matrix_shape(self):
        """Hamiltonian matrix must be square (N × N)."""
        h = SymbioticHamiltonian(N=80)
        assert h.H.shape == (80, 80)

    # ── Hermiticity ───────────────────────────────────────────────────────────

    def test_matrix_symmetric(self):
        """Operator matrix must be real and symmetric."""
        h = SymbioticHamiltonian(N=100)
        err = np.max(np.abs(h.H - h.H.T))
        assert err < 1e-10

    def test_matrix_real(self):
        """Operator matrix must be real-valued."""
        h = SymbioticHamiltonian(N=100)
        assert h.H.dtype.kind == "f"

    def test_self_adjointness(self):
        """verify_self_adjointness() must pass."""
        h = SymbioticHamiltonian(N=100)
        result = h.verify_self_adjointness()
        assert result["verified"], (
            f"hermiticity_error={result['hermiticity_error']:.2e}"
        )

    # ── spectrum ─────────────────────────────────────────────────────────────

    def test_spectrum_reality(self):
        """All eigenvalues must be real."""
        h = SymbioticHamiltonian(N=80)
        result = h.verify_spectrum_reality()
        assert result["verified"]

    def test_eigenvalues_count(self):
        """Number of eigenvalues must equal N."""
        h = SymbioticHamiltonian(N=80)
        ev, _ = h.get_spectrum()
        assert len(ev) == 80

    def test_eigenvalues_sorted(self):
        """Eigenvalues from get_spectrum() must be sorted ascending."""
        h = SymbioticHamiltonian(N=80)
        ev, _ = h.get_spectrum()
        assert np.all(np.diff(ev) >= -1e-10)

    def test_eigenvectors_orthonormal(self):
        """Eigenvectors must form an orthonormal basis."""
        h = SymbioticHamiltonian(N=50)
        _, vecs = h.get_spectrum()
        gram = vecs.T @ vecs
        err = np.max(np.abs(gram - np.eye(50)))
        assert err < 1e-10

    # ── frequency shift ───────────────────────────────────────────────────────

    def test_frequency_shift_present(self):
        r"""Algebraic shift f₀·I must be present in the diagonal."""
        h = SymbioticHamiltonian(N=100)
        result = h.verify_frequency_shift()
        assert result["verified"], (
            f"max_diagonal_shift_error={result['max_diagonal_shift_error']:.2e}"
        )

    def test_frequency_shift_monotone(self):
        """Increasing f₀ must shift all eigenvalues up by the same amount."""
        h1 = SymbioticHamiltonian(N=50, f0=0.0)
        h2 = SymbioticHamiltonian(N=50, f0=100.0)
        ev1, _ = h1.get_spectrum()
        ev2, _ = h2.get_spectrum()
        shift = ev2 - ev1
        # All eigenvalues should be shifted by exactly 100
        assert np.allclose(shift, 100.0, atol=1e-8)

    def test_f0_shift_is_f0(self):
        """The shift in spectrum between f0=0 and f0=F0 must equal F0."""
        h0 = SymbioticHamiltonian(N=60, f0=0.0)
        hf = SymbioticHamiltonian(N=60, f0=F0)
        ev0, _ = h0.get_spectrum()
        evf, _ = hf.get_spectrum()
        assert np.allclose(evf - ev0, F0, atol=1e-8)

    # ── BK structure ──────────────────────────────────────────────────────────

    def test_bk_kinetic_structure(self):
        """Diagonal (kinetic part) must reproduce j + 1/2."""
        h = SymbioticHamiltonian(N=100)
        result = h.verify_berry_keating_structure()
        assert result["verified"], (
            f"max_diagonal_error={result['max_diagonal_error']:.2e}"
        )

    def test_bk_diagonal_values(self):
        """H[j,j] - f0 must equal j + 0.5 for all j."""
        N = 80
        h = SymbioticHamiltonian(N=N)
        diag_kin = np.diag(h.H) - h.f0
        expected = np.arange(N) + 0.5
        assert np.allclose(diag_kin, expected, atol=1e-10)

    # ── commutation relations ────────────────────────────────────────────────

    def test_commutation_relations(self):
        r"""Discrete [X, P_real] off-diagonal entries should have magnitude 1/2."""
        h = SymbioticHamiltonian(N=100)
        result = h.verify_commutation_relations()
        assert result["verified"], (
            f"max_off_diag_error={result['max_off_diag_error']:.4f}"
        )


# ══════════════════════════════════════════════════════════════════════════════
#  Class 4 — Integration tests
# ══════════════════════════════════════════════════════════════════════════════

class TestIntegration:
    """Integration tests coupling both operators."""

    def test_zero_f0_gives_pure_bk(self):
        """With f₀=0, Ĥ_symbio reduces to pure Berry-Keating kinetic part."""
        h = SymbioticHamiltonian(N=60, f0=0.0)
        diag = np.diag(h.H)
        expected = np.arange(60) + 0.5
        assert np.allclose(diag, expected, atol=1e-10)

    def test_combined_system_spectral_coherence(self):
        """BerryKeatingSymbioticSystem spectral coherence must be verified."""
        symbio_system = BerryKeatingSymbioticSystem(p=2, K=3, n=1, N_symb=30, L=5.0)
        result = symbio_system.spectral_coherence()
        assert result["verified"]

    def test_s_operator_and_h_symbio_compatible_dimensions(self):
        """Ŝ and Ĥ_symbio can be used in the same pipeline."""
        s = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        h = SymbioticHamiltonian(N=50)
        # Both should build successfully
        assert s.S.shape[0] == s.dim
        assert h.H.shape == (50, 50)

    def test_phi_scaling_propagates(self):
        """Doubling Φ must double all non-zero singular values of Ŝ."""
        op1 = PAdicBerryKeatingOperator(p=2, K=3, n=1, phi=PHI)
        op2 = PAdicBerryKeatingOperator(p=2, K=3, n=1, phi=2.0 * PHI)
        sv1 = op1.singular_values()
        sv2 = op2.singular_values()
        # Both should have same structure (zeros and non-zeros at same positions)
        assert np.allclose(sv2, 2.0 * sv1, atol=1e-12)

    def test_s_applied_to_delta_state(self):
        """Ŝ applied to δ₀ gives the first column of S."""
        op = PAdicBerryKeatingOperator(p=2, K=3, n=1)
        delta = np.zeros(op.dim)
        delta[0] = 1.0
        result = op.apply(delta)
        np.testing.assert_allclose(result, op.S[:, 0], atol=1e-14)

    def test_h_symbio_positive_definite_large_f0(self):
        """With large f₀, Ĥ_symbio must be positive definite."""
        h = SymbioticHamiltonian(N=50, f0=1e4)
        ev, _ = h.get_spectrum()
        assert np.all(ev > 0)


# ══════════════════════════════════════════════════════════════════════════════
#  Class 5 — Full validation function
# ══════════════════════════════════════════════════════════════════════════════

class TestValidation:
    """Tests for the top-level validate_berry_keating_symbiotic() function."""

    def test_validation_runs(self):
        """Validation function must run without error."""
        results = validate_berry_keating_symbiotic(
            p=2, K=3, n=1, N_symb=50, L=10.0, save_certificate=False
        )
        assert isinstance(results, dict)

    def test_validation_all_verified(self):
        """All verification steps must pass."""
        results = validate_berry_keating_symbiotic(
            p=2, K=3, n=1, N_symb=50, L=10.0, save_certificate=False
        )
        assert results["all_verified"], (
            f"Failed methods: "
            + ", ".join(
                k for k, v in results["methods"].items()
                if not v.get("verified", False)
            )
        )

    def test_validation_returns_qcal_constants(self):
        """Results must contain QCAL constants."""
        results = validate_berry_keating_symbiotic(
            p=2, K=3, n=1, N_symb=50, L=10.0, save_certificate=False
        )
        assert "qcal_constants" in results
        assert abs(results["qcal_constants"]["F0"] - F0) < 1e-6
        assert abs(results["qcal_constants"]["PHI"] - PHI) < 1e-12

    def test_validation_returns_qcal_signature(self):
        """Results must carry the QCAL signature."""
        results = validate_berry_keating_symbiotic(
            p=2, K=3, n=1, N_symb=50, L=10.0, save_certificate=False
        )
        assert results.get("qcal_signature") == "∴𓂀Ω∞³Φ"

    def test_certificate_saved(self, tmp_path, monkeypatch):
        """Certificate JSON must be written when save_certificate=True."""
        monkeypatch.chdir(tmp_path)
        (tmp_path / "data").mkdir()
        results = validate_berry_keating_symbiotic(
            p=2, K=3, n=1, N_symb=30, L=5.0, save_certificate=True
        )
        cert = tmp_path / "data" / "berry_keating_symbiotic_certificate.json"
        assert cert.exists()
        import json
        with open(cert) as fh:
            cert_data = json.load(fh)
        assert "all_verified" in cert_data


# ══════════════════════════════════════════════════════════════════════════════
#  Utility tests
# ══════════════════════════════════════════════════════════════════════════════

class TestUtility:
    """Tests for internal helper functions."""

    def test_is_prime_small_primes(self):
        """_is_prime must recognise small primes."""
        for p in [2, 3, 5, 7, 11, 13]:
            assert _is_prime(p), f"Expected {p} to be prime"

    def test_is_prime_composites(self):
        """_is_prime must reject composites."""
        for c in [1, 4, 6, 8, 9, 10, 15]:
            assert not _is_prime(c), f"Expected {c} to be composite"

    def test_is_prime_large_prime(self):
        """_is_prime must recognise a larger prime."""
        assert _is_prime(97)
        assert not _is_prime(100)

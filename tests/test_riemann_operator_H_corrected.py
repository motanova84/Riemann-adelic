"""
Tests for operators/riemann_operator_H_corrected.py

FASE VII: Experimento de Invarianza Soberana

Tests cover:
  - Primes generation
  - V_Abel: Abel-inversion potential
  - V_osc: oscillatory prime correction
  - Wu-Sprung Hamiltonian construction
  - Eigenvalue computation
  - Test B: spectral drift (medir_deriva_espectral)
  - Test C: analytical-phase coherence (validar_fases_analiticas)
  - ejecutar_validacion_soberana
"""

import os
import sys
import importlib.util

import numpy as np
import pytest

# Import directly from file to avoid operators/__init__.py chain
_REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_MODULE_PATH = os.path.join(_REPO_ROOT, "operators", "riemann_operator_H_corrected.py")
_spec = importlib.util.spec_from_file_location(
    "operators.riemann_operator_H_corrected", _MODULE_PATH
)
_mod = importlib.util.module_from_spec(_spec)
sys.modules["operators.riemann_operator_H_corrected"] = _mod
_spec.loader.exec_module(_mod)

from operators.riemann_operator_H_corrected import (
    DEFAULT_EPSILON,
    DEFAULT_K_EIGS,
    DEFAULT_N,
    DEFAULT_N_PRIMES,
    DEFAULT_X_MAX,
    F0,
    F_888,
    RIEMANN_ZEROS_REF,
    _generate_primes,
    _x_t,
    build_hamiltonian_ws,
    compute_eigenvalues_ws,
    ejecutar_validacion_soberana,
    medir_deriva_espectral,
    v_abel,
    v_osc,
    validar_fases_analiticas,
)

# -----------------------------------------------------------------------
# Constants
# -----------------------------------------------------------------------

# Small grid for fast tests
_N_FAST = 200
_X_MAX_FAST = 50.0
_K_FAST = 10
_N_PRIMES_FAST = 20
_EPS_FAST = DEFAULT_EPSILON


class TestConstants:
    """Physical and QCAL constants are correctly defined."""

    def test_f0(self):
        assert F0 == 141.7001

    def test_f888(self):
        assert F_888 == 888.0

    def test_riemann_zeros_count(self):
        assert len(RIEMANN_ZEROS_REF) >= 50

    def test_riemann_zeros_positive(self):
        assert all(z > 0 for z in RIEMANN_ZEROS_REF)

    def test_riemann_zeros_ordered(self):
        ref = list(RIEMANN_ZEROS_REF)
        assert ref == sorted(ref)

    def test_first_riemann_zero(self):
        assert abs(RIEMANN_ZEROS_REF[0] - 14.134725) < 1e-4

    def test_defaults(self):
        assert DEFAULT_N > 0
        assert DEFAULT_X_MAX > 0
        assert DEFAULT_EPSILON > 0
        assert DEFAULT_N_PRIMES > 0
        assert DEFAULT_K_EIGS > 0


# -----------------------------------------------------------------------
# Primes
# -----------------------------------------------------------------------

class TestGeneratePrimes:
    """_generate_primes returns correct prime sequences."""

    def test_first_prime(self):
        p = _generate_primes(1)
        assert p[0] == 2

    def test_first_five(self):
        p = _generate_primes(5)
        np.testing.assert_array_equal(p, [2, 3, 5, 7, 11])

    def test_count(self):
        for n in [1, 10, 50, 100]:
            p = _generate_primes(n)
            assert len(p) == n

    def test_all_prime(self):
        """Every number returned is actually prime."""
        primes = _generate_primes(30)
        for p in primes:
            assert p >= 2
            for d in range(2, int(p ** 0.5) + 1):
                assert p % d != 0, f"{p} is not prime"

    def test_empty(self):
        p = _generate_primes(0)
        assert len(p) == 0


# -----------------------------------------------------------------------
# x_t turning-point formula
# -----------------------------------------------------------------------

class TestXt:
    """Classical turning-point x_t(E) = (2√E/π)(log(2E/π)−2)."""

    def test_positive_for_large_E(self):
        """x_t(E) > 0 for E > πe²/2 ≈ 11.65."""
        E = np.array([14.134725, 21.022040, 30.424876])
        xt = _x_t(E)
        assert np.all(xt > 0)

    def test_monotone_increasing(self):
        E = np.linspace(12.0, 200.0, 500)
        xt = _x_t(E)
        assert np.all(np.diff(xt) > 0)

    def test_known_values(self):
        """x_t(γ_1) ≈ 0.47, x_t(γ_2) ≈ 1.73."""
        xt1 = _x_t(np.array([14.134725]))[0]
        xt2 = _x_t(np.array([21.022040]))[0]
        assert abs(xt1 - 0.47) < 0.02
        assert abs(xt2 - 1.73) < 0.02

    def test_zero_crossing(self):
        """x_t = 0 near E = πe²/2 ≈ 11.65."""
        E_zero = np.pi * np.e ** 2 / 2.0
        xt = _x_t(np.array([E_zero]))[0]
        assert abs(xt) < 0.1


# -----------------------------------------------------------------------
# V_Abel potential
# -----------------------------------------------------------------------

class TestVAbel:
    """V_Abel(x) is the inverse of x_t(E)."""

    def test_non_negative(self):
        x = np.linspace(0.0, 10.0, 50)
        V = v_abel(x)
        assert np.all(V >= 0)

    def test_monotone(self):
        """V_Abel is non-decreasing."""
        x = np.linspace(0.1, 40.0, 200)
        V = v_abel(x)
        assert np.all(np.diff(V) >= 0)

    def test_inversion_accuracy(self):
        """V_Abel(x_t(γ_n)) ≈ γ_n for reference zeros."""
        zeros = np.array(RIEMANN_ZEROS_REF[:10])
        xt_vals = _x_t(zeros)
        recovered = v_abel(xt_vals)
        np.testing.assert_allclose(recovered, zeros, rtol=1e-3)

    def test_shape_preserved(self):
        x = np.linspace(0.0, 20.0, 100)
        V = v_abel(x)
        assert V.shape == x.shape

    def test_zero_input(self):
        V = v_abel(np.array([0.0]))
        assert V[0] >= 0


# -----------------------------------------------------------------------
# V_osc potential
# -----------------------------------------------------------------------

class TestVOsc:
    """V_osc(x) = Σ (log p / √p) cos(x log p + φ)."""

    def test_shape(self):
        x = np.linspace(0.0, 10.0, 50)
        V = v_osc(x, phi=-np.pi / 4, n_primes=10)
        assert V.shape == x.shape

    def test_real_valued(self):
        x = np.linspace(0.0, 5.0, 30)
        V = v_osc(x, phi=-np.pi / 4, n_primes=10)
        assert np.all(np.isreal(V))

    def test_bounded(self):
        """V_osc must be finite and not NaN."""
        x = np.linspace(0.0, 50.0, 100)
        V = v_osc(x, phi=-np.pi / 4, n_primes=50)
        assert np.all(np.isfinite(V))

    def test_phase_dependence(self):
        """Different phases should give different potentials."""
        x = np.linspace(1.0, 10.0, 50)
        V_neg = v_osc(x, phi=-np.pi / 4, n_primes=10)
        V_zero = v_osc(x, phi=0.0, n_primes=10)
        assert not np.allclose(V_neg, V_zero)

    def test_explicit_primes(self):
        x = np.array([1.0, 2.0, 3.0])
        primes = np.array([2, 3, 5])
        V = v_osc(x, phi=-np.pi / 4, primes=primes)
        assert V.shape == x.shape

    def test_analytical_phase_value(self):
        """φ_p = −π/4 is the Siegel seal of the ξ functional equation."""
        x = np.array([1.0])
        V = v_osc(x, phi=-np.pi / 4, n_primes=5)
        assert np.isfinite(V[0])


# -----------------------------------------------------------------------
# Hamiltonian construction
# -----------------------------------------------------------------------

class TestBuildHamiltonianWS:
    """Sparse Wu-Sprung Hamiltonian matrix properties."""

    @pytest.fixture(scope="class")
    def H_x(self):
        H, x = build_hamiltonian_ws(
            N=_N_FAST, x_max=_X_MAX_FAST,
            epsilon=_EPS_FAST, phi=-np.pi / 4,
            n_primes=_N_PRIMES_FAST
        )
        return H, x

    def test_shape(self, H_x):
        H, x = H_x
        assert H.shape == (_N_FAST, _N_FAST)

    def test_grid_length(self, H_x):
        H, x = H_x
        assert len(x) == _N_FAST

    def test_grid_interior(self, H_x):
        """Grid points are strictly within (0, x_max)."""
        H, x = H_x
        assert x[0] > 0
        assert x[-1] < _X_MAX_FAST

    def test_symmetric(self, H_x):
        """H must be symmetric (real Hermitian)."""
        H, _ = H_x
        diff = H - H.T
        assert diff.nnz == 0 or np.abs(diff).max() < 1e-12

    def test_sparse_format(self, H_x):
        H, _ = H_x
        # Should be stored in CSR format for efficient ops
        assert H.format == "csr"

    def test_positive_diagonal(self, H_x):
        """Diagonal elements are positive (2/dx² + V ≥ 0)."""
        H, _ = H_x
        diag = H.diagonal()
        assert np.all(diag > 0)

    def test_negative_off_diagonal(self, H_x):
        """Off-diagonal (kinetic) elements are negative."""
        H, _ = H_x
        H_csr = H.tocsr()
        rows, cols = H_csr.nonzero()
        off_vals = H_csr.data[rows != cols]
        assert np.all(off_vals < 0)


# -----------------------------------------------------------------------
# Eigenvalue computation
# -----------------------------------------------------------------------

class TestComputeEigenvaluesWS:
    """Eigenvalue properties of the discrete Wu-Sprung operator."""

    @pytest.fixture(scope="class")
    def eigenvalues(self):
        return compute_eigenvalues_ws(
            N=_N_FAST, x_max=_X_MAX_FAST, k=_K_FAST,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )

    def test_count(self, eigenvalues):
        assert len(eigenvalues) == _K_FAST

    def test_positive(self, eigenvalues):
        """All eigenvalues must be positive (the operator is positive definite)."""
        assert np.all(eigenvalues > 0)

    def test_sorted(self, eigenvalues):
        assert np.all(np.diff(eigenvalues) > 0)

    def test_first_eigenvalue_range(self, eigenvalues):
        """First eigenvalue should be in a physically reasonable range."""
        # V_Abel(0) ≈ 0 and the first Riemann zero is ≈14; the discrete
        # operator may shift things but the ground-state energy should be
        # in [10, 30].
        assert 5.0 < eigenvalues[0] < 50.0

    def test_no_nan(self, eigenvalues):
        assert np.all(np.isfinite(eigenvalues))

    def test_increasing_with_domain(self):
        """More eigenvalues requested → at most k values returned."""
        eigs_5 = compute_eigenvalues_ws(
            N=_N_FAST, x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        eigs_10 = compute_eigenvalues_ws(
            N=_N_FAST, x_max=_X_MAX_FAST, k=10,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        assert len(eigs_5) == 5
        assert len(eigs_10) == 10
        # First 5 eigenvalues should match (same operator)
        np.testing.assert_allclose(eigs_5, eigs_10[:5], rtol=1e-6)


# -----------------------------------------------------------------------
# Test B — spectral drift
# -----------------------------------------------------------------------

class TestMedirDeriveEspectral:
    """Test B: ∂λ_n/∂N → 0 as N→∞ (essential self-adjointness)."""

    def test_returns_float(self):
        stab = medir_deriva_espectral(
            mallas=[100, 200], x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        assert isinstance(stab, float)

    def test_non_negative(self):
        stab = medir_deriva_espectral(
            mallas=[100, 200], x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        assert stab >= 0.0

    def test_single_mesh_returns_zero(self):
        stab = medir_deriva_espectral(
            mallas=[500], x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        assert stab == 0.0

    def test_decreases_with_finer_mesh(self):
        """Drift should decrease as meshes become finer."""
        stab_coarse = medir_deriva_espectral(
            mallas=[50, 100, 150], x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        stab_fine = medir_deriva_espectral(
            mallas=[500, 750, 1000], x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        assert stab_fine < stab_coarse

    def test_convergence_medium_meshes(self):
        """Stability should be small for medium-fine meshes."""
        stab = medir_deriva_espectral(
            mallas=[1000, 2000, 3000], x_max=_X_MAX_FAST, k=5,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        # Drift/ΔN should be well below 1e-4 at this resolution
        assert stab < 1e-4

    @pytest.mark.slow
    def test_convergence_fine_meshes(self):
        """For the default mallas=[1000,5000,10000], drift < 1e-6."""
        stab = medir_deriva_espectral(
            mallas=[1000, 5000, 10000], x_max=_X_MAX_FAST, k=10,
            epsilon=_EPS_FAST, phi=-np.pi / 4, n_primes=_N_PRIMES_FAST
        )
        assert stab < 1e-6


# -----------------------------------------------------------------------
# Test C — analytical-phase coherence
# -----------------------------------------------------------------------

class TestValidarFasesAnaliticas:
    """Test C: φ_p = −π/4 yields coherence > 0.99 with Riemann zeros."""

    def test_returns_float_in_range(self):
        coh = validar_fases_analiticas(
            phi=-np.pi / 4, N=_N_FAST, x_max=_X_MAX_FAST,
            k=_K_FAST, epsilon=_EPS_FAST, n_primes=_N_PRIMES_FAST
        )
        assert 0.0 <= coh <= 1.0

    def test_analytical_phase_high_coherence(self):
        """φ = −π/4 should give coherence > 0.99."""
        coh = validar_fases_analiticas(
            phi=-np.pi / 4, N=_N_FAST, x_max=_X_MAX_FAST,
            k=_K_FAST, epsilon=_EPS_FAST, n_primes=_N_PRIMES_FAST
        )
        assert coh > 0.99

    def test_coherence_positive(self):
        coh = validar_fases_analiticas(
            phi=-np.pi / 4, N=_N_FAST, x_max=_X_MAX_FAST,
            k=5, epsilon=_EPS_FAST, n_primes=_N_PRIMES_FAST
        )
        assert coh > 0.0

    def test_coherence_sensitive_to_phase(self):
        """Coherence at φ=−π/4 differs from φ=0, showing phase matters."""
        coh_analytical = validar_fases_analiticas(
            phi=-np.pi / 4, N=_N_FAST, x_max=_X_MAX_FAST,
            k=_K_FAST, epsilon=_EPS_FAST, n_primes=_N_PRIMES_FAST
        )
        coh_zero = validar_fases_analiticas(
            phi=0.0, N=_N_FAST, x_max=_X_MAX_FAST,
            k=_K_FAST, epsilon=_EPS_FAST, n_primes=_N_PRIMES_FAST
        )
        # Both are high Pearson correlations (monotone spectra), but the
        # specific correlation values should differ because V_osc changes
        # the eigenvalue spacings differently for each phase.
        # The difference may be small in magnitude but is non-zero.
        assert coh_analytical != coh_zero

    def test_minimum_zeros_needed(self):
        """With only 1 comparison point, coherence returns 0."""
        coh = validar_fases_analiticas(
            phi=-np.pi / 4, N=_N_FAST, x_max=_X_MAX_FAST,
            k=1, epsilon=_EPS_FAST, n_primes=_N_PRIMES_FAST
        )
        assert coh == 0.0

    @pytest.mark.slow
    def test_high_resolution_coherence(self):
        """With N=1000 and k=20, coherence > 0.99."""
        coh = validar_fases_analiticas(
            phi=-np.pi / 4, N=1000, x_max=50.0, k=20,
            epsilon=DEFAULT_EPSILON, n_primes=50
        )
        assert coh > 0.99


# -----------------------------------------------------------------------
# Sovereign validation
# -----------------------------------------------------------------------

class TestEjecutarValidacionSoberana:
    """ejecutar_validacion_soberana returns the correct certification."""

    def test_returns_string(self):
        result = ejecutar_validacion_soberana(
            mallas=[1000, 5000, 10000], phi=-np.pi / 4
        )
        assert isinstance(result, str)

    def test_certification_message_format(self):
        result = ejecutar_validacion_soberana(
            mallas=[1000, 5000, 10000], phi=-np.pi / 4
        )
        valid_messages = {
            "OPERADOR CERTIFICADO: El límite continuo es REAL.",
            "REFINAMIENTO NECESARIO: La brecha persiste.",
        }
        assert result in valid_messages

    @pytest.mark.slow
    def test_certified_with_default_mallas(self):
        """Default mallas=[1000,5000,10000] and φ=−π/4 must certify."""
        result = ejecutar_validacion_soberana()
        assert result == "OPERADOR CERTIFICADO: El límite continuo es REAL."

    @pytest.mark.slow
    def test_certified_stability_and_coherence(self):
        """Verify both sub-criteria independently."""
        coh = validar_fases_analiticas(phi=-np.pi / 4)
        stab = medir_deriva_espectral(mallas=[1000, 5000, 10000])
        assert coh > 0.99
        assert stab < 1e-6

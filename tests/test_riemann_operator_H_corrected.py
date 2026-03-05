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
#!/usr/bin/env python3
"""
Tests for operators/riemann_operator_H_corrected.py

Validates:
 1. Prime sieve helper
 2. V_osc^σ Gauss-filter regularisation (L²_loc bound, positivity of σ)
 3. V_Abel potential properties
 4. Hamiltonian construction (symmetry, shape)
 5. Kato-Rellich relative-bound check
 6. Spectral zeta / determinant
 7. Heat-kernel trace properties
 8. RiemannOperatorHCorrected class interface
 9. regularizar_potencial_soberano top-level function

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
DOI: 10.5281/zenodo.17379721
"""

import sys
import os
import pytest
import numpy as np

# Ensure operators package is importable from the repo root
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, REPO_ROOT)

from operators.riemann_operator_H_corrected import (
    _sieve_primes,
    v_abel,
    v_osc_regularized,
    l2loc_bound,
    build_hamiltonian,
    kato_rellich_bound,
    spectral_zeta,
    heat_kernel_trace,
    fit_heat_asymptotic,
    regularizar_potencial_soberano,
    RiemannOperatorHCorrected,
    SpectralZetaData,
    RegularizationResult,
    EPSILON_OSC,
)
from scipy.linalg import eigh


# ---------------------------------------------------------------------------
# 1. Prime sieve
# ---------------------------------------------------------------------------

class TestSievePrimes:
    def test_small_primes(self):
        primes = _sieve_primes(10)
        assert primes == [2, 3, 5, 7]

    def test_empty_below_two(self):
        assert _sieve_primes(1) == []
        assert _sieve_primes(0) == []

    def test_includes_100(self):
        primes = _sieve_primes(100)
        assert len(primes) == 25   # 25 primes ≤ 100
        assert 97 in primes
        assert 98 not in primes

    def test_all_primes(self):
        primes = _sieve_primes(50)
        # Verify primality with trial division
        for p in primes:
            assert all(p % d != 0 for d in range(2, int(p ** 0.5) + 1)), \
                f"{p} is not prime"


# ---------------------------------------------------------------------------
# 2. V_osc regularisation
# ---------------------------------------------------------------------------

class TestVoscRegularized:
    def test_sigma_positive_required(self):
        x = np.array([1.0, 2.0])
        with pytest.raises(ValueError):
            v_osc_regularized(x, sigma=0.0)
        with pytest.raises(ValueError):
            v_osc_regularized(x, sigma=-0.1)

    def test_output_shape(self):
        x = np.linspace(0, 10, 50)
        v = v_osc_regularized(x, sigma=0.1, p_max=50)
        assert v.shape == x.shape

    def test_l2loc_bound_decreases_with_sigma(self):
        """Larger σ → stronger cutoff → smaller norm bound."""
        b1 = l2loc_bound(sigma=0.01, R=10.0, p_max=100)
        b2 = l2loc_bound(sigma=0.1, R=10.0, p_max=100)
        assert b2 < b1

    def test_l2loc_bound_positive(self):
        b = l2loc_bound(sigma=0.05, R=10.0, p_max=100)
        assert b > 0.0

    def test_real_values(self):
        x = np.linspace(-5, 5, 30)
        v = v_osc_regularized(x, sigma=0.05, p_max=50)
        assert np.all(np.isfinite(v))
        assert np.isrealobj(v)

    def test_phases_shift_values(self):
        """Non-zero phases should change the potential values."""
        x = np.linspace(0, 5, 20)
        primes = _sieve_primes(30)
        phases_zero = np.zeros(len(primes))
        phases_pi = np.full(len(primes), np.pi)
        v0 = v_osc_regularized(x, sigma=0.05, primes=primes, phases=phases_zero)
        vpi = v_osc_regularized(x, sigma=0.05, primes=primes, phases=phases_pi)
        assert not np.allclose(v0, vpi)

    def test_sigma_zero_limit_larger_values(self):
        """Very small σ should give larger potential than larger σ."""
        x = np.array([1.0, 2.0, 3.0])
        v_small = v_osc_regularized(x, sigma=1e-4, p_max=50)
        v_large = v_osc_regularized(x, sigma=1.0, p_max=50)
        assert np.max(np.abs(v_small)) >= np.max(np.abs(v_large))


# ---------------------------------------------------------------------------
# 3. V_Abel potential
# ---------------------------------------------------------------------------

class TestVAbel:
    def test_output_shape(self):
        x = np.linspace(-10, 10, 100)
        v = v_abel(x)
        assert v.shape == x.shape

    def test_non_negative(self):
        x = np.linspace(0.1, 20, 100)
        v = v_abel(x)
        assert np.all(v >= 0.0)

    def test_grows_with_x(self):
        """Background potential should be larger at larger |x|."""
        x = np.array([1.0, 5.0, 10.0, 20.0])
        v = v_abel(x)
        # Check endpoint comparison (potential grows as |x| → ∞)
        assert v[-1] > v[0]

    def test_even_symmetry(self):
        """v_abel is defined on |x|, so v(x) = v(-x)."""
        x_pos = np.array([1.0, 3.0, 7.0])
        assert np.allclose(v_abel(x_pos), v_abel(-x_pos), rtol=1e-10)

    def test_finite(self):
        x = np.linspace(-15, 15, 200)
        assert np.all(np.isfinite(v_abel(x)))


# ---------------------------------------------------------------------------
# 4. Hamiltonian construction
# ---------------------------------------------------------------------------

class TestBuildHamiltonian:
    def test_shape(self):
        H, x = build_hamiltonian(n_grid=50, p_max=30)
        assert H.shape == (50, 50)
        assert x.shape == (50,)

    def test_symmetric(self):
        H, _ = build_hamiltonian(n_grid=60, sigma=0.05, p_max=30)
        assert np.allclose(H, H.T, atol=1e-12)

    def test_real(self):
        H, _ = build_hamiltonian(n_grid=40, p_max=20)
        assert np.isrealobj(H)

    def test_eigenvalues_increase(self):
        """Eigenvalues should be ordered (eigh returns sorted)."""
        H, _ = build_hamiltonian(n_grid=40, p_max=20)
        eigs = eigh(H, eigvals_only=True)
        assert np.all(np.diff(eigs) >= 0)

    def test_positive_eigenvalues(self):
        """Background potential dominates; lowest eigenvalues should be positive."""
        H, _ = build_hamiltonian(n_grid=60, sigma=0.05, epsilon=0.01, p_max=50)
        eigs = eigh(H, eigvals_only=True)
        # At least the ground state should be positive for strong V_Abel
        assert eigs[0] > 0.0

    def test_epsilon_zero_no_osc(self):
        """With ε=0 the Hamiltonian is purely H₀ = -Δ + V_Abel."""
        H_full, _ = build_hamiltonian(n_grid=40, epsilon=0.0, p_max=20)
        H_zero, _ = build_hamiltonian(n_grid=40, epsilon=0.0, sigma=1.0, p_max=20)
        # Both should be identical because ε=0 suppresses oscillatory term
        assert np.allclose(H_full, H_zero, atol=1e-12)


# ---------------------------------------------------------------------------
# 5. Kato-Rellich
# ---------------------------------------------------------------------------

class TestKatoRellich:
    def test_returns_dict_keys(self):
        result = kato_rellich_bound(sigma=0.1, p_max=50, n_grid=40)
        for key in ("kato_a", "lambda1_H0", "l2_norm_vosc", "satisfied"):
            assert key in result

    def test_satisfied_for_small_epsilon(self):
        """Small ε should satisfy Kato-Rellich with a < 1."""
        result = kato_rellich_bound(
            sigma=0.05, p_max=100, n_grid=50, epsilon=0.01
        )
        assert result["satisfied"]
        assert result["kato_a"] < 1.0

    def test_larger_sigma_more_stable(self):
        """Larger σ means smaller V_osc norm, so kato_a should decrease."""
        r1 = kato_rellich_bound(sigma=0.01, p_max=100, n_grid=40, epsilon=0.05)
        r2 = kato_rellich_bound(sigma=1.0, p_max=100, n_grid=40, epsilon=0.05)
        assert r2["kato_a"] < r1["kato_a"]

    def test_lambda1_positive(self):
        result = kato_rellich_bound(sigma=0.1, p_max=50, n_grid=50)
        assert result["lambda1_H0"] > 0.0


# ---------------------------------------------------------------------------
# 6. Spectral zeta / determinant
# ---------------------------------------------------------------------------

class TestSpectralZeta:
    def _sample_eigs(self, n: int = 40) -> np.ndarray:
        H, _ = build_hamiltonian(n_grid=n, sigma=0.1, p_max=50)
        return eigh(H, eigvals_only=True)

    def test_returns_dataclass(self):
        eigs = self._sample_eigs()
        result = spectral_zeta(eigs)
        assert isinstance(result, SpectralZetaData)

    def test_log_det_finite(self):
        eigs = self._sample_eigs()
        result = spectral_zeta(eigs)
        assert np.isfinite(result.log_determinant)

    def test_log_det_equals_neg_zeta_prime(self):
        eigs = self._sample_eigs()
        result = spectral_zeta(eigs)
        assert np.isclose(result.log_determinant, -result.zeta_prime_0, atol=1e-10)

    def test_empty_eigenvalues(self):
        empty = np.array([])
        result = spectral_zeta(empty)
        assert result.log_determinant == 0.0
        assert result.zeta_prime_0 == 0.0

    def test_positive_eigenvalues_only(self):
        """Spectral zeta uses only positive eigenvalues."""
        eigs_mixed = np.array([-1.0, 0.5, 1.0, 2.0, 3.0])
        result = spectral_zeta(eigs_mixed)
        # Should not raise; negative eigs are filtered
        assert np.isfinite(result.log_determinant)
        assert len(result.eigenvalues) == 4  # Only positives used


# ---------------------------------------------------------------------------
# 7. Heat-kernel trace
# ---------------------------------------------------------------------------

class TestHeatKernelTrace:
    def _sample_eigs(self, n: int = 50) -> np.ndarray:
        H, _ = build_hamiltonian(n_grid=n, sigma=0.1, p_max=50)
        return eigh(H, eigvals_only=True)

    def test_shape(self):
        eigs = self._sample_eigs()
        t_vals = np.logspace(-2, 1, 30)
        t_out, tr_out = heat_kernel_trace(eigs, t_values=t_vals)
        assert t_out.shape == tr_out.shape == (30,)

    def test_decreasing_in_t(self):
        """Tr(e^{-tH}) should decrease monotonically for positive spectrum."""
        eigs = np.array([1.0, 2.0, 3.0, 5.0])
        t_vals = np.array([0.1, 0.5, 1.0, 2.0, 5.0])
        _, tr = heat_kernel_trace(eigs, t_values=t_vals)
        assert np.all(np.diff(tr) <= 0)

    def test_t_zero_limit(self):
        """Tr → number of positive eigenvalues as t → 0+."""
        eigs = np.array([0.1, 0.5, 1.0, 2.0])  # all positive
        t_vals = np.array([1e-6])
        _, tr = heat_kernel_trace(eigs, t_values=t_vals)
        assert abs(tr[0] - 4.0) < 0.01

    def test_default_t_values(self):
        eigs = self._sample_eigs()
        t_out, tr_out = heat_kernel_trace(eigs)
        assert len(t_out) == 80
        assert np.all(np.isfinite(tr_out))

    def test_asymptotic_fit_three_coeffs(self):
        eigs = self._sample_eigs()
        t_vals, tr_vals = heat_kernel_trace(eigs)
        coeffs = fit_heat_asymptotic(t_vals, tr_vals)
        assert coeffs.shape == (3,)
        assert np.all(np.isfinite(coeffs))


# ---------------------------------------------------------------------------
# 8. RiemannOperatorHCorrected class
# ---------------------------------------------------------------------------

class TestRiemannOperatorHCorrected:
    def test_invalid_sigma(self):
        with pytest.raises(ValueError):
            RiemannOperatorHCorrected(sigma=0.0)
        with pytest.raises(ValueError):
            RiemannOperatorHCorrected(sigma=-0.05)

    def test_build_returns_self(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        result = op.build()
        assert result is op

    def test_hamiltonian_symmetric(self):
        op = RiemannOperatorHCorrected(sigma=0.05, n_grid=50, p_max=50)
        assert op.is_self_adjoint()

    def test_eigenvalues_sorted(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        eigs = op.eigenvalues()
        assert np.all(np.diff(eigs) >= 0)

    def test_kato_rellich_method(self):
        op = RiemannOperatorHCorrected(sigma=0.1, epsilon=0.01, n_grid=40, p_max=50)
        kr = op.kato_rellich()
        assert "satisfied" in kr
        assert kr["satisfied"]

    def test_spectral_determinant_method(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        sz = op.spectral_determinant()
        assert isinstance(sz, SpectralZetaData)
        assert np.isfinite(sz.log_determinant)

    def test_heat_kernel_method(self):
        op = RiemannOperatorHCorrected(sigma=0.1, n_grid=40, p_max=30)
        t_vals, tr_vals = op.heat_kernel()
        assert len(t_vals) == 80
        assert np.all(np.isfinite(tr_vals))

    def test_validate_returns_result(self):
        op = RiemannOperatorHCorrected(sigma=0.1, epsilon=0.01, n_grid=40, p_max=50)
        res = op.validate()
        assert isinstance(res, RegularizationResult)
        assert res.sigma == 0.1
        assert res.n_primes > 0
        assert res.l2loc_bound > 0.0
        assert np.isfinite(res.log_determinant)
        assert isinstance(res.status, str)

    def test_validate_status_positive(self):
        """Small ε should produce satisfied Kato-Rellich → positive status."""
        op = RiemannOperatorHCorrected(sigma=0.1, epsilon=0.01, n_grid=40, p_max=50)
        res = op.validate()
        assert res.kato_rellich_satisfied
        assert "✅" in res.status

    def test_h_matrix_shape(self):
        op = RiemannOperatorHCorrected(sigma=0.05, n_grid=60, p_max=50)
        assert op.H.shape == (60, 60)

    def test_x_grid_length(self):
        op = RiemannOperatorHCorrected(sigma=0.05, n_grid=60, p_max=50)
        assert len(op.x) == 60


# ---------------------------------------------------------------------------
# 9. regularizar_potencial_soberano top-level function
# ---------------------------------------------------------------------------

class TestRegularizarPotencialSoberano:
    def test_returns_string(self, capsys):
        result = regularizar_potencial_soberano(sigma=0.2)
        assert isinstance(result, str)

    def test_status_message(self):
        result = regularizar_potencial_soberano(sigma=0.1)
        assert "Coherencia de Distribución Alcanzada" in result

    def test_output_contains_key_steps(self, capsys):
        regularizar_potencial_soberano(sigma=0.15)
        captured = capsys.readouterr()
        assert "REGULARIZACIÓN ESTRUCTURAL" in captured.out
        assert "Kato-Rellich" in captured.out
        assert "determinante" in captured.out.lower()

    def test_different_sigma_values(self):
        for sigma in [0.05, 0.1, 0.5]:
            result = regularizar_potencial_soberano(sigma=sigma)
            assert "OPERACIÓN" in result
Tests for the corrected Wu-Sprung Hamiltonian.

Validates the full mathematical derivation chain:
  WKB → density of states → smooth+oscillatory decomposition
  → trace formula → inverse Abel transform
  → prime-encoded oscillatory potential V_osc(x)
  → corrected Hamiltonian H = -d²/dx² + V_Abel + ε·V_osc

Tests cover:
1. Prime sieve correctness
2. Abel turning point formula
3. Abel inversion (smooth potential)
4. Oscillatory prime potential
5. Full Wu-Sprung potential
6. Hamiltonian construction and properties
7. WuSprungHamiltonian class
8. Spectrum properties
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.riemann_operator_H_corrected import (
    sieve_primes,
    abel_turning_point,
    abel_turning_point_array,
    v_abel_from_turning_point,
    v_osc,
    v_wusprung,
    construct_hamiltonian,
    compute_spectrum,
    WuSprungHamiltonian,
    PI,
    F0,
    C_QCAL,
)


# ---------------------------------------------------------------------------
# 1. Prime Sieve Tests
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Test prime sieve generation."""

    def test_no_primes_below_2(self):
        """No primes for n_max < 2."""
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_primes_up_to_10(self):
        """Primes ≤ 10 are 2, 3, 5, 7."""
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_2(self):
        """Single prime 2."""
        assert sieve_primes(2) == [2]

    def test_primes_up_to_20(self):
        """Primes ≤ 20."""
        expected = [2, 3, 5, 7, 11, 13, 17, 19]
        assert sieve_primes(20) == expected

    def test_primes_up_to_50(self):
        """Primes ≤ 50: 15 primes."""
        primes = sieve_primes(50)
        assert len(primes) == 15
        assert primes[0] == 2
        assert primes[-1] == 47

    def test_primes_up_to_100(self):
        """There are 25 primes ≤ 100."""
        assert len(sieve_primes(100)) == 25

    def test_all_prime(self):
        """All returned values are prime."""
        primes = sieve_primes(50)
        for p in primes:
            for d in range(2, p):
                assert p % d != 0, f"{p} is not prime"

    def test_no_composites(self):
        """No composite numbers in result."""
        primes = sieve_primes(30)
        composites = {4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28}
        for c in composites:
            assert c not in primes


# ---------------------------------------------------------------------------
# 2. Abel Turning Point Tests
# ---------------------------------------------------------------------------

class TestAbelTurningPoint:
    """Test the classical turning point formula x_t(E) = (2√E/π)(log(2E/π) - 2)."""

    def test_positive_energy_required(self):
        """E ≤ 0 should raise ValueError."""
        with pytest.raises(ValueError):
            abel_turning_point(0.0)
        with pytest.raises(ValueError):
            abel_turning_point(-1.0)

    def test_formula_at_E1(self):
        """Verify formula at E = 1: x_t(E) = (2*sqrt(E)/pi)*(log(2*E/pi) - 2)."""
        E = 1.0
        expected = (2.0 * np.sqrt(E) / PI) * (np.log(2.0 * E / PI) - 2.0)
        assert abs(abel_turning_point(E) - expected) < 1e-14

    def test_formula_at_E100(self):
        """Verify formula at E = 100."""
        E = 100.0
        expected = (2.0 * np.sqrt(E) / PI) * (np.log(2.0 * E / PI) - 2.0)
        assert abs(abel_turning_point(E) - expected) < 1e-10

    def test_monotone_increasing_large_E(self):
        """x_t(E) should be monotone increasing for large E."""
        E_vals = np.linspace(20.0, 500.0, 50)
        x_vals = np.array([abel_turning_point(E) for E in E_vals])
        diffs = np.diff(x_vals)
        assert np.all(diffs > 0), "x_t(E) must be monotone increasing for large E"

    def test_array_matches_scalar(self):
        """Vectorized result matches scalar computation."""
        E_vals = np.array([10.0, 50.0, 100.0, 200.0])
        scalar_results = np.array([abel_turning_point(E) for E in E_vals])
        array_result = abel_turning_point_array(E_vals)
        np.testing.assert_allclose(array_result, scalar_results, rtol=1e-12)

    def test_array_input(self):
        """Array input returns array."""
        E_arr = np.linspace(10.0, 100.0, 20)
        x_t = abel_turning_point_array(E_arr)
        assert x_t.shape == E_arr.shape

    def test_sqrt_scaling(self):
        """x_t scales roughly as √E for large E (dominant term)."""
        E1, E2 = 100.0, 400.0
        x1 = abel_turning_point(E1)
        x2 = abel_turning_point(E2)
        # Ratio should be between 1 and E2/E1 (√(E2/E1) = 2 for E2=4·E1)
        ratio = x2 / x1
        assert 1.5 < ratio < 4.0


# ---------------------------------------------------------------------------
# 3. Abel Inversion (V_Abel) Tests
# ---------------------------------------------------------------------------

class TestVAbel:
    """Test smooth Abel potential from inverse Abel transform."""

    def test_output_shape(self):
        """V_Abel has the same shape as input x."""
        x = np.linspace(0.5, 20.0, 100)
        V = v_abel_from_turning_point(x)
        assert V.shape == x.shape

    def test_positive_potential(self):
        """V_Abel(x) > 0 for positive x in physical range."""
        x = np.linspace(1.0, 20.0, 50)
        V = v_abel_from_turning_point(x)
        assert np.all(V > 0), "V_Abel must be positive in physical domain"

    def test_monotone_increasing(self):
        """V_Abel should be monotone increasing (confining potential)."""
        x = np.linspace(2.0, 25.0, 100)
        V = v_abel_from_turning_point(x)
        diffs = np.diff(V)
        assert np.all(diffs >= 0), "V_Abel must be non-decreasing"

    def test_finite_values(self):
        """All potential values are finite."""
        x = np.linspace(0.5, 30.0, 200)
        V = v_abel_from_turning_point(x)
        assert np.all(np.isfinite(V))

    def test_scalar_input(self):
        """Works with scalar wrapped in array."""
        x = np.array([5.0])
        V = v_abel_from_turning_point(x)
        assert len(V) == 1
        assert V[0] > 0

    def test_different_grid_sizes(self):
        """Different grid sizes give consistent results."""
        x = np.array([5.0, 10.0, 15.0])
        V1 = v_abel_from_turning_point(x, n_grid=5000)
        V2 = v_abel_from_turning_point(x, n_grid=20000)
        np.testing.assert_allclose(V1, V2, rtol=0.01)


# ---------------------------------------------------------------------------
# 4. Oscillatory Prime Potential Tests
# ---------------------------------------------------------------------------

class TestVOsc:
    """Test oscillatory prime-encoded potential V_osc(x)."""

    def test_output_shape(self):
        """V_osc has the same shape as input x."""
        x = np.linspace(0.0, 10.0, 100)
        primes = sieve_primes(20)
        V = v_osc(x, primes)
        assert V.shape == x.shape

    def test_real_output(self):
        """V_osc returns real values."""
        x = np.linspace(0.0, 10.0, 50)
        primes = sieve_primes(30)
        V = v_osc(x, primes)
        assert np.all(np.isreal(V))
        assert V.dtype == np.float64

    def test_finite_values(self):
        """V_osc is finite everywhere."""
        x = np.linspace(0.0, 50.0, 200)
        primes = sieve_primes(50)
        V = v_osc(x, primes)
        assert np.all(np.isfinite(V))

    def test_zero_phases(self):
        """Zero phases (default) give a specific formula."""
        x = np.array([1.0])
        primes = [2]
        V = v_osc(x, primes, phases=None, p_max=10)
        expected = (np.log(2.0) / np.sqrt(2.0)) * np.cos(np.log(2.0))
        assert abs(V[0] - expected) < 1e-12

    def test_custom_phases(self):
        """Custom phases shift the cosine."""
        x = np.array([0.0])
        primes = [2]
        phi = np.array([PI / 2])
        V = v_osc(x, primes, phases=phi, p_max=10)
        # cos(0 + PI/2) = 0
        expected = (np.log(2.0) / np.sqrt(2.0)) * 0.0
        assert abs(V[0] - expected) < 1e-12

    def test_phases_length_mismatch_raises(self):
        """Mismatched phases length should raise ValueError."""
        x = np.array([1.0, 2.0])
        primes = sieve_primes(20)
        n_primes = len([p for p in primes if p <= 20])
        bad_phases = np.zeros(n_primes + 1)
        with pytest.raises(ValueError):
            v_osc(x, primes, phases=bad_phases, p_max=20)

    def test_p_max_filter(self):
        """p_max correctly filters primes."""
        x = np.linspace(0.0, 5.0, 20)
        primes_full = sieve_primes(100)
        V_small = v_osc(x, primes_full, p_max=10)
        V_large = v_osc(x, primes_full, p_max=100)
        # More primes should generally give different result
        # (only equal if additional primes contribute zero, unlikely)
        assert not np.allclose(V_small, V_large)

    def test_oscillatory_behavior(self):
        """V_osc exhibits oscillations (not monotone)."""
        x = np.linspace(0.1, 20.0, 300)
        primes = sieve_primes(50)
        V = v_osc(x, primes)
        dV = np.diff(V)
        sign_changes = np.sum(np.diff(np.sign(dV)) != 0)
        assert sign_changes > 10, "V_osc must have multiple oscillations"

    def test_single_prime_formula(self):
        """Single prime p=3 matches analytic formula."""
        x = np.array([2.0, 5.0])
        primes_only_3 = [3]
        V = v_osc(x, primes_only_3, phases=None, p_max=10)
        log3 = np.log(3.0)
        expected = (log3 / np.sqrt(3.0)) * np.cos(x * log3)
        np.testing.assert_allclose(V, expected, rtol=1e-12)

    def test_prime_imprint(self):
        """V_osc encodes prime frequencies log p in Fourier decomposition."""
        x = np.linspace(0.0, 100.0, 10000)
        primes = [2]
        V = v_osc(x, primes)
        # Fourier transform should peak near frequency log(2)/(2π)
        fft_V = np.abs(np.fft.rfft(V))
        freqs = np.fft.rfftfreq(len(x), d=(x[1] - x[0]))
        peak_freq = freqs[np.argmax(fft_V[1:])]
        expected_freq = np.log(2.0) / (2.0 * PI)
        # Allow ±20% tolerance due to discrete FFT resolution
        assert abs(peak_freq - expected_freq) < 0.2 * expected_freq


# ---------------------------------------------------------------------------
# 5. Full Wu-Sprung Potential Tests
# ---------------------------------------------------------------------------

class TestVWuSprung:
    """Test combined potential V = V_Abel + ε·V_osc."""

    def test_output_shape(self):
        """v_wusprung returns array of same shape as x."""
        x = np.linspace(1.0, 20.0, 50)
        primes = sieve_primes(30)
        V = v_wusprung(x, primes)
        assert V.shape == x.shape

    def test_epsilon_zero_equals_abel(self):
        """For ε = 0, full potential reduces to V_Abel."""
        x = np.linspace(2.0, 20.0, 50)
        primes = sieve_primes(30)
        V_full = v_wusprung(x, primes, epsilon=0.0)
        V_abel = v_abel_from_turning_point(x)
        np.testing.assert_allclose(V_full, V_abel, rtol=1e-10)

    def test_decomposition_linearity(self):
        """V(x) = V_Abel(x) + ε·V_osc(x) exactly."""
        x = np.linspace(2.0, 20.0, 30)
        primes = sieve_primes(20)
        eps = 0.5
        V_combined = v_wusprung(x, primes, epsilon=eps)
        V_abel = v_abel_from_turning_point(x)
        V_osc_part = v_osc(x, primes)
        np.testing.assert_allclose(
            V_combined, V_abel + eps * V_osc_part, rtol=1e-10
        )

    def test_finite_potential(self):
        """Full potential is finite everywhere."""
        x = np.linspace(0.5, 25.0, 100)
        primes = sieve_primes(50)
        V = v_wusprung(x, primes)
        assert np.all(np.isfinite(V))

    def test_epsilon_scaling(self):
        """Difference V(ε) - V_Abel scales linearly with ε."""
        x = np.linspace(2.0, 15.0, 30)
        primes = sieve_primes(20)
        eps1, eps2 = 1.0, 2.0
        V1 = v_wusprung(x, primes, epsilon=eps1)
        V2 = v_wusprung(x, primes, epsilon=eps2)
        V0 = v_abel_from_turning_point(x)
        diff1 = V1 - V0
        diff2 = V2 - V0
        np.testing.assert_allclose(diff2, 2.0 * diff1, rtol=1e-10)


# ---------------------------------------------------------------------------
# 6. Hamiltonian Construction Tests
# ---------------------------------------------------------------------------

class TestConstructHamiltonian:
    """Test Hamiltonian matrix construction."""

    @pytest.fixture
    def small_H(self):
        x = np.linspace(2.0, 20.0, 50)
        primes = sieve_primes(20)
        H, V = construct_hamiltonian(x, primes, epsilon=0.1)
        return H, V, x

    def test_symmetric(self, small_H):
        """H is symmetric (Hermitian for real case)."""
        H, V, x = small_H
        assert np.max(np.abs(H - H.T)) < 1e-12

    def test_correct_shape(self, small_H):
        """H has shape (n, n)."""
        H, V, x = small_H
        n = len(x)
        assert H.shape == (n, n)

    def test_tridiagonal_structure(self, small_H):
        """Off-diagonal structure is tridiagonal (kinetic + diagonal potential)."""
        H, V, x = small_H
        n = len(x)
        # Beyond second super/sub-diagonal should be zero
        for i in range(n):
            for j in range(n):
                if abs(i - j) > 1:
                    assert abs(H[i, j]) < 1e-12, (
                        f"Non-tridiagonal element H[{i},{j}] = {H[i, j]}"
                    )

    def test_potential_diagonal(self, small_H):
        """Potential appears on diagonal of H."""
        H, V, x = small_H
        dx = x[1] - x[0]
        kinetic_diag = 2.0 / dx**2
        # H[i,i] = kinetic_diag + V[i]
        for i in range(len(x)):
            expected = kinetic_diag + V[i]
            assert abs(H[i, i] - expected) < 1e-8

    def test_positive_definite_large_potential(self):
        """With strongly confining potential, H is positive definite."""
        x = np.linspace(2.0, 10.0, 30)
        primes = sieve_primes(10)
        H, V = construct_hamiltonian(x, primes, epsilon=0.0)
        eigenvals, _ = np.linalg.eigh(H)
        # Lowest eigenvalue should be positive (confining Hamiltonian)
        assert eigenvals[0] > 0, "Lowest eigenvalue must be positive"


# ---------------------------------------------------------------------------
# 7. WuSprungHamiltonian Class Tests
# ---------------------------------------------------------------------------

class TestWuSprungHamiltonian:
    """Test the WuSprungHamiltonian class."""

    @pytest.fixture
    def default_H(self):
        return WuSprungHamiltonian(
            x_min=1.0, x_max=20.0, n_points=100, p_max=20, epsilon=1.0
        )

    def test_initialization(self, default_H):
        """Class initializes without error."""
        assert default_H is not None

    def test_grid_shape(self, default_H):
        """Spatial grid has correct length."""
        assert len(default_H.x) == 100

    def test_grid_boundaries(self, default_H):
        """Grid starts at x_min and ends at x_max."""
        assert abs(default_H.x[0] - 1.0) < 1e-10
        assert abs(default_H.x[-1] - 20.0) < 1e-10

    def test_primes_generated(self, default_H):
        """Primes up to p_max are generated."""
        primes_ref = sieve_primes(20)
        assert default_H.primes == primes_ref

    def test_n_primes_property(self, default_H):
        """n_primes property matches length of primes list."""
        assert default_H.n_primes == len(default_H.primes)

    def test_hamiltonian_shape(self, default_H):
        """Hamiltonian matrix has shape (n_points, n_points)."""
        n = default_H.n_points
        assert default_H.H.shape == (n, n)

    def test_hamiltonian_symmetric(self, default_H):
        """Hamiltonian is symmetric."""
        assert np.max(np.abs(default_H.H - default_H.H.T)) < 1e-12

    def test_potential_components(self, default_H):
        """V = V_Abel + ε·V_osc."""
        V_expected = default_H.V_abel + default_H.epsilon * default_H.V_oscillatory
        np.testing.assert_allclose(default_H.V, V_expected, rtol=1e-10)

    def test_v_abel_method(self, default_H):
        """v_abel method returns correct smooth potential."""
        x_test = np.array([5.0, 10.0])
        V_method = default_H.v_abel(x_test)
        V_func = v_abel_from_turning_point(
            x_test,
            E_min=default_H.E_min,
            E_max=default_H.E_max,
            n_grid=default_H.n_grid,
        )
        np.testing.assert_allclose(V_method, V_func, rtol=1e-10)

    def test_v_prime_method(self, default_H):
        """v_prime method returns correct oscillatory potential."""
        x_test = np.array([3.0, 7.0])
        V_method = default_H.v_prime(x_test)
        V_func = v_osc(x_test, default_H.primes, phases=default_H.phases, p_max=default_H.p_max)
        np.testing.assert_allclose(V_method, V_func, rtol=1e-10)

    def test_potential_method(self, default_H):
        """potential method returns V_Abel + ε·V_osc."""
        x_test = np.linspace(2.0, 15.0, 20)
        V_method = default_H.potential(x_test)
        V_expected = default_H.v_abel(x_test) + default_H.epsilon * default_H.v_prime(x_test)
        np.testing.assert_allclose(V_method, V_expected, rtol=1e-10)

    def test_compute_spectrum(self, default_H):
        """compute_spectrum returns correct number of eigenvalues."""
        eigvals, eigvecs = default_H.compute_spectrum(n_eigenvalues=5)
        assert len(eigvals) == 5
        assert eigvecs.shape == (100, 5)

    def test_eigenvalues_real(self, default_H):
        """All eigenvalues are real."""
        eigvals, _ = default_H.compute_spectrum(n_eigenvalues=5)
        assert np.all(np.isreal(eigvals))

    def test_eigenvalues_sorted(self, default_H):
        """Eigenvalues are returned in ascending order."""
        eigvals, _ = default_H.compute_spectrum(n_eigenvalues=10)
        assert np.all(np.diff(eigvals) >= 0)

    def test_eigenvectors_normalized(self, default_H):
        """Eigenvectors are normalized."""
        _, eigvecs = default_H.compute_spectrum(n_eigenvalues=5)
        for i in range(5):
            norm = np.linalg.norm(eigvecs[:, i])
            assert abs(norm - 1.0) < 1e-8

    def test_epsilon_zero_reduces_to_smooth(self):
        """ε = 0 gives Hamiltonian with only V_Abel."""
        H_obj = WuSprungHamiltonian(
            x_min=2.0, x_max=15.0, n_points=50, p_max=10, epsilon=0.0
        )
        np.testing.assert_allclose(H_obj.V, H_obj.V_abel, rtol=1e-10)

    def test_invalid_x_min_raises(self):
        """x_min ≤ 0 should raise ValueError."""
        with pytest.raises(ValueError):
            WuSprungHamiltonian(x_min=0.0)

    def test_invalid_domain_raises(self):
        """x_max ≤ x_min should raise ValueError."""
        with pytest.raises(ValueError):
            WuSprungHamiltonian(x_min=10.0, x_max=5.0)

    def test_repr(self, default_H):
        """__repr__ returns a descriptive string."""
        r = repr(default_H)
        assert "WuSprungHamiltonian" in r
        assert "p_max=20" in r

    def test_positive_eigenvalues(self, default_H):
        """Lowest eigenvalues are positive (confining potential)."""
        eigvals, _ = default_H.compute_spectrum(n_eigenvalues=3)
        assert eigvals[0] > 0, "Lowest eigenvalue must be positive"

    def test_different_epsilon_different_spectrum(self):
        """Different ε values give different spectra."""
        params = dict(x_min=2.0, x_max=20.0, n_points=80, p_max=20)
        H1 = WuSprungHamiltonian(epsilon=0.0, **params)
        H2 = WuSprungHamiltonian(epsilon=1.0, **params)
        e1, _ = H1.compute_spectrum(n_eigenvalues=5)
        e2, _ = H2.compute_spectrum(n_eigenvalues=5)
        # Spectra should differ due to oscillatory correction
        assert not np.allclose(e1, e2, atol=1e-6)


# ---------------------------------------------------------------------------
# 8. Spectrum (standalone function) Tests
# ---------------------------------------------------------------------------

class TestComputeSpectrum:
    """Test standalone compute_spectrum function."""

    def test_returns_sorted(self):
        """compute_spectrum returns sorted eigenvalues."""
        H = np.array([[3.0, 1.0], [1.0, 2.0]])
        eigvals, _ = compute_spectrum(H)
        assert eigvals[0] <= eigvals[1]

    def test_n_eigenvalues_parameter(self):
        """n_eigenvalues parameter limits returned count."""
        n = 20
        H = np.diag(np.arange(1.0, n + 1))
        eigvals, eigvecs = compute_spectrum(H, n_eigenvalues=5)
        assert len(eigvals) == 5
        assert eigvecs.shape == (n, 5)

    def test_all_eigenvalues_when_none(self):
        """n_eigenvalues=None returns all eigenvalues."""
        n = 10
        H = np.diag(np.arange(1.0, n + 1))
        eigvals, _ = compute_spectrum(H, n_eigenvalues=None)
        assert len(eigvals) == n

    def test_symmetric_input(self):
        """Works correctly for symmetric real matrix."""
        A = np.random.default_rng(0).standard_normal((10, 10))
        H = A + A.T  # Make symmetric
        eigvals, eigvecs = compute_spectrum(H)
        assert len(eigvals) == 10
        assert np.all(np.isreal(eigvals))


# ---------------------------------------------------------------------------
# 9. Physical Constants Tests
# ---------------------------------------------------------------------------

class TestConstants:
    """Test QCAL physical constants."""

    def test_fundamental_frequency(self):
        """f₀ = 141.7001 Hz."""
        assert abs(F0 - 141.7001) < 1e-6

    def test_qcal_coherence_constant(self):
        """C_QCAL = 244.36."""
        assert abs(C_QCAL - 244.36) < 1e-6

    def test_pi_value(self):
        """PI is correct."""
        assert abs(PI - np.pi) < 1e-15


# ---------------------------------------------------------------------------
# 10. Integration Tests
# ---------------------------------------------------------------------------

class TestIntegration:
    """Integration tests for the full pipeline."""

    def test_full_pipeline(self):
        """Complete pipeline: construct → spectrum → validate positivity."""
        primes = sieve_primes(30)
        x = np.linspace(2.0, 25.0, 200)

        # Build potential
        V = v_wusprung(x, primes, epsilon=0.5)
        assert V.shape == x.shape
        assert np.all(np.isfinite(V))

        # Build Hamiltonian
        H, _ = construct_hamiltonian(x, primes, epsilon=0.5)
        assert H.shape == (200, 200)
        assert np.max(np.abs(H - H.T)) < 1e-10

        # Compute spectrum
        eigvals, eigvecs = compute_spectrum(H, n_eigenvalues=10)
        assert len(eigvals) == 10
        assert np.all(eigvals > 0)

    def test_class_pipeline(self):
        """WuSprungHamiltonian full pipeline."""
        H = WuSprungHamiltonian(
            x_min=2.0, x_max=20.0, n_points=100, p_max=20, epsilon=1.0
        )
        assert H.n_primes > 0
        eigvals, eigvecs = H.compute_spectrum(n_eigenvalues=5)
        assert len(eigvals) == 5
        assert np.all(eigvals > 0)
        assert np.all(np.isfinite(eigvals))

    def test_prime_encoding_in_potential(self):
        """Primes encode their log-frequencies in V_osc spectrum."""
        x = np.linspace(0.0, 200.0, 20000)
        primes = [2, 3]
        V = v_osc(x, primes, p_max=10)
        dx = x[1] - x[0]
        freqs = np.fft.rfftfreq(len(x), d=dx)
        fft_mag = np.abs(np.fft.rfft(V))

        # Find peaks
        peak_freqs = freqs[np.argsort(fft_mag[1:])[-5:] + 1]

        # Expected frequencies: log(p)/(2*PI)
        expected_freqs = sorted([np.log(p) / (2 * PI) for p in [2, 3]])

        # At least one prime frequency should appear in the top peaks
        found = any(
            any(abs(pf - ef) < 0.05 for ef in expected_freqs)
            for pf in peak_freqs
        )
        assert found, (
            f"Prime frequencies {expected_freqs} not found in V_osc FFT peaks {sorted(peak_freqs)}"
        )

    def test_abel_turning_point_inversion_consistency(self):
        """V_Abel(x_t(E)) ≈ E (inversion consistency)."""
        E_vals = np.array([20.0, 50.0, 100.0, 200.0])
        x_t_vals = abel_turning_point_array(E_vals)
        V_recovered = v_abel_from_turning_point(
            x_t_vals, E_min=1.0, E_max=500.0, n_grid=50000
        )
        # Should recover E within reasonable tolerance of interpolation
        np.testing.assert_allclose(V_recovered, E_vals, rtol=0.05)


if __name__ == "__main__":
    pytest.main([__file__, "-v", "-s"])

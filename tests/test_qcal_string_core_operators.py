#!/usr/bin/env python3
"""
Tests for QCAL-Strings Core: Noetic String Forcing for Navier-Stokes (#260)

Validates:
1. GAMMAS: first 20 Riemann zeros loaded correctly
2. QCALSpectralOperator: modulation_potential, compute_eigenvalue, certify_critical_line
3. string_noetic_forcing: shape, threshold suppression, superradiant gain
4. compute_psi: range, coherence formula
5. rk4_step: incompressibility preservation, shape
6. QCALStringCore: initialization, step, energy_spectrum, summary

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import pytest
import numpy as np
from scipy.fft import fft2, ifft2, fftfreq
import sys
import os

# Ensure repo root is in path (conftest.py normally handles this)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.qcal_string_core import (
    GAMMAS,
    N_ZEROS_DEFAULT,
    PSI_THRESHOLD,
    N_MICROTUBULES_DEFAULT,
    ALPHA_SCALE_DEFAULT,
    HBAR_SI,
    HBAR_NATURAL,
    QCALSpectralOperator,
    QCALStringCore,
    string_noetic_forcing,
    compute_psi,
    rk4_step,
    _GAMMAS_FALLBACK,
)


# ---------------------------------------------------------------------------
# Constants and GAMMAS
# ---------------------------------------------------------------------------

class TestGammas:
    """Tests for the Riemann-zero table GAMMAS."""

    def test_gammas_count(self):
        """GAMMAS should contain N_ZEROS_DEFAULT entries."""
        assert len(GAMMAS) == N_ZEROS_DEFAULT

    def test_gammas_positive(self):
        """All imaginary parts of Riemann zeros are positive."""
        assert np.all(GAMMAS > 0)

    def test_gammas_first_value(self):
        """First Riemann zero ≈ 14.1347 (known to high precision)."""
        assert abs(GAMMAS[0] - 14.134725141734694) < 1e-6

    def test_gammas_increasing(self):
        """Riemann zeros are arranged in increasing order."""
        assert np.all(np.diff(GAMMAS) > 0)

    def test_gammas_fallback_length(self):
        """Fallback table has at least 20 entries."""
        assert len(_GAMMAS_FALLBACK) == 20


class TestConstants:
    """Tests for module-level constants."""

    def test_psi_threshold(self):
        """PSI_THRESHOLD = 0.888."""
        assert PSI_THRESHOLD == pytest.approx(0.888, rel=1e-9)

    def test_hbar_si(self):
        """HBAR_SI ≈ 1.05e-34 J·s."""
        assert HBAR_SI == pytest.approx(1.0545718e-34, rel=1e-6)

    def test_hbar_natural(self):
        """HBAR_NATURAL = 1.0 in natural units."""
        assert HBAR_NATURAL == 1.0

    def test_n_zeros_default(self):
        """N_ZEROS_DEFAULT = 20."""
        assert N_ZEROS_DEFAULT == 20

    def test_alpha_scale_default(self):
        """ALPHA_SCALE_DEFAULT = 0.05."""
        assert ALPHA_SCALE_DEFAULT == pytest.approx(0.05, rel=1e-9)


# ---------------------------------------------------------------------------
# QCALSpectralOperator
# ---------------------------------------------------------------------------

class TestQCALSpectralOperator:
    """Tests for the lightweight spectral operator."""

    @pytest.fixture
    def op(self):
        return QCALSpectralOperator()

    def test_default_f0(self, op):
        """Default f₀ = 141.7001 Hz."""
        assert op.f0 == pytest.approx(141.7001, rel=1e-6)

    def test_default_C(self, op):
        """Default C = 244.36."""
        assert op.C == pytest.approx(244.36, rel=1e-4)

    def test_default_hbar(self, op):
        """Default ℏ = 1 (natural units)."""
        assert op.hbar == 1.0

    def test_modulation_potential_formula(self, op):
        """V_mod = γ · ℏ / C."""
        expected = op.gamma * op.hbar / op.C
        assert op.modulation_potential() == pytest.approx(expected, rel=1e-10)

    def test_modulation_potential_positive(self, op):
        """Modulation potential is positive."""
        assert op.modulation_potential() > 0

    def test_compute_eigenvalue_formula(self, op):
        """λₙ = γₙ · f₀ + V_mod."""
        gamma_n = GAMMAS[0]
        expected = gamma_n * op.f0 + op.modulation_potential()
        assert op.compute_eigenvalue(gamma_n) == pytest.approx(expected, rel=1e-10)

    def test_compute_eigenvalue_positive(self, op):
        """All KK eigenvalues should be positive."""
        for g in GAMMAS[:5]:
            assert op.compute_eigenvalue(g) > 0

    def test_compute_eigenvalue_scaling(self, op):
        """Larger γₙ → larger eigenvalue (monotone in γ)."""
        lambdas = [op.compute_eigenvalue(g) for g in GAMMAS[:5]]
        assert np.all(np.diff(lambdas) > 0)

    def test_certify_critical_line_exact(self, op):
        """At σ = 0.5 exactly, Ψ should be 1.0."""
        status, psi = op.certify_critical_line(0.5)
        assert psi == pytest.approx(1.0, abs=1e-12)
        assert "CRITICAL" in status.upper() or "ON" in status.upper()

    def test_certify_critical_line_off_critical(self, op):
        """Off the critical line, Ψ < 1."""
        _, psi = op.certify_critical_line(0.7)
        assert psi < 1.0
        assert psi > 0.0

    def test_certify_critical_line_decay_monotone(self, op):
        """Coherence decreases as σ moves farther from 0.5."""
        _, psi_05 = op.certify_critical_line(0.5)
        _, psi_06 = op.certify_critical_line(0.6)
        _, psi_07 = op.certify_critical_line(0.7)
        assert psi_05 >= psi_06 >= psi_07

    def test_certify_critical_line_symmetry(self, op):
        """Ψ(σ) = Ψ(1−σ) by symmetry |σ − 0.5|."""
        _, psi_left = op.certify_critical_line(0.3)
        _, psi_right = op.certify_critical_line(0.7)
        assert psi_left == pytest.approx(psi_right, rel=1e-10)

    def test_certify_status_is_string(self, op):
        """certify_critical_line returns a string as first element."""
        result = op.certify_critical_line(0.5)
        assert isinstance(result[0], str)

    def test_custom_decay(self):
        """Custom decay parameter controls coherence drop rate."""
        op_fast = QCALSpectralOperator(decay=1000.0)
        op_slow = QCALSpectralOperator(decay=1.0)
        _, psi_fast = op_fast.certify_critical_line(0.6)
        _, psi_slow = op_slow.certify_critical_line(0.6)
        assert psi_fast < psi_slow

    def test_si_hbar(self):
        """Operator with SI ℏ has tiny V_mod."""
        op_si = QCALSpectralOperator(hbar=HBAR_SI)
        # V_mod = ℏ_SI / C ≈ 4.3e-37 (extremely small)
        assert op_si.modulation_potential() < 1e-30


# ---------------------------------------------------------------------------
# string_noetic_forcing
# ---------------------------------------------------------------------------

class TestStringNoeticForcing:
    """Tests for the KK-mode string forcing function."""

    @pytest.fixture
    def setup(self):
        N = 16
        L = 2 * np.pi
        x = np.linspace(0, L, N, endpoint=False)
        y = np.linspace(0, L, N, endpoint=False)
        xx, yy = np.meshgrid(x, y)
        op = QCALSpectralOperator()
        lambdas = [op.compute_eigenvalue(g) for g in GAMMAS[:5]]
        return xx, yy, op, lambdas

    def test_zero_below_threshold(self, setup):
        """Forcing is zero when Ψ < threshold."""
        xx, yy, op, lambdas = setup
        fx, fy = string_noetic_forcing(0.1, xx, yy, op, 0.5, lambdas)
        assert np.all(fx == 0)
        assert np.all(fy == 0)

    def test_nonzero_above_threshold(self, setup):
        """Forcing is non-zero when Ψ ≥ threshold."""
        xx, yy, op, lambdas = setup
        fx, fy = string_noetic_forcing(0.1, xx, yy, op, 0.9, lambdas)
        assert not np.all(fx == 0)
        assert not np.all(fy == 0)

    def test_output_shape(self, setup):
        """Output arrays have same shape as xx, yy."""
        xx, yy, op, lambdas = setup
        fx, fy = string_noetic_forcing(0.0, xx, yy, op, 0.9, lambdas)
        assert fx.shape == xx.shape
        assert fy.shape == yy.shape

    def test_finite_values(self, setup):
        """Forcing values are finite."""
        xx, yy, op, lambdas = setup
        fx, fy = string_noetic_forcing(1.0, xx, yy, op, 0.95, lambdas)
        assert np.all(np.isfinite(fx))
        assert np.all(np.isfinite(fy))

    def test_superradiant_scaling(self, setup):
        """Forcing amplitude scales with N² (superradiant gain)."""
        xx, yy, op, lambdas = setup
        fx1, _ = string_noetic_forcing(0.0, xx, yy, op, 0.9, lambdas,
                                        N_microtubules=1.0)
        fx2, _ = string_noetic_forcing(0.0, xx, yy, op, 0.9, lambdas,
                                        N_microtubules=2.0)
        # Gain ratio should be (2/1)² = 4
        if np.max(np.abs(fx1)) > 0:
            ratio = np.max(np.abs(fx2)) / np.max(np.abs(fx1))
            assert ratio == pytest.approx(4.0, rel=1e-6)

    def test_psi_squared_scaling(self, setup):
        """Forcing amplitude scales with Ψ²."""
        xx, yy, op, lambdas = setup
        fx_a, _ = string_noetic_forcing(0.0, xx, yy, op, 0.9, lambdas,
                                         N_microtubules=1.0)
        fx_b, _ = string_noetic_forcing(0.0, xx, yy, op, 1.8, lambdas,
                                         N_microtubules=1.0)
        # Ψ doubled → Ψ² quadrupled
        if np.max(np.abs(fx_a)) > 0:
            ratio = np.max(np.abs(fx_b)) / np.max(np.abs(fx_a))
            assert ratio == pytest.approx(4.0, rel=1e-6)

    def test_alpha_scale_controls_amplitude(self, setup):
        """Smaller alpha_scale → smaller forcing."""
        xx, yy, op, lambdas = setup
        fx1, _ = string_noetic_forcing(0.0, xx, yy, op, 0.9, lambdas,
                                        alpha_scale=0.1)
        fx2, _ = string_noetic_forcing(0.0, xx, yy, op, 0.9, lambdas,
                                        alpha_scale=0.05)
        assert np.max(np.abs(fx1)) > np.max(np.abs(fx2))

    def test_empty_lambda_list(self, setup):
        """Empty lambda list → zero forcing."""
        xx, yy, op, _ = setup
        fx, fy = string_noetic_forcing(0.0, xx, yy, op, 0.9, [])
        assert np.all(fx == 0)
        assert np.all(fy == 0)


# ---------------------------------------------------------------------------
# compute_psi
# ---------------------------------------------------------------------------

class TestComputePsi:
    """Tests for the coherence field Ψ computation."""

    @pytest.fixture
    def grid(self):
        N = 16
        L = 2 * np.pi
        x = np.linspace(0, L, N, endpoint=False)
        y = np.linspace(0, L, N, endpoint=False)
        xx, yy = np.meshgrid(x, y)
        op = QCALSpectralOperator()
        return xx, yy, op

    def test_range(self, grid):
        """Ψ ∈ [0, 1] for random velocity field."""
        xx, _, op = grid
        N = xx.shape[0]
        rng = np.random.default_rng(0)
        u = rng.standard_normal((N, N))
        v = rng.standard_normal((N, N))
        psi = compute_psi(u, v, xx, op)
        assert 0.0 <= psi <= 1.0

    def test_type(self, grid):
        """Ψ is a Python float."""
        xx, _, op = grid
        N = xx.shape[0]
        u = np.ones((N, N))
        v = np.ones((N, N))
        psi = compute_psi(u, v, xx, op)
        assert isinstance(psi, float)

    def test_constant_velocity_zero_correlation(self, grid):
        """Constant velocity has zero correlation with the oscillating carrier."""
        xx, _, op = grid
        N = xx.shape[0]
        u = np.ones((N, N))
        v = np.ones((N, N))
        psi = compute_psi(u, v, xx, op)
        # Constant signal → zero Pearson corr → psi_bio = 0
        assert psi == pytest.approx(0.0, abs=1e-12)

    def test_resonant_velocity_higher_psi(self, grid):
        """Velocity field aligned with the carrier should give higher Ψ than random."""
        xx, _, op = grid
        N = xx.shape[0]
        L = 2 * np.pi
        u_resonant = np.sin(2 * np.pi * op.f0 * xx / L)
        v_resonant = np.cos(2 * np.pi * op.f0 * xx / L)
        psi_resonant = compute_psi(u_resonant, v_resonant, xx, op)

        rng = np.random.default_rng(99)
        u_random = rng.standard_normal((N, N))
        v_random = rng.standard_normal((N, N))
        psi_random = compute_psi(u_random, v_random, xx, op)

        # Resonant field should have higher coherence than random
        assert psi_resonant >= psi_random

    def test_finite(self, grid):
        """Ψ is finite for any input."""
        xx, _, op = grid
        N = xx.shape[0]
        rng = np.random.default_rng(7)
        u = rng.standard_normal((N, N)) * 100
        v = rng.standard_normal((N, N)) * 100
        psi = compute_psi(u, v, xx, op)
        assert np.isfinite(psi)


# ---------------------------------------------------------------------------
# rk4_step
# ---------------------------------------------------------------------------

class TestRK4Step:
    """Tests for the RK4 integration step."""

    @pytest.fixture
    def solver_state(self):
        N = 8  # small for speed
        dt = 0.001
        rho = 1.0
        op = QCALSpectralOperator()
        mu = 1.0 / op.f0

        L = 2 * np.pi
        x = np.linspace(0, L, N, endpoint=False)
        y = np.linspace(0, L, N, endpoint=False)
        xx, yy = np.meshgrid(x, y)

        kx = fftfreq(N, d=1.0 / N)
        ky = fftfreq(N, d=1.0 / N)
        kxx, kyy = np.meshgrid(kx, ky)
        k2 = kxx ** 2 + kyy ** 2

        rng = np.random.default_rng(123)
        u0 = rng.standard_normal((N, N)) * 0.01
        v0 = rng.standard_normal((N, N)) * 0.01
        uhat = fft2(u0)
        vhat = fft2(v0)

        grad_px = np.zeros((N, N), dtype=complex)
        grad_py = np.zeros((N, N), dtype=complex)

        lambdas = [op.compute_eigenvalue(g) for g in GAMMAS[:3]]

        return {
            "uhat": uhat, "vhat": vhat, "dt": dt, "rho": rho, "mu": mu,
            "k2": k2, "kxx": kxx, "kyy": kyy,
            "grad_px": grad_px, "grad_py": grad_py,
            "xx": xx, "yy": yy, "op": op, "lambdas": lambdas, "t": 0.0,
        }

    def test_output_shape(self, solver_state):
        """Output Fourier arrays have same shape as input."""
        s = solver_state
        uh_new, vh_new = rk4_step(
            s["uhat"], s["vhat"], s["dt"], s["rho"], s["mu"],
            s["k2"], s["kxx"], s["kyy"],
            s["grad_px"], s["grad_py"],
            s["t"], s["xx"], s["yy"], s["op"], s["lambdas"],
        )
        assert uh_new.shape == s["uhat"].shape
        assert vh_new.shape == s["vhat"].shape

    def test_output_finite(self, solver_state):
        """Output values are finite after one step."""
        s = solver_state
        uh_new, vh_new = rk4_step(
            s["uhat"], s["vhat"], s["dt"], s["rho"], s["mu"],
            s["k2"], s["kxx"], s["kyy"],
            s["grad_px"], s["grad_py"],
            s["t"], s["xx"], s["yy"], s["op"], s["lambdas"],
        )
        assert np.all(np.isfinite(uh_new))
        assert np.all(np.isfinite(vh_new))

    def test_incompressibility_preserved(self, solver_state):
        """After step, the velocity field remains approximately divergence-free."""
        s = solver_state
        uh_new, vh_new = rk4_step(
            s["uhat"], s["vhat"], s["dt"], s["rho"], s["mu"],
            s["k2"], s["kxx"], s["kyy"],
            s["grad_px"], s["grad_py"],
            s["t"], s["xx"], s["yy"], s["op"], s["lambdas"],
        )
        # div(u) in Fourier space = i·(kx·û + ky·v̂)
        div_hat = 1j * (s["kxx"] * uh_new + s["kyy"] * vh_new)
        # Ignore k=0 (mean) mode; check all other modes
        k2 = s["k2"]
        non_dc = k2 > 0
        divergence_error = np.max(np.abs(div_hat[non_dc]))
        assert divergence_error < 1e-8

    def test_output_complex(self, solver_state):
        """Output arrays are complex-valued (Fourier coefficients)."""
        s = solver_state
        uh_new, vh_new = rk4_step(
            s["uhat"], s["vhat"], s["dt"], s["rho"], s["mu"],
            s["k2"], s["kxx"], s["kyy"],
            s["grad_px"], s["grad_py"],
            s["t"], s["xx"], s["yy"], s["op"], s["lambdas"],
        )
        assert uh_new.dtype in [np.complex64, np.complex128]
        assert vh_new.dtype in [np.complex64, np.complex128]


# ---------------------------------------------------------------------------
# QCALStringCore
# ---------------------------------------------------------------------------

class TestQCALStringCore:
    """Tests for the high-level simulation driver."""

    @pytest.fixture
    def core(self):
        return QCALStringCore(N=8, dt=0.005, n_zeros=5)

    def test_initialization(self, core):
        """QCALStringCore initialises without errors."""
        assert core.N == 8
        assert core.dt == pytest.approx(0.005)
        assert core.step_count == 0
        assert core.t == pytest.approx(0.0)

    def test_gammas_loaded(self, core):
        """GAMMAS are loaded for the requested number of zeros."""
        assert len(core.GAMMAS) == 5

    def test_lambda_list_length(self, core):
        """lambda_list matches the number of zeros."""
        assert len(core.lambda_list) == 5

    def test_lambda_positive(self, core):
        """All KK-mode eigenvalues are positive."""
        for lam in core.lambda_list:
            assert lam > 0

    def test_mu_adelic(self, core):
        """Adelic viscosity μ = 1/f₀."""
        assert core.mu == pytest.approx(1.0 / core.op.f0, rel=1e-9)

    def test_single_step(self, core):
        """step() advances time and returns a valid record."""
        record = core.step()
        assert record["step"] == 1
        assert record["t"] == pytest.approx(core.dt, rel=1e-9)
        assert 0.0 <= record["psi"] <= 1.0
        assert np.isfinite(record["emission"])
        assert np.isfinite(record["energy_total"])

    def test_run_multiple_steps(self, core):
        """run(5) returns 5 records and advances step count."""
        history = core.run(5)
        assert len(history) == 5
        assert core.step_count == 5
        assert core.t == pytest.approx(5 * core.dt, rel=1e-6)

    def test_psi_in_range(self, core):
        """Ψ remains in [0, 1] over several steps."""
        history = core.run(3)
        for record in history:
            assert 0.0 <= record["psi"] <= 1.0

    def test_energy_spectrum_shape(self, core):
        """energy_spectrum returns arrays of matching shape."""
        k_bins, E_k = core.energy_spectrum()
        assert len(k_bins) == len(E_k)
        assert len(k_bins) > 0

    def test_energy_spectrum_nonnegative(self, core):
        """Energy spectrum values are non-negative."""
        _, E_k = core.energy_spectrum()
        assert np.all(E_k >= 0)

    def test_summary_keys(self, core):
        """summary() returns a dict with expected keys."""
        s = core.summary()
        expected_keys = {
            "step", "t", "n_zeros", "lambda_1_hz", "f0", "C",
            "mu_adelic", "psi_threshold", "gammas_first3",
        }
        assert expected_keys.issubset(set(s.keys()))

    def test_summary_values(self, core):
        """summary() has plausible values."""
        s = core.summary()
        assert s["f0"] == pytest.approx(141.7001, rel=1e-6)
        assert s["psi_threshold"] == pytest.approx(0.888, rel=1e-9)
        assert s["n_zeros"] == 5
        assert len(s["gammas_first3"]) == 3
        assert s["lambda_1_hz"] > 0

    def test_history_grows(self, core):
        """history list grows with each call to step()."""
        assert len(core.history) == 0
        core.step()
        assert len(core.history) == 1
        core.step()
        assert len(core.history) == 2

    def test_custom_f0(self):
        """Core respects custom f₀."""
        core = QCALStringCore(N=8, f0=200.0, n_zeros=3)
        assert core.op.f0 == pytest.approx(200.0)
        assert core.mu == pytest.approx(1.0 / 200.0, rel=1e-9)


# ---------------------------------------------------------------------------
# Integration: full small simulation
# ---------------------------------------------------------------------------

class TestIntegration:
    """End-to-end integration test for the string core pipeline."""

    def test_short_simulation(self):
        """Run 10 steps with a small grid and verify no numerical blowup."""
        core = QCALStringCore(N=8, dt=0.001, n_zeros=3)
        history = core.run(10)

        # No NaN / Inf in energy
        energies = [h["energy_total"] for h in history]
        assert all(np.isfinite(e) for e in energies)

        # Ψ always in [0, 1]
        psis = [h["psi"] for h in history]
        assert all(0.0 <= p <= 1.0 for p in psis)

    def test_kk_eigenvalue_first_peak(self):
        """λ₁ ≈ γ₁ · f₀ (first photonic peak)."""
        op = QCALSpectralOperator()
        lam1 = op.compute_eigenvalue(GAMMAS[0])
        # λ₁ ≈ 14.1347 × 141.7001 ≈ 2003 Hz (as stated in problem)
        assert lam1 == pytest.approx(GAMMAS[0] * 141.7001 + op.modulation_potential(),
                                      rel=1e-10)
        # Rough numerical check: λ₁ should be ~2003 Hz
        assert 1900 < lam1 < 2200

    def test_string_core_exports(self):
        """Key symbols are accessible from operators package."""
        from operators import (
            GAMMAS as G,
            QCALStringCore as SC,
            string_noetic_forcing as SNF,
            compute_psi_string as CPS,
        )
        assert len(G) == N_ZEROS_DEFAULT
        assert SC is QCALStringCore
        assert SNF is string_noetic_forcing
        assert CPS is compute_psi

#!/usr/bin/env python3
"""
Tests for QCAL Chamber 261 — Tachyonic Censorship & UPE Signal

Validates:
1. tachyonic_censorship() — spectral mode suppression
2. compute_upe_signal() — UPE beat generation via HRV modulation
3. QCALChamber261 solver — RK4 integration with censorship

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
import sys
import os
import importlib.util

_spec = importlib.util.spec_from_file_location(
    "qcal_chamber_261",
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                 "operators", "qcal_chamber_261.py")
)
_chamber_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_chamber_mod)

tachyonic_censorship = _chamber_mod.tachyonic_censorship
compute_upe_signal = _chamber_mod.compute_upe_signal
Chamber261Config = _chamber_mod.Chamber261Config
QCALChamber261 = _chamber_mod.QCALChamber261
run_chamber_261 = _chamber_mod.run_chamber_261
PSI_CENSORSHIP = _chamber_mod.PSI_CENSORSHIP
F_HRV_DEFAULT = _chamber_mod.F_HRV_DEFAULT
LAMBDA_RIEMANN_DEFAULT = _chamber_mod.LAMBDA_RIEMANN_DEFAULT
HBAR_CHAMBER = _chamber_mod.HBAR_CHAMBER
GAMMA_CHAMBER = _chamber_mod.GAMMA_CHAMBER
_C_CHAMBER = _chamber_mod._C_CHAMBER


# ---------------------------------------------------------------------------
# Tests for tachyonic_censorship
# ---------------------------------------------------------------------------

class TestTachyonicCensorship:
    """Tests for the tachyonic_censorship() function."""

    def _make_grids(self, N=8):
        """Helper: build 2-D wavenumber meshgrids of size N×N."""
        kx = np.fft.fftfreq(N) * N
        ky = np.fft.fftfreq(N) * N
        kxx, kyy = np.meshgrid(kx, ky, indexing='ij')
        return kxx, kyy

    def test_output_shape(self):
        """Output shape must match input shape."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.ones((N, N), dtype=complex)
        result = tachyonic_censorship(field, kxx, kyy)
        assert result.shape == field.shape

    def test_dc_mode_preserved(self):
        """DC mode (k=0) should have σ = 1/2 → Ψ = 1 → always certified."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.zeros((N, N), dtype=complex)
        field[0, 0] = 1.0 + 0j  # DC component only
        result = tachyonic_censorship(field, kxx, kyy)
        # DC mode: k=0, σ_mapped = 0.5, |σ−0.5| = 0, Ψ = 1.0 ≥ 0.888
        assert abs(result[0, 0]) == pytest.approx(1.0, rel=1e-9)

    def test_high_k_modes_censored(self):
        """High-k modes map to σ close to 1, so they should be zeroed."""
        N = 16
        kxx, kyy = self._make_grids(N)
        field = np.ones((N, N), dtype=complex)
        result = tachyonic_censorship(field, kxx, kyy)
        # Not all modes should be non-zero — some must be censored
        assert np.any(result == 0.0), "Expected some modes to be censored"

    def test_certified_modes_nonzero(self):
        """Low-k certified modes must survive (non-zero)."""
        N = 16
        kxx, kyy = self._make_grids(N)
        field = np.zeros((N, N), dtype=complex)
        # Set only the DC and near-DC modes
        field[0, 0] = 1.0
        field[0, 1] = 0.5
        result = tachyonic_censorship(field, kxx, kyy)
        # DC mode must be non-zero
        assert abs(result[0, 0]) > 0.0

    def test_returns_copy_not_inplace(self):
        """tachyonic_censorship must not modify the input array."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.ones((N, N), dtype=complex)
        original = field.copy()
        tachyonic_censorship(field, kxx, kyy)
        np.testing.assert_array_equal(field, original)

    def test_shape_mismatch_raises(self):
        """Mismatched shapes must raise ValueError."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.ones((N + 1, N), dtype=complex)
        with pytest.raises(ValueError, match="shape"):
            tachyonic_censorship(field, kxx, kyy)

    def test_zero_gamma_raises(self):
        """gamma=0 must raise ValueError (division by zero in decay rate)."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.ones((N, N), dtype=complex)
        with pytest.raises(ValueError, match="gamma"):
            tachyonic_censorship(field, kxx, kyy, gamma=0.0)

    def test_zero_hbar_raises(self):
        """hbar=0 must raise ValueError."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.ones((N, N), dtype=complex)
        with pytest.raises(ValueError, match="hbar"):
            tachyonic_censorship(field, kxx, kyy, hbar=0.0)

    def test_all_zero_field(self):
        """Zero field input must return zero field."""
        N = 8
        kxx, kyy = self._make_grids(N)
        field = np.zeros((N, N), dtype=complex)
        result = tachyonic_censorship(field, kxx, kyy)
        np.testing.assert_array_equal(result, np.zeros((N, N), dtype=complex))

    def test_mask_is_binary(self):
        """The censorship mask must be binary (0 or 1) — no partial damping."""
        N = 16
        kxx, kyy = self._make_grids(N)
        # Use a constant field so we can check the mask directly
        field = np.ones((N, N), dtype=complex)
        result = tachyonic_censorship(field, kxx, kyy)
        # Each entry must be either 0 or 1
        for val in result.ravel():
            assert val == pytest.approx(0.0, abs=1e-12) or \
                   val == pytest.approx(1.0, abs=1e-12), \
                   f"Expected 0 or 1, got {val}"

    def test_custom_threshold_less_restrictive(self):
        """Lower psi_threshold should certify more modes than the default."""
        N = 16
        kxx, kyy = self._make_grids(N)
        field = np.ones((N, N), dtype=complex)
        result_strict = tachyonic_censorship(field, kxx, kyy, psi_threshold=0.999)
        result_loose = tachyonic_censorship(field, kxx, kyy, psi_threshold=0.001)
        n_certified_strict = int(np.sum(np.abs(result_strict)))
        n_certified_loose = int(np.sum(np.abs(result_loose)))
        assert n_certified_loose >= n_certified_strict


# ---------------------------------------------------------------------------
# Tests for compute_upe_signal
# ---------------------------------------------------------------------------

class TestComputeUPESignal:
    """Tests for the compute_upe_signal() function."""

    def test_returns_scalar(self):
        """Output must be a scalar float."""
        val = compute_upe_signal(0.0)
        assert isinstance(val, float)

    def test_zero_at_t0_with_default_params(self):
        """At t=0, sin(2π·λ·0) = 0 for all λ → UPE(0) = 0."""
        val = compute_upe_signal(0.0)
        assert val == pytest.approx(0.0, abs=1e-12)

    def test_finite_at_nonzero_t(self):
        """UPE signal must be finite for t > 0."""
        val = compute_upe_signal(1.0)
        assert np.isfinite(val)

    def test_amplitude_bounded(self):
        """Max amplitude is bounded by alpha_scale * sum(1/(n+1)) ~ O(alpha_scale)."""
        max_val = max(abs(compute_upe_signal(t)) for t in np.linspace(0.001, 10, 500))
        # Theoretical max: alpha_scale * H_N * 1 (HRV max = 1)
        n = len(LAMBDA_RIEMANN_DEFAULT)
        harmonic = sum(1.0 / (k + 1) for k in range(n))
        upper_bound = 0.05 * harmonic  # alpha_scale * harmonic number
        assert max_val < upper_bound + 1e-10

    def test_custom_lambda_list(self):
        """Custom lambda list must be used correctly."""
        val = compute_upe_signal(0.5, lambda_list=[14.134725])
        assert np.isfinite(val)

    def test_empty_lambda_list_raises(self):
        """Empty lambda_list must raise ValueError."""
        with pytest.raises(ValueError, match="lambda_list"):
            compute_upe_signal(1.0, lambda_list=[])

    def test_modulation_by_hrv(self):
        """UPE is zero when HRV carrier is zero (integer multiples of 1/f_HRV)."""
        # sin(2π * f_HRV * t) = 0 when t = k / f_HRV for k integer
        f_hrv = 0.1
        t_zero = 1.0 / f_hrv  # t = 10 → sin(2π * 0.1 * 10) = sin(2π) = 0
        val = compute_upe_signal(t_zero, f_hrv=f_hrv)
        assert val == pytest.approx(0.0, abs=1e-8)

    def test_alpha_scale_scales_amplitude(self):
        """Doubling alpha_scale should double the amplitude."""
        t = 0.5
        val1 = compute_upe_signal(t, alpha_scale=0.05)
        val2 = compute_upe_signal(t, alpha_scale=0.10)
        if abs(val1) > 1e-12:
            assert val2 == pytest.approx(2.0 * val1, rel=1e-9)

    def test_reproducible_at_same_t(self):
        """Same input must always yield the same output (deterministic)."""
        t = 3.14159
        assert compute_upe_signal(t) == compute_upe_signal(t)


# ---------------------------------------------------------------------------
# Tests for QCALChamber261 solver
# ---------------------------------------------------------------------------

class TestQCALChamber261:
    """Tests for the QCALChamber261 RK4 solver."""

    def test_initialize_default(self):
        """Solver can be initialized without arguments."""
        solver = QCALChamber261()
        solver.initialize()
        assert solver._omega is not None

    def test_initialize_custom_omega(self):
        """Custom omega0 is accepted and stored."""
        N = 8
        cfg = Chamber261Config(N=N)
        solver = QCALChamber261(config=cfg)
        omega0 = np.ones((N, N))
        solver.initialize(omega0=omega0)
        np.testing.assert_array_equal(solver._omega, omega0)

    def test_initialize_wrong_shape_raises(self):
        """Wrong omega0 shape must raise ValueError."""
        N = 8
        cfg = Chamber261Config(N=N)
        solver = QCALChamber261(config=cfg)
        with pytest.raises(ValueError, match="shape"):
            solver.initialize(omega0=np.ones((N + 1, N)))

    def test_step_without_initialize_raises(self):
        """step() before initialize() must raise RuntimeError."""
        solver = QCALChamber261()
        with pytest.raises(RuntimeError, match="initialize"):
            solver.step(0.0)

    def test_run_without_initialize_raises(self):
        """run() before initialize() must raise RuntimeError."""
        solver = QCALChamber261()
        with pytest.raises(RuntimeError, match="initialize"):
            solver.run(n_steps=10)

    def test_step_returns_diagnostics(self):
        """step() must return dict with psi, upe_emission, entropy."""
        solver = QCALChamber261()
        solver.initialize()
        diag = solver.step(0.0)
        assert 'psi' in diag
        assert 'upe_emission' in diag
        assert 'entropy' in diag

    def test_psi_in_range(self):
        """Ψ diagnostic must be in [0, 1]."""
        N = 8
        cfg = Chamber261Config(N=N)
        solver = QCALChamber261(config=cfg)
        solver.initialize()
        for i in range(20):
            diag = solver.step(i * cfg.dt)
            assert 0.0 <= diag['psi'] <= 1.0

    def test_omega_remains_finite(self):
        """Vorticity field must stay finite after multiple steps."""
        N = 16
        cfg = Chamber261Config(N=N, dt=0.001)
        solver = QCALChamber261(config=cfg)
        solver.initialize()
        for i in range(50):
            solver.step(i * cfg.dt)
        assert np.all(np.isfinite(solver._omega))

    def test_run_returns_history(self):
        """run() must return history with non-empty lists."""
        N = 8
        cfg = Chamber261Config(N=N, dt=0.01)
        solver = QCALChamber261(config=cfg)
        solver.initialize()
        result = solver.run(n_steps=30, log_interval=5)
        assert 'history' in result
        assert len(result['history']['psi']) > 0

    def test_run_returns_omega_final(self):
        """run() must return omega_final with correct shape."""
        N = 8
        cfg = Chamber261Config(N=N)
        solver = QCALChamber261(config=cfg)
        solver.initialize()
        result = solver.run(n_steps=10, log_interval=5)
        assert result['omega_final'].shape == (N, N)


# ---------------------------------------------------------------------------
# Tests for run_chamber_261 convenience wrapper
# ---------------------------------------------------------------------------

class TestRunChamber261:
    """Tests for the run_chamber_261() module-level function."""

    def test_basic_run(self):
        """run_chamber_261 must complete without errors."""
        result = run_chamber_261(n_steps=20, N=8, log_interval=5)
        assert 'history' in result
        assert 'omega_final' in result
        assert 'config' in result

    def test_omega_final_shape(self):
        """Final vorticity must have correct shape."""
        N = 8
        result = run_chamber_261(n_steps=10, N=N, log_interval=5)
        assert result['omega_final'].shape == (N, N)

    def test_history_psi_values_valid(self):
        """All logged Ψ values must be in [0, 1]."""
        result = run_chamber_261(n_steps=40, N=8, log_interval=5)
        for psi_val in result['history']['psi']:
            assert 0.0 <= psi_val <= 1.0

    def test_config_returned(self):
        """Config object must be present and have correct N."""
        N = 8
        result = run_chamber_261(n_steps=10, N=N, log_interval=5)
        assert result['config'].N == N

    def test_custom_omega0(self):
        """Custom omega0 can be passed to run_chamber_261."""
        N = 8
        omega0 = np.zeros((N, N))
        result = run_chamber_261(n_steps=10, N=N, log_interval=5, omega0=omega0)
        assert result['omega_final'].shape == (N, N)


# ---------------------------------------------------------------------------
# Tests for module-level constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Tests for Chamber 261 module constants."""

    def test_psi_censorship_value(self):
        """PSI_CENSORSHIP threshold must be 0.888."""
        assert PSI_CENSORSHIP == pytest.approx(0.888, rel=1e-6)

    def test_f_hrv_default(self):
        """Default HRV frequency must be 0.1 Hz."""
        assert F_HRV_DEFAULT == pytest.approx(0.1, rel=1e-9)

    def test_lambda_riemann_default_length(self):
        """Default λ list must have 10 entries."""
        assert len(LAMBDA_RIEMANN_DEFAULT) == 10

    def test_lambda_riemann_first_zero(self):
        """First Riemann zero imaginary part must be ~14.134725."""
        assert LAMBDA_RIEMANN_DEFAULT[0] == pytest.approx(14.134725, rel=1e-5)

    def test_c_chamber_value(self):
        """QCAL coherence constant must be 244.36."""
        assert _C_CHAMBER == pytest.approx(244.36, rel=1e-6)

    def test_hbar_is_one(self):
        """Natural-unit ℏ must be 1.0."""
        assert HBAR_CHAMBER == pytest.approx(1.0, rel=1e-12)

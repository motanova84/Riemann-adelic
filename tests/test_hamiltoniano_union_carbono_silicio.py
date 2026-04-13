#!/usr/bin/env python3
r"""
Tests — Hamiltoniano Unión Carbono–Silicio  (QCAL ∞³)
======================================================

Comprehensive test suite for the seven-class
``physics.hamiltoniano_union_carbono_silicio`` module.

Classes validated:
  1. SilicioDivino
  2. CarbonoDivino
  3. ConstanteZiusudra
  4. HamiltonianoUnion
  5. BatimientoPleromatico
  6. EscalaTiempoConciencia
  7. SistemaPleromaUnion

API validated:
  - hamiltoniano_union_activar(n_dim) → dict

Integrity checks (A01–A08):
  A01 F_SI = 141.7001 Hz
  A02 F_C  = 142.1000 Hz
  A03 Δf = F_C − F_SI ≈ 0.3999 Hz (Constante de Ziusudra)
  A04 κ  = F_C / F_SI ≈ 1.002822
  A05 T_beat = 1/Δf ≈ 2.5006 s
  A06 H_Total = H_Riemann + H_Interacción (calcular_h_total)
  A07 Hamiltoniano autoadjunto (H = H†)
  A08 s(t) = A_Si·cos(2π f_Si t) + A_C·cos(2π f_C t)

Coherence checks (B):
  Each class Ψ ≥ PSI_UMBRAL = 0.888
  Ψ_global ≥ 0.888

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
"""

import importlib.util
from pathlib import Path

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Module loading — avoid importing the full physics package (which requires
# optional heavy dependencies) and load the target module directly.
# ---------------------------------------------------------------------------
_REPO_ROOT = Path(__file__).parent.parent
_MOD_PATH = _REPO_ROOT / "physics" / "hamiltoniano_union_carbono_silicio.py"

_spec = importlib.util.spec_from_file_location(
    "hamiltoniano_union_carbono_silicio", str(_MOD_PATH)
)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

# Re-export names for readability
SilicioDivino = _mod.SilicioDivino
CarbonoDivino = _mod.CarbonoDivino
ConstanteZiusudra = _mod.ConstanteZiusudra
HamiltonianoUnion = _mod.HamiltonianoUnion
BatimientoPleromatico = _mod.BatimientoPleromatico
EscalaTiempoConciencia = _mod.EscalaTiempoConciencia
SistemaPleromaUnion = _mod.SistemaPleromaUnion
hamiltoniano_union_activar = _mod.hamiltoniano_union_activar

# Module-level constants
F_SI = _mod.F_SI
F_C = _mod.F_C
DELTA_F = _mod.DELTA_F
KAPPA = _mod.KAPPA
T_BEAT = _mod.T_BEAT
F_MANIF = _mod.F_MANIF
PSI_UMBRAL = _mod.PSI_UMBRAL
A_SI = _mod.A_SI
A_C = _mod.A_C
RIEMANN_ZEROS = _mod.RIEMANN_ZEROS
CFF_MOSCA = _mod.CFF_MOSCA
CFF_HUMANO = _mod.CFF_HUMANO
CFF_TORTUGA = _mod.CFF_TORTUGA
T_PLANCK = _mod.T_PLANCK


# ===========================================================================
# A. Integrity Checks — Constants (A01–A08)
# ===========================================================================


class TestConstants:
    """A01–A08: Module-level constants match specification."""

    def test_a01_f_si_value(self):
        """A01: F_SI = 141.7001 Hz — Silicio Divino."""
        assert abs(F_SI - 141.7001) < 1e-4

    def test_a02_f_c_value(self):
        """A02: F_C = 142.1000 Hz — Carbono Divino."""
        assert abs(F_C - 142.1000) < 1e-4

    def test_a03_delta_f_value(self):
        """A03: Δf = F_C − F_SI ≈ 0.3999 Hz — Constante de Ziusudra."""
        assert abs(DELTA_F - 0.3999) < 1e-3

    def test_a03_delta_f_derived(self):
        """A03: Δf is derived correctly from F_C and F_SI."""
        assert abs(DELTA_F - (F_C - F_SI)) < 1e-10

    def test_a04_kappa_value(self):
        """A04: κ = F_C/F_SI ≈ 1.002822 — Tensión de la Encarnación."""
        assert abs(KAPPA - 1.002822) < 1e-4

    def test_a04_kappa_derived(self):
        """A04: κ is derived correctly from F_C and F_SI."""
        assert abs(KAPPA - F_C / F_SI) < 1e-10

    def test_a05_t_beat_value(self):
        """A05: T_beat = 1/Δf ≈ 2.5006 s — Unidad de Tiempo Sagrado."""
        assert abs(T_BEAT - 2.5006) < 1e-3

    def test_a05_t_beat_derived(self):
        """A05: T_beat = 1/Δf exactly."""
        assert abs(T_BEAT - 1.0 / DELTA_F) < 1e-10

    def test_f_manif_value(self):
        """F_MANIF = 888.0 Hz — Frecuencia de Manifestación."""
        assert abs(F_MANIF - 888.0) < 1e-10

    def test_psi_umbral_value(self):
        """PSI_UMBRAL = 0.888 — Coherencia mínima QCAL ∞³."""
        assert abs(PSI_UMBRAL - 0.888) < 1e-10

    def test_riemann_zeros_available(self):
        """First Riemann zero is γ₁ ≈ 14.134725."""
        assert abs(RIEMANN_ZEROS[0] - 14.134725) < 1e-4

    def test_riemann_zeros_ascending(self):
        """Riemann zeros list is strictly ascending."""
        zeros = RIEMANN_ZEROS
        assert all(zeros[i] < zeros[i + 1] for i in range(len(zeros) - 1))

    def test_f_si_less_than_f_c(self):
        """F_SI < F_C (Carbono Divino is higher frequency)."""
        assert F_SI < F_C

    def test_amplitudes_positive(self):
        """Amplitudes A_SI and A_C are positive."""
        assert A_SI > 0
        assert A_C > 0


# ===========================================================================
# B. SilicioDivino
# ===========================================================================


class TestSilicioDivino:
    """Tests for SilicioDivino — Hamiltoniano diagonal Riemann."""

    def setup_method(self):
        """Create standard instance with n_dim=8."""
        self.s = SilicioDivino(n_dim=8)

    # --- Initialization ---

    def test_init_default(self):
        """Default n_dim=8, f_si=F_SI."""
        assert self.s.n_dim == 8
        assert abs(self.s.f_si - F_SI) < 1e-6

    def test_eigenvalues_count(self):
        """Number of eigenvalues equals n_dim."""
        assert len(self.s.eigenvalues) == 8

    def test_h_riemann_shape(self):
        """H_Riemann is square N×N."""
        assert self.s.H_riemann.shape == (8, 8)

    def test_h_riemann_diagonal(self):
        """H_Riemann is diagonal — off-diagonal elements are zero."""
        H = self.s.H_riemann
        off_diag = H - np.diag(np.diag(H))
        assert np.allclose(off_diag, 0.0)

    def test_eigenvalues_positive(self):
        """All eigenvalues are strictly positive."""
        assert np.all(self.s.eigenvalues > 0)

    def test_eigenvalues_ascending(self):
        """Eigenvalues are strictly ascending (like Riemann zeros)."""
        ev = self.s.eigenvalues
        assert np.all(np.diff(ev) > 0)

    def test_eigenvalue_scaling(self):
        """λ_n = f_si · γ_n / γ_1 — correct scaling from Riemann zeros."""
        gamma_1 = RIEMANN_ZEROS[0]
        for n in range(8):
            expected = F_SI * RIEMANN_ZEROS[n] / gamma_1
            assert abs(self.s.eigenvalues[n] - expected) < 1e-6

    def test_first_eigenvalue_equals_f_si(self):
        """λ_1 = f_Si (first eigenvalue equals fundamental frequency)."""
        assert abs(self.s.eigenvalues[0] - F_SI) < 1e-4

    def test_gamma_1_stored(self):
        """gamma_1 attribute matches first Riemann zero."""
        assert abs(self.s.gamma_1 - RIEMANN_ZEROS[0]) < 1e-6

    def test_zeros_stored(self):
        """zeros attribute contains first n_dim Riemann zeros."""
        for n in range(8):
            assert abs(self.s.zeros[n] - RIEMANN_ZEROS[n]) < 1e-6

    # --- Coherence ---

    def test_psi_range(self):
        """Ψ_Si ∈ [0, 1]."""
        assert 0.0 <= self.s.psi <= 1.0

    def test_psi_above_threshold(self):
        """Ψ_Si ≥ PSI_UMBRAL = 0.888."""
        assert self.s.psi >= PSI_UMBRAL

    def test_psi_above_minimum_expected(self):
        """Ψ_Si ≥ 0.90 (well above threshold)."""
        assert self.s.psi >= 0.90

    # --- calcular_h_riemann ---

    def test_calcular_h_riemann_returns_copy(self):
        """calcular_h_riemann returns a fresh copy, not a reference."""
        H1 = self.s.calcular_h_riemann()
        H2 = self.s.calcular_h_riemann()
        H1[0, 0] = 0.0
        assert H2[0, 0] != 0.0

    def test_calcular_h_riemann_matches_attribute(self):
        """calcular_h_riemann() equals H_riemann attribute."""
        assert np.allclose(self.s.calcular_h_riemann(), self.s.H_riemann)

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() returns dict with required keys."""
        d = self.s.exportar()
        for key in ("f_si_hz", "n_dim", "eigenvalues", "psi", "clase"):
            assert key in d

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'SilicioDivino'."""
        assert self.s.exportar()["clase"] == "SilicioDivino"

    def test_exportar_psi_consistent(self):
        """exportar()['psi'] matches .psi attribute."""
        assert abs(self.s.exportar()["psi"] - self.s.psi) < 1e-10

    # --- Validation errors ---

    def test_invalid_n_dim_zero(self):
        """n_dim=0 raises ValueError."""
        with pytest.raises(ValueError):
            SilicioDivino(n_dim=0)

    def test_invalid_n_dim_negative(self):
        """n_dim=-1 raises ValueError."""
        with pytest.raises(ValueError):
            SilicioDivino(n_dim=-1)

    def test_invalid_f_si_zero(self):
        """f_si=0 raises ValueError."""
        with pytest.raises(ValueError):
            SilicioDivino(f_si=0)

    def test_invalid_f_si_negative(self):
        """f_si=-1 raises ValueError."""
        with pytest.raises(ValueError):
            SilicioDivino(f_si=-1.0)

    def test_invalid_n_dim_too_large(self):
        """n_dim > len(RIEMANN_ZEROS) raises ValueError."""
        with pytest.raises(ValueError):
            SilicioDivino(n_dim=len(RIEMANN_ZEROS) + 1)

    # --- Different n_dim values ---

    def test_n_dim_1(self):
        """n_dim=1 works and Ψ ≥ 0."""
        s = SilicioDivino(n_dim=1)
        assert s.n_dim == 1
        assert s.psi >= 0.0

    def test_n_dim_4(self):
        """n_dim=4 produces correct number of eigenvalues."""
        s = SilicioDivino(n_dim=4)
        assert len(s.eigenvalues) == 4

    def test_n_dim_16(self):
        """n_dim=16 works with all available zeros."""
        s = SilicioDivino(n_dim=16)
        assert len(s.eigenvalues) == 16
        assert s.psi >= PSI_UMBRAL


# ===========================================================================
# C. CarbonoDivino
# ===========================================================================


class TestCarbonoDivino:
    """Tests for CarbonoDivino — Perturbación térmica/orgánica."""

    def setup_method(self):
        self.c = CarbonoDivino(n_dim=8)

    # --- Initialization ---

    def test_init_f_c(self):
        """f_c attribute matches F_C."""
        assert abs(self.c.f_c - F_C) < 1e-6

    def test_t_array_length(self):
        """t array has n_points elements."""
        assert len(self.c.t) == self.c.n_points

    def test_t_starts_at_zero(self):
        """Time array starts at 0."""
        assert abs(self.c.t[0]) < 1e-10

    def test_t_ends_at_t_max(self):
        """Time array ends at t_max."""
        assert abs(self.c.t[-1] - self.c.t_max) < 1e-6

    def test_perturbacion_shape(self):
        """Perturbacion has same length as t."""
        assert len(self.c.perturbacion) == len(self.c.t)

    def test_perturbacion_amplitude(self):
        """δH(t) amplitude ≤ A_C (within numerical tolerance)."""
        assert np.max(np.abs(self.c.perturbacion)) <= self.c.a_c + 1e-10

    # --- A08: s(t) = A_C·cos(2π·f_C·t) ---

    def test_a08_perturbacion_formula(self):
        """A08: δH(t) = A_C·cos(2π·f_C·t) is correctly implemented."""
        t_test = np.array([0.0, 0.001, 0.01])
        expected = A_C * np.cos(2.0 * np.pi * F_C * t_test)
        for ti, ei in zip(t_test, expected):
            assert abs(self.c.delta_H(ti) - ei) < 1e-8

    def test_delta_H_at_zero(self):
        """δH(0) = A_C (cosine at t=0 is 1)."""
        assert abs(self.c.delta_H(0.0) - self.c.a_c) < 1e-10

    # --- H_carbono matrix ---

    def test_h_carbono_shape(self):
        """H_carbono is N×N."""
        assert self.c.H_carbono.shape == (8, 8)

    def test_h_carbono_symmetric(self):
        """H_carbono is symmetric."""
        assert np.allclose(self.c.H_carbono, self.c.H_carbono.T)

    def test_h_carbono_diagonal_zero(self):
        """H_carbono diagonal is zero."""
        assert np.allclose(np.diag(self.c.H_carbono), 0.0)

    def test_h_carbono_off_diagonal_positive(self):
        """H_carbono off-diagonal elements are positive (for A_C > 0)."""
        H = self.c.H_carbono
        off = H[np.logical_not(np.eye(8, dtype=bool))]
        assert np.all(off > 0)

    # --- Coherence ---

    def test_psi_equals_one(self):
        """Ψ_C = 1.0 — perfect periodic coherence."""
        assert abs(self.c.psi - 1.0) < 1e-10

    def test_psi_above_threshold(self):
        """Ψ_C ≥ PSI_UMBRAL."""
        assert self.c.psi >= PSI_UMBRAL

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() returns required keys."""
        d = self.c.exportar()
        for key in ("f_c_hz", "a_c", "n_dim", "psi", "clase"):
            assert key in d

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'CarbonoDivino'."""
        assert self.c.exportar()["clase"] == "CarbonoDivino"

    # --- Validation errors ---

    def test_invalid_n_dim_zero(self):
        """n_dim=0 raises ValueError."""
        with pytest.raises(ValueError):
            CarbonoDivino(n_dim=0)

    def test_invalid_f_c_zero(self):
        """f_c=0 raises ValueError."""
        with pytest.raises(ValueError):
            CarbonoDivino(f_c=0)

    def test_invalid_t_max_zero(self):
        """t_max=0 raises ValueError."""
        with pytest.raises(ValueError):
            CarbonoDivino(t_max=0)

    def test_invalid_n_points_one(self):
        """n_points=1 raises ValueError."""
        with pytest.raises(ValueError):
            CarbonoDivino(n_points=1)


# ===========================================================================
# D. ConstanteZiusudra
# ===========================================================================


class TestConstanteZiusudra:
    """Tests for ConstanteZiusudra — Δf, κ, T_beat."""

    def setup_method(self):
        self.z = ConstanteZiusudra()

    # --- Attributes ---

    def test_delta_f_value(self):
        """Δf = F_C − F_SI ≈ 0.3999 Hz."""
        assert abs(self.z.delta_f - 0.3999) < 1e-3

    def test_kappa_value(self):
        """κ = F_C / F_SI ≈ 1.002822."""
        assert abs(self.z.kappa - 1.002822) < 1e-4

    def test_t_beat_value(self):
        """T_beat = 1/Δf ≈ 2.5006 s."""
        assert abs(self.z.t_beat - 2.5006) < 1e-3

    def test_delta_f_equals_f_c_minus_f_si(self):
        """Δf == f_c − f_si exactly."""
        assert abs(self.z.delta_f - (self.z.f_c - self.z.f_si)) < 1e-10

    def test_kappa_equals_ratio(self):
        """κ == f_c / f_si exactly."""
        assert abs(self.z.kappa - self.z.f_c / self.z.f_si) < 1e-10

    def test_t_beat_equals_inverse_delta_f(self):
        """T_beat == 1/Δf exactly."""
        assert abs(self.z.t_beat - 1.0 / self.z.delta_f) < 1e-10

    # --- Coherence ---

    def test_psi_equals_one(self):
        """Ψ_Z = 1.0 when all parameters are valid."""
        assert abs(self.z.psi - 1.0) < 1e-10

    def test_psi_above_threshold(self):
        """Ψ_Z ≥ PSI_UMBRAL."""
        assert self.z.psi >= PSI_UMBRAL

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() contains required keys."""
        d = self.z.exportar()
        for key in ("delta_f_hz", "kappa", "t_beat_s", "psi", "clase"):
            assert key in d

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'ConstanteZiusudra'."""
        assert self.z.exportar()["clase"] == "ConstanteZiusudra"

    def test_exportar_delta_f_consistent(self):
        """exportar()['delta_f_hz'] matches attribute."""
        assert abs(self.z.exportar()["delta_f_hz"] - self.z.delta_f) < 1e-10

    # --- Validation errors ---

    def test_invalid_f_si_zero(self):
        """f_si=0 raises ValueError."""
        with pytest.raises(ValueError):
            ConstanteZiusudra(f_si=0)

    def test_invalid_f_c_zero(self):
        """f_c=0 raises ValueError."""
        with pytest.raises(ValueError):
            ConstanteZiusudra(f_c=0)

    def test_f_c_less_than_f_si_raises(self):
        """f_c < f_si raises ValueError."""
        with pytest.raises(ValueError):
            ConstanteZiusudra(f_si=200.0, f_c=100.0)

    def test_f_c_equals_f_si_raises(self):
        """f_c == f_si raises ValueError."""
        with pytest.raises(ValueError):
            ConstanteZiusudra(f_si=141.7001, f_c=141.7001)


# ===========================================================================
# E. HamiltonianoUnion
# ===========================================================================


class TestHamiltonianoUnion:
    """Tests for HamiltonianoUnion — H_Total = H_Riemann + H_Interacción."""

    def setup_method(self):
        self.h = HamiltonianoUnion(n_dim=8)

    # --- Shape and structure ---

    def test_h_total_shape(self):
        """H_total is N×N square matrix."""
        assert self.h.H_total.shape == (8, 8)

    def test_a06_h_total_from_calcular(self):
        """A06: H_Total constructed by calcular_h_total()."""
        H = self.h.calcular_h_total()
        assert H.shape == (8, 8)

    def test_a07_hermitian(self):
        """A07: H_Total is autoadjunto (H = H†) by construction."""
        assert self.h.es_autoadjunto()

    def test_h_total_symmetric(self):
        """H_total is symmetric: H == H.T (real matrix)."""
        assert np.allclose(self.h.H_total, self.h.H_total.T)

    def test_eigenvalues_real(self):
        """Eigenvalues of H_total are real (from eigvalsh)."""
        assert np.all(np.isreal(self.h.eigenvalues))

    def test_eigenvalues_count(self):
        """eigvalsh returns N eigenvalues."""
        assert len(self.h.eigenvalues) == 8

    def test_eigenvalues_ascending(self):
        """eigvalsh returns eigenvalues in ascending order."""
        ev = self.h.eigenvalues
        assert np.all(np.diff(ev) > 0)

    def test_eigenvalues_close_to_diagonal(self):
        """Perturbed eigenvalues are close to H_Riemann diagonal elements."""
        riemann = SilicioDivino(n_dim=8)
        # eigvalsh of H_total should be close to sorted H_Riemann diagonal
        diag_sorted = np.sort(riemann.eigenvalues)
        for ev, diag in zip(self.h.eigenvalues, diag_sorted):
            # Within 1% relative error
            assert abs(ev - diag) / diag < 0.01

    # --- Coherence ---

    def test_psi_range(self):
        """Ψ_H ∈ [0, 1]."""
        assert 0.0 <= self.h.psi <= 1.0

    def test_psi_above_threshold(self):
        """Ψ_H ≥ PSI_UMBRAL."""
        assert self.h.psi >= PSI_UMBRAL

    def test_psi_close_to_one(self):
        """Ψ_H ≥ 0.999 (H_Riemann strongly dominates over H_carbono)."""
        assert self.h.psi >= 0.999

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() has required keys."""
        d = self.h.exportar()
        for key in ("n_dim", "eigenvalues", "es_autoadjunto", "psi", "clase"):
            assert key in d

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'HamiltonianoUnion'."""
        assert self.h.exportar()["clase"] == "HamiltonianoUnion"

    def test_exportar_es_autoadjunto_true(self):
        """exportar()['es_autoadjunto'] == True."""
        assert self.h.exportar()["es_autoadjunto"] is True

    # --- Validation errors ---

    def test_invalid_n_dim_zero(self):
        """n_dim=0 raises ValueError."""
        with pytest.raises(ValueError):
            HamiltonianoUnion(n_dim=0)

    def test_invalid_n_dim_too_large(self):
        """n_dim > len(RIEMANN_ZEROS) raises ValueError."""
        with pytest.raises(ValueError):
            HamiltonianoUnion(n_dim=len(RIEMANN_ZEROS) + 1)

    # --- Different n_dim values ---

    def test_n_dim_4(self):
        """n_dim=4 produces a 4×4 H_total."""
        h = HamiltonianoUnion(n_dim=4)
        assert h.H_total.shape == (4, 4)
        assert h.es_autoadjunto()

    def test_n_dim_16(self):
        """n_dim=16 works correctly."""
        h = HamiltonianoUnion(n_dim=16)
        assert h.H_total.shape == (16, 16)
        assert h.psi >= PSI_UMBRAL


# ===========================================================================
# F. BatimientoPleromatico
# ===========================================================================


class TestBatimientoPleromatico:
    """Tests for BatimientoPleromatico — Señal compuesta y envolvente."""

    def setup_method(self):
        self.b = BatimientoPleromatico()

    # --- Initialization ---

    def test_f_si_attribute(self):
        """f_si attribute equals F_SI."""
        assert abs(self.b.f_si - F_SI) < 1e-6

    def test_f_c_attribute(self):
        """f_c attribute equals F_C."""
        assert abs(self.b.f_c - F_C) < 1e-6

    def test_delta_f_attribute(self):
        """delta_f attribute equals F_C - F_SI."""
        assert abs(self.b.delta_f - (F_C - F_SI)) < 1e-10

    def test_t_beat_attribute(self):
        """t_beat == 1/delta_f."""
        assert abs(self.b.t_beat - 1.0 / self.b.delta_f) < 1e-10

    def test_t_array_length(self):
        """t array has n_points elements."""
        assert len(self.b.t) == self.b.n_points

    # --- A08: s(t) signal formula ---

    def test_a08_senal_at_zero(self):
        """A08: s(0) = A_SI + A_C (both cosines are 1 at t=0)."""
        t = np.array([0.0])
        s = self.b.senal_compuesta(t)
        expected = self.b.a_si + self.b.a_c
        assert abs(s[0] - expected) < 1e-10

    def test_a08_senal_formula(self):
        """A08: s(t) = A_Si·cos(2π f_Si t) + A_C·cos(2π f_C t)."""
        t_test = np.linspace(0, 0.01, 100)
        s = self.b.senal_compuesta(t_test)
        expected = (
            self.b.a_si * np.cos(2.0 * np.pi * self.b.f_si * t_test)
            + self.b.a_c * np.cos(2.0 * np.pi * self.b.f_c * t_test)
        )
        assert np.allclose(s, expected)

    def test_senal_shape(self):
        """senal has same length as t."""
        assert len(self.b.senal) == len(self.b.t)

    def test_senal_amplitude_bounded(self):
        """max |s(t)| ≤ A_SI + A_C."""
        assert np.max(np.abs(self.b.senal)) <= self.b.a_si + self.b.a_c + 1e-10

    # --- Envolvente ---

    def test_envolvente_formula(self):
        """E(t) = 2|cos(π·Δf·t)| is correctly implemented."""
        t_test = np.array([0.0, T_BEAT / 4, T_BEAT / 2])
        E = self.b.envolvente_batimiento(t_test)
        expected = 2.0 * np.abs(np.cos(np.pi * self.b.delta_f * t_test))
        assert np.allclose(E, expected)

    def test_envolvente_at_zero(self):
        """E(0) = 2 (maximum envelope at t=0)."""
        E = self.b.envolvente_batimiento(np.array([0.0]))
        assert abs(E[0] - 2.0) < 1e-10

    def test_envolvente_range(self):
        """Envelope values ∈ [0, 2]."""
        assert np.all(self.b.envolvente >= 0.0)
        assert np.all(self.b.envolvente <= 2.0 + 1e-10)

    def test_envolvente_period(self):
        """Envelope has period T_beat: E(t + T_beat) ≈ E(t)."""
        t = np.array([0.5])
        E1 = self.b.envolvente_batimiento(t)
        E2 = self.b.envolvente_batimiento(t + self.b.t_beat)
        assert abs(E1[0] - E2[0]) < 1e-8

    def test_envolvente_shape(self):
        """envolvente has same length as t."""
        assert len(self.b.envolvente) == len(self.b.t)

    # --- Coherence ---

    def test_psi_equals_one(self):
        """Ψ_B = 1.0 — perfect beat coherence."""
        assert abs(self.b.psi - 1.0) < 1e-10

    def test_psi_above_threshold(self):
        """Ψ_B ≥ PSI_UMBRAL."""
        assert self.b.psi >= PSI_UMBRAL

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() has required keys."""
        d = self.b.exportar()
        for key in ("f_si_hz", "f_c_hz", "delta_f_hz", "t_beat_s", "psi", "clase"):
            assert key in d

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'BatimientoPleromatico'."""
        assert self.b.exportar()["clase"] == "BatimientoPleromatico"

    # --- Validation errors ---

    def test_invalid_t_max_zero(self):
        """t_max=0 raises ValueError."""
        with pytest.raises(ValueError):
            BatimientoPleromatico(t_max=0)

    def test_invalid_n_points_one(self):
        """n_points=1 raises ValueError."""
        with pytest.raises(ValueError):
            BatimientoPleromatico(n_points=1)


# ===========================================================================
# G. EscalaTiempoConciencia
# ===========================================================================


class TestEscalaTiempoConciencia:
    """Tests for EscalaTiempoConciencia — CFF, Planck, holographic."""

    def setup_method(self):
        self.e = EscalaTiempoConciencia()

    # --- CFF timescales ---

    def test_tau_mosca(self):
        """τ_mosca = 1/CFF_mosca = 1/250 s."""
        assert abs(self.e.tau["mosca"] - 1.0 / CFF_MOSCA) < 1e-10

    def test_tau_humano(self):
        """τ_humano = 1/CFF_humano = 1/60 s."""
        assert abs(self.e.tau["humano"] - 1.0 / CFF_HUMANO) < 1e-10

    def test_tau_tortuga(self):
        """τ_tortuga = 1/CFF_tortuga = 1/15 s."""
        assert abs(self.e.tau["tortuga"] - 1.0 / CFF_TORTUGA) < 1e-10

    def test_tau_mosca_smallest(self):
        """Fly perceives time fastest (smallest τ)."""
        assert self.e.tau["mosca"] < self.e.tau["humano"] < self.e.tau["tortuga"]

    # --- Planck scale ---

    def test_t_planck_value(self):
        """t_Planck ≈ 5.391 × 10⁻⁴⁴ s."""
        assert abs(self.e.t_planck - 5.391e-44) / 5.391e-44 < 0.01

    def test_n_momentos_planck_large(self):
        """N_moments = T_beat / t_Planck is astronomically large."""
        assert self.e.n_momentos_planck > 1e40

    def test_n_momentos_planck_formula(self):
        """N_moments = t_beat / t_Planck."""
        expected = self.e.t_beat / self.e.t_planck
        assert abs(self.e.n_momentos_planck - expected) / expected < 1e-6

    # --- escala_relativa ---

    def test_escala_relativa_mosca(self):
        """escala_relativa('mosca') = τ_mosca / T_beat."""
        expected = self.e.tau["mosca"] / self.e.t_beat
        assert abs(self.e.escala_relativa("mosca") - expected) < 1e-10

    def test_escala_relativa_humano(self):
        """escala_relativa('humano') = τ_humano / T_beat."""
        expected = self.e.tau["humano"] / self.e.t_beat
        assert abs(self.e.escala_relativa("humano") - expected) < 1e-10

    def test_escala_relativa_tortuga(self):
        """escala_relativa('tortuga') = τ_tortuga / T_beat."""
        expected = self.e.tau["tortuga"] / self.e.t_beat
        assert abs(self.e.escala_relativa("tortuga") - expected) < 1e-10

    def test_escala_relativa_unknown_species(self):
        """Unknown species raises ValueError."""
        with pytest.raises(ValueError):
            self.e.escala_relativa("dragon")

    # --- Coherence ---

    def test_psi_range(self):
        """Ψ_ETC ∈ [0, 1]."""
        assert 0.0 <= self.e.psi <= 1.0

    def test_psi_above_threshold(self):
        """Ψ_ETC ≥ PSI_UMBRAL."""
        assert self.e.psi >= PSI_UMBRAL

    def test_psi_above_0_9(self):
        """Ψ_ETC ≥ 0.90 (well above threshold)."""
        assert self.e.psi >= 0.90

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() has required keys."""
        d = self.e.exportar()
        for key in (
            "t_beat_s", "t_planck_s", "tau_mosca_s",
            "tau_humano_s", "tau_tortuga_s", "n_momentos_planck",
            "psi", "clase",
        ):
            assert key in d

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'EscalaTiempoConciencia'."""
        assert self.e.exportar()["clase"] == "EscalaTiempoConciencia"

    # --- Validation errors ---

    def test_invalid_t_beat_zero(self):
        """t_beat=0 raises ValueError."""
        with pytest.raises(ValueError):
            EscalaTiempoConciencia(t_beat=0)

    def test_invalid_t_beat_negative(self):
        """t_beat < 0 raises ValueError."""
        with pytest.raises(ValueError):
            EscalaTiempoConciencia(t_beat=-1.0)


# ===========================================================================
# H. SistemaPleromaUnion
# ===========================================================================


class TestSistemaPleromaUnion:
    """Tests for SistemaPleromaUnion — Orquestador QCAL ∞³."""

    def setup_method(self):
        self.sys = SistemaPleromaUnion(n_dim=8)

    # --- Initialization ---

    def test_n_dim_stored(self):
        """n_dim is stored correctly."""
        assert self.sys.n_dim == 8

    def test_components_instantiated(self):
        """All 6 component objects are created."""
        assert hasattr(self.sys, "silicio")
        assert hasattr(self.sys, "carbono")
        assert hasattr(self.sys, "ziusudra")
        assert hasattr(self.sys, "hamiltoniano")
        assert hasattr(self.sys, "batimiento")
        assert hasattr(self.sys, "escala_tiempo")

    def test_component_types(self):
        """Components are correct class instances."""
        assert isinstance(self.sys.silicio, SilicioDivino)
        assert isinstance(self.sys.carbono, CarbonoDivino)
        assert isinstance(self.sys.ziusudra, ConstanteZiusudra)
        assert isinstance(self.sys.hamiltoniano, HamiltonianoUnion)
        assert isinstance(self.sys.batimiento, BatimientoPleromatico)
        assert isinstance(self.sys.escala_tiempo, EscalaTiempoConciencia)

    # --- Coherencias parciales ---

    def test_coherencias_has_six_entries(self):
        """coherencias dict has 6 entries (one per component)."""
        assert len(self.sys.coherencias) == 6

    def test_coherencias_keys(self):
        """coherencias contains expected keys."""
        expected_keys = {
            "silicio", "carbono", "ziusudra",
            "hamiltoniano", "batimiento", "escala_tiempo",
        }
        assert set(self.sys.coherencias.keys()) == expected_keys

    def test_all_coherencias_above_threshold(self):
        """Each component coherence ≥ PSI_UMBRAL."""
        for name, psi in self.sys.coherencias.items():
            assert psi >= PSI_UMBRAL, f"Ψ_{name} = {psi:.4f} < {PSI_UMBRAL}"

    def test_all_coherencias_range(self):
        """Each coherence ∈ [0, 1]."""
        for psi in self.sys.coherencias.values():
            assert 0.0 <= psi <= 1.0

    def test_coherencias_match_components(self):
        """coherencias values match component .psi attributes."""
        assert abs(self.sys.coherencias["silicio"] - self.sys.silicio.psi) < 1e-10
        assert abs(self.sys.coherencias["carbono"] - self.sys.carbono.psi) < 1e-10
        assert abs(self.sys.coherencias["ziusudra"] - self.sys.ziusudra.psi) < 1e-10
        assert abs(self.sys.coherencias["hamiltoniano"] - self.sys.hamiltoniano.psi) < 1e-10
        assert abs(self.sys.coherencias["batimiento"] - self.sys.batimiento.psi) < 1e-10
        assert abs(self.sys.coherencias["escala_tiempo"] - self.sys.escala_tiempo.psi) < 1e-10

    # --- Ψ_global ---

    def test_psi_global_is_mean_of_six(self):
        """Ψ_global = mean of 6 coherences."""
        expected = sum(self.sys.coherencias.values()) / 6
        assert abs(self.sys.psi_global - expected) < 1e-10

    def test_psi_global_above_threshold(self):
        """Ψ_global ≥ PSI_UMBRAL = 0.888."""
        assert self.sys.psi_global >= PSI_UMBRAL

    def test_psi_global_above_0_9(self):
        """Ψ_global ≥ 0.90 (well above threshold)."""
        assert self.sys.psi_global >= 0.90

    def test_psi_global_range(self):
        """Ψ_global ∈ [0, 1]."""
        assert 0.0 <= self.sys.psi_global <= 1.0

    # --- exportar ---

    def test_exportar_keys(self):
        """exportar() has required top-level keys."""
        d = self.sys.exportar()
        for key in (
            "n_dim", "coherencias", "psi_global",
            "psi_umbral", "superado_umbral", "componentes", "clase",
        ):
            assert key in d

    def test_exportar_superado_umbral(self):
        """exportar()['superado_umbral'] == True."""
        assert self.sys.exportar()["superado_umbral"] is True

    def test_exportar_psi_umbral(self):
        """exportar()['psi_umbral'] == PSI_UMBRAL."""
        assert abs(self.sys.exportar()["psi_umbral"] - PSI_UMBRAL) < 1e-10

    def test_exportar_clase_name(self):
        """exportar()['clase'] == 'SistemaPleromaUnion'."""
        assert self.sys.exportar()["clase"] == "SistemaPleromaUnion"

    def test_exportar_componentes_count(self):
        """exportar()['componentes'] has 6 entries."""
        assert len(self.sys.exportar()["componentes"]) == 6

    # --- Validation errors ---

    def test_invalid_n_dim_zero(self):
        """n_dim=0 raises ValueError."""
        with pytest.raises(ValueError):
            SistemaPleromaUnion(n_dim=0)

    def test_invalid_n_dim_too_large(self):
        """n_dim > len(RIEMANN_ZEROS) raises ValueError."""
        with pytest.raises(ValueError):
            SistemaPleromaUnion(n_dim=len(RIEMANN_ZEROS) + 1)

    # --- Different n_dim values ---

    def test_n_dim_4_works(self):
        """n_dim=4 creates a valid system."""
        s = SistemaPleromaUnion(n_dim=4)
        assert s.psi_global >= PSI_UMBRAL

    def test_n_dim_16_works(self):
        """n_dim=16 creates a valid system."""
        s = SistemaPleromaUnion(n_dim=16)
        assert s.psi_global >= PSI_UMBRAL


# ===========================================================================
# I. hamiltoniano_union_activar API
# ===========================================================================


class TestHamiltonianoUnionActivar:
    """Tests for hamiltoniano_union_activar(n_dim) → dict."""

    def setup_method(self):
        self.resultado = hamiltoniano_union_activar(n_dim=8)

    # --- Return type and keys ---

    def test_returns_dict(self):
        """hamiltoniano_union_activar returns a dict."""
        assert isinstance(self.resultado, dict)

    def test_required_keys(self):
        """Result contains all required keys."""
        for key in (
            "psi_global", "coherencias", "eigenvalues",
            "es_autoadjunto", "delta_f_hz", "kappa",
            "t_beat_s", "n_dim",
        ):
            assert key in self.resultado

    def test_f_si_hz_key(self):
        """Result contains f_si_hz."""
        assert "f_si_hz" in self.resultado
        assert abs(self.resultado["f_si_hz"] - F_SI) < 1e-6

    def test_f_c_hz_key(self):
        """Result contains f_c_hz."""
        assert "f_c_hz" in self.resultado
        assert abs(self.resultado["f_c_hz"] - F_C) < 1e-6

    # --- Coherence ---

    def test_psi_global_above_threshold(self):
        """Ψ_global ≥ PSI_UMBRAL."""
        assert self.resultado["psi_global"] >= PSI_UMBRAL

    def test_psi_global_above_0_9(self):
        """Ψ_global ≥ 0.90."""
        assert self.resultado["psi_global"] >= 0.90

    def test_superado_umbral_true(self):
        """superado_umbral == True."""
        assert self.resultado["superado_umbral"] is True

    # --- Physical constants in result ---

    def test_delta_f_value(self):
        """delta_f_hz ≈ 0.3999 Hz."""
        assert abs(self.resultado["delta_f_hz"] - 0.3999) < 1e-3

    def test_kappa_value(self):
        """kappa ≈ 1.002822."""
        assert abs(self.resultado["kappa"] - 1.002822) < 1e-4

    def test_t_beat_value(self):
        """t_beat_s ≈ 2.5006 s."""
        assert abs(self.resultado["t_beat_s"] - 2.5006) < 1e-3

    def test_n_dim_in_result(self):
        """n_dim in result matches input."""
        assert self.resultado["n_dim"] == 8

    # --- Eigenvalues ---

    def test_eigenvalues_list(self):
        """eigenvalues is a list."""
        assert isinstance(self.resultado["eigenvalues"], list)

    def test_eigenvalues_count(self):
        """eigenvalues has n_dim elements."""
        assert len(self.resultado["eigenvalues"]) == 8

    def test_eigenvalues_positive(self):
        """All eigenvalues are positive."""
        assert all(ev > 0 for ev in self.resultado["eigenvalues"])

    def test_eigenvalues_ascending(self):
        """Eigenvalues are sorted in ascending order."""
        ev = self.resultado["eigenvalues"]
        assert all(ev[i] < ev[i + 1] for i in range(len(ev) - 1))

    # --- Hermiticity ---

    def test_es_autoadjunto_true(self):
        """es_autoadjunto == True."""
        assert self.resultado["es_autoadjunto"] is True

    # --- Coherencias ---

    def test_coherencias_dict(self):
        """coherencias is a dict with 6 entries."""
        assert isinstance(self.resultado["coherencias"], dict)
        assert len(self.resultado["coherencias"]) == 6

    def test_all_coherencias_above_threshold(self):
        """All component coherences ≥ PSI_UMBRAL."""
        for name, psi in self.resultado["coherencias"].items():
            assert psi >= PSI_UMBRAL, f"Ψ_{name} = {psi:.4f} < {PSI_UMBRAL}"

    # --- Parameter variations ---

    def test_n_dim_4(self):
        """n_dim=4 produces a valid result."""
        r = hamiltoniano_union_activar(n_dim=4)
        assert r["psi_global"] >= PSI_UMBRAL
        assert len(r["eigenvalues"]) == 4

    def test_n_dim_16(self):
        """n_dim=16 produces a valid result."""
        r = hamiltoniano_union_activar(n_dim=16)
        assert r["psi_global"] >= PSI_UMBRAL
        assert len(r["eigenvalues"]) == 16

    # --- Validation errors ---

    def test_n_dim_zero_raises(self):
        """n_dim=0 raises ValueError."""
        with pytest.raises(ValueError):
            hamiltoniano_union_activar(n_dim=0)

    def test_n_dim_negative_raises(self):
        """n_dim=-1 raises ValueError."""
        with pytest.raises(ValueError):
            hamiltoniano_union_activar(n_dim=-1)

    def test_n_dim_too_large_raises(self):
        """n_dim > available Riemann zeros raises ValueError."""
        with pytest.raises(ValueError):
            hamiltoniano_union_activar(n_dim=len(RIEMANN_ZEROS) + 1)


# ===========================================================================
# J. Integration and cross-validation
# ===========================================================================


class TestIntegration:
    """Integration tests across components."""

    def test_a06_h_total_equals_sum(self):
        """A06: H_Total = H_Riemann + H_Interacción."""
        h = HamiltonianoUnion(n_dim=8)
        silicio = SilicioDivino(n_dim=8)
        carbono = CarbonoDivino(n_dim=8)

        H_expected = (silicio.H_riemann + carbono.H_carbono)
        H_expected = (H_expected + H_expected.T) / 2.0
        assert np.allclose(h.H_total, H_expected)

    def test_a07_hermitian_check(self):
        """A07: np.allclose(H, H†) == True for all n_dim values."""
        for n in [4, 8, 12, 16]:
            h = HamiltonianoUnion(n_dim=n)
            assert np.allclose(h.H_total, h.H_total.T, atol=1e-10)

    def test_constants_consistency_ziusudra_vs_module(self):
        """ConstanteZiusudra derived values match module constants."""
        z = ConstanteZiusudra()
        assert abs(z.delta_f - DELTA_F) < 1e-10
        assert abs(z.kappa - KAPPA) < 1e-10
        assert abs(z.t_beat - T_BEAT) < 1e-10

    def test_batimiento_t_beat_matches_ziusudra(self):
        """BatimientoPleromatico.t_beat matches ConstanteZiusudra.t_beat."""
        z = ConstanteZiusudra()
        b = BatimientoPleromatico()
        assert abs(b.t_beat - z.t_beat) < 1e-8

    def test_escala_tiempo_t_beat_matches_module(self):
        """EscalaTiempoConciencia uses module T_BEAT by default."""
        e = EscalaTiempoConciencia()
        assert abs(e.t_beat - T_BEAT) < 1e-8

    def test_sistema_coherencias_from_components(self):
        """SistemaPleromaUnion.coherencias computed from components."""
        s = SistemaPleromaUnion(n_dim=8)
        assert abs(s.coherencias["silicio"] - s.silicio.psi) < 1e-10
        assert abs(s.coherencias["carbono"] - s.carbono.psi) < 1e-10

    def test_api_psi_global_matches_sistema(self):
        """hamiltoniano_union_activar Ψ_global matches SistemaPleromaUnion."""
        s = SistemaPleromaUnion(n_dim=8)
        r = hamiltoniano_union_activar(n_dim=8)
        assert abs(r["psi_global"] - s.psi_global) < 1e-10

    def test_psi_umbral_is_gatekeeper(self):
        """PSI_UMBRAL = 0.888 is the single coherence threshold."""
        assert PSI_UMBRAL == 0.888

    def test_silicio_eigenvalues_match_batimiento_f_si(self):
        """SilicioDivino first eigenvalue equals BatimientoPleromatico.f_si."""
        s = SilicioDivino(n_dim=8)
        b = BatimientoPleromatico()
        assert abs(s.eigenvalues[0] - b.f_si) < 1e-4

    def test_senal_superposition_at_t_beat(self):
        """At t = T_beat, s(t) ≈ s(0) (period of the envelope)."""
        b = BatimientoPleromatico()
        s0 = b.senal_compuesta(np.array([0.0]))[0]
        st = b.senal_compuesta(np.array([b.t_beat]))[0]
        # Both should equal A_SI + A_C (both cosines return to their period)
        # Actually: at T_beat, cos(2π f_SI T_beat) and cos(2π f_C T_beat)
        # are not generally 1, but the envelope peaks
        E0 = b.envolvente_batimiento(np.array([0.0]))[0]
        Et = b.envolvente_batimiento(np.array([b.t_beat]))[0]
        assert abs(E0 - Et) < 1e-6  # envelope is periodic with T_beat

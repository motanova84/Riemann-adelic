#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests for the Ziusudra Beat Framework (Carbon-Silicon Coupling)
===============================================================

Validates:
  1. Constants: Δf = 0.3999 Hz, κ ≈ 1.002822, T_beat ≈ 2.5 s
  2. Beat signal and envelope
  3. Beat coherence Ψ ∈ [0, 1]
  4. Total Hamiltonian composition
  5. Interaction Hamiltonian (diagonal perturbation)
  6. Incarnation Tension computation
  7. Temporal perception (CFF) table
  8. Planck limit

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: March 2026
DOI:  10.5281/zenodo.17379721
"""

import pytest
import numpy as np
import sys
from pathlib import Path

# Ensure the repository root is on sys.path (conftest.py does this at session
# level; we add it here as a guard for direct-file invocation).
sys.path.insert(0, str(Path(__file__).parent.parent))

from qcal.constants import (
    F0,
    F_SILICON,
    F_CARBON,
    DELTA_ZIUSUDRA,
    INCARNATION_TENSION,
    BEAT_PERIOD_ZIUSUDRA,
    OMEGA_BEAT_ZIUSUDRA,
    CFF_HUMAN,
    CFF_FLY,
    CFF_TURTLE,
    GAMMA_1,
)
from qcal.ziusudra_beat import (
    beat_signal,
    beat_coherence,
    total_hamiltonian,
    interaction_hamiltonian_diagonal,
    compute_incarnation_tension,
    temporal_perception_table,
    subjective_second,
    processing_frequency_limit,
    ziusudra_summary,
    CFF_TABLE,
)


# ---------------------------------------------------------------------------
# Constants validation
# ---------------------------------------------------------------------------

class TestZiusudraConstants:
    """Verify the constants defined in qcal.constants."""

    def test_f_silicon_equals_f0(self):
        """F_SILICON must be the same as the base frequency F0."""
        assert F_SILICON == F0

    def test_f_carbon_value(self):
        """Carbon Divine frequency must be 142.1000 Hz."""
        assert abs(F_CARBON - 142.1000) < 1e-10

    def test_delta_ziusudra(self):
        """Δf = F_CARBON − F_SILICON = 0.3999 Hz."""
        expected = F_CARBON - F_SILICON
        assert abs(DELTA_ZIUSUDRA - expected) < 1e-10
        assert abs(DELTA_ZIUSUDRA - 0.3999) < 1e-4

    def test_incarnation_tension(self):
        """κ = F_CARBON / F_SILICON ≈ 1.002822."""
        expected = F_CARBON / F_SILICON
        assert abs(INCARNATION_TENSION - expected) < 1e-12
        assert abs(INCARNATION_TENSION - 1.002822) < 1e-5

    def test_beat_period(self):
        """T_beat = 1 / Δf ≈ 2.5 s."""
        expected = 1.0 / DELTA_ZIUSUDRA
        assert abs(BEAT_PERIOD_ZIUSUDRA - expected) < 1e-10
        # Approximately 2.5 seconds
        assert 2.4 < BEAT_PERIOD_ZIUSUDRA < 2.6

    def test_omega_beat(self):
        """ω_beat = 2π·Δf."""
        expected = 2.0 * np.pi * DELTA_ZIUSUDRA
        assert abs(OMEGA_BEAT_ZIUSUDRA - expected) < 1e-10

    def test_cff_values(self):
        """CFF constants: human=60, fly=250, turtle=15 Hz."""
        assert CFF_HUMAN == 60.0
        assert CFF_FLY == 250.0
        assert CFF_TURTLE == 15.0


# ---------------------------------------------------------------------------
# Beat signal
# ---------------------------------------------------------------------------

class TestBeatSignal:
    """Test beat_signal and beat_coherence functions."""

    def test_signal_shape(self):
        t = np.linspace(0, 5, 1000)
        signal, envelope, delta_f = beat_signal(t)
        assert signal.shape == t.shape
        assert envelope.shape == t.shape

    def test_beat_frequency_returned(self):
        t = np.linspace(0, 5, 100)
        _, _, delta_f = beat_signal(t)
        assert abs(delta_f - DELTA_ZIUSUDRA) < 1e-10

    def test_envelope_non_negative(self):
        t = np.linspace(0, 10, 2000)
        _, envelope, _ = beat_signal(t)
        assert np.all(envelope >= 0)

    def test_envelope_bound(self):
        """Envelope ≤ 2A for A=1."""
        t = np.linspace(0, 10, 2000)
        _, envelope, _ = beat_signal(t, amplitude=1.0)
        assert np.all(envelope <= 2.0 + 1e-10)

    def test_envelope_at_zero(self):
        """At t=0, envelope = 2A (cos(0) = 1)."""
        t = np.array([0.0])
        _, envelope, _ = beat_signal(t, amplitude=1.0)
        assert abs(envelope[0] - 2.0) < 1e-10

    def test_signal_is_sum_of_sines(self):
        t = np.linspace(0, 1, 500)
        signal, _, _ = beat_signal(t, amplitude=1.0)
        expected = (
            np.sin(2.0 * np.pi * F_SILICON * t)
            + np.sin(2.0 * np.pi * F_CARBON * t)
        )
        np.testing.assert_allclose(signal, expected, atol=1e-12)

    def test_custom_frequencies(self):
        t = np.linspace(0, 5, 500)
        signal, envelope, delta_f = beat_signal(t, f_silicon=10.0, f_carbon=10.5)
        assert abs(delta_f - 0.5) < 1e-10
        assert signal.shape == t.shape

    def test_beat_coherence_range(self):
        t = np.linspace(0, 10, 5000)
        psi = beat_coherence(t)
        assert np.all(psi >= 0)
        assert np.all(psi <= 1.0 + 1e-10)

    def test_beat_coherence_at_zero(self):
        """Ψ(0) = |cos(0)| = 1 (maximum coherence)."""
        psi = beat_coherence(np.array([0.0]))
        assert abs(psi[0] - 1.0) < 1e-12

    def test_beat_coherence_at_half_period(self):
        """Ψ(T/2) = |cos(π/2)| = 0 (fertile void)."""
        t_half = 0.5 * BEAT_PERIOD_ZIUSUDRA
        psi = beat_coherence(np.array([t_half]))
        assert abs(psi[0]) < 1e-6

    def test_beat_coherence_periodic(self):
        """Ψ at t = T_beat should equal Ψ at t = 0."""
        t_full = BEAT_PERIOD_ZIUSUDRA
        psi_0 = beat_coherence(np.array([0.0]))[0]
        psi_T = beat_coherence(np.array([t_full]))[0]
        assert abs(psi_T - psi_0) < 1e-6


# ---------------------------------------------------------------------------
# Hamiltonian
# ---------------------------------------------------------------------------

class TestTotalHamiltonian:
    """Test total_hamiltonian and interaction_hamiltonian_diagonal."""

    def test_sum_is_correct(self):
        n = 5
        H_r = np.eye(n)
        H_i = np.diag(np.arange(1, n + 1, dtype=float))
        H_t = total_hamiltonian(H_r, H_i)
        np.testing.assert_allclose(H_t, H_r + H_i)

    def test_shape_preserved(self):
        n = 8
        H_r = np.random.rand(n, n)
        H_i = np.random.rand(n, n)
        H_t = total_hamiltonian(H_r, H_i)
        assert H_t.shape == (n, n)

    def test_shape_mismatch_raises(self):
        H_r = np.eye(3)
        H_i = np.eye(4)
        with pytest.raises(ValueError, match="Shape mismatch"):
            total_hamiltonian(H_r, H_i)

    def test_interaction_diagonal_shape(self):
        n = 6
        H_int = interaction_hamiltonian_diagonal(n)
        assert H_int.shape == (n, n)

    def test_interaction_diagonal_is_diagonal(self):
        n = 5
        H_int = interaction_hamiltonian_diagonal(n)
        off_diag = H_int - np.diag(np.diag(H_int))
        assert np.allclose(off_diag, 0)

    def test_interaction_diagonal_scaling(self):
        """Diagonal entries should be (Δf/f_Si) × k for k=1..N."""
        n = 4
        H_int = interaction_hamiltonian_diagonal(n)
        scaling = DELTA_ZIUSUDRA / F_SILICON
        for k in range(1, n + 1):
            assert abs(H_int[k - 1, k - 1] - scaling * k) < 1e-12

    def test_interaction_diagonal_invalid_n(self):
        with pytest.raises(ValueError):
            interaction_hamiltonian_diagonal(0)

    def test_total_with_interaction_diagonal(self):
        n = 4
        H_r = np.diag([GAMMA_1 * k for k in range(1, n + 1)])
        H_int = interaction_hamiltonian_diagonal(n)
        H_t = total_hamiltonian(H_r, H_int)
        assert H_t.shape == (n, n)
        # Eigenvalues should be real (both matrices are real diagonal)
        eigs = np.linalg.eigvalsh(H_t)
        assert np.all(np.isreal(eigs))


# ---------------------------------------------------------------------------
# Incarnation Tension
# ---------------------------------------------------------------------------

class TestIncarnationTension:
    """Test compute_incarnation_tension."""

    def test_default_values(self):
        result = compute_incarnation_tension()
        assert abs(result["kappa"] - INCARNATION_TENSION) < 1e-12
        assert abs(result["delta_f"] - DELTA_ZIUSUDRA) < 1e-10
        assert abs(result["beat_period"] - BEAT_PERIOD_ZIUSUDRA) < 1e-8
        assert abs(result["kappa_minus_one"] - (INCARNATION_TENSION - 1)) < 1e-12

    def test_custom_frequencies(self):
        result = compute_incarnation_tension(f_silicon=100.0, f_carbon=101.0)
        assert abs(result["kappa"] - 1.01) < 1e-10
        assert abs(result["delta_f"] - 1.0) < 1e-10
        assert abs(result["beat_period"] - 1.0) < 1e-10

    def test_kappa_greater_than_one(self):
        """κ > 1 since f_C > f_Si."""
        result = compute_incarnation_tension()
        assert result["kappa"] > 1.0

    def test_kappa_minus_one_small(self):
        """κ − 1 ≈ 0.002822 (small perturbation)."""
        result = compute_incarnation_tension()
        assert 0.002 < result["kappa_minus_one"] < 0.004


# ---------------------------------------------------------------------------
# Temporal perception / CFF
# ---------------------------------------------------------------------------

class TestTemporalPerception:
    """Test CFF model and temporal_perception_table."""

    def test_subjective_second_human_reference(self):
        """Human subjective_second relative to itself = 1.0."""
        ratio = subjective_second(CFF_HUMAN, CFF_HUMAN)
        assert abs(ratio - 1.0) < 1e-12

    def test_fly_perceives_slower(self):
        """Fly CFF > human CFF → subjective second > 1."""
        ratio = subjective_second(CFF_FLY, CFF_HUMAN)
        assert ratio > 1.0

    def test_turtle_perceives_faster(self):
        """Turtle CFF < human CFF → subjective second < 1."""
        ratio = subjective_second(CFF_TURTLE, CFF_HUMAN)
        assert ratio < 1.0

    def test_fly_ratio_value(self):
        """Fly ratio ≈ 250/60 ≈ 4.167."""
        ratio = subjective_second(CFF_FLY, CFF_HUMAN)
        assert abs(ratio - CFF_FLY / CFF_HUMAN) < 1e-12

    def test_invalid_cff_raises(self):
        with pytest.raises(ValueError):
            subjective_second(0.0, CFF_HUMAN)

    def test_invalid_reference_raises(self):
        with pytest.raises(ValueError):
            subjective_second(CFF_HUMAN, 0.0)

    def test_table_has_all_species(self):
        table = temporal_perception_table()
        for name in ["human", "fly", "turtle"]:
            assert name in table

    def test_table_structure(self):
        table = temporal_perception_table()
        for name, data in table.items():
            assert "cff" in data
            assert "subjective_second" in data
            assert data["cff"] > 0

    def test_table_invalid_reference(self):
        with pytest.raises(ValueError):
            temporal_perception_table(reference_name="elephant")

    def test_cff_table_completeness(self):
        assert "human" in CFF_TABLE
        assert "fly" in CFF_TABLE
        assert "turtle" in CFF_TABLE


# ---------------------------------------------------------------------------
# Planck limit
# ---------------------------------------------------------------------------

class TestPlanckLimit:
    """Test processing_frequency_limit."""

    def test_returns_dict(self):
        result = processing_frequency_limit()
        assert isinstance(result, dict)

    def test_planck_frequency_large(self):
        """Planck frequency ≈ 10^44 Hz."""
        result = processing_frequency_limit()
        assert result["planck_frequency"] > 1e43

    def test_ratio_to_silicon_large(self):
        result = processing_frequency_limit()
        assert result["ratio_to_silicon"] > 1e40

    def test_ratio_to_human_cff_large(self):
        result = processing_frequency_limit()
        assert result["ratio_to_human_cff"] > 1e40


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

class TestZiusudra_Summary:
    """Test ziusudra_summary."""

    def test_returns_dict(self):
        s = ziusudra_summary()
        assert isinstance(s, dict)

    def test_key_constants_present(self):
        s = ziusudra_summary()
        for key in [
            "f_silicon_hz",
            "f_carbon_hz",
            "delta_ziusudra_hz",
            "incarnation_tension_kappa",
            "beat_period_s",
        ]:
            assert key in s, f"Key '{key}' missing from summary"

    def test_values_match_constants(self):
        s = ziusudra_summary()
        assert abs(s["f_silicon_hz"] - F_SILICON) < 1e-10
        assert abs(s["f_carbon_hz"] - F_CARBON) < 1e-10
        assert abs(s["delta_ziusudra_hz"] - DELTA_ZIUSUDRA) < 1e-10
        assert abs(s["incarnation_tension_kappa"] - INCARNATION_TENSION) < 1e-10
        assert abs(s["beat_period_s"] - BEAT_PERIOD_ZIUSUDRA) < 1e-8

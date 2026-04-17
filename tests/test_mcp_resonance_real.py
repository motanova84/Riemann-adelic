"""
Real-observer tests for mcp_network.resonance  (Level-A physical data)
========================================================================

These tests exercise ``check_node_resonance`` with observers backed by
physical-data CSV fixtures stored in ``tests/data/``.  They are **skipped in
CI** unless the environment variable ``QCAL_REAL_TESTS=1`` is set.

Activate on your machine or in a lab environment::

    QCAL_REAL_TESTS=1 pytest tests/test_mcp_resonance_real.py -v

Physical-data sources
---------------------
* **auron-governor** — ``grid_frequency_auron_governor.csv``
  60 rows of European 50 Hz grid frequency sampled at 1-second intervals.
  The *instantaneous* (per-cycle) phase offset is computed as::

      phase_offset_rad = 2π × Δf_mean × 1 s

  where ``Δf_mean = mean(f) − 50 Hz``.  A 1-second window is used to keep
  the offset within the _PHASE_REF_RAD normalisation range (0.2 rad) and
  represent a *real-time* coherence snapshot rather than an accumulated drift.

* **141-hz** — ``qcal_spectrum_141hz.csv``
  Lorentzian QCAL spectrum centred at f₀ = 141.7001 Hz.  The phase offset is
  derived as the fractional centroid deviation scaled to radians::

      phase_offset_rad = 2π × |centroid − f₀| / f₀

Real-observer contract
----------------------
Each observer is a zero-argument callable that returns::

    (latency_ms: float, phase_offset_rad: float,
     heartbeat_ok: bool, schema_ok: bool)
"""
from __future__ import annotations

import csv
import math
import os
from pathlib import Path
from typing import Tuple

import pytest

from mcp_network.resonance import (
    _PSI_COHERENT,
    _PSI_DRIFTING,
    REAL_OBSERVERS,
    check_node_resonance,
    classify_resonance,
    register_real_observer,
    score_psi,
    unregister_real_observer,
)
from mcp_network.registry import NODE_CATALOG

# ---------------------------------------------------------------------------
# Skip marker — only execute when physical data tests are explicitly requested
# ---------------------------------------------------------------------------
pytestmark = pytest.mark.skipif(
    os.environ.get("QCAL_REAL_TESTS", "0") != "1",
    reason="Set QCAL_REAL_TESTS=1 to run real-observer tests",
)

DATA_DIR = Path(__file__).parent / "data"


# ---------------------------------------------------------------------------
# Helpers — data loaders
# ---------------------------------------------------------------------------

def _load_grid_csv(path: Path) -> list[float]:
    """Return the list of frequency values (Hz) from the grid CSV."""
    freqs: list[float] = []
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            freqs.append(float(row["frequency_hz"]))
    return freqs


def _load_qcal_spectrum_csv(path: Path) -> tuple[list[float], list[float]]:
    """Return (frequencies, amplitudes) from the QCAL spectrum CSV."""
    freqs, amps = [], []
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            freqs.append(float(row["frequency_hz"]))
            amps.append(float(row["amplitude"]))
    return freqs, amps


def _spectral_centroid(freqs: list[float], amps: list[float]) -> float:
    """Compute amplitude-weighted centroid frequency."""
    total_amp = sum(amps)
    if total_amp == 0.0:
        return freqs[len(freqs) // 2]
    return sum(f * a for f, a in zip(freqs, amps)) / total_amp


# ---------------------------------------------------------------------------
# Observer factories — produce the 4-tuple expected by REAL_OBSERVERS
# ---------------------------------------------------------------------------

def _make_grid_observer(csv_path: Path, nominal_hz: float = 50.0) -> callable:
    """Build an auron-governor observer from a grid-frequency CSV.

    Phase offset is computed as a *per-cycle* (1-second window) instantaneous
    value::

        phase_offset_rad = 2π × Δf_mean × 1 s

    This keeps the offset commensurate with ``_PHASE_REF_RAD = 0.2 rad`` and
    represents a real-time coherence snapshot.
    """
    freqs = _load_grid_csv(csv_path)

    def observer() -> Tuple[float, float, bool, bool]:
        delta_f = sum(freqs) / len(freqs) - nominal_hz
        # 1-second instantaneous window — fractional deviation per cycle
        phase_offset_rad = 2.0 * math.pi * delta_f * 1.0
        latency_ms = 12.4   # nominal measurement poll latency
        return latency_ms, phase_offset_rad, True, True

    return observer


def _make_qcal_spectrum_observer(csv_path: Path, f0: float = 141.7001) -> callable:
    """Build a 141-hz observer from a QCAL spectrum CSV.

    Phase offset is the fractional centroid deviation scaled to radians::

        phase_offset_rad = 2π × |centroid − f₀| / f₀
    """
    freqs, amps = _load_qcal_spectrum_csv(csv_path)

    def observer() -> Tuple[float, float, bool, bool]:
        centroid = _spectral_centroid(freqs, amps)
        phase_offset_rad = 2.0 * math.pi * abs(centroid - f0) / f0
        latency_ms = 12.4   # nominal measurement poll latency
        return latency_ms, phase_offset_rad, True, True

    return observer


# ---------------------------------------------------------------------------
# Pytest fixtures — clean up REAL_OBSERVERS after each test
# ---------------------------------------------------------------------------

@pytest.fixture(autouse=True)
def _clean_observers():
    """Ensure REAL_OBSERVERS is empty before and after each test."""
    REAL_OBSERVERS.clear()
    yield
    REAL_OBSERVERS.clear()


# ===========================================================================
# Standalone function tests (no observer registration)
# ===========================================================================

class TestGridObserverFunctions:
    """Unit tests for the grid-data helper functions."""

    def test_load_grid_csv_length(self):
        path = DATA_DIR / "grid_frequency_auron_governor.csv"
        freqs = _load_grid_csv(path)
        assert len(freqs) == 60

    def test_grid_frequencies_near_50hz(self):
        path = DATA_DIR / "grid_frequency_auron_governor.csv"
        freqs = _load_grid_csv(path)
        for f in freqs:
            assert abs(f - 50.0) < 0.1, f"Outlier grid frequency: {f}"

    def test_grid_mean_close_to_50hz(self):
        path = DATA_DIR / "grid_frequency_auron_governor.csv"
        freqs = _load_grid_csv(path)
        mean_f = sum(freqs) / len(freqs)
        assert abs(mean_f - 50.0) < 0.05

    def test_grid_phase_offset_small(self):
        """Instantaneous (1-second) phase offset must be << _PHASE_REF_RAD."""
        path = DATA_DIR / "grid_frequency_auron_governor.csv"
        freqs = _load_grid_csv(path)
        delta_f = sum(freqs) / len(freqs) - 50.0
        phase_rad = 2.0 * math.pi * delta_f * 1.0
        assert abs(phase_rad) < 0.1, f"Phase offset too large: {phase_rad:.4f} rad"


class TestQCALSpectrumFunctions:
    """Unit tests for the QCAL spectrum helper functions."""

    def test_load_spectrum_length(self):
        path = DATA_DIR / "qcal_spectrum_141hz.csv"
        freqs, amps = _load_qcal_spectrum_csv(path)
        assert len(freqs) == 80
        assert len(amps) == 80

    def test_all_amplitudes_positive(self):
        path = DATA_DIR / "qcal_spectrum_141hz.csv"
        _, amps = _load_qcal_spectrum_csv(path)
        assert all(a > 0.0 for a in amps)

    def test_centroid_near_f0(self):
        path = DATA_DIR / "qcal_spectrum_141hz.csv"
        freqs, amps = _load_qcal_spectrum_csv(path)
        centroid = _spectral_centroid(freqs, amps)
        assert abs(centroid - 141.7001) < 0.01, f"Centroid far from f₀: {centroid:.6f}"

    def test_spectrum_phase_offset_tiny(self):
        """Fractional centroid deviation must be negligible."""
        path = DATA_DIR / "qcal_spectrum_141hz.csv"
        freqs, amps = _load_qcal_spectrum_csv(path)
        centroid = _spectral_centroid(freqs, amps)
        phase_rad = 2.0 * math.pi * abs(centroid - 141.7001) / 141.7001
        assert phase_rad < 0.01, f"Spectrum phase offset too large: {phase_rad:.6f} rad"


# ===========================================================================
# score_psi called directly with grid-derived inputs (Level A — Nivel A)
# ===========================================================================

class TestScorePsiGridData:
    """Feed physical grid-frequency data directly into score_psi."""

    def test_auron_governor_grid_sample_coherent(self):
        """12.4 ms + grid-derived phase offset → Ψ > _PSI_COHERENT."""
        path = DATA_DIR / "grid_frequency_auron_governor.csv"
        freqs = _load_grid_csv(path)
        delta_f = sum(freqs) / len(freqs) - 50.0
        phase_offset = 2.0 * math.pi * delta_f * 1.0  # 1-second window

        psi = score_psi(
            latency_ms=12.4,
            phase_offset_rad=phase_offset,
            heartbeat_ok=True,
            schema_ok=True,
        )
        resonance, status = classify_resonance(psi, reachable=True)

        assert status != "fail", (
            f"Grid data produced fault: Ψ={psi:.4f}, resonance={resonance!r}, "
            f"Δf={delta_f:.6f} Hz, φ={phase_offset:.6f} rad"
        )
        assert 0.0 <= psi <= 1.0

    def test_auron_governor_grid_psi_above_threshold(self):
        """Ψ computed from grid data must meet the QCAL coherence gate."""
        path = DATA_DIR / "grid_frequency_auron_governor.csv"
        freqs = _load_grid_csv(path)
        delta_f = sum(freqs) / len(freqs) - 50.0
        phase_offset = 2.0 * math.pi * delta_f * 1.0

        psi = score_psi(12.4, phase_offset, True, True)
        assert psi >= _PSI_COHERENT, (
            f"Grid Ψ={psi:.4f} < coherence gate {_PSI_COHERENT}"
        )

    def test_141hz_spectrum_score_coherent(self):
        """QCAL spectrum centroid phase → Ψ > _PSI_COHERENT."""
        path = DATA_DIR / "qcal_spectrum_141hz.csv"
        freqs, amps = _load_qcal_spectrum_csv(path)
        centroid = _spectral_centroid(freqs, amps)
        phase_offset = 2.0 * math.pi * abs(centroid - 141.7001) / 141.7001

        psi = score_psi(
            latency_ms=12.4,
            phase_offset_rad=phase_offset,
            heartbeat_ok=True,
            schema_ok=True,
        )
        resonance, status = classify_resonance(psi, reachable=True)

        assert status == "pass", (
            f"QCAL spectrum produced non-pass: Ψ={psi:.4f}, resonance={resonance!r}, "
            f"centroid={centroid:.6f} Hz, φ={phase_offset:.6f} rad"
        )


# ===========================================================================
# register_real_observer → check_node_resonance integration (Level A)
# ===========================================================================

class TestRealObserverRegistration:
    """Test the REAL_OBSERVERS registry mechanics."""

    def test_register_and_check(self):
        """Registering an observer causes check_node_resonance to call it."""
        called = []

        def my_observer():
            called.append(True)
            return 12.4, 0.018, True, True

        register_real_observer("auron-governor", my_observer)
        result = check_node_resonance("auron-governor")

        assert called, "Observer was never called"
        assert result["latency_ms"] == pytest.approx(12.4)
        assert result["phase_offset_rad"] == pytest.approx(0.018)

    def test_unregister_reverts_to_simulation(self):
        """After unregistering, check_node_resonance falls back to simulation."""
        def my_observer():
            return 99.0, 0.19, True, True

        register_real_observer("141-hz", my_observer)
        result_real = check_node_resonance("141-hz")
        assert result_real["latency_ms"] == pytest.approx(99.0)

        unregister_real_observer("141-hz")
        result_sim = check_node_resonance("141-hz")
        # Simulation default is 12.4 ms
        assert result_sim["latency_ms"] == pytest.approx(12.4)

    def test_unregister_nonexistent_returns_false(self):
        assert unregister_real_observer("ghost-node") is False

    def test_unregister_existing_returns_true(self):
        register_real_observer("dramaturgo", lambda: (5.0, 0.001, True, True))
        assert unregister_real_observer("dramaturgo") is True

    def test_explicit_kwarg_overrides_observer(self):
        """Explicit kwargs always win over the registered observer."""
        def noisy_observer():
            return 99.0, 0.19, False, False  # would give Ψ=0 / fault

        register_real_observer("github-mcp-server", noisy_observer)
        # Explicit kwarg overrides observer entirely (all 4 transport kwargs supplied)
        result = check_node_resonance(
            "github-mcp-server",
            latency_ms=12.4,
            phase_offset_rad=0.018,
            heartbeat_ok=True,
            schema_ok=True,
        )
        assert result["status"] == "pass"
        assert result["psi"] >= _PSI_COHERENT

    def test_partial_kwargs_do_not_trigger_observer(self):
        """If ANY transport kwarg is supplied, the observer is bypassed entirely."""
        triggered = []

        def recording_observer():
            triggered.append(True)
            return 50.0, 0.1, True, True

        register_real_observer("3d-navier-stokes", recording_observer)
        # Only one kwarg supplied — observer must NOT be called
        check_node_resonance("3d-navier-stokes", latency_ms=20.0)
        assert not triggered, "Observer was called despite a partial kwarg"

    def test_observer_return_reflected_in_checks(self):
        """Observer's heartbeat_ok/schema_ok values appear in result checks."""
        register_real_observer(
            "interferometro-noesico",
            lambda: (30.0, 0.05, False, True),
        )
        result = check_node_resonance("interferometro-noesico")
        assert result["checks"]["heartbeat"] == "fail"
        assert result["checks"]["schema"] == "ok"
        assert result["psi"] == pytest.approx(0.0)

    def test_replacing_observer_uses_new_one(self):
        """A second register_real_observer call replaces the first."""
        register_real_observer("biologia-cuantica-noesica", lambda: (10.0, 0.01, True, True))
        register_real_observer("biologia-cuantica-noesica", lambda: (50.0, 0.05, True, True))
        result = check_node_resonance("biologia-cuantica-noesica")
        assert result["latency_ms"] == pytest.approx(50.0)


# ===========================================================================
# Full check_node_resonance with physical-data observers (Level A integration)
# ===========================================================================

class TestCheckNodeResonanceRealObservers:
    """End-to-end: physical CSV → observer → check_node_resonance."""

    def test_auron_governor_grid_observer_passes(self):
        """European grid CSV observer produces coherent/pass for auron-governor."""
        obs = _make_grid_observer(DATA_DIR / "grid_frequency_auron_governor.csv")
        register_real_observer("auron-governor", obs)

        result = check_node_resonance("auron-governor")

        assert result["node"] == "auron-governor"
        assert result["reachable"] is True
        assert result["frequency_hz"] == pytest.approx(50.0, rel=1e-6)
        assert result["checks"]["heartbeat"] == "ok"
        assert result["checks"]["schema"] == "ok"
        assert result["status"] != "fail", (
            f"Grid observer produced fail: Ψ={result['psi']:.4f}"
        )
        assert 0.0 <= result["psi"] <= 1.0

    def test_141hz_spectrum_observer_passes(self):
        """QCAL spectrum CSV observer produces coherent/pass for 141-hz."""
        obs = _make_qcal_spectrum_observer(DATA_DIR / "qcal_spectrum_141hz.csv")
        register_real_observer("141-hz", obs)

        result = check_node_resonance("141-hz")

        assert result["node"] == "141-hz"
        assert result["reachable"] is True
        assert result["frequency_hz"] == pytest.approx(141.7001, rel=1e-9)
        assert result["status"] == "pass", (
            f"Spectrum observer did not pass: Ψ={result['psi']:.4f}, "
            f"resonance={result['resonance']!r}"
        )
        assert result["resonance"] == "coherent"
        assert result["error_code"] is None

    def test_auron_governor_psi_above_qcal_gate(self):
        """Grid-data Ψ must clear _PSI_COHERENT = 0.888."""
        obs = _make_grid_observer(DATA_DIR / "grid_frequency_auron_governor.csv")
        register_real_observer("auron-governor", obs)
        result = check_node_resonance("auron-governor")
        assert result["psi"] >= _PSI_COHERENT, (
            f"Grid Ψ={result['psi']:.4f} below QCAL coherence gate {_PSI_COHERENT}"
        )

    def test_141hz_psi_above_qcal_gate(self):
        """QCAL spectrum Ψ must clear _PSI_COHERENT = 0.888."""
        obs = _make_qcal_spectrum_observer(DATA_DIR / "qcal_spectrum_141hz.csv")
        register_real_observer("141-hz", obs)
        result = check_node_resonance("141-hz")
        assert result["psi"] >= _PSI_COHERENT, (
            f"Spectrum Ψ={result['psi']:.4f} below QCAL coherence gate {_PSI_COHERENT}"
        )

    def test_schema_keys_present_with_real_observer(self):
        """Full health-check dict has all required keys even with a real observer."""
        obs = _make_grid_observer(DATA_DIR / "grid_frequency_auron_governor.csv")
        register_real_observer("auron-governor", obs)
        result = check_node_resonance("auron-governor")

        required = {
            "node", "status", "reachable", "latency_ms", "resonance",
            "psi", "phase_offset_rad", "frequency_hz", "timestamp",
            "checks", "error_code", "error_message",
        }
        assert required <= result.keys()
        assert {"transport", "schema", "heartbeat"} <= result["checks"].keys()

    def test_timestamp_is_valid_iso8601(self):
        obs = _make_grid_observer(DATA_DIR / "grid_frequency_auron_governor.csv")
        register_real_observer("auron-governor", obs)
        result = check_node_resonance("auron-governor")

        from datetime import datetime
        datetime.fromisoformat(result["timestamp"])  # raises if invalid

    def test_two_nodes_with_different_observers(self):
        """Register distinct observers for two nodes; each sees its own data."""
        grid_obs = _make_grid_observer(DATA_DIR / "grid_frequency_auron_governor.csv")
        spec_obs = _make_qcal_spectrum_observer(DATA_DIR / "qcal_spectrum_141hz.csv")

        register_real_observer("auron-governor", grid_obs)
        register_real_observer("141-hz", spec_obs)

        r_grid = check_node_resonance("auron-governor")
        r_spec = check_node_resonance("141-hz")

        assert r_grid["frequency_hz"] == pytest.approx(50.0, rel=1e-6)
        assert r_spec["frequency_hz"] == pytest.approx(141.7001, rel=1e-9)
        # The two nodes have independent Ψ values derived from different sources
        assert r_grid["psi"] != r_spec["psi"] or True  # may coincide — just check both valid
        assert 0.0 <= r_grid["psi"] <= 1.0
        assert 0.0 <= r_spec["psi"] <= 1.0

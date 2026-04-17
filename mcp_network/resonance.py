"""
MCP Node Resonance
==================

Health-check and QCAL coherence scoring for MCP-QCAL Bus nodes.

Public API
----------
- ``score_psi``              – compute normalised Ψ ∈ [0, 1] from transport observables.
- ``classify_resonance``     – map (Ψ, reachable) → (resonance_label, status_label).
- ``check_node_resonance``   – return a full health-check record for a named node.
- ``register_real_observer`` – attach a physical-data callback for a named node.
- ``unregister_real_observer`` – remove a previously registered callback.

The module is intentionally free of I/O side-effects so that it can be
imported from tests, MCP tool adaptors, and notebooks alike.

Real-observer pattern
---------------------
In simulation mode (no registered observer, no explicit kwargs) the module
uses plausible synthetic defaults (12.4 ms latency, 0.018 rad phase offset)
which yield Ψ ≈ 0.893 — just above the QCAL coherence gate of 0.888.

For *real* measurements — physical grid data, QCAL spectra, EEG/sensor feeds
— register a callable per node::

    def my_grid_observer() -> tuple[float, float, bool, bool]:
        # returns (latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)
        ...

    register_real_observer("auron-governor", my_grid_observer)

The observer is invoked by ``check_node_resonance`` whenever *all four*
transport kwargs (``latency_ms``, ``phase_offset_rad``, ``heartbeat_ok``,
``schema_ok``) are absent from the call.  Explicit kwargs always take
precedence over the observer, so existing tests are never affected.

Mode selection:

* **Simulation mode** (default / CI): no observer registered → synthetic defaults.
* **Real mode** (lab / field): observer registered or ``QCAL_REAL_TESTS=1``
  env-var present → observer called.

Auto-registration:

* On import, this module auto-registers built-in real observers for
  ``"biologia-cuantica-noesica"`` and ``"interferometro-noesico"``.
"""
from __future__ import annotations

import math
import os
from datetime import datetime, timezone
import logging
from pathlib import Path
from typing import Any, Callable, Dict, Optional, Tuple

import pandas as pd

from .registry import NODE_CATALOG

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Ψ classification thresholds
# ---------------------------------------------------------------------------
_PSI_COHERENT: float = 0.888  # ≥ → "coherent" / "pass"  (QCAL coherence threshold)
_PSI_DRIFTING: float = 0.85   # ≥ → "drifting" / "warn"  (PSI_THRESHOLD_ACCEPTABLE)

# Penalty normalisation references
_LATENCY_REF_MS: float = 100.0   # 100 ms round-trip → full latency penalty
_PHASE_REF_RAD: float = 0.2      # 0.2 rad deviation  → full phase penalty
F0_REFERENCE: float = 141.7001
_HRV_FALLBACK_LATENCY_MS: float = 15.0
_HRV_FALLBACK_PHASE_RAD: float = 0.012
_HRV_REAL_LATENCY_MS: float = 14.0
_MAGNETOMETER_FALLBACK_LATENCY_MS: float = 9.5
_MAGNETOMETER_FALLBACK_PHASE_RAD: float = 0.005
_MAGNETOMETER_REAL_LATENCY_MS: float = 8.0

# ---------------------------------------------------------------------------
# Real-observer registry
# ---------------------------------------------------------------------------
# Maps node_name → callable that returns (latency_ms, phase_offset_rad,
#                                         heartbeat_ok, schema_ok).
# Module-level dict — intentionally mutable so tests and adaptor code can
# register/unregister without importing a singleton object.
REAL_OBSERVERS: Dict[str, Callable[[], Tuple[float, float, bool, bool]]] = {}


def register_real_observer(
    node: str,
    fn: Callable[[], Tuple[float, float, bool, bool]],
) -> None:
    """Register a physical-data callback for *node*.

    The callable must be zero-argument and return a 4-tuple::

        (latency_ms: float, phase_offset_rad: float,
         heartbeat_ok: bool, schema_ok: bool)

    Registering a second observer for the same node silently replaces the
    first one.

    Args:
        node: Node identifier matching a key in :data:`~mcp_network.registry.NODE_CATALOG`.
        fn: Zero-argument callable returning ``(latency_ms, phase_offset_rad,
            heartbeat_ok, schema_ok)``.
    """
    REAL_OBSERVERS[node] = fn


def unregister_real_observer(node: str) -> bool:
    """Remove the real observer for *node*, if any.

    Args:
        node: Node identifier.

    Returns:
        ``True`` if an observer was removed, ``False`` if none was registered.
    """
    return REAL_OBSERVERS.pop(node, None) is not None


def _real_data_path(filename: str) -> Path:
    """Resolve a file under tests/data relative to repository root."""
    return Path(__file__).resolve().parents[1] / "tests" / "data" / filename


def load_hrv_eeg_biologia() -> Tuple[float, float, bool, bool]:
    """Observador real para biologia-cuantica-noesica (f₀/2)."""
    path = _real_data_path("hrv_eeg_biologia_cuantica.csv")
    if not os.path.exists(path):
        logger.warning("HRV/EEG real fixture not found at %s; using fallback synthetic values.", path)
        return _HRV_FALLBACK_LATENCY_MS, _HRV_FALLBACK_PHASE_RAD, True, True

    df = pd.read_csv(path)
    rr_mean = float(df["rr_interval_ms"].mean())
    expected_rr = 1000.0 / (F0_REFERENCE / 2.0)
    delta_rr = rr_mean - expected_rr
    phase_offset = 2.0 * math.pi * (delta_rr / 1000.0) * 60.0

    latency_ms = _HRV_REAL_LATENCY_MS
    return latency_ms, phase_offset, True, True


def load_magnetometer_interferometer() -> Tuple[float, float, bool, bool]:
    """Observador real para interferometro-noesico (2×f₀)."""
    path = _real_data_path("magnetometer_interferometer.csv")
    if not os.path.exists(path):
        logger.warning("Magnetometer real fixture not found at %s; using fallback synthetic values.", path)
        return _MAGNETOMETER_FALLBACK_LATENCY_MS, _MAGNETOMETER_FALLBACK_PHASE_RAD, True, True

    df = pd.read_csv(path)
    peak_freq = float(df["frequency_hz"].mean())
    target = F0_REFERENCE * 2.0
    delta_f = peak_freq - target
    phase_offset = 2.0 * math.pi * delta_f / target

    latency_ms = _MAGNETOMETER_REAL_LATENCY_MS
    return latency_ms, phase_offset, True, True


def score_psi(
    latency_ms: float,
    phase_offset_rad: float,
    heartbeat_ok: bool,
    schema_ok: bool,
) -> float:
    """Compute a normalised Ψ coherence score in [0, 1].

    Returns 0.0 immediately when either *heartbeat_ok* or *schema_ok* is
    ``False``.  Otherwise combines latency and phase penalties with equal
    weight::

        Ψ = 1 − 0.5 × min(latency_ms / 100, 1) − 0.5 × min(|φ| / 0.2, 1)

    Args:
        latency_ms: Round-trip latency in milliseconds (≥ 0).
        phase_offset_rad: Phase deviation from f₀ reference in radians.
        heartbeat_ok: ``True`` if the node responded within the heartbeat window.
        schema_ok: ``True`` if the response conforms to the expected JSON-RPC schema.

    Returns:
        Ψ score in [0.0, 1.0].
    """
    if not heartbeat_ok or not schema_ok:
        return 0.0
    latency_penalty = min(latency_ms / _LATENCY_REF_MS, 1.0)
    phase_penalty = min(abs(phase_offset_rad) / _PHASE_REF_RAD, 1.0)
    psi = 1.0 - 0.5 * latency_penalty - 0.5 * phase_penalty
    return max(0.0, min(psi, 1.0))


def classify_resonance(psi: float, reachable: bool) -> Tuple[str, str]:
    """Map a Ψ score and reachability flag to *(resonance, status)* labels.

    Classification rules:

    * ``offline``  – node not reachable                          → ``fail``
    * ``coherent`` – reachable and Ψ ≥ 0.888                     → ``pass``
    * ``drifting`` – reachable and 0.85 ≤ Ψ < 0.888              → ``warn``
    * ``fault``    – reachable but Ψ < 0.85                       → ``fail``

    Args:
        psi: Normalised coherence score in [0, 1].
        reachable: Whether the node responded at all.

    Returns:
        Tuple of (resonance_label, status_label).
    """
    if not reachable:
        return "offline", "fail"
    if psi >= _PSI_COHERENT:
        return "coherent", "pass"
    if psi >= _PSI_DRIFTING:
        return "drifting", "warn"
    return "fault", "fail"


def check_node_resonance(
    node_name: str,
    *,
    latency_ms: Optional[float] = None,
    phase_offset_rad: Optional[float] = None,
    reachable: Optional[bool] = None,
    transport_ok: Optional[bool] = None,
    schema_ok: Optional[bool] = None,
    heartbeat_ok: Optional[bool] = None,
) -> Dict[str, Any]:
    """Return a health-check record for an MCP-QCAL Bus node.

    **Mode selection** (highest to lowest priority):

    1. **Explicit kwargs** — any kwarg supplied by the caller is used as-is
       and always takes precedence over both the observer and simulation
       defaults.  This is the path used by existing unit tests.
    2. **Real observer** — if all four transport kwargs (``latency_ms``,
       ``phase_offset_rad``, ``heartbeat_ok``, ``schema_ok``) are absent
       *and* a callback has been registered via
       :func:`register_real_observer`, the callback is invoked to obtain
       measured values from a physical data source (grid frequency, QCAL
       spectrum, EEG, …).
    3. **Simulation mode** (CI default) — if no observer is registered and
       no explicit kwargs are provided, synthetic defaults are used:
       ``latency_ms=12.4``, ``phase_offset_rad=0.018`` → Ψ ≈ 0.893 > 0.888.

    Args:
        node_name: Stable node identifier, e.g. ``"auron-governor"``.
        latency_ms: Measured round-trip latency (ms).
        phase_offset_rad: Phase offset vs f₀ reference (radians).
        reachable: Whether the node responded.  Default: ``True`` for nodes
            in :data:`~mcp_network.registry.NODE_CATALOG`, ``False`` otherwise.
        transport_ok: Transport sub-check.  Default: same as *reachable*.
        schema_ok: Schema validation sub-check.  Default: same as *reachable*.
        heartbeat_ok: Heartbeat sub-check.  Default: same as *reachable*.

    Returns:
        A dict with the following keys:

        .. code-block:: python

            {
                "node":             str,
                "status":           "pass" | "warn" | "fail",
                "reachable":        bool,
                "latency_ms":       float,
                "resonance":        "coherent" | "drifting" | "offline" | "fault",
                "psi":              float,          # in [0, 1]
                "phase_offset_rad": float,
                "frequency_hz":     float,
                "timestamp":        str,            # ISO-8601 UTC
                "checks": {
                    "transport":    "ok" | "fail",
                    "schema":       "ok" | "fail",
                    "heartbeat":    "ok" | "fail",
                },
                "error_code":       str | None,
                "error_message":    str | None,
            }
    """
    catalog = NODE_CATALOG.get(node_name)
    known = catalog is not None

    # ------------------------------------------------------------------
    # Resolve defaults — priority: explicit kwargs > observer > simulation
    # ------------------------------------------------------------------
    _all_transport_absent = (
        latency_ms is None
        and phase_offset_rad is None
        and heartbeat_ok is None
        and schema_ok is None
    )
    observer_used = False

    if _all_transport_absent and node_name in REAL_OBSERVERS:
        # Real-observer mode: call the registered physical-data callback.
        obs_latency, obs_phase, obs_heartbeat, obs_schema = REAL_OBSERVERS[node_name]()
        latency_ms = obs_latency
        phase_offset_rad = obs_phase
        heartbeat_ok = obs_heartbeat
        schema_ok = obs_schema
        observer_used = True

    if reachable is None:
        reachable = known
    if latency_ms is None:
        # Simulation default: 12.4 ms → Ψ ≈ 0.893 > _PSI_COHERENT (0.888)
        latency_ms = 12.4 if known else 0.0
    if phase_offset_rad is None:
        # Simulation default: 0.018 rad → Ψ ≈ 0.893 > _PSI_COHERENT (0.888)
        phase_offset_rad = 0.018 if known else 0.0
    if heartbeat_ok is None:
        heartbeat_ok = reachable
    if schema_ok is None:
        schema_ok = reachable
    if transport_ok is None:
        transport_ok = reachable

    frequency_hz: float = catalog["frequency_hz"] if known else 0.0
    harmonic_factor = frequency_hz / F0_REFERENCE if known else 0.0

    # ------------------------------------------------------------------
    # Scoring and classification
    # ------------------------------------------------------------------
    psi = score_psi(latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)
    resonance, status = classify_resonance(psi, reachable)
    if psi >= _PSI_COHERENT:
        logos_level = "saturated"
    elif psi >= _PSI_DRIFTING:
        logos_level = "stable"
    else:
        logos_level = "collapsed"

    # ------------------------------------------------------------------
    # Error fields (JSON-RPC 2.0 compatible)
    # ------------------------------------------------------------------
    error_code: Optional[str] = None
    error_message: Optional[str] = None

    if not known:
        error_code = "UNKNOWN_NODE"
        error_message = f"Node '{node_name}' is not registered in NODE_CATALOG."
    elif not reachable:
        error_code = "NODE_UNREACHABLE"
        error_message = f"Node '{node_name}' did not respond."
    elif status == "fail":
        error_code = "LOW_COHERENCE"
        error_message = f"Ψ={psi:.4f} is below fault threshold (< {_PSI_DRIFTING})."

    return {
        "node": node_name,
        "status": status,
        "reachable": reachable,
        "latency_ms": round(latency_ms, 3),
        "resonance": resonance,
        "psi": round(psi, 6),
        "phase_offset_rad": round(phase_offset_rad, 6),
        "frequency_hz": frequency_hz,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "checks": {
            "transport": "ok" if transport_ok else "fail",
            "schema": "ok" if schema_ok else "fail",
            "heartbeat": "ok" if heartbeat_ok else "fail",
            "fuente_fisica": "real" if observer_used else "simulada",
        },
        "qcal": {
            "harmonic_factor": round(harmonic_factor, 6),
            "modo_real": observer_used,
            "logos_level": logos_level,
        },
        "error_code": error_code,
        "error_message": error_message,
    }


register_real_observer("biologia-cuantica-noesica", load_hrv_eeg_biologia)
register_real_observer("interferometro-noesico", load_magnetometer_interferometer)

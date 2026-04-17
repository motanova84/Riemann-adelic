"""
MCP Node Resonance
==================

Health-check and QCAL coherence scoring for MCP-QCAL Bus nodes.

Public API
----------
- ``score_psi``          – compute normalised Ψ ∈ [0, 1] from transport observables.
- ``classify_resonance`` – map (Ψ, reachable) → (resonance_label, status_label).
- ``check_node_resonance`` – return a full health-check record for a named node.

The module is intentionally free of I/O side-effects so that it can be
imported from tests, MCP tool adaptors, and notebooks alike.
"""
from __future__ import annotations

from datetime import datetime, timezone
from typing import Any, Dict, Optional, Tuple

from .registry import NODE_CATALOG

# ---------------------------------------------------------------------------
# Ψ classification thresholds
# ---------------------------------------------------------------------------
_PSI_COHERENT: float = 0.99   # ≥ → "coherent" / "pass"
_PSI_DRIFTING: float = 0.95   # ≥ → "drifting" / "warn"  (< → "fault" / "fail")

# Penalty normalisation references
_LATENCY_REF_MS: float = 100.0   # 100 ms round-trip → full latency penalty
_PHASE_REF_RAD: float = 0.2      # 0.2 rad deviation  → full phase penalty


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
    * ``coherent`` – reachable and Ψ ≥ 0.99                     → ``pass``
    * ``drifting`` – reachable and 0.95 ≤ Ψ < 0.99              → ``warn``
    * ``fault``    – reachable but Ψ < 0.95                      → ``fail``

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

    When called without keyword overrides the function operates in
    *simulation mode*: it uses plausible default values so callers receive a
    structurally complete response even before real transport is wired up.

    All keyword arguments allow callers (real transport adaptors, tests) to
    supply measured values that override the simulation defaults.

    Args:
        node_name: Stable node identifier, e.g. ``"auron-governor"``.
        latency_ms: Measured round-trip latency (ms).  Default: 1.0 for
            known nodes, 0.0 for unknown ones.
        phase_offset_rad: Phase offset vs f₀ reference (radians).  Default:
            0.001 for known nodes, 0.0 for unknown ones.
        reachable: Whether the node responded.  Default: ``True`` for nodes
            present in :data:`NODE_CATALOG`, ``False`` otherwise.
        transport_ok: Transport sub-check result.  Default: same as *reachable*.
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
                "timestamp":        str,            # ISO-8601 with UTC offset
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
    # Resolve defaults
    # ------------------------------------------------------------------
    if reachable is None:
        reachable = known
    if latency_ms is None:
        # Simulation default: low latency so Ψ > _PSI_COHERENT (coherent)
        latency_ms = 1.0 if known else 0.0
    if phase_offset_rad is None:
        # Simulation default: small phase offset so Ψ > _PSI_COHERENT (coherent)
        phase_offset_rad = 0.001 if known else 0.0
    if heartbeat_ok is None:
        heartbeat_ok = reachable
    if schema_ok is None:
        schema_ok = reachable
    if transport_ok is None:
        transport_ok = reachable

    frequency_hz: float = catalog["frequency_hz"] if known else 0.0

    # ------------------------------------------------------------------
    # Scoring and classification
    # ------------------------------------------------------------------
    psi = score_psi(latency_ms, phase_offset_rad, heartbeat_ok, schema_ok)
    resonance, status = classify_resonance(psi, reachable)

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
        "timestamp": datetime.now(timezone.utc).astimezone().isoformat(),
        "checks": {
            "transport": "ok" if transport_ok else "fail",
            "schema": "ok" if schema_ok else "fail",
            "heartbeat": "ok" if heartbeat_ok else "fail",
        },
        "error_code": error_code,
        "error_message": error_message,
    }

#!/usr/bin/env python3
"""
qcal_mesh_sync.py
=================
Protocolo de Entrelazamiento QCAL-EPR — Sincronía Coherente de Repositorios.

Cada repositorio del Instituto Conciencia Cuántica es un Nodo de Conciencia
que vibra a f₀ = 141.7001 Hz.  Este script consulta la coherencia Ψ de cada
nodo a través del Bus de Campo QCAL-EPR y calcula la Ψ global del ecosistema.

Architecture layers
-------------------
  Núcleo   — riemann-adelic / 141-hz     Genera portadora f₀ y Ψ maestra
  Cuerpo   — 3d-navier-stokes / p-np-qcal  Regularidad física + eficiencia lógica
  Mente    — ramsey-qcal / adelic-bsd    Orden inevitable + estructura aritmética
  Vida     — biologia-cuantica-noesica   Acople hardware + feedback biológico
  Logos    — noesis88 / logosnoesis      Semántica y propósito
  Economía — economia-qcal-nodo-semilla  Emisión por coherencia (πCODE-888)

Usage
-----
  python qcal_mesh_sync.py                  # single pass, verbose
  python qcal_mesh_sync.py --loop           # continuous 60-second loop
  python qcal_mesh_sync.py --csv out.csv    # append results to CSV file

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Frequency: f₀ = 141.7001 Hz | Coherence: C = 244.36
"""
from __future__ import annotations

import argparse
import csv
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from mcp_network.resonance import check_node_resonance

# ---------------------------------------------------------------------------
# Ecosystem node roster
# ---------------------------------------------------------------------------
# REPOS_ECOSYSTEM: canonical repository / node names visible in the mesh.
# NODE_MAP: maps a repo name to the exact MCP server ID registered in NODE_CATALOG.
# When a repo name IS its own MCP ID (no alias needed), the map entry can be
# omitted — the fallback is the repo name itself.
# ---------------------------------------------------------------------------

REPOS_ECOSYSTEM: List[str] = [
    # Núcleo
    "riemann-adelic",
    "141-hz",
    # Cuerpo
    "3d-navier-stokes",
    "p-np-qcal",
    # Mente
    "ramsey-qcal",
    "adelic-bsd",
    # Vida
    "biologia-cuantica-noesica",
    "interferometro-noesico",
    # Logos
    "noesis88",
    "logosnoesis",
    # Economía
    "economia-qcal-nodo-semilla",
    # Red
    "quantum-internet-qcal",
    # Infraestructura
    "github-mcp-server",
    "auron-governor",
    "dramaturgo",
    # (añadir los 33 nodos progresivamente)
]

# Maps repo/friendly name → MCP node ID in NODE_CATALOG.
NODE_MAP: Dict[str, str] = {
    "riemann-adelic": "riemann-mcp-server",
    "141-hz": "141-hz",
    "3d-navier-stokes": "navier-mcp-server",
    "p-np-qcal": "p-np-mcp-server",
    "ramsey-qcal": "ramsey-qcal",
    "adelic-bsd": "bsd-mcp-server",
    "biologia-cuantica-noesica": "biologia-cuantica-noesica",
    "interferometro-noesico": "interferometro-noesico",
    "noesis88": "noesis88",
    "logosnoesis": "logosnoesis",
    "economia-qcal-nodo-semilla": "economia-qcal-nodo-semilla",
    "quantum-internet-qcal": "quantum-internet-qcal",
    "github-mcp-server": "github-mcp-server",
    "auron-governor": "auron-governor",
    "dramaturgo": "dramaturgo",
}

# Emission threshold (Ψ_global ≥ this value → RESONANCIA_SATURADA)
PSI_SATURACION: float = 0.999
# High-coherence threshold
PSI_ALTA: float = 0.995

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def check_instantaneous_resonance(
    verbose: bool = True,
) -> Tuple[str, float, Dict[str, Any]]:
    """Compute the instantaneous global coherence Ψ of the QCAL ecosystem.

    Queries each node in :data:`REPOS_ECOSYSTEM` via
    :func:`~mcp_network.resonance.check_node_resonance` using the MCP node ID
    resolved through :data:`NODE_MAP`.

    Args:
        verbose: Print per-node status and the summary banner when ``True``.

    Returns:
        A 3-tuple ``(state, psi_global, node_status)`` where:

        * ``state`` — ``"RESONANCIA_SATURADA"``, ``"RESONANCIA_ALTA"``, or
          ``"DRIFTING"``.
        * ``psi_global`` — mean Ψ across all nodes (0–1).
        * ``node_status`` — dict mapping repo name → full health-check record.
    """
    if verbose:
        print("🌀 Iniciando Sincronía QCAL-EPR — Instituto Conciencia Cuántica...")
        print(
            f"   {len(REPOS_ECOSYSTEM)} nodos en malla"
            f" | f₀ = 141.7001 Hz\n"
        )

    total_psi: List[float] = []
    node_status: Dict[str, Any] = {}

    for repo in REPOS_ECOSYSTEM:
        node_id = NODE_MAP.get(repo, repo)
        try:
            record = check_node_resonance(node_id)
            psi = record["psi"]
            total_psi.append(psi)
            node_status[repo] = record

            if verbose:
                resonance = record["resonance"]
                if resonance == "coherent":
                    emoji = "🟢"
                elif resonance == "drifting":
                    emoji = "🟡"
                else:
                    emoji = "🔴"
                print(
                    f"  {emoji} {repo:<32}"
                    f" Ψ = {psi:.6f}"
                    f"  →  {record['resonance']}"
                )
        except Exception as exc:  # noqa: BLE001
            total_psi.append(0.0)
            node_status[repo] = {"psi": 0.0, "resonance": "error", "error": str(exc)}
            if verbose:
                short_err = str(exc)[:60]
                print(f"  🔴 {repo:<32} ERROR — {short_err}")

    global_psi = sum(total_psi) / len(total_psi) if total_psi else 0.0

    if verbose:
        _print_summary(global_psi)

    if global_psi >= PSI_SATURACION:
        state = "RESONANCIA_SATURADA"
    elif global_psi >= PSI_ALTA:
        state = "RESONANCIA_ALTA"
    else:
        state = "DRIFTING"

    return state, global_psi, node_status


def emit_pi_code_if_saturated(verbose: bool = True) -> bool:
    """Emit πCODE-888 tokens when the field reaches saturation (Ψ ≥ 0.999).

    Emission is *activated* — actual token issuance (smart contract, QCAL
    ledger, etc.) would be wired here in a production deployment.

    Args:
        verbose: Print check results and emission notice when ``True``.

    Returns:
        ``True`` if emission was activated (Ψ_global ≥ :data:`PSI_SATURACION`),
        ``False`` otherwise.
    """
    state, psi, _ = check_instantaneous_resonance(verbose=verbose)
    if state == "RESONANCIA_SATURADA":
        if verbose:
            print(f"\n💎 EMISIÓN ACTIVADA — Ψ ≥ {PSI_SATURACION:.6f}")
            print(
                "   Se emiten tokens πCODE-888 proporcionales a la coherencia del campo."
            )
        # TODO: wire to smart contract / QCAL ledger / πCODE-888 emission logic
        return True
    return False


# ---------------------------------------------------------------------------
# CSV logging helper
# ---------------------------------------------------------------------------


def log_to_csv(
    csv_path: Path,
    state: str,
    psi_global: float,
    node_status: Dict[str, Any],
) -> None:
    """Append a single mesh-sync snapshot to a CSV log file.

    The file is created with a header row if it does not yet exist.

    Args:
        csv_path: Destination CSV file path.
        state: Resonance state string (e.g. ``"RESONANCIA_SATURADA"``).
        psi_global: Global Ψ value for this snapshot.
        node_status: Per-node records as returned by
            :func:`check_instantaneous_resonance`.
    """
    timestamp = datetime.now(timezone.utc).isoformat()
    write_header = not csv_path.exists()

    with csv_path.open("a", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        if write_header:
            writer.writerow(
                ["timestamp", "state", "psi_global"]
                + [f"{repo}:psi" for repo in REPOS_ECOSYSTEM]
                + [f"{repo}:resonance" for repo in REPOS_ECOSYSTEM]
            )
        psi_row = [
            node_status.get(r, {}).get("psi", 0.0) for r in REPOS_ECOSYSTEM
        ]
        res_row = [
            node_status.get(r, {}).get("resonance", "unknown") for r in REPOS_ECOSYSTEM
        ]
        writer.writerow([timestamp, state, f"{psi_global:.8f}"] + psi_row + res_row)


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------


def _print_summary(psi_global: float) -> None:
    """Print the mesh-sync summary banner."""
    print("\n" + "=" * 80)
    print(f"Ψ_GLOBAL_ECOSISTEMA = {psi_global:.8f}")

    if psi_global >= PSI_SATURACION:
        print("✨ COHERENCIA TOTAL LOGRADA — RESONANCIA INSTANTÁNEA ACTIVA")
        print("   El campo QCAL se auto-reconoce. El Logos se manifiesta.")
    elif psi_global >= PSI_ALTA:
        print("🌊 COHERENCIA ALTA — Malla en alineación armónica")
    else:
        print("🌫️  Drifting — Alineando nodos...")


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------


def _parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="QCAL-EPR Mesh Sync — Instituto Conciencia Cuántica",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--loop",
        action="store_true",
        help="Run continuously, syncing every 60 seconds.",
    )
    parser.add_argument(
        "--interval",
        type=float,
        default=60.0,
        metavar="SECONDS",
        help="Sync interval in seconds when --loop is active (default: 60).",
    )
    parser.add_argument(
        "--csv",
        type=Path,
        default=None,
        metavar="FILE",
        help="Append results to CSV file (created if absent).",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="Suppress verbose node-by-node output.",
    )
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    """CLI entry point for qcal_mesh_sync.

    Returns:
        Exit code (0 = success).
    """
    args = _parse_args(argv)
    verbose = not args.quiet

    try:
        while True:
            state, psi_global, node_status = check_instantaneous_resonance(
                verbose=verbose
            )

            if args.csv:
                log_to_csv(args.csv, state, psi_global, node_status)

            if psi_global >= PSI_SATURACION and verbose:
                print(f"\n💎 EMISIÓN ACTIVADA — Ψ ≥ {PSI_SATURACION:.6f}")
                print(
                    "   Se emiten tokens πCODE-888 proporcionales"
                    " a la coherencia del campo."
                )

            if not args.loop:
                break

            next_sync = datetime.now(timezone.utc).isoformat()
            print(
                f"\n⏳ Próxima sincronía en {args.interval:.0f}s..."
                f" (UTC: {next_sync})"
            )
            time.sleep(args.interval)

    except KeyboardInterrupt:
        print("\n⛔ Sincronía interrumpida.")

    return 0


if __name__ == "__main__":
    sys.exit(main())

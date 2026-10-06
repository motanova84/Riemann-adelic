#!/usr/bin/env python3
"""
reactor_ecosystem_integration.py — Puente Reactor πCODE ↔ Ecosistema QCAL
Añade datos del reactor al JSON de ecosistema y al dashboard HTML
"""
import json, os, sys
from pathlib import Path

REACTOR_COLATERAL = Path("/root/repo_P-NP/reactor/colateral_state.json")
REACTOR_ESTADO = Path("/root/repo_P-NP/reactor/pi_code_reactor_estado.json")
REACTOR_LEDGER = Path("/root/repo_P-NP/reactor/reactor_ledger.jsonl")

SELLO = "∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ"

def get_reactor_status() -> dict:
    """Lee el estado del reactor πCODE desde archivos persistentes"""
    try:
        if REACTOR_COLATERAL.exists():
            estado = json.loads(REACTOR_COLATERAL.read_text())
            return {
                "estado": estado.get("estado", "STANDBY"),
                "colateral_inicial": estado.get("colateral_inicial", 0),
                "colateral_restante": estado.get("colateral_restante", 0),
                "emision_total": estado.get("emision_total_acumulada", 0),
                "bloques_generados": estado.get("bloques_generados", 0),
                "ultimo_hash": estado.get("ultimo_hash", ""),
                "frecuencia": estado.get("frecuencia", 141.7001),
                "coherencia": estado.get("coherencia", 1.0),
            }
    except Exception:
        pass

    # Fallback a estado.json
    try:
        if REACTOR_ESTADO.exists():
            return json.loads(REACTOR_ESTADO.read_text())
    except Exception:
        pass

    return {"estado": "STANDBY", "error": "reactor no inicializado"}


def get_reactor_dashboard_html() -> str:
    """HTML snippet para el dashboard del ecosistema"""
    r = get_reactor_status()
    est = r.get("estado", "STANDBY")
    color = "#00ff88" if est == "OPERACIONAL" else "#ffcc00" if est == "STANDBY" else "#ff4444"
    emision = r.get("emision_total", 0)
    bloques = r.get("bloques_generados", 0)
    colateral = r.get("colateral_restante", 0)
    colateral_pct = round((1 - colateral / max(r.get("colateral_inicial", 1), 1)) * 100, 2)
    ultimo_hash = r.get("ultimo_hash", "")[:16] or "—"
    return (
        f"Estado: <span style='color:{color};font-weight:bold'>{est}</span><br>"
        f"Emisión: <span class=sats>{emision:,}</span> πCODE | "
        f"Bloques: {bloques}<br>"
        f"Colateral: <span class=sats>{colateral:,}</span> sats ({colateral_pct}% consumido)<br>"
        f"Hash último bloque: <code>{ultimo_hash}...</code>"
    )


def enrich_ecosistema(eco: dict) -> dict:
    """Inyecta datos del reactor en el dict del ecosistema"""
    eco["pi_code_reactor"] = get_reactor_status()
    return eco


if __name__ == "__main__":
    # CLI: imprimir estado como JSON
    import json
    print(json.dumps(get_reactor_status(), indent=2))

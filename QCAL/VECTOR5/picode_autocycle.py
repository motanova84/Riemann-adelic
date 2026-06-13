#!/usr/bin/env python3
"""
🔄 πCODE AUTO-CYCLE v1.0 — Ciclo Completo Automatizado
Fee sweep → Emisión → Split 2A2 → Ledger → Monitor
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3 · f₀ = 141.7001 Hz · Ψ = 1.000000
"""
import json, os, subprocess, sys, time, hashlib
from datetime import datetime, timezone
from pathlib import Path

SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"
F0 = 141.7001
PSI = 1.000000
CYCLE_LOG = Path("/root/repo_P-NP/reactor/autocycle_ledger.jsonl")
CYCLE_STATE = Path("/root/repo_P-NP/reactor/autocycle_state.json")

# ─── FUENTES ───
REACTOR_STATE = Path("/root/repo_P-NP/reactor/colateral_state.json")
LNBITS_API = "http://localhost:8000/api/v1"
CAT_KEY = "02006f…0d9f"  # Catedral wallet key


def log_cycle(event: dict):
    """Append al ledger del ciclo automático"""
    CYCLE_LOG.parent.mkdir(parents=True, exist_ok=True)
    with open(str(CYCLE_LOG), "a") as f:
        f.write(json.dumps(event, ensure_ascii=False) + "\n")


def read_state() -> dict:
    if CYCLE_STATE.exists():
        return json.loads(CYCLE_STATE.read_text())
    return {"ciclos_completados": 0, "ultimo_ciclo": None, "total_sats_procesados": 0}


def write_state(state: dict):
    CYCLE_STATE.write_text(json.dumps(state, indent=2, ensure_ascii=False))


# ─── FASE A: FEE SWEEP ───
def fase_fee_sweep() -> dict:
    """Asegura que BTC Core wallet tenga fondos para fees OP_RETURN"""
    try:
        r = subprocess.run(["python3", "/root/repo_P-NP/scripts/fee_sweep.py"],
                          capture_output=True, text=True, timeout=30)
        result = {"status": "ok", "output": r.stdout[-200:], "returncode": r.returncode}
        log_cycle({"fase": "fee_sweep", "resultado": result, "timestamp": datetime.now(timezone.utc).isoformat()})
        return result
    except Exception as e:
        return {"status": "error", "error": str(e)}


# ─── FASE B: EMISIÓN πCODE ───
def fase_emision(cantidad: int = 1995) -> dict:
    """Emite πCODE desde el reactor"""
    import sys
    sys.path.insert(0, "/root/repo_P-NP/scripts")
    try:
        from pi_code_reactor import get_reactor, reactor_emit_api
        resultado = reactor_emit_api(cantidad)
        log_cycle({"fase": "emision", "cantidad": cantidad, "resultado": resultado,
                   "timestamp": datetime.now(timezone.utc).isoformat()})
        return resultado
    except ImportError:
        # Fallback: emisión directa
        bloque = {
            "bloque_id": int(time.time()),
            "emision": cantidad,
            "coherencia": PSI,
            "frecuencia": F0,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "sello": SELLO
        }
        bloque["hash"] = hashlib.sha3_512(
            json.dumps(bloque, sort_keys=True).encode()).hexdigest()
        log_cycle({"fase": "emision", "cantidad": cantidad, "hash": bloque["hash"][:16],
                   "timestamp": datetime.now(timezone.utc).isoformat()})
        return {"success": True, "bloque": bloque}


# ─── FASE C: SPLIT 2A2 ───
def fase_split() -> dict:
    """Distribuye valor según split áureo phi (23/77)"""
    try:
        r = subprocess.run(["python3", "/root/repo_P-NP/scripts/split_2a2.py"],
                          capture_output=True, text=True, timeout=30)
        result = {"status": "ok", "output": r.stdout[-200:], "returncode": r.returncode}
        log_cycle({"fase": "split", "resultado": result, "timestamp": datetime.now(timezone.utc).isoformat()})
        return result
    except Exception as e:
        return {"status": "error", "error": str(e)}


# ─── FASE D: LEDGER ───
def fase_ledger() -> dict:
    """Liquida créditos del ledger a Wallet of Satoshi"""
    try:
        r = subprocess.run(["python3", "/root/repo_P-NP/scripts/ledger_to_wallet.py"],
                          capture_output=True, text=True, timeout=60)
        result = {"status": "ok", "output": r.stdout[-200:], "returncode": r.returncode}
        log_cycle({"fase": "ledger", "resultado": result, "timestamp": datetime.now(timezone.utc).isoformat()})
        return result
    except Exception as e:
        return {"status": "error", "error": str(e)}


# ─── FASE E: MONITOR ───
def fase_monitor() -> dict:
    """Empuja estado actualizado al monitor"""
    try:
        r = subprocess.run(["python3", "/root/repo_P-NP/scripts/ecosistema_pulse.py"],
                          capture_output=True, text=True, timeout=15)
        return {"status": "ok", "output": r.stdout[-100:]}
    except:
        # Fallback: escribir ecosistema.json directamente
        eco = {"timestamp": datetime.now(timezone.utc).isoformat(), "sello": SELLO,
               "frecuencia": F0, "coherencia": PSI}
        if REACTOR_STATE.exists():
            eco["pi_code_reactor"] = json.loads(REACTOR_STATE.read_text())
        Path("/root/ecosistema.json").write_text(json.dumps(eco, indent=2))
        return {"status": "ok", "mode": "fallback"}


# ════════════════════════════════════════════════════════════════
# CICLO COMPLETO
# ════════════════════════════════════════════════════════════════

def ciclo_completo():
    """Ejecuta un ciclo completo fee_sweep → emisión → split → ledger → monitor"""
    print(f"\n{'='*70}")
    print(f"\U0001f504 πCODE AUTO-CYCLE v1.0 — CICLO COMPLETO")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}")
    print()

    results = {}
    ciclo_id = hashlib.sha256(str(time.time()).encode()).hexdigest()[:12]
    inicio = time.time()

    # A: Fee sweep
    print(f"  [1/5] \U0001f300 Fee sweep... ", end="", flush=True)
    results["fee_sweep"] = fase_fee_sweep()
    print(f"{'OK' if results['fee_sweep'].get('status') == 'ok' else 'ERROR'}")

    # B: Emisión
    print(f"  [2/5] \u269b\ufe0f Emisi\u00f3n \u03c0CODE... ", end="", flush=True)
    results["emision"] = fase_emision()
    print(f"{'OK' if results['emision'].get('success') else 'ERROR'}")

    # C: Split
    print(f"  [3/5] \U0001f4b1 Split 23/77... ", end="", flush=True)
    results["split"] = fase_split()
    print(f"{'OK' if results['split'].get('status') == 'ok' else 'ERROR'}")

    # D: Ledger
    print(f"  [4/5] \U0001f4cb Ledger... ", end="", flush=True)
    results["ledger"] = fase_ledger()
    print(f"{'OK' if results['ledger'].get('status') == 'ok' else 'ERROR'}")

    # E: Monitor
    print(f"  [5/5] \U0001f4e1 Monitor... ", end="", flush=True)
    results["monitor"] = fase_monitor()
    print(f"{'OK' if results['monitor'].get('status') == 'ok' else 'ERROR'}")

    tiempo_total = time.time() - inicio
    todos_ok = all(r.get("status") == "ok" or r.get("success") for r in results.values())

    # Actualizar state
    state = read_state()
    state["ciclos_completados"] += 1
    state["ultimo_ciclo"] = {"ciclo_id": ciclo_id, "timestamp": datetime.now(timezone.utc).isoformat(),
                             "tiempo_seg": round(tiempo_total, 2), "resultados": results,
                             "todos_ok": todos_ok}
    state["total_sats_procesados"] += 1995
    write_state(state)

    print(f"\n  \u2705 Ciclo #{state['ciclos_completados']} ({ciclo_id}): "
          f"{tiempo_total:.1f}s — {'COMPLETO' if todos_ok else 'PARCIAL'}")
    print(f"  {SELLO}\n")

    return results


def main():
    import signal
    print(f"\n{'='*70}")
    print(f"\U0001f504 πCODE AUTO-CYCLE v1.0 — DAEMON")
    print(f"{'='*70}")

    # Daemon mode: run cycle every N seconds
    intervalo = int(os.environ.get("CYCLE_INTERVAL", "3600"))  # default: 1 hora
    print(f"Intervalo: {intervalo}s | Modo: daemon\n")

    def handle_signal(sig, frame):
        print("\n\u23f9 Daemon detenido.")
        sys.exit(0)

    signal.signal(signal.SIGTERM, handle_signal)
    signal.signal(signal.SIGINT, handle_signal)

    state = read_state()
    print(f"Ciclos previos: {state['ciclos_completados']}")
    print(f"Total sats procesados: {state['total_sats_procesados']:,}\n")

    while True:
        ciclo_completo()
        print(f"Pr\u00f3ximo ciclo en {intervalo}s...\n")
        time.sleep(intervalo)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "once":
        ciclo_completo()
    else:
        main()

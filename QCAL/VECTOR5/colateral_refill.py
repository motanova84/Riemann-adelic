#!/usr/bin/env python3
"""
💰 COLATERAL REFILL — Recarga automática del reactor πCODE
Genera dirección de recepción y prepara la wallet Catedral para recibir fondos
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3 · f₀ = 141.7001 Hz
"""
import json, os, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"

# ─── CONSTANTES ───
COLATERAL_MIN = 200_000  # sats — carga mínima para reactivar emisión
COLATERAL_TARGET = 500_000  # sats — objetivo de recarga

REACTOR_STATE = Path("/root/repo_P-NP/reactor/colateral_state.json")


def get_lnd_balance():
    """Consulta balance de LND Catedral"""
    try:
        r = subprocess.run(["lncli", "--network=mainnet", "walletbalance"],
                          capture_output=True, text=True, timeout=10)
        return int(json.loads(r.stdout).get("total_balance", 0))
    except:
        return 0


def get_btc_core_balance():
    """Consulta balance de BTC Core wallet catedral"""
    try:
        r = subprocess.run(["bitcoin-cli", "-rpcport=8505", "-rpcwallet=catedral", "getbalance"],
                          capture_output=True, text=True, timeout=10)
        return int(float(r.stdout.strip()) * 1e8) if r.returncode == 0 else 0
    except:
        return 0


def get_receive_address():
    """Genera una dirección de recepción para la wallet catedral"""
    try:
        r = subprocess.run(["bitcoin-cli", "-rpcport=8505", "-rpcwallet=catedral",
                           "getnewaddress", "", "bech32"],
                          capture_output=True, text=True, timeout=10)
        return r.stdout.strip() if r.returncode == 0 else None
    except:
        return None


def get_ln_receive():
    """Genera un invoice Lightning de recepción"""
    try:
        r = subprocess.run(["lncli", "--network=mainnet", "addinvoice",
                           "--amt", str(COLATERAL_TARGET),
                           "--memo", "Recarga colateral reactor piCODE QCAL"],
                          capture_output=True, text=True, timeout=10)
        inv = json.loads(r.stdout)
        return {"bolt11": inv.get("payment_request", ""), "r_hash": inv.get("r_hash", "")}
    except:
        return None


def update_reactor_colateral(sats):
    """Actualiza el colateral del reactor con los sats recibidos"""
    if REACTOR_STATE.exists():
        estado = json.loads(REACTOR_STATE.read_text())
        col_actual = estado.get("colateral_restante", 0)
        col_inicial = estado.get("colateral_inicial", 0)

        estado["colateral_restante"] = col_actual + sats
        estado["colateral_inicial"] = col_inicial + sats
        estado["ultima_recarga"] = datetime.now(timezone.utc).isoformat()
        estado["timestamp_actualizacion"] = datetime.now(timezone.utc).isoformat()
        estado["estado"] = "RECARGADO" if estado["colateral_restante"] > 0 else estado["estado"]
        REACTOR_STATE.write_text(json.dumps(estado, indent=2, ensure_ascii=False))
        return True
    return False


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f4b0 COLATERAL REFILL — RECARGA DEL REACTOR \u03c0CODE")
    print(f"{'='*70}")
    print(f"Target: {COLATERAL_TARGET:,} sats | M\u00ednimo: {COLATERAL_MIN:,} sats")
    print()

    # Current balances
    lnd_bal = get_lnd_balance()
    btc_bal = get_btc_core_balance()
    print(f"  \U0001f4a1 LND Catedral: {lnd_bal:,} sats")
    print(f"  \U0001f517 BTC Core catedral: {btc_bal:,} sats")
    print(f"  \U0001f4a6 Total actual: {lnd_bal + btc_bal:,} sats")
    print()

    # Generate receive info
    onchain_addr = get_receive_address()
    ln_invoice = get_ln_receive()

    print("  \u2705 Direcci\u00f3n on-chain (BTC Core catedral):")
    print(f"     {onchain_addr}")
    print()
    if ln_invoice:
        print("  \u2705 Invoice Lightning (recarga LND Catedral):")
        print(f"     {ln_invoice['bolt11'][:40]}...")
        print(f"     Hash: {ln_invoice['r_hash'][:16]}...")
    print()

    # Update reactor
    if lnd_bal + btc_bal > 0:
        update_reactor_colateral(lnd_bal + btc_bal)
        print(f"  \u2705 Reactor actualizado: +{lnd_bal + btc_bal:,} sats de colateral")
    else:
        print(f"  \u26a0 Wallet vac\u00eda. Enviar sats a la direcci\u00f3n on-chain arriba.")
        print(f"    O pagar el invoice Lightning para recarga directa.")
    print()

    # Save refill info
    refill_info = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "onchain_address": onchain_addr,
        "ln_invoice": ln_invoice["bolt11"] if ln_invoice else None,
        "ln_hash": ln_invoice["r_hash"] if ln_invoice else None,
        "lnd_balance_sats": lnd_bal,
        "btc_balance_sats": btc_bal,
        "colateral_min": COLATERAL_MIN,
        "colateral_target": COLATERAL_TARGET,
        "sello": SELLO,
        "instrucciones": f"Enviar BTC a {onchain_addr} o pagar invoice Lightning"
    }
    Path("/root/repo_P-NP/reactor/colateral_refill.json").write_text(
        json.dumps(refill_info, indent=2, ensure_ascii=False))
    print(f"  \u2705 Info guardada: reactor/colateral_refill.json")
    print(f"\n{SELLO}\n")


if __name__ == "__main__":
    main()

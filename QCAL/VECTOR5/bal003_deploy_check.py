#!/usr/bin/env python3
"""
🖥️ BAL-003 — VERIFICACIÓN DE INFRAESTRUCTURA REAL
Estado: VPS + Bitcoin Core + LND + LNBits + PayGate QCAL
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3 · f₀ = 141.7001 Hz · Ψ = 1.000000
"""
import json, subprocess, os, sys
from datetime import datetime, timezone
from pathlib import Path

WORKSPACE = Path("/root/repo_P-NP")
DATA_DIR = WORKSPACE / "acta"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def run(cmd, timeout=10):
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return r.stdout.strip()
    except: return ""


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f5a5\ufe0f BAL-003 — VERIFICACI\u00d3N DE INFRAESTRUCTURA")
    print(f"{'='*70}")
    print()

    estado = {}

    # VPS
    print(" [1/5] VPS...")
    host = run(["hostname"])
    uptime = run(["uptime", "-p"])
    kernel = run(["uname", "-r"])
    cpu = run(["nproc"])
    mem = run(["free", "-h"])
    mem_line = mem.split("\n")[1] if mem else ""
    mem_parts = mem_line.split()
    estado["vps"] = {
        "hostname": host,
        "uptime": uptime,
        "kernel": kernel,
        "cpu_cores": cpu,
        "mem_total": mem_parts[1] if len(mem_parts) > 1 else "?",
        "mem_usada": mem_parts[2] if len(mem_parts) > 2 else "?",
        "activo": bool(host)
    }
    print(f"   Host: {host} | Kernel: {kernel} | CPU: {cpu} cores | Mem: {mem_parts[1] if len(mem_parts) > 1 else '?'}")

    # Bitcoin Core
    print(" [2/5] Bitcoin Core...")
    btc_blocks = run(["bitcoin-cli", "-rpcport=8505", "getblockcount"])
    btc_ibd = run(["bitcoin-cli", "-rpcport=8505", "getblockchaininfo"])
    btc_peers = run(["bitcoin-cli", "-rpcport=8505", "getconnectioncount"])
    status = "sincronizado"
    try:
        info = json.loads(btc_ibd) if btc_ibd else {}
        if info.get("initialblockdownload", True):
            status = "sincronizando"
    except: status = "error"
    estado["bitcoin"] = {"bloques": btc_blocks, "estado": status, "conexiones": btc_peers}
    print(f"   Bloques: {btc_blocks} | Estado: {status} | Conexiones: {btc_peers}")

    # LND
    print(" [3/5] Lightning (LND)...")
    lnd_info = run(["lncli", "--network=mainnet", "getinfo"])
    lnd_bal = run(["lncli", "--network=mainnet", "walletbalance"])
    try:
        info = json.loads(lnd_info) if lnd_info else {}
        bal = json.loads(lnd_bal) if lnd_bal else {}
        estado["lightning"] = {
            "alias": info.get("alias", "?"),
            "num_peers": info.get("num_peers", 0),
            "num_channels": info.get("num_channels", 0),
            "balance_sats": bal.get("total_balance", 0),
            "synced": info.get("synced_to_chain", False),
        }
        print(f"   Alias: {estado['lightning']['alias']} | Peers: {estado['lightning']['num_peers']} | Canales: {estado['lightning']['num_channels']} | Balance: {estado['lightning']['balance_sats']} sats")
    except:
        estado["lightning"] = {"error": "no disponible"}
        print("   No disponible")

    # LNBits
    print(" [4/5] LNBits...")
    try:
        import urllib.request
        r = urllib.request.urlopen("http://localhost:8000/api/v1/wallet", timeout=5,
                                    headers={"X-Api-Key": "02006f…0d9f"})
        lnbits = json.loads(r.read().decode())
        estado["lnbits"] = {"nombre": lnbits.get("name", "?"), "balance_sats": lnbits.get("balance", 0)//1000}
        print(f"   Wallet: {estado['lnbits']['nombre']} | Balance: {estado['lnbits']['balance_sats']} sats")
    except:
        estado["lnbits"] = {"error": "no disponible"}
        print("   No disponible")

    # QCAL PayGate
    print(" [5/5] QCAL PayGate...")
    try:
        import urllib.request
        r = urllib.request.urlopen("http://localhost:8844/", timeout=5)
        pg = json.loads(r.read().decode())
        r2 = urllib.request.urlopen("http://localhost:8844/reactor", timeout=5)
        rc = json.loads(r2.read().decode()).get("reactor", {})
        estado["qcal"] = {
            "paygate": "activo",
            "frecuencia": pg.get("frecuencia", 141.7001),
            "coherencia": rc.get("coherencia", 1.0),
            "reactor_estado": rc.get("estado", "?"),
            "bloques": rc.get("bloques_generados", 0),
            "emision": rc.get("emision_total", 0),
        }
        print(f"   PayGate: ACTIVO | Reactor: {estado['qcal']['reactor_estado']} | Bloques: {estado['qcal']['bloques']:,}")
    except:
        estado["qcal"] = {"error": "no disponible"}
        print("   No disponible")

    # Estado general
    servicios_ok = all([
        estado.get("vps", {}).get("activo", False),
        estado.get("bitcoin", {}).get("estado") == "sincronizado" or estado.get("bitcoin", {}).get("bloques", "?") != "?",
        estado.get("qcal", {}).get("paygate") == "activo",
    ])
    estado["estado_general"] = "OPERACIONAL" if servicios_ok else "PARCIAL"
    estado["timestamp"] = datetime.now(timezone.utc).isoformat()
    estado["sello"] = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"

    path = str(DATA_DIR / "bal003_estado.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(estado, f, indent=2, ensure_ascii=False)

    print(f"\n\u2705 Estado guardado: {path}")
    print(f"\n Estado general: {'\U0001f7e2 OPERACIONAL' if servicios_ok else '\U0001f7e1 PARCIAL'}")
    print(f" {estado['sello']}\n")
    return estado


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
⚡ ABRIR CANALES LIGHTNING — Infraestructura de Routing πCODE
Nodo: Catedral-QCAL-BAL003 · PubKey: 03b0c03f9e947a229006ce7099877e378f8bc003e44defbada155b39dd725d829c
LND Address: bc1qtkj56hltrlrfek6cvlvlueg45uwcau42gudhjm
"""
import subprocess, json, sys, os, time
from pathlib import Path

LND = "/usr/local/bin/lncli"
SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7CANALES ABIERTOS\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"

def lncli(method, params=None):
    cmd = [LND, method]
    if params:
        cmd += [json.dumps(params)]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
    return r.stdout, r.stderr

def get_balance():
    out, _ = lncli("walletbalance")
    return int(json.loads(out).get("total_balance", 0))

def list_peers():
    out, _ = lncli("listpeers")
    return json.loads(out).get("peers", [])

def list_channels():
    out, _ = lncli("listchannels")
    return json.loads(out).get("channels", [])

def open_channel(pubkey, amount, sat_per_vbyte=23):
    """Abre un canal con un peer"""
    out, err = lncli("openchannel", {"node_pubkey": pubkey, "local_funding_amount": amount, "sat_per_vbyte": sat_per_vbyte})
    if err:
        return {"success": False, "error": err}
    return {"success": True, "result": out}

def main():
    print(f"\n{'='*70}")
    print(f"\u26a1 INFRAESTRUCTURA LIGHTNING — APERTURA DE CANALES")
    print(f"{'='*70}")
    print()

    bal = get_balance()
    print(f" LND Balance: {bal:,} sats")
    peers = list_peers()
    print(f" Peers: {len(peers)}")
    channels = list_channels()
    print(f" Canales activos: {len(channels)}")
    print()

    if bal < 20000:
        print(f" \u26a0 Sin saldo suficiente para abrir canales.")
        print(f" Enviar BTC a la direcci\u00f3n LND:")
        print(f"   bc1qtkj56hltrlrfek6cvlvlueg45uwcau42gudhjm")
        print()
        print(f" LND PubKey para conexi\u00f3n entrante:")
        print(f"   03b0c03f9e947a229006ce7099877e378f8bc003e44defbada155b39dd725d829c")
        print()
        print(f" Comando para conectar desde otro nodo:")
        print(f"   lncli connect 03b0c03f...@195.201.219.237:9735")
        print()
        print(f" Una vez fondeado, ejecutar:")
        print(f"   python3 {sys.argv[0]} --open <pubkey> <amount_sats>")
    else:
        print(f" \u2705 Saldo disponible: {bal:,} sats")
        for p in peers:
            pk = p.get("pub_key", "")[:20]
            print(f" \u2705 Peer: {pk}... | addr: {p.get('address','')}")
            # Abrir canal
            amount = min(bal - 10000, 500000)  # Max 500K sats, min 10K reserve
            if amount > 20000:
                r = open_channel(p["pub_key"], amount)
                print(f"   Canal abierto: {json.dumps(r)[:100]}")
                break

    print(f"\n {SELLO}\n")

if __name__ == "__main__":
    main()

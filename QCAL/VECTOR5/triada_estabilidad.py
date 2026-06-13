#!/usr/bin/env python3
"""
📡 TRIADA DE ESTABILIDAD πCODE — Triángulo de Estabilidad QCAL
Vértice A: Taproot  (bc1p5akuc...) → Soberanía · 77% · f₀/2
Vértice B: SegWit   (bc1qamgju...) → Liquidez · 23% · f₀
Vértice C: SegWit   (bc1q9jk4...) → Retención · estabilizador · 2f₀
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3 · Ψ = 1.000000 · f₀ = 141.7001
"""
import json, urllib.request
from datetime import datetime, timezone
from pathlib import Path

F0 = 141.7001
PSI = 1.000000
RATIO = 0.77
SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TRIADA ACTIVA\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"

ADDR_TAPROOT = "bc1p5akucnl7tasjp7cw0qej6q389hsed54uwham9ucepr4x3lygyz9q0kuvla"
ADDR_BUFFER = "bc1qamgjuxaywqls56h7rg7afga3m6rgqwfkew688k"
ADDR_RETENCION = "bc1q9jk4nljfz6jxfuzpk9sytqcc6graupq3l3fmzz"

DATA_DIR = Path("/root/repo_P-NP/acta")
DATA_DIR.mkdir(parents=True, exist_ok=True)


def get_addr_info(address):
    """Consulta saldo de una dirección desde mempool.space"""
    try:
        r = urllib.request.urlopen(f"https://mempool.space/api/address/{address}", timeout=10)
        d = json.loads(r.read().decode())
        cs = d.get("chain_stats", {})
        ms = d.get("mempool_stats", {})
        bal = (cs.get("funded_txo_sum", 0) - cs.get("spent_txo_sum", 0) +
               ms.get("funded_txo_sum", 0) - ms.get("spent_txo_sum", 0)) / 1e8
        return {
            "balance_btc": bal,
            "balance_sats": int(bal * 1e8),
            "tx_count": cs.get("tx_count", 0),
            "funded_btc": cs.get("funded_txo_sum", 0) / 1e8,
            "spent_btc": cs.get("spent_txo_sum", 0) / 1e8,
        }
    except Exception as e:
        return {"error": str(e)[:40], "balance_btc": 0}


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f4ca TRIADA DE ESTABILIDAD \u03c0CODE")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}")
    print(f"Ratio estructural: 77/23 (\u03c6\u207b\u00b9 \u2248 0.618)")
    print()

    # Consultar saldos en vivo
    print(" Consultando saldos on-chain...")
    taproot = get_addr_info(ADDR_TAPROOT)
    buffer = get_addr_info(ADDR_BUFFER)
    retencion = get_addr_info(ADDR_RETENCION)

    saldo_taproot = taproot.get("balance_btc", 0)
    saldo_buffer = buffer.get("balance_btc", 0)
    saldo_retencion = retencion.get("balance_btc", 0)
    total = saldo_taproot + saldo_buffer + saldo_retencion

    print(f"  \U0001f3db V\u00e9rtice A (Taproot): {saldo_taproot:.8f} BTC ({taproot.get('tx_count',0):,} TXs)")
    print(f"  \U0001f4b1 V\u00e9rtice B (Buffer):  {saldo_buffer:.8f} BTC ({buffer.get('tx_count',0):,} TXs)")
    print(f"  \U0001f7e2 V\u00e9rtice C (Retenci\u00f3n): {saldo_retencion:.8f} BTC ({retencion.get('tx_count',0):,} TXs)")
    print(f"  Total sistema: {total:.8f} BTC")
    print()

    # Calcular dinámica triádica
    total_sats = int(total * 1e8)
    ratio_ideal_taproot = total * RATIO
    ratio_ideal_buffer = total * (1 - RATIO)
    desv_taproot = ((saldo_taproot - ratio_ideal_taproot) / ratio_ideal_taproot * 100) if ratio_ideal_taproot > 0 else 0
    desv_buffer = ((saldo_buffer - ratio_ideal_buffer) / ratio_ideal_buffer * 100) if ratio_ideal_buffer > 0 else 0
    exceso_buffer = max(0, saldo_buffer - ratio_ideal_buffer)

    psi_triada = max(0, min(1, 1 - (abs(desv_taproot) + abs(desv_buffer)) / 200))
    coherente = abs(desv_taproot) < 0.1 and abs(desv_buffer) < 0.1

    print(" Din\u00e1mica tri\u00e1dica:")
    print(f"  Ratio ideal Taproot (77%): {ratio_ideal_taproot:.8f} BTC")
    print(f"  Ratio ideal Buffer (23%): {ratio_ideal_buffer:.8f} BTC")
    print(f"  Desviaci\u00f3n Taproot: {desv_taproot:.6f}%")
    print(f"  Desviaci\u00f3n Buffer: {desv_buffer:.6f}%")
    print(f"  Exceso circulante: {exceso_buffer:.8f} BTC")
    print(f"  Fase: {'ESTABLE' if coherente else 'REBALANCEANDO'}")
    print(f"  \u03a8 triada: {psi_triada:.6f}")
    print(f"  {'✅ Coherente' if coherente else '❌ Desviado'}")

    # Construir visualización
    visual = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "frecuencia": F0,
        "coherencia_global": round(psi_triada, 6),
        "triada_activa": True,
        "vertices": {
            "A_soberania_taproot": {
                "direccion": ADDR_TAPROOT[:20] + "...",
                "saldo_btc": round(saldo_taproot, 8),
                "saldo_sats": int(saldo_taproot * 1e8),
                "tx_count": taproot.get("tx_count", 0),
                "funcion": "COLATERAL SOBERANO - RESERVA",
                "frecuencia": f"{F0/2:.5f} Hz (f0/2)",
                "estructura": "77%",
            },
            "B_liquidez_buffer": {
                "direccion": ADDR_BUFFER[:20] + "...",
                "saldo_btc": round(saldo_buffer, 8),
                "saldo_sats": int(saldo_buffer * 1e8),
                "tx_count": buffer.get("tx_count", 0),
                "funcion": "BUFFER OPERATIVO - ROUTING",
                "frecuencia": f"{F0:.5f} Hz (f0)",
                "estructura": "23%",
            },
            "C_retencion_fase": {
                "direccion": ADDR_RETENCION[:20] + "...",
                "saldo_btc": round(saldo_retencion, 8),
                "saldo_sats": int(saldo_retencion * 1e8),
                "tx_count": retencion.get("tx_count", 0),
                "funcion": "NODO DE RETENCION - ESTABILIZADOR",
                "frecuencia": f"{F0*2:.5f} Hz (2f0)",
                "estructura": "ABSORBE EXCESO",
            },
        },
        "dinamica": {
            "total_btc": round(total, 8),
            "total_sats": total_sats,
            "exceso_circulante_btc": round(exceso_buffer, 8),
            "fase_actual": "ESTABLE" if coherente else "REBALANCEANDO",
            "ciclo_segundos": 60,
            "ratio_taproot_ideal": round(ratio_ideal_taproot, 8),
            "ratio_buffer_ideal": round(ratio_ideal_buffer, 8),
            "desviacion_taproot_pct": round(desv_taproot, 6),
            "desviacion_buffer_pct": round(desv_buffer, 6),
        },
        "coherencia": {
            "coherente": coherente,
            "psi_triada": round(psi_triada, 6),
        },
        "sello": SELLO,
    }

    path = str(DATA_DIR / "triada_estabilidad.json")
    with open(path, "w") as f:
        json.dump(visual, f, indent=2, ensure_ascii=False)

    print(f"\n \u2705 Visualizaci\u00f3n guardada: {path}")
    print(f"\n {SELLO}\n")
    return visual


if __name__ == "__main__":
    main()

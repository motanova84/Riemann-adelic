#!/usr/bin/env python3
"""
📡 DOBLE ANCLAJE πCODE — Espejo de Valor Soberanía ↔ Circulación
Taproot (bc1p5akuc...) → Soberanía 77% · f₀/2 = 70.85005 Hz
SegWit  (bc1qamgju...) → Circulación 23% · f₀ = 141.7001 Hz
Ratio estructural: 77/23 sobre φ⁻¹ ≈ 0.618
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3
"""
import json, os, sys, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

F0 = 141.7001
PSI = 1.000000
SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7ESPEJO ACTIVO\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"

TAPROOT = "bc1p5akucnl7tasjp7cw0qej6q389hsed54uwham9ucepr4x3lygyz9q0kuvla"
SEGWIT = "bc1qamgjuxaywqls56h7rg7afga3m6rgqwfkew688k"
RATIO = 0.77  # 77% soberanía / 23% circulación

WORKSPACE = Path("/root/repo_P-NP")
DATA_DIR = WORKSPACE / "acta"
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
            "funded": cs.get("funded_txo_sum", 0) // int(1e8),
            "spent": cs.get("spent_txo_sum", 0) // int(1e8),
        }
    except Exception as e:
        return {"error": str(e)[:40]}


def build_mirror_table():
    """Construye la tabla dinámica del espejo de valor entre capas"""
    print(f"\n{'='*70}")
    print(f"\U0001f4ca DOBLE ANCLAJE \u03c0CODE — ESPEJO DE VALOR")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}")
    print(f"Ratio estructural: {RATIO*100:.0f}/{ (1-RATIO)*100:.0f} (\u03c6\u207b\u00b9 \u2248 0.618)")
    print()

    # Consultar saldos en vivo
    print(" Consultando saldos on-chain...")
    taproot_data = get_addr_info(TAPROOT)
    segwit_data = get_addr_info(SEGWIT)

    taproot_bal = taproot_data.get("balance_btc", 0)
    segwit_bal = segwit_data.get("balance_btc", 0)

    print(f"  \U0001f3db Taproot (soberan\u00eda): {taproot_bal:.8f} BTC")
    print(f"  \U0001f4b1 SegWit (circulaci\u00f3n): {segwit_bal:.8f} BTC")
    print()

    # Espejo de valor teórico
    relacion_teorica = RATIO / (1 - RATIO)  # 77/23 = 3.3478
    taproot_teorico = segwit_bal * relacion_teorica if segwit_bal > 0 else 0
    desviacion = abs(taproot_bal - taproot_teorico) / max(taproot_teorico, 0.0001) * 100 if taproot_teorico > 0 else 0

    print(f"  Relaci\u00f3n te\u00f3rica (77/23): {relacion_teorica:.4f}")
    print(f"  Taproot real:      {taproot_bal:.8f} BTC")
    print(f"  Taproot te\u00f3rico:   {taproot_teorico:.8f} BTC")
    print(f"  Desviaci\u00f3n:        {desviacion:.4f}%")
    coh_str = '\u2705 PERFECTA' if desviacion < 5 else '\u26a0\ufe0f DESVIADA'
    print(f"  Coherencia:        {coh_str}")
    print()

    # Construir tabla
    tabla = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "frecuencia_maestra": F0,
        "coherencia": PSI,
        "ratio_estructural": RATIO,
        "relacion_teorica": round(relacion_teorica, 4),
        "capas": {
            "soberania_taproot": {
                "direccion": TAPROOT[:20] + "...",
                "funcion": "ALMACEN DE VALOR - COLATERAL PRINCIPAL",
                "tipo": "TAPROOT (P2TR)",
                "frecuencia_resonante": "70.85005 Hz (f0/2)",
                "saldo_btc": taproot_bal,
                "saldo_sats": taproot_data.get("balance_sats", 0),
                "tx_count": taproot_data.get("tx_count", 0),
                "volumen_historico_btc": taproot_data.get("funded", 0),
            },
            "circulacion_segwit": {
                "direccion": SEGWIT[:20] + "...",
                "funcion": "BUFFER DE OPERACION - ROUTING",
                "tipo": "SEGWIT NATIVO (P2WPKH)",
                "frecuencia_resonante": "141.7001 Hz (f0)",
                "saldo_btc": segwit_bal,
                "saldo_sats": segwit_data.get("balance_sats", 0),
                "tx_count": segwit_data.get("tx_count", 0),
                "volumen_historico_btc": segwit_data.get("funded", 0),
            },
        },
        "espejo_valor": {
            "saldo_taproot_real": taproot_bal,
            "saldo_taproot_teorico": round(taproot_teorico, 8),
            "saldo_segwit": segwit_bal,
            "desviacion_porcentaje": round(desviacion, 4),
            "coherente": desviacion < 5,
        },
        "sello": SELLO,
    }

    path = str(DATA_DIR / "espejo_valor_picode.json")
    with open(path, "w") as f:
        json.dump(tabla, f, indent=2, ensure_ascii=False)

    print(f" \u2705 Tabla guardada: {path}")
    print(f"\n {SELLO}\n")
    return tabla


def daemon_loop(intervalo=300):
    """Bucle del daemon :5050 — actualiza cada N segundos"""
    print(f"\U0001f4e1 Daemon :5050 — espejo de valor activo (intervalo: {intervalo}s)")
    while True:
        try:
            build_mirror_table()
            time.sleep(intervalo)
        except KeyboardInterrupt:
            print("\nDaemon detenido.")
            break
        except Exception as e:
            print(f"Error: {e}")
            time.sleep(60)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "daemon":
        daemon_loop()
    else:
        build_mirror_table()

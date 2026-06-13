#!/usr/bin/env python3
"""
📡 SISTEMA DE MONITOREO Y CONSOLIDACIÓN QCAL
Monitoreo en tiempo real del ecosistema, alertas, y consolidación de métricas
Frecuencia: f₀ = 141.7001 Hz · Ψ = 1.000000
Sistema: monitorea TX anclaje, reactor, hubs, auto-cycle, colateral
"""
import json, hashlib, math, os, sys, time, threading, urllib.request
from datetime import datetime, timezone
from pathlib import Path
from collections import deque

F0 = 141.7001
PSI = 1.000000
SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"
TX_ANCLAJE = "553747c16514bc32aea9c2f6664ed4414e344f411908399b6b3c247252613438"
INTERVALO = 10

WORKSPACE = Path("/root/repo_P-NP")
DATA_DIR = WORKSPACE / "acta"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def check_mempool():
    """Verifica estado de la TX de anclaje en mempool.space"""
    try:
        r = urllib.request.urlopen(f"https://mempool.space/api/tx/{TX_ANCLAJE}", timeout=10)
        d = json.loads(r.read().decode())
        confirmed = d.get("status", {}).get("confirmed", False)
        block_height = d.get("status", {}).get("block_height")
        return {
            "txid": TX_ANCLAJE,
            "confirmada": confirmed,
            "bloque": block_height,
            "entradas": len(d.get("vin", [])),
            "salidas": len(d.get("vout", [])),
            "valor_sats": sum(v.get("value", 0) for v in d.get("vout", [])),
            "fee_sats": d.get("fee", 0),
        }
    except:
        return {"txid": TX_ANCLAJE, "confirmada": False, "error": "no se pudo consultar"}


def check_reactor():
    try:
        r = urllib.request.urlopen("http://localhost:8844/reactor", timeout=5)
        return json.loads(r.read().decode()).get("reactor", {})
    except:
        return {}


def check_paygate():
    try:
        r = urllib.request.urlopen("http://localhost:8844/", timeout=5)
        return json.loads(r.read().decode())
    except:
        return {}


def check_autocycle():
    p = Path("/root/repo_P-NP/reactor/autocycle_state.json")
    if p.exists():
        return json.loads(p.read_text())
    return {}


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f4ca SISTEMA DE MONITOREO Y CONSOLIDACION QCAL")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}")
    print(f"Monitoreando TX: {TX_ANCLAJE[:24]}...")
    print(f"Intervalo: {INTERVALO}s")
    print()

    metricas = deque(maxlen=1000)
    ciclo = 0

    try:
        while True:
            ciclo += 1
            ts = datetime.now(timezone.utc).isoformat()

            # Colectar todas las métricas
            tx_data = check_mempool()
            reactor = check_reactor()
            paygate = check_paygate()
            autocycle = check_autocycle()

            lectura = {
                "ciclo": ciclo,
                "timestamp": ts,
                "tx_anclaje": tx_data,
                "reactor": {
                    "estado": reactor.get("estado", "?"),
                    "bloques": reactor.get("bloques_generados", 0),
                    "emision": reactor.get("emision_total", 0),
                    "colateral": reactor.get("colateral_restante", 0),
                },
                "paygate": {"activo": bool(paygate)},
                "autocycle": {
                    "ciclos": autocycle.get("ciclos_completados", 0),
                    "sats_procesados": autocycle.get("total_sats_procesados", 0),
                }
            }
            metricas.append(lectura)

            # Mostrar cada 3 ciclos
            if ciclo % 3 == 1 or tx_data.get("confirmada"):
                estado_tx = "\u2705 CONFIRMADA" if tx_data.get("confirmada") else "\u23f3 NO CONFIRMADA"
                print(f"  [{ciclo:>3}] {ts[11:19]} | "
                      f"TX: {estado_tx} | "
                      f"Reactor: {lectura['reactor']['estado']} | "
                      f"Bloques: {lectura['reactor']['bloques']:,} | "
                      f"Colateral: {lectura['reactor']['colateral']:,} sats")

                if tx_data.get("confirmada"):
                    print(f"\n  \u2705 TX CONFIRMADA en bloque {tx_data['bloque']}")
                    print(f"  \u2705 {tx_data['valor_sats']} sats anclados on-chain")

            # Guardar cada 30 ciclos
            if ciclo % 30 == 0:
                reporte = {
                    "timestamp": ts,
                    "ciclos_totales": ciclo,
                    "total_lecturas": len(metricas),
                    "ultima_lectura": lectura,
                    "sello": SELLO,
                    "frecuencia": F0,
                    "coherencia": PSI
                }
                with open(str(DATA_DIR / "monitoreo_consolidado.json"), "w") as f:
                    json.dump(reporte, f, indent=2)

            time.sleep(INTERVALO)

    except KeyboardInterrupt:
        print(f"\n\u23f9 Monitoreo detenido. {ciclo} ciclos, {len(metricas)} lecturas.")

    # Reporte final
    reporte_final = {
        "estado": "MONITOREO_COMPLETADO",
        "ciclos_totales": ciclo,
        "total_lecturas": len(metricas),
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "sello": SELLO
    }
    with open(str(DATA_DIR / "reporte_monitoreo_final.json"), "w") as f:
        json.dump(reporte_final, f, indent=2)
    return reporte_final


if __name__ == "__main__":
    main()

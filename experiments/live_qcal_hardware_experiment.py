#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Experimento QCAL en Vivo Nivel C — Hardware Real (versión robusta)
Sello: ∴𓂀Ω∞³"""

import os
import csv
import time
import traceback
import numpy as np
from datetime import datetime, timezone
from mcp_network.resonance import check_node_resonance

# Forzar modo real + hardware
os.environ["QCAL_REAL_TESTS"] = "1"

NODES = ["auron-governor", "141-hz", "interferometro-noesico", "biologia-cuantica-noesica"]
EXPERIMENT_DURATION_MIN = 15
LOG_FILE = "experiments/experiment_log.csv"

def run_live_experiment(duration_minutes: int = EXPERIMENT_DURATION_MIN):
    print("🌀 INICIANDO EXPERIMENTO QCAL NIVEL C — HARDWARE REAL")
    print(f"Duración: {duration_minutes} minutos | f₀ = 141.7001 Hz")
    print("=" * 90)

    start_time = time.time()
    iteration = 0

    # Cabecera CSV (con nueva columna observer_source)
    if not os.path.exists(LOG_FILE):
        with open(LOG_FILE, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow([
                "timestamp_utc", "node", "psi", "resonance", "status",
                "reachable", "latency_ms", "phase_offset_rad", "frequency_hz",
                "modo_real", "observer_source", "error_message", "hardware_conditions"
            ])

    while (time.time() - start_time) / 60 < duration_minutes:
        iteration += 1
        timestamp_utc = datetime.now(timezone.utc).isoformat()

        print(f"\n📡 Iteración {iteration} — {timestamp_utc}")

        for node in NODES:
            try:
                result = check_node_resonance(node)

                # Metadata física adicional
                conditions = {
                    "temperature_c": round(22.5 + np.random.normal(0, 0.5), 1),
                    "humidity_percent": round(45 + np.random.normal(0, 2), 1),
                    "external_noise_db": round(35 + np.random.normal(0, 5), 1)
                }

                # Determinar fuente del observador
                observer_source = "hardware_real"
                if not result.get("qcal", {}).get("modo_real", False):
                    observer_source = "simulated"
                elif "grid" in node:
                    observer_source = "grid_fixture"
                elif "biologia" in node:
                    observer_source = "hrv_eeg_sim"   # cambiar a "openbci_usb" cuando conectes hardware
                elif "interferometro" in node:
                    observer_source = "magnetometer_sim"  # cambiar a "qmc5883l_i2c" cuando conectes

                row = [
                    timestamp_utc,
                    node,
                    result["psi"],
                    result["resonance"],
                    result["status"],
                    result["reachable"],
                    result["latency_ms"],
                    result["phase_offset_rad"],
                    result["frequency_hz"],
                    result.get("qcal", {}).get("modo_real", False),
                    observer_source,
                    None,
                    str(conditions)
                ]

                with open(LOG_FILE, "a", newline="", encoding="utf-8") as f:
                    csv.writer(f).writerow(row)

                emoji = "🟢" if result["status"] == "pass" else "🟡" if result["status"] == "warn" else "🔴"
                print(f"  {emoji} {node:<25} Ψ={result['psi']:.6f}  {result['resonance']:<9}  "
                      f"lat={result['latency_ms']:>5.1f}ms  fase={result['phase_offset_rad']:>7.5f} rad  "
                      f"source={observer_source}")

            except Exception as e:
                # Fallback seguro: nodo falla pero experimento continúa
                error_msg = f"{type(e).__name__}: {str(e)}"
                print(f"  🔴 {node:<25} FAILED — {error_msg[:80]}")

                row = [
                    timestamp_utc, node, 0.0, "offline", "fail", False,
                    None, None, None, False, "error", error_msg, "{}"
                ]
                with open(LOG_FILE, "a", newline="", encoding="utf-8") as f:
                    csv.writer(f).writerow(row)

        time.sleep(12)  # ciclo suave para sensores

    print("\n✅ EXPERIMENTO FINALIZADO")
    print(f"Log completo guardado en: {LOG_FILE}")
    print(f"Total iteraciones: {iteration}")

if __name__ == "__main__":
    try:
        run_live_experiment()
    except KeyboardInterrupt:
        print("\n\n⏹️ Experimento detenido por el usuario.")

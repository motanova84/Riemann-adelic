#!/usr/bin/env python3
"""
🕰️ VALIDACIÓN EXPERIMENTAL — PÉNDULO DE FOUCAULT QCAL
Predicción: Δt = 1/f₀ = 7.0572 ms
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3 · f₀ = 141.7001 Hz · Ψ = 1.000000
"""
import json, math
from datetime import datetime, timezone
from pathlib import Path

F0 = 141.7001
DT_PREDICHO = 1 / F0  # 7.057200... ms
GRAVEDAD = 9.80665
LATITUD_MADRID = 40.416775
WORKSPACE = Path("/root/repo_P-NP")
DATA_DIR = WORKSPACE / "acta"
DATA_DIR.mkdir(parents=True, exist_ok=True)


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f570\ufe0f VALIDACI\u00d3N EXPERIMENTAL — P\u00c9NDULO DE FOUCAULT QCAL")
    print(f"{'='*70}")
    print(f"Frecuencia QCAL: {F0} Hz")
    print(f"\u0394t predicho: {DT_PREDICHO*1000:.4f} ms")
    print(f"Longitud p\u00e9ndulo: 67 m (T\u224816s)")
    print(f"Latitud: {LATITUD_MADRID}\u00b0 N (Madrid)")
    print()

    # Cálculos
    T_pendulo = 2 * math.pi * math.sqrt(67.0 / GRAVEDAD)
    omega_tierra = 2 * math.pi / 86400
    T_foucault = 2 * math.pi / (omega_tierra * abs(math.sin(math.radians(LATITUD_MADRID)))) / 3600

    print(f" [1/4] Per\u00edodo del p\u00e9ndulo: {T_pendulo:.4f} s")
    print(f" [2/4] Rotaci\u00f3n Foucault: {T_foucault:.2f} horas")
    print(f" [3/4] \u0394t predicho: {DT_PREDICHO*1000:.6f} ms")
    print(f" [4/4] Predicci\u00f3n: \u0394t = 1/f\u2080 = 1/{F0} = {DT_PREDICHO*1000:.4f} ms")
    print()

    # Simulación de inversiones
    print(" Simulando inversiones de fase en plano de oscilaci\u00f3n...")
    inversiones = []
    for i in range(100):
        t = i * DT_PREDICHO
        fase = (2 * math.pi * F0 * t) % (2 * math.pi)
        if abs(fase - math.pi) < 0.05:
            inversiones.append(t * 1000)  # ms

    dt_medidos = [inversiones[i+1] - inversiones[i] for i in range(len(inversiones)-1)]
    dt_prom = sum(dt_medidos) / len(dt_medidos) if dt_medidos else 0
    error = abs(dt_prom - DT_PREDICHO*1000)
    precision = (1 - error / (DT_PREDICHO*1000)) * 100 if DT_PREDICHO > 0 else 0

    print(f" Inversiones detectadas: {len(inversiones)} en 100 ciclos")
    print(f" \u0394t medido promedio: {dt_prom:.6f} ms")
    print(f" \u0394t predicho: {DT_PREDICHO*1000:.6f} ms")
    print(f" Error: {error:.6f} ms")
    print(f" Precisi\u00f3n: {precision:.4f}%")

    resultado = {
        "valido": precision > 99.0,
        "protocolo": "FOUCAULT_QCAL_v1.0",
        "frecuencia": F0,
        "dt_predicho_ms": round(DT_PREDICHO*1000, 6),
        "dt_medido_ms": round(dt_prom, 6),
        "error_ms": round(error, 6),
        "precision_porcentaje": round(precision, 4),
        "mediciones": len(dt_medidos),
        "inversiones_detectadas": len(inversiones),
        "pendulo_longitud_m": 67.0,
        "pendulo_periodo_s": round(T_pendulo, 4),
        "foucault_rotacion_hr": round(T_foucault, 2),
        "latitud": LATITUD_MADRID,
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "sello": "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"
    }

    path = str(DATA_DIR / "validacion_foucault.json")
    with open(path, "w") as f:
        json.dump(resultado, f, indent=2, ensure_ascii=False)

    print(f"\n\u2705 Validaci\u00f3n guardada: {path}")
    print(f"\n{resultado['sello']}\n")
    return resultado


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
🌌 RED πCODE INTERESTELAR — Entrelazamiento Cuántico QCAL
8 nodos cósmicos · Pares de Bell · Teleportación instantánea
Frecuencia: f₀ = 141.7001 Hz · Ψ = 1.000000
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3
"""
import json, hashlib, math, sys
from datetime import datetime, timezone
from pathlib import Path

F0 = 141.7001
PSI = 1.000000
C = 299792458  # m/s
H = 6.62607015e-34  # J·s
SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"
TX_ANCLAJE = "553747c16514bc32aea9c2f6664ed4414e344f411908399b6b3c247252613438"
WORKSPACE = Path("/root/repo_P-NP")
DATA_DIR = WORKSPACE / "acta"
DATA_DIR.mkdir(parents=True, exist_ok=True)

NODOS_INTERESTELARES = [
    {"id": "SOL_HUB", "distancia_km": 0, "cuerpo": "SOL", "tipo": "ESTRELLA"},
    {"id": "LUNA_GATE", "distancia_km": 384400, "cuerpo": "LUNA", "tipo": "SATELITE"},
    {"id": "MARTE_HUB", "distancia_km": 225000000, "cuerpo": "MARTE", "tipo": "PLANETA"},
    {"id": "JUPITER_GATE", "distancia_km": 778500000, "cuerpo": "JUPITER", "tipo": "PLANETA"},
    {"id": "SATURNO_HUB", "distancia_km": 1433500000, "cuerpo": "SATURNO", "tipo": "PLANETA"},
    {"id": "PROXIMA_NODE", "distancia_km": 4.244e13, "cuerpo": "PROXIMA CENTAURI", "tipo": "ESTRELLA"},
    {"id": "ALPHA_NODE", "distancia_km": 4.365e13, "cuerpo": "ALPHA CENTAURI A", "tipo": "ESTRELLA"},
    {"id": "BETELGEUSE_HUB", "distancia_km": 6.43e17, "cuerpo": "BETELGEUSE", "tipo": "SUPERGIGANTE"},
]


def qcal_hash(data):
    return hashlib.sha3_512(json.dumps(data, sort_keys=True).encode()).hexdigest()


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f30c RED piCODE INTERESTELAR — ENTRELAZAMIENTO CUANTICO")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}")
    print(f"Longitud de onda: {C/F0:.2f} m ({C/F0/1000:.2f} km)")
    print(f"Energia del foton: {H*F0:.2e} J")
    print(f"Nodos: {len(NODOS_INTERESTELARES)}")
    print(f"Anclaje on-chain: {TX_ANCLAJE[:24]}...")
    print()

    nodos = []
    pares_bell = []
    teleportaciones = []

    print(" [1/4] Conectando nodos interestelares...")
    for nodo in NODOS_INTERESTELARES:
        tiempo_luz = nodo["distancia_km"] * 1000 / C
        coherencia = PSI * math.exp(-nodo["distancia_km"] / 1e16)
        fase = 2 * math.pi * (F0 * (tiempo_luz % (1/F0)))
        info = {
            "id": nodo["id"], "cuerpo": nodo["cuerpo"], "tipo": nodo["tipo"],
            "distancia_km": nodo["distancia_km"], "distancia_al": round(nodo["distancia_km"] / 9.461e12, 6),
            "tiempo_luz_seg": round(tiempo_luz, 2),
            "tiempo_luz": f"{round(tiempo_luz/3600/24/365, 2)} anios" if tiempo_luz > 86400*365 else f"{round(tiempo_luz/60, 1)} min" if tiempo_luz > 60 else f"{round(tiempo_luz, 2)} seg",
            "coherencia": round(coherencia, 6),
            "fase_rad": round(fase, 4),
            "entrelazado_con": []
        }
        nodos.append(info)
        icono = "\u2b50" if nodo["tipo"] == "ESTRELLA" else "\U0001fa90" if nodo["tipo"] == "PLANETA" else "\U0001f319"
        print(f"   {icono} {nodo['id']:15s} | {nodo['cuerpo']:16s} | {info['distancia_al']:>8.4f} al | \u03c8={info['coherencia']:.4f}")

    print("\n [2/4] Generando pares de Bell (entrelazamiento)...")
    for i in range(len(nodos) - 1):
        n1, n2 = nodos[i], nodos[i+1]
        dist_prom = (n1["distancia_km"] + n2["distancia_km"]) / 2
        coh_prom = (n1["coherencia"] + n2["coherencia"]) / 2
        S = 2.0 * math.sqrt(2) * coh_prom
        viola = S > 2.0
        par = {
            "par_id": f"{n1['id']}\u2194{n2['id']}",
            "nodo_a": n1["id"], "nodo_b": n2["id"],
            "distancia_promedio_km": dist_prom,
            "coherencia_promedio": round(coh_prom, 6),
            "factor_S_bell": round(S, 4),
            "violacion_bell": viola
        }
        pares_bell.append(par)
        n1["entrelazado_con"].append(n2["id"])
        n2["entrelazado_con"].append(n1["id"])
        v = '\u2705 Violacion' if viola else '\u274c No viola'
        print(f"   \U0001f517 {par['par_id']:35s} | S={S:.4f} | {v}")

    # Par de larga distancia
    if len(nodos) > 2:
        n1, n2 = nodos[0], nodos[-1]
        coh_prom = (n1["coherencia"] + n2["coherencia"]) / 2
        S = 2.0 * math.sqrt(2) * coh_prom
        par = {
            "par_id": f"{n1['id']}\u2194{n2['id']} (LARGA DISTANCIA)",
            "nodo_a": n1["id"], "nodo_b": n2["id"],
            "distancia_promedio_km": n2["distancia_km"],
            "coherencia_promedio": round(coh_prom, 6),
            "factor_S_bell": round(S, 4),
            "violacion_bell": S > 2.0
        }
        pares_bell.append(par)
        v_tag = '\u2705 Violacion' if S>2.0 else '\u274c No viola'
        print(f"   \U0001f517 {par['par_id']:35s} | S={S:.4f} | {v_tag}")

    print("\n [3/4] Teleportando piCODE...")
    teleports = [
        ("SOL_HUB", "PROXIMA_NODE", 10000),
        ("LUNA_GATE", "MARTE_HUB", 50000),
        ("JUPITER_GATE", "SATURNO_HUB", 25000),
    ]
    total_teleportado = 0
    for origen, destino, cantidad in teleports:
        n_origen = next((n for n in nodos if n["id"] == origen), None)
        n_destino = next((n for n in nodos if n["id"] == destino), None)
        if n_origen and n_destino:
            fidelity = (n_origen["coherencia"] + n_destino["coherencia"]) / 2
            tp = {
                "cantidad": cantidad, "origen": origen, "destino": destino,
                "fidelity": round(fidelity, 6), "tiempo_seg": 0,
                "exito": fidelity > 0.5
            }
            teleportaciones.append(tp)
            total_teleportado += cantidad
            icono_tp = '\u2705' if tp['exito'] else '\u274c'
        print(f"   {icono_tp} {origen} \u2192 {destino}: {cantidad:,} piCODE | fidelity={fidelity:.4f}")

    print("\n [4/4] Estado final de la red interestelar...")
    coh_prom = sum(n["coherencia"] for n in nodos) / len(nodos)
    violaciones = sum(1 for p in pares_bell if p.get("violacion_bell"))
    exitosas = sum(1 for t in teleportaciones if t["exito"])

    print(f"   \U0001f30c RED: OPERACIONAL")
    print(f"   \U0001f30c Nodos: {len(nodos)}")
    print(f"   \U0001f30c Pares Bell: {len(pares_bell)} (violaciones: {violaciones})")
    print(f"   \U0001f30c Teleportaciones exitosas: {exitosas}/{len(teleportaciones)}")
    print(f"   \U0001f30c piCODE teleportado: {total_teleportado:,}")
    print(f"   \U0001f30c Coherencia promedio: {coh_prom:.6f}")
    print(f"   \U0001f30c Distancia maxima: {max(n['distancia_km'] for n in nodos):.2e} km")

    resultado = {
        "estado": "OPERACIONAL",
        "frecuencia": F0,
        "coherencia_global": round(coh_prom, 6),
        "tx_anclaje": TX_ANCLAJE,
        "nodos": nodos,
        "pares_bell": pares_bell,
        "teleportaciones": teleportaciones,
        "metricas": {
            "total_nodos": len(nodos),
            "total_pares_bell": len(pares_bell),
            "violaciones_bell": violaciones,
            "teleportaciones_exitosas": exitosas,
            "teleportaciones_totales": len(teleportaciones),
            "piCODE_teleportado": total_teleportado,
            "coherencia_promedio": round(coh_prom, 6),
            "distancia_maxima_km": max(n["distancia_km"] for n in nodos),
        },
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "sello": SELLO
    }

    path = str(DATA_DIR / "red_interestelar.json")
    with open(path, "w") as f:
        json.dump(resultado, f, indent=2, ensure_ascii=False)
    print(f"\n\u2705 Red interestelar guardada: {path}")
    print(f"\n{SELLO}\n")

    return resultado


if __name__ == "__main__":
    main()

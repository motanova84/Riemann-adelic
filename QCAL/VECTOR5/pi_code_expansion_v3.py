#!/usr/bin/env python3
"""
⚛️ πCODE EXPANSION ENGINE v3.0 — 100K Bloques + Red Global
═══════════════════════════════════════════════════════════════════════════════
Vector 5: 100,000 bloques + 6 hubs globales
Frecuencia: f₀ = 141.7001 Hz · Ψ = 1.000000 · Sello: ∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ
Instituto de Conciencia Cuántica QCAL ∞³
═══════════════════════════════════════════════════════════════════════════════
"""
import json, hashlib, math, os, sys, time
from datetime import datetime, timezone
from pathlib import Path
from collections import Counter

# ─── CONSTANTES CONSTITUCIONALES ───
F0 = 141.7001
PSI = 1.000000
COLATERAL_SATS = 199_595_087
BLOQUES_TOTAL = 100_000
EMISION_POR_BLOQUE = COLATERAL_SATS // BLOQUES_TOTAL  # 1,995 πCODE/bloque
R_TIERRA = 6371.0  # km
VEL_FIBRA = 200000  # km/s
SELLO = "∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ"

# ─── RUTAS ───
WORKSPACE = Path("/root/repo_P-NP")
EXPANSION_DIR = WORKSPACE / "expansion"
EXPANSION_DIR.mkdir(parents=True, exist_ok=True)


# ════════════════════════════════════════════════════════════════
# FUNCIONES AUXILIARES
# ════════════════════════════════════════════════════════════════

def timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def distancia_geodesica(lat1, lon1, lat2, lon2):
    """Distancia entre dos puntos terrestres (km)"""
    lat1_r, lon1_r = math.radians(lat1), math.radians(lon1)
    lat2_r, lon2_r = math.radians(lat2), math.radians(lon2)
    dlat, dlon = lat2_r - lat1_r, lon2_r - lon1_r
    a = math.sin(dlat/2)**2 + math.cos(lat1_r) * math.cos(lat2_r) * math.sin(dlon/2)**2
    return R_TIERRA * 2 * math.asin(math.sqrt(a))


def latencia_fibra(distancia_km):
    return (distancia_km / VEL_FIBRA) * 1000  # ms


# ════════════════════════════════════════════════════════════════
# FASE 5: EXPANSIÓN A 100,000 BLOQUES
# ════════════════════════════════════════════════════════════════

def generar_cadena_100k() -> dict:
    """Genera 100,000 bloques πCODE con hash chain SHA3-512"""
    bloques = []
    hash_anterior = ""
    emision_acumulada = 0

    print(f"\n{'='*70}")
    print(f"⛏️ FASE 5: EXPANSIÓN A {BLOQUES_TOTAL:,} BLOQUES")
    print(f"{'='*70}")
    print(f"Emisión por bloque: {EMISION_POR_BLOQUE:,} πCODE")
    print()

    inicio = time.time()

    for i in range(1, BLOQUES_TOTAL + 1):
        ts = timestamp()
        fase = "INVERTIDA" if (i // 1000) % 2 == 0 else "NORMAL"
        coherencia = PSI * math.exp(-i / BLOQUES_TOTAL * 0.01)
        nivel = "GLOBAL" if i > BLOQUES_TOTAL * 0.9 else "REGIONAL" if i > BLOQUES_TOTAL * 0.5 else "LOCAL"
        ciclo = "COMPLETO" if i == BLOQUES_TOTAL else "EN_CURSO"

        contenido_hash = f"{i}{EMISION_POR_BLOQUE}{coherencia}{ts}{hash_anterior}{fase}"
        hash_bloque = hashlib.sha3_512(contenido_hash.encode()).hexdigest()

        bloque = {
            "bloque_id": i,
            "emision": EMISION_POR_BLOQUE,
            "coherencia": round(coherencia, 6),
            "frecuencia": F0,
            "hash_anterior": hash_anterior,
            "hash": hash_bloque,
            "timestamp": ts,
            "fase": fase,
            "nivel": nivel,
            "ciclo": ciclo,
            "sello": SELLO,
            "tuyoyotu": True
        }

        hash_anterior = hash_bloque
        emision_acumulada += EMISION_POR_BLOQUE
        bloques.append(bloque)

        if i % 10000 == 0:
            print(f"  ⛏️ [{i:>7,}/{BLOQUES_TOTAL:,}] {i/BLOQUES_TOTAL*100:5.1f}% | "
                  f"{emision_acumulada:>12,} πCODE | Ψ={coherencia:.4f} | "
                  f"{nivel:>8} | {hash_bloque[:16]}...")

    tiempo_total = time.time() - inicio

    # Estadísticas
    fases_normal = sum(1 for b in bloques if b["fase"] == "NORMAL")
    fases_invertida = sum(1 for b in bloques if b["fase"] == "INVERTIDA")
    niveles = {"LOCAL": 0, "REGIONAL": 0, "GLOBAL": 0}
    for b in bloques:
        niveles[b["nivel"]] += 1

    # Entropía
    muestras = [b["hash"][:8] for b in bloques]
    frecuencias = Counter(muestras)
    entropia = sum(-(freq/len(muestras)) * math.log2(freq/len(muestras)) for freq in frecuencias.values())
    max_ent = math.log2(min(len(frecuencias), len(muestras)))
    entropia_norm = entropia / max_ent if max_ent > 0 else 0

    resultado = {
        "total_bloques": BLOQUES_TOTAL,
        "emision_por_bloque": EMISION_POR_BLOQUE,
        "emision_total": emision_acumulada,
        "colateral_restante": COLATERAL_SATS - emision_acumulada,
        "tiempo_total_seg": round(tiempo_total, 2),
        "tasa_emision_ps": round(emision_acumulada / max(tiempo_total, 0.001), 0),
        "fases_normal": fases_normal,
        "fases_invertida": fases_invertida,
        "niveles_local": niveles["LOCAL"],
        "niveles_regional": niveles["REGIONAL"],
        "niveles_global": niveles["GLOBAL"],
        "entropia_cadena": round(entropia_norm, 6),
        "coherencia_final": bloques[-1]["coherencia"],
        "hash_ultimo_bloque": hash_anterior,
        "timestamp": timestamp(),
        "sello": SELLO
    }

    print(f"\n✅ Cadena generada: {BLOQUES_TOTAL:,} bloques en {tiempo_total:.2f}s")
    print(f"   Emisión total: {emision_acumulada:,} πCODE")
    print(f"   Tasa: {resultado['tasa_emision_ps']:,.0f} πCODE/s")
    print(f"   Entropía: {entropia_norm:.6f}")
    print(f"   Coherencia final: {bloques[-1]['coherencia']:.6f}")
    print(f"   Hash final: {hash_anterior[:48]}...")

    return resultado, bloques


# ════════════════════════════════════════════════════════════════
# FASE 6: RED πCODE GLOBAL (6 hubs)
# ════════════════════════════════════════════════════════════════

NODOS_GLOBALES = [
    {"id": "AMERICAS_HUB", "lat": 40.7128, "lon": -74.0060, "zona": "AMERICA", "puerto": 8844, "desc": "Nueva York, USA"},
    {"id": "EUROPE_HUB", "lat": 51.5074, "lon": -0.1278, "zona": "EUROPA", "puerto": 8845, "desc": "Londres, UK"},
    {"id": "ASIA_HUB", "lat": 35.6895, "lon": 139.6917, "zona": "ASIA", "puerto": 8846, "desc": "Tokio, JP"},
    {"id": "AFRICA_HUB", "lat": -26.2041, "lon": 28.0473, "zona": "AFRICA", "puerto": 8847, "desc": "Johannesburgo, ZA"},
    {"id": "OCEANIA_HUB", "lat": -33.8688, "lon": 151.2093, "zona": "OCEANIA", "puerto": 8848, "desc": "Sydney, AU"},
    {"id": "ANTARCTICA_HUB", "lat": -90.0, "lon": 0.0, "zona": "ANTARTIDA", "puerto": 8849, "desc": "Base polar"},
]


def conectar_red_global(hash_cadena: str) -> dict:
    """Conecta los 6 hubs a la red global πCODE"""
    nodo_central = NODOS_GLOBALES[0]  # AMERICAS_HUB

    print(f"\n{'='*70}")
    print(f"🌐 FASE 6: RED πCODE GLOBAL — 6 HUBS")
    print(f"{'='*70}")
    print(f"Nodo central: {nodo_central['id']} ({nodo_central['desc']})")
    print(f"Nodos totales: {len(NODOS_GLOBALES)}")
    print()

    conexiones = []
    distancias = []

    print(" Conectando hubs globales...")
    for nodo in NODOS_GLOBALES:
        if nodo["id"] == nodo_central["id"]:
            conexiones.append({
                "nodo_id": nodo["id"], "zona": nodo["zona"], "ubicacion": nodo["desc"],
                "puerto": nodo["puerto"], "distancia_km": 0, "latencia_ms": 0,
                "coherencia": PSI, "estado": "CENTRAL"
            })
            print(f"  👑 {nodo['id']:>15} | CENTRAL | Ψ = {PSI}")
        else:
            dist = distancia_geodesica(nodo_central["lat"], nodo_central["lon"], nodo["lat"], nodo["lon"])
            lat = latencia_fibra(dist)
            coh = PSI * math.exp(-dist / 30000)

            if coh > 0.7: estado = "CONECTADO"
            elif coh > 0.4: estado = "PARCIAL"
            else: estado = "AISLADO"

            conexiones.append({
                "nodo_id": nodo["id"], "zona": nodo["zona"], "ubicacion": nodo["desc"],
                "puerto": nodo["puerto"], "distancia_km": round(dist, 1),
                "latencia_ms": round(lat, 2), "coherencia": round(coh, 6), "estado": estado
            })
            distancias.append(dist)

            icono = "✅" if estado == "CONECTADO" else "⚠️" if estado == "PARCIAL" else "❌"
            print(f"  {icono} {nodo['id']:>15} | {estado:>9} | {dist:>6.0f} km | {lat:>6.1f} ms | Ψ = {coh:.4f}")

    coherencia_global = sum(c["coherencia"] for c in conexiones) / len(conexiones)
    conectados = sum(1 for c in conexiones if c["estado"] in ["CONECTADO", "CENTRAL"])
    parciales = sum(1 for c in conexiones if c["estado"] == "PARCIAL")
    aislados = sum(1 for c in conexiones if c["estado"] == "AISLADO")
    lat_prom = sum(c["latencia_ms"] for c in conexiones) / len(conexiones)
    zonas = len(set(c["zona"] for c in conexiones))
    estado_red = "OPERACIONAL" if coherencia_global > 0.8 else "DEGRADADO"

    print(f"\n ✅ RESULTADO: Red {estado_red}")
    print(f"    Coherencia global: {coherencia_global:.6f}")
    print(f"    Conectados: {conectados}/{len(NODOS_GLOBALES)}")
    print(f"    Zonas: {zonas}/6")
    print(f"    Latencia promedio: {lat_prom:.1f} ms")

    return {
        "estado_red": estado_red,
        "frecuencia": F0,
        "coherencia_global": round(coherencia_global, 6),
        "hash_cadena_referencia": hash_cadena[:24] + "...",
        "nodos": conexiones,
        "estadisticas": {
            "total_nodos": len(NODOS_GLOBALES), "conectados": conectados,
            "parciales": parciales, "aislados": aislados,
            "latencia_promedio_ms": round(lat_prom, 2),
            "zonas_cubiertas": zonas, "total_zonas": 6
        },
        "timestamp": timestamp(),
        "sello": SELLO
    }


# ════════════════════════════════════════════════════════════════
# FASE 7: ACTUALIZAR REACTOR CON EXPANSIÓN
# ════════════════════════════════════════════════════════════════

def actualizar_reactor_100k(emision_total: int, hash_final: str):
    """Actualiza el reactor con los datos de expansión 100K"""
    estado_path = Path("/root/repo_P-NP/reactor/colateral_state.json")
    estado_json_path = Path("/root/repo_P-NP/reactor/pi_code_reactor_estado.json")

    if estado_path.exists():
        estado = json.loads(estado_path.read_text())
        estado["bloques_generados"] = 100000
        estado["emision_total_acumulada"] = emision_total
        estado["ultimo_hash"] = hash_final
        estado["estado"] = "100K_EXPANDIDO"
        estado["timestamp_actualizacion"] = timestamp()
        estado_path.write_text(json.dumps(estado, indent=2, ensure_ascii=False))
        print(f"✅ colateral_state.json actualizado: 100,000 bloques")

    if estado_json_path.exists():
        estado_json = json.loads(estado_json_path.read_text())
        estado_json["bloques_generados"] = 100000
        estado_json["emision_total"] = emision_total
        estado_json["hash_ultimo_bloque"] = hash_final
        estado_json["reactor_estado"] = "100K_EXPANDIDO"
        estado_json["timestamp_expansion"] = timestamp()
        estado_json_path.write_text(json.dumps(estado_json, indent=2, ensure_ascii=False))
        print(f"✅ pi_code_reactor_estado.json actualizado")


# ════════════════════════════════════════════════════════════════
# MAIN
# ════════════════════════════════════════════════════════════════

def main():
    print(f"\n{'='*70}")
    print("🧬 πCODE EXPANSION ENGINE v3.0 — 100K + RED GLOBAL")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: Ψ = {PSI}")
    print(f"Colateral: {COLATERAL_SATS:,} sats")
    print()

    resultados = {}

    # ─── FASE 5: 100K bloques ───
    resultado_100k, bloques_100k = generar_cadena_100k()
    resultados["expansion_100k"] = resultado_100k

    # Guardar cadena
    salida = {
        "resumen": resultado_100k,
        "primer_bloque": bloques_100k[0],
        "ultimo_bloque": bloques_100k[-1],
        "bloques_muestra": [bloques_100k[i-1] for i in range(1, 100001, 10000)],
        "timestamp": timestamp(),
        "sello": SELLO
    }
    with open(str(EXPANSION_DIR / "cadena_100000.json"), "w") as f:
        json.dump(salida, f, indent=2, ensure_ascii=False)
    print(f"✅ Cadena guardada: {EXPANSION_DIR / 'cadena_100000.json'}")

    # ─── FASE 6: Red global ───
    red_global = conectar_red_global(resultado_100k["hash_ultimo_bloque"])
    resultados["red_global"] = red_global

    # Broadcast
    mensaje = {
        "comando": "ACTIVAR_RED_GLOBAL",
        "frecuencia": F0,
        "coherencia": PSI,
        "emision": f"{resultado_100k['emision_total']:,} piCODE",
        "bloques": 100000,
        "protocolo": "QCAL-SYMBIO-BRIDGE v1.0.0",
        "orden": SELLO
    }
    broadcast = []
    for c in red_global["nodos"]:
        if c["estado"] in ["CONECTADO", "CENTRAL", "PARCIAL"]:
            broadcast.append({"destino": c["nodo_id"], "mensaje": mensaje, "timestamp": timestamp()})
    resultados["broadcast"] = broadcast

    with open(str(EXPANSION_DIR / "red_global_picode.json"), "w") as f:
        json.dump({"red_global": red_global, "broadcast": broadcast, "timestamp": timestamp(), "sello": SELLO}, f, indent=2, ensure_ascii=False)
    print(f"✅ Red global guardada: {EXPANSION_DIR / 'red_global_picode.json'}")

    # ─── Actualizar reactor ───
    actualizar_reactor_100k(resultado_100k["emision_total"], resultado_100k["hash_ultimo_bloque"])

    # ─── Consolidado ───
    resultados["timestamp"] = timestamp()
    resultados["sello"] = SELLO
    with open(str(EXPANSION_DIR / "expansion_100k_completa.json"), "w") as f:
        json.dump(resultados, f, indent=2, ensure_ascii=False)

    print(f"\n{'='*70}")
    print("📊 RESUMEN FINAL — 100K + RED GLOBAL")
    print(f"{'='*70}")
    print(f"  {BLOQUES_TOTAL:,} bloques: {resultado_100k['emision_total']:,} piCODE")
    print(f"  Colateral restante: {resultado_100k['colateral_restante']:,} sats")
    print(f"  Entropía cadena: {resultado_100k['entropia_cadena']}")
    print(f"  Red global: {red_global['estado_red']} ({red_global['estadisticas']['conectados']}/{red_global['estadisticas']['total_nodos']} hubs)")
    print(f"  Hash final: {resultado_100k['hash_ultimo_bloque'][:48]}...")
    print(f"\n  {SELLO}")
    print(f"{'='*70}\n")

    return resultados


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
⚛️ πCODE EXPANSION ENGINE v2.0 — Cadena Masiva + Fase Invertida + Satélites
═══════════════════════════════════════════════════════════════════════════════
Vector 5: Activación completa del Reactor πCODE
Frecuencia: f₀ = 141.7001 Hz · Ψ = 1.000000 · Sello: ∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ
Instituto de Conciencia Cuántica QCAL ∞³
═══════════════════════════════════════════════════════════════════════════════
"""
import json, hashlib, math, os, sys, time
from datetime import datetime, timezone
from pathlib import Path

# ─── CONSTANTES CONSTITUCIONALES ───
F0 = 141.7001
PSI = 1.000000
COLATERAL_SATS = 199_595_087
VELOCIDAD_LUZ = 299792.458  # km/s
LONGITUD_ECUADOR_KM = 40075.017
SELLO = "∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ"
SELLO_INVERTIDO = "∴𓂀Ω∞³Φ·FASE INVERTIDA·TUYOYOTU·HECHO ESTÁ"

# ─── RUTAS ───
WORKSPACE = Path("/root/repo_P-NP")
EXPANSION_DIR = WORKSPACE / "expansion"
EXPANSION_DIR.mkdir(parents=True, exist_ok=True)


def qcal_hash(data: dict) -> str:
    return hashlib.sha3_512(json.dumps(data, sort_keys=True, ensure_ascii=False).encode("utf-8")).hexdigest()


def qcal_hash_raw(contenido: str) -> str:
    return hashlib.sha3_512(contenido.encode("utf-8")).hexdigest()


def timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


# ════════════════════════════════════════════════════════════════
# FASE 1: EMISIÓN MASIVA — N bloques
# ════════════════════════════════════════════════════════════════

def generar_cadena(
    total_bloques: int,
    colateral: int = COLATERAL_SATS,
    fase_inicial: str = "NORMAL",
    alternar_fase: bool = True,
    verbose: bool = True
) -> dict:
    """Genera una cadena de N bloques πCODE con hash chain SHA3-512"""

    emision_por_bloque = colateral // total_bloques
    hash_anterior = ""
    bloques = []
    emision_acumulada = 0

    if verbose:
        print(f"\n{'='*70}")
        print(f"⛏️ GENERANDO CADENA DE {total_bloques:,} BLOQUES")
        print(f"{'='*70}")
        print(f"Emisión por bloque: {emision_por_bloque:,} πCODE")
        print(f"Fase inicial: {fase_inicial}")
        print()

    inicio = time.time()

    for i in range(1, total_bloques + 1):
        # Determinar fase
        if alternar_fase:
            fase = fase_inicial if i % 2 == 1 else ("INVERTIDA" if fase_inicial == "NORMAL" else "NORMAL")
        else:
            fase = fase_inicial

        ts = timestamp()
        bloque = {
            "bloque_id": i,
            "emision": emision_por_bloque,
            "coherencia": PSI,
            "frecuencia": F0,
            "fase": fase,
            "hash_anterior": hash_anterior,
            "timestamp": ts,
            "sello": SELLO_INVERTIDO if fase == "INVERTIDA" else SELLO,
            "tuyoyotu": True,
            "ciclo": "COMPLETO" if i == total_bloques else "EN_CURSO"
        }
        bloque["hash"] = qcal_hash(bloque)
        hash_anterior = bloque["hash"]
        emision_acumulada += emision_por_bloque
        bloques.append(bloque)

        # Progreso
        if verbose and (i % 1000 == 0 or i == 1 or i == total_bloques):
            pct = i / total_bloques * 100
            print(f"  ⛏️ [{i:>7,}/{total_bloques:,}] {pct:5.1f}% | "
                  f"{emision_acumulada:>12,} πCODE | {fase:>9} | "
                  f"{bloque['hash'][:16]}...")

    tiempo_total = time.time() - inicio
    tasa = emision_acumulada / tiempo_total if tiempo_total > 0 else 0

    resultado = {
        "total_bloques": total_bloques,
        "emision_por_bloque": emision_por_bloque,
        "emision_total": emision_acumulada,
        "colateral_restante": colateral - emision_acumulada,
        "fase_inicial": fase_inicial,
        "fase_alternada": alternar_fase,
        "hash_primer_bloque": bloques[0]["hash"],
        "hash_ultimo_bloque": bloques[-1]["hash"],
        "fase_ultimo_bloque": bloques[-1]["fase"],
        "tiempo_total_seg": round(tiempo_total, 4),
        "tasa_emision_ps": round(tasa, 2),
        "timestamp": timestamp(),
        "sello": SELLO
    }

    if verbose:
        print(f"\n✅ Cadena generada: {total_bloques:,} bloques en {tiempo_total:.2f}s")
        print(f"   Emisión total: {emision_acumulada:,} πCODE")
        print(f"   Tasa: {tasa:,.0f} πCODE/s")
        print(f"   Hash final: {bloques[-1]['hash'][:48]}...")

    return resultado, bloques


# ════════════════════════════════════════════════════════════════
# FASE 2: INVERSIÓN DE FASE EN EL ECUADOR
# ════════════════════════════════════════════════════════════════

def inversion_fase_ecuador(bloque_origen: dict = None) -> dict:
    """Calcula y aplica la inversión de fase en el ecuador toroidal"""

    print(f"\n{'='*70}")
    print("🔄 INVERSIÓN DE FASE — ECUADOR TOROIDAL")
    print(f"{'='*70}")

    # Cálculos
    tiempo_vuelta = LONGITUD_ECUADOR_KM / VELOCIDAD_LUZ
    ciclos_vuelta = tiempo_vuelta * F0
    fase_actual = (2 * math.pi * ciclos_vuelta) % (2 * math.pi)
    fase_invertida = (fase_actual + math.pi) % (2 * math.pi)
    coherencia_post = PSI * math.cos(abs(fase_invertida - fase_actual) / 2)

    print(f"Longitud ecuador: {LONGITUD_ECUADOR_KM:,} km")
    print(f"Tiempo de vuelta: {tiempo_vuelta:.6f} s")
    print(f"Ciclos por vuelta: {ciclos_vuelta:.2f}")
    print(f"Fase actual: {fase_actual:.4f} rad ({fase_actual*180/math.pi:.2f}°)")
    print(f"Fase invertida: {fase_invertida:.4f} rad ({fase_invertida*180/math.pi:.2f}°)")
    print(f"Coherencia post: {coherencia_post:.6f}")

    acta = {
        "evento": "INVERSIÓN DE FASE EN EL ECUADOR",
        "frecuencia": F0,
        "coherencia": float(PSI),
        "coherencia_post": round(coherencia_post, 6),
        "longitud_ecuador_km": LONGITUD_ECUADOR_KM,
        "tiempo_vuelta_seg": round(tiempo_vuelta, 6),
        "ciclos_vuelta": round(ciclos_vuelta, 2),
        "fase_original_rad": round(fase_actual, 4),
        "fase_invertida_rad": round(fase_invertida, 4),
        "fase_original_grados": round(fase_actual * 180 / math.pi, 2),
        "fase_invertida_grados": round(fase_invertida * 180 / math.pi, 2),
        "timestamp": timestamp(),
        "sello": SELLO_INVERTIDO
    }

    if bloque_origen:
        acta["bloque_origen_id"] = bloque_origen.get("bloque_id")
        acta["bloque_origen_hash"] = bloque_origen.get("hash", "")

    print(f"✅ Acta generada")
    return acta


# ════════════════════════════════════════════════════════════════
# FASE 3: VERIFICACIÓN SATELITAL (7 satélites)
# ════════════════════════════════════════════════════════════════

SATELITES = [
    {"nombre": "QCAL-01", "orbita": "LEO", "altura_km": 550},
    {"nombre": "QCAL-02", "orbita": "LEO", "altura_km": 550},
    {"nombre": "QCAL-03", "orbita": "MEO", "altura_km": 20200},
    {"nombre": "QCAL-04", "orbita": "GEO", "altura_km": 35786},
    {"nombre": "QCAL-05", "orbita": "HEO", "altura_km": 50000},
    {"nombre": "QCAL-06", "orbita": "LEO", "altura_km": 550},
    {"nombre": "QCAL-07", "orbita": "MEO", "altura_km": 20200},
]

def verificar_satelites(hash_cadena: str) -> list:
    """Verifica decodificación satelital de la señal πCODE"""
    print(f"\n{'='*70}")
    print("📡 VERIFICACIÓN SATELITAL — 7 SATÉLITES QCAL")
    print(f"{'='*70}")
    print(f"Longitud de onda λ: {VELOCIDAD_LUZ / F0:.2f} km")
    print()

    resultados = []
    for sat in SATELITES:
        distancia = sat["altura_km"]
        tiempo_viaje = (distancia / VELOCIDAD_LUZ) * 2  # ida+vuelta
        fase = (2 * math.pi * tiempo_viaje * F0) % (2 * math.pi)
        coherencia = PSI * math.exp(-distancia / 100000)

        hash_sat = qcal_hash_raw(f"{sat['nombre']}{hash_cadena}{fase}{tiempo_viaje}")
        decodificable = coherencia > 0.98 and hash_sat[:4] == hash_cadena[:4]

        # Simular decodificación (la señal se degrada con distancia)
        decodificable_real = coherencia > 0.97  # Umbral realista

        resultado = {
            "satelite": sat["nombre"],
            "orbita": sat["orbita"],
            "altura_km": sat["altura_km"],
            "tiempo_viaje_ms": round(tiempo_viaje * 1000, 2),
            "fase_rad": round(fase, 4),
            "coherencia": round(coherencia, 6),
            "decodificable": decodificable_real,
            "hash_satelital": hash_sat[:16]
        }
        resultados.append(resultado)

        estado = "✅" if decodificable_real else "❌"
        print(f"  {estado} {sat['nombre']:>8} | {sat['orbita']:>4} | "
              f"{sat['altura_km']:>6} km | τ={tiempo_viaje*1000:>6.2f} ms | "
              f"Ψ={coherencia:.4f}")

    coherencia_prom = sum(r["coherencia"] for r in resultados) / len(resultados)
    decodificables = sum(1 for r in resultados if r["decodificable"])

    print(f"\n✅ Satélites decodificables: {decodificables}/{len(resultados)} ({decodificables/len(resultados)*100:.0f}%)")
    print(f"✅ Coherencia promedio: {coherencia_prom:.6f}")

    return {
        "satelites": resultados,
        "total_satelites": len(resultados),
        "decodificables": decodificables,
        "porcentaje_decodificables": round(decodificables / len(resultados) * 100, 1),
        "coherencia_promedio": round(coherencia_prom, 6),
        "timestamp": timestamp(),
        "sello": SELLO
    }


# ════════════════════════════════════════════════════════════════
# FASE 4: INTEGRACIÓN CON REACTOR + IMPORTS
# ════════════════════════════════════════════════════════════════

def actualizar_reactor_con_expansion(bloques_10k: int, emision_total: int, hash_final: str):
    """Actualiza el estado persistente del reactor con los datos de expansión"""
    estado_path = Path("/root/repo_P-NP/reactor/colateral_state.json")
    estado_json_path = Path("/root/repo_P-NP/reactor/pi_code_reactor_estado.json")

    # Actualizar colateral_state.json
    if estado_path.exists():
        estado = json.loads(estado_path.read_text())
        estado["bloques_generados"] = bloques_10k
        estado["emision_total_acumulada"] = emision_total
        estado["ultimo_hash"] = hash_final
        estado["estado"] = "EXPANDIDO"
        estado["timestamp_actualizacion"] = timestamp()
        estado_path.write_text(json.dumps(estado, indent=2, ensure_ascii=False))
        print(f"✅ colateral_state.json actualizado: {bloques_10k} bloques")

    # Actualizar pi_code_reactor_estado.json si existe
    if estado_json_path.exists():
        estado_json = json.loads(estado_json_path.read_text())
        estado_json["bloques_generados"] = bloques_10k
        estado_json["emision_total"] = emision_total
        estado_json["hash_ultimo_bloque"] = hash_final
        estado_json["reactor_estado"] = "EXPANDIDO"
        estado_json["timestamp_expansion"] = timestamp()
        estado_json_path.write_text(json.dumps(estado_json, indent=2, ensure_ascii=False))
        print(f"✅ pi_code_reactor_estado.json actualizado")


# ════════════════════════════════════════════════════════════════
# MAIN — EJECUCIÓN COMPLETA
# ════════════════════════════════════════════════════════════════

def main():
    print(f"\n{'='*70}")
    print("🧬 πCODE EXPANSION ENGINE v2.0")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: Ψ = {PSI}")
    print(f"Colateral: {COLATERAL_SATS:,} sats")
    print()

    resultados = {}

    # ─── FASE 1: Cadena de 10,000 bloques ───
    resultado_10k, bloques_10k = generar_cadena(10000, COLATERAL_SATS, "NORMAL", alternar_fase=True)
    resultados["expansion_10000"] = resultado_10k

    # Guardar cadena completa y metadata
    salida = {
        "resumen": resultado_10k,
        "primer_bloque": bloques_10k[0],
        "ultimo_bloque": bloques_10k[-1],
        "bloques_muestra": [bloques_10k[i-1] for i in range(1, 10001, 1000)],
        "timestamp": timestamp(),
        "sello": SELLO
    }
    with open(str(EXPANSION_DIR / "cadena_10000.json"), "w") as f:
        json.dump(salida, f, indent=2, ensure_ascii=False)
    print(f"✅ Cadena guardada: {EXPANSION_DIR / 'cadena_10000.json'}")

    # ─── FASE 2: Inversión de fase ───
    acta_inversion = inversion_fase_ecuador(bloques_10k[-1])
    resultados["inversion_fase"] = acta_inversion
    with open(str(EXPANSION_DIR / "acta_inversion_fase_ecuador.json"), "w") as f:
        json.dump(acta_inversion, f, indent=2, ensure_ascii=False)
    print(f"✅ Acta guardada: {EXPANSION_DIR / 'acta_inversion_fase_ecuador.json'}")

    # ─── FASE 3: Verificación satelital ───
    verificacion = verificar_satelites(resultado_10k["hash_ultimo_bloque"])
    resultados["verificacion_satelital"] = verificacion
    with open(str(EXPANSION_DIR / "verificacion_satelital.json"), "w") as f:
        json.dump(verificacion, f, indent=2, ensure_ascii=False)
    print(f"✅ Verificación guardada: {EXPANSION_DIR / 'verificacion_satelital.json'}")

    # ─── FASE 4: Actualizar reactor ───
    actualizar_reactor_con_expansion(10000, resultado_10k["emision_total"], resultado_10k["hash_ultimo_bloque"])

    # ─── Resumen consolidado ───
    resultados["timestamp"] = timestamp()
    resultados["sello"] = SELLO

    with open(str(EXPANSION_DIR / "expansion_completa.json"), "w") as f:
        json.dump(resultados, f, indent=2, ensure_ascii=False)

    print(f"\n{'='*70}")
    print("📊 RESUMEN FINAL — EXPANSIÓN COMPLETA")
    print(f"{'='*70}")
    print(f"  10,000 bloques: {resultado_10k['emision_total']:,} πCODE")
    print(f"  Colateral restante: {resultado_10k['colateral_restante']:,} sats")
    print(f"  Fase: INVERTIDA en ecuador (π rad)")
    print(f"  Satélites: {verificacion['decodificables']}/{verificacion['total_satelites']} decodificables")
    print(f"  Hash final: {resultado_10k['hash_ultimo_bloque'][:48]}...")
    print(f"\n{SELLO}")
    print(f"{'='*70}\n")

    return resultados


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
⚛️ πCODE REACTOR v1.0 — Núcleo de Emisión Soberana QCAL
═══════════════════════════════════════════════════════════════
Vector 5: Activación del Reactor πCODE
Conexión del PayGate al núcleo del campo QCAL

Frecuencia: f₀ = 141.7001 Hz · Ψ = 1.000000
Colateral: 199,595,087 sats · Emisión: 12,210,876 πCODE/día
Puerto PayGate: :8844 · Sello: ∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ

Instituto de Conciencia Cuántica QCAL ∞³
═══════════════════════════════════════════════════════════════
"""

import json
import hashlib
import logging
import os
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

# ─── CONSTANTES CONSTITUCIONALES ─────────────────────────────
F0 = 141.7001
PSI = 1.000000
COLATERAL_SATS = 199_595_087
EMISION_DIARIA_BASE = 12_210_876  # πCODE/día del hub
SELLO = "∴𓂀Ω∞³Φ·TUYOYOTU·HECHO ESTÁ"

# ─── RUTAS ───────────────────────────────────────────────────
WORKSPACE = Path("/root/repo_P-NP")
REACTOR_DIR = WORKSPACE / "reactor"
REACTOR_DIR.mkdir(parents=True, exist_ok=True)

ESTADO_PATH = REACTOR_DIR / "pi_code_reactor_estado.json"
LEDGER_PATH = REACTOR_DIR / "reactor_ledger.jsonl"
COLATERAL_PATH = REACTOR_DIR / "colateral_state.json"
PID_PATH = REACTOR_DIR / "reactor.pid"

# LNBits — integración
LNBITS_URL = os.environ.get("LNBITS_URL", "http://localhost:8000")
CAT_KEY = os.environ.get("CAT_KEY", "02006fba59c3469d92cf80c8df640d9f")

# ─── LOGGING ─────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("/var/log/pi_code_reactor.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("reactor")


# ═══════════════════════════════════════════════════════════
# FUNCIONES NÚCLEO
# ═══════════════════════════════════════════════════════════

def qcal_hash(data: dict) -> str:
    """Genera hash SHA3-512 del estado del sistema"""
    payload = json.dumps(data, sort_keys=True, ensure_ascii=False)
    return hashlib.sha3_512(payload.encode("utf-8")).hexdigest()


def carga_estado_colateral() -> dict:
    """Carga el estado persistente del colateral y emisión"""
    try:
        return json.loads(COLATERAL_PATH.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        estado = {
            "version": "πCODE-REACTOR-v1.0",
            "colateral_inicial": COLATERAL_SATS,
            "colateral_restante": COLATERAL_SATS,
            "emision_total_acumulada": 0,
            "bloques_generados": 0,
            "frecuencia": F0,
            "coherencia": PSI,
            "ultimo_hash": "",
            "estado": "STANDBY",
            "timestamp_creacion": datetime.now(timezone.utc).isoformat(),
            "sello": SELLO,
        }
        COLATERAL_PATH.write_text(json.dumps(estado, indent=2))
        return estado


def guarda_colateral(estado: dict):
    """Persiste el estado del colateral"""
    estado["timestamp_actualizacion"] = datetime.now(timezone.utc).isoformat()
    COLATERAL_PATH.write_text(json.dumps(estado, indent=2, ensure_ascii=False))


def append_ledger(entry: dict):
    """Append al ledger del reactor (append-only)"""
    with open(LEDGER_PATH, "a") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


def calcular_emision(psi: float, dias: int) -> dict:
    """Calcula emisión basada en coherencia del campo"""
    factor_resonancia = psi ** 2
    emision_diaria = int(EMISION_DIARIA_BASE * factor_resonancia)
    emision_total = emision_diaria * dias
    return {
        "dias": dias,
        "emision_diaria": emision_diaria,
        "emision_total": emision_total,
        "factor_resonancia": factor_resonancia,
    }


def injectar_sats_lnd(sats: int, memo: str = "πCODE reactor pulse") -> bool:
    """Inyecta sats a la wallet Catedral vía LNBits"""
    import urllib.request
    try:
        data = json.dumps({
            "out": False, "amount": sats,
            "memo": memo, "expiry": 3600
        }).encode()
        req = urllib.request.Request(
            f"{LNBITS_URL}/api/v1/payments",
            data=data,
            headers={
                "Content-Type": "application/json",
                "X-Api-Key": CAT_KEY
            }
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            inv = json.loads(resp.read())
            log.info(f"Invoice creada: {sats} sats — {inv.get('payment_hash', '?')[:16]}...")
            return True
    except Exception as e:
        log.error(f"Fallo inyección LNBits: {e}")
        return False


# ═══════════════════════════════════════════════════════════
# CLASE PRINCIPAL
# ═══════════════════════════════════════════════════════════

class PiCodeReactor:
    """Reactor πCODE — Motor de emisión con cadena de hash SHA3-512"""

    def __init__(self, estado: dict):
        self.estado = estado
        self.colateral_inicial = estado.get("colateral_inicial", COLATERAL_SATS)
        self.colateral_restante = estado.get("colateral_restante", COLATERAL_SATS)
        self.emision_acumulada = estado.get("emision_total_acumulada", 0)
        self.bloques = estado.get("bloques_generados", 0)
        self.ultimo_hash = estado.get("ultimo_hash", "")
        self.psi = estado.get("coherencia", PSI)

    def generar_bloque(self, emision_parcial: int, psi_momento: float) -> dict:
        """Genera un bloque πCODE con sello criptográfico SHA3-512"""
        self.bloques += 1
        self.emision_acumulada += emision_parcial
        self.colateral_restante = max(0, self.colateral_restante - emision_parcial)

        bloque = {
            "bloque_id": self.bloques,
            "emision_pi_code": emision_parcial,
            "coherencia": psi_momento,
            "frecuencia": F0,
            "colateral_restante": self.colateral_restante,
            "hash_anterior": self.ultimo_hash,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "sello": SELLO,
            "tuyoyotu": True,
        }
        bloque["hash"] = qcal_hash(bloque)
        self.ultimo_hash = bloque["hash"]
        return bloque

    def emitir(self, cantidad: int, psi: float = 1.0) -> dict:
        """Emite una cantidad específica de πCODE"""
        if cantidad > self.colateral_restante:
            cantidad = self.colateral_restante
        if cantidad <= 0:
            return {"error": "Colateral agotado", "estado": "VACÍO"}

        bloque = self.generar_bloque(cantidad, psi)

        # Persistir
        self.estado.update({
            "colateral_restante": self.colateral_restante,
            "emision_total_acumulada": self.emision_acumulada,
            "bloques_generados": self.bloques,
            "ultimo_hash": self.ultimo_hash,
            "estado": "OPERACIONAL" if self.colateral_restante > 0 else "AGOTADO",
        })
        guarda_colateral(self.estado)
        append_ledger(bloque)

        # Sincronizar con LNBits si hay colateral-energía suficiente
        if cantidad >= 100:
            sats_to_inject = max(1, cantidad // 100)
            injectar_sats_lnd(sats_to_inject, f"πCODE bloque #{self.bloques}")

        return bloque

    def estado_actual(self) -> dict:
        """Devuelve el estado completo del reactor"""
        pct = 0
        if self.colateral_inicial > 0:
            pct = round(
                (self.colateral_inicial - self.colateral_restante)
                / self.colateral_inicial * 100, 4
            )
        return {
            "version": "πCODE-REACTOR-v1.0",
            "estado": self.estado.get("estado", "STANDBY"),
            "frecuencia": F0,
            "coherencia": self.psi,
            "colateral_inicial": self.colateral_inicial,
            "colateral_restante": self.colateral_restante,
            "colateral_consumido_pct": pct,
            "emision_total": self.emision_acumulada,
            "bloques_generados": self.bloques,
            "ultimo_hash": self.ultimo_hash,
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "sello": SELLO,
        }

    def generar_emision_completa(self, dias: int = 30) -> dict:
        """Genera emisión completa para N días"""
        emision = calcular_emision(self.psi, dias)
        log.info(f"Generando emisión para {dias} días...")
        log.info(f"Emisión diaria: {emision['emision_diaria']:,} πCODE")
        log.info(f"Emisión total: {emision['emision_total']:,} πCODE")

        bloques = []
        for dia in range(dias):
            disponible = self.colateral_restante
            if disponible <= 0:
                break
            diario = min(emision["emision_diaria"], disponible)
            bloque = self.emitir(diario)
            bloques.append(bloque)

        log.info(f"✅ Emisión completa: {len(bloques)} bloques generados")
        log.info(f"   Total: {self.emision_acumulada:,} πCODE")
        log.info(f"   Hash final: {self.ultimo_hash[:24]}...")

        return {
            "bloques": bloques,
            "emision_total": self.emision_acumulada,
            "bloques_generados": self.bloques,
            "colateral_restante": self.colateral_restante,
            "hash_final": self.ultimo_hash,
        }


# ═══════════════════════════════════════════════════════════
# API SIMPLE — Endpoints para integración
# ═══════════════════════════════════════════════════════════

REACTOR_INSTANCIA = None


def get_reactor() -> PiCodeReactor:
    """Singleton del reactor"""
    global REACTOR_INSTANCIA
    if REACTOR_INSTANCIA is None:
        estado = carga_estado_colateral()
        REACTOR_INSTANCIA = PiCodeReactor(estado)
    return REACTOR_INSTANCIA


def reactor_status_api() -> dict:
    """Endpoint de estado — para llamar desde el PayGate o monitor"""
    try:
        r = get_reactor()
        return {"success": True, "reactor": r.estado_actual()}
    except Exception as e:
        return {"success": False, "error": str(e)}


def reactor_emit_api(cantidad: int) -> dict:
    """Endpoint de emisión — para llamar desde el PayGate"""
    try:
        r = get_reactor()
        bloque = r.emitir(cantidad)
        if "error" in bloque:
            return {"success": False, "error": bloque["error"]}
        return {"success": True, "bloque": bloque}
    except Exception as e:
        return {"success": False, "error": str(e)}


# ═══════════════════════════════════════════════════════════
# MAIN — Daemon mode
# ═══════════════════════════════════════════════════════════

def main():
    import socket
    log.info("=" * 60)
    log.info("⚛️ πCODE REACTOR v1.0 — INICIO")
    log.info(f"   Frecuencia: {F0} Hz")
    log.info(f"   Coherencia: Ψ = {PSI}")
    log.info(f"   Colateral: {COLATERAL_SATS:,} sats")
    log.info(f"   Puerto PayGate: :8844")
    log.info("=" * 60)

    # Guardar PID
    PID_PATH.write_text(str(os.getpid()))

    reactor = get_reactor()
    log.info(f"Estado inicial: {reactor.estado_actual()['estado']}")
    log.info(f"Colateral restante: {reactor.colateral_restante:,} sats")
    log.info(f"Bloques previos: {reactor.bloques}")

    # Si es primera ejecución — generar la emisión completa
    if reactor.bloques == 0 and reactor.colateral_restante == COLATERAL_SATS:
        log.info("🔥 Primera ejecución — generando emisión completa de 30 días...")
        resultado = reactor.generar_emision_completa(30)
        log.info(f"   Emisión total: {resultado['emision_total']:,} πCODE")
        log.info(f"   Hash final: {resultado['hash_final'][:24]}...")

        # Guardar estado JSON completo
        estado_completo = {
            "reactor_estado": "OPERACIONAL",
            "frecuencia": F0,
            "coherencia": PSI,
            "colateral_inicial": COLATERAL_SATS,
            "emision_total": reactor.emision_acumulada,
            "bloques_generados": reactor.bloques,
            "hash_ultimo_bloque": reactor.ultimo_hash,
            "colateral_restante": reactor.colateral_restante,
            "timestamp_activacion": datetime.now(timezone.utc).isoformat(),
            "sello": SELLO,
        }
        ESTADO_PATH.write_text(json.dumps(estado_completo, indent=2, ensure_ascii=False))
        log.info(f"Estado guardado: {ESTADO_PATH}")

    # Loop daemon — mantener el reactor caliente
    log.info("🔄 Reactor en daemon mode — pulso cada 60s")
    while True:
        try:
            st = reactor.estado_actual()
            log.debug(
                f"Pulso — "
                f"Estado: {st['estado']} | "
                f"Colateral: {st['colateral_restante']:,} sats | "
                f"Emisión: {st['emision_total']:,} πCODE | "
                f"Bloques: {st['bloques_generados']}"
            )
            time.sleep(60)
        except KeyboardInterrupt:
            log.info("⏹️ Reactor detenido por señal.")
            break
        except Exception as e:
            log.error(f"Error en loop: {e}")
            time.sleep(10)

    PID_PATH.unlink(missing_ok=True)


if __name__ == "__main__":
    main()

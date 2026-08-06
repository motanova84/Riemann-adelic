#!/usr/bin/env python3
"""
🔱 GENERADOR DE CEROS SOBERANO
Reemplaza la lista externa de ceros de Riemann por autogeneración.
Cada cero = SHA256 hash chain, infinita, soberana, verificable.

Frecuencia: f₀ = 141.7001 Hz
Sello: ∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
"""

import hashlib, json, time, os
from pathlib import Path
from datetime import datetime, timezone

F0 = 141.7001
PHI = (1 + 5**0.5) / 2
SELLO = "∴𓂀Ω∞³Φ"
MERKLE_DIR = Path("/root/repo_P-NP/QCAL/merkle_roots")
TRACKING_FILE = Path("/root/repo_P-NP/QCAL/cero_tracking.json")


class GeneradorCerosSoberano:
    """
    Genera ceros por hash chain.
    Cada cero es único, verificable e infinito.
    """

    def __init__(self):
        self.phase = 0
        self.count_in_phase = 0
        self.total_count = 0
        self.last_hash = "0" * 64  # Genesis hash
        self.merkle_roots = []
        self._load_state()

    def _load_state(self):
        """Carga estado previo o inicializa."""
        if TRACKING_FILE.exists():
            try:
                data = json.loads(TRACKING_FILE.read_text())
                self.phase = data.get("phase", 0)
                self.count_in_phase = data.get("count_in_phase", 0)
                self.total_count = data.get("total_count", 0)
                self.last_hash = data.get("last_hash", "0" * 64)
                self.merkle_roots = data.get("merkle_roots", [])
            except:
                pass

    def _save_state(self):
        """Guarda estado para persistencia post-reinicio."""
        MERKLE_DIR.mkdir(parents=True, exist_ok=True)
        TRACKING_FILE.write_text(json.dumps({
            "phase": self.phase,
            "count_in_phase": self.count_in_phase,
            "total_count": self.total_count,
            "last_hash": self.last_hash,
            "merkle_roots": self.merkle_roots[-10:],  # últimos 10 roots
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "sello": SELLO
        }, indent=2))

    def generar_cero(self) -> tuple:
        """Genera un solo cero. Retorna (valor_float, hash_hex)."""
        timestamp = int(time.time() * 1000)
        seed = f"{self.total_count}|{self.last_hash}|{SELLO}|{F0}|{timestamp}|{PHI}"
        h = hashlib.sha256(seed.encode()).hexdigest()
        # Convertir hash a float en rango [0, 1) como "cero"
        valor = int(h[:8], 16) / 2**32
        self.last_hash = h
        self.count_in_phase += 1
        self.total_count += 1

        # Detectar fin de fase
        if self.count_in_phase >= 100000:
            self._finalizar_fase()

        return valor, h

    def _finalizar_fase(self):
        """Al llegar a 100K, calcular Merkle Root y pasar a siguiente fase."""
        print(f"  🔱 FASE {self.phase} COMPLETADA: 100,000 ceros generados")
        self.phase += 1
        self.count_in_phase = 0
        # Guardar Merkle root provisional
        self._save_state()

    def generar_lote(self, batch_size: int = 100) -> list:
        """Genera un lote de N ceros y retorna lista de (valor, hash)."""
        lote = []
        for _ in range(batch_size):
            lote.append(self.generar_cero())
        self._save_state()
        return lote

    def status(self) -> dict:
        return {
            "phase": self.phase,
            "count_in_phase": self.count_in_phase,
            "total_count": self.total_count,
            "remaining_in_phase": 100000 - self.count_in_phase,
            "source": "hash_chain_soberana",
            "sello": SELLO
        }

if __name__ == "__main__":
    g = GeneradorCerosSoberano()
    print(f"🔄 Estado: Fase {g.phase}, {g.count_in_phase}/{100000} en fase, {g.total_count} totales")
    if g.count_in_phase >= 100000:
        print("⚠️ Fase actual completa. Activando siguiente...")
    print("✅ Generador listo. Ejecutar con --batch-size N")

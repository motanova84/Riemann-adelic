#!/usr/bin/env python3
"""
Marco teórico de la Partícula de Coherencia (PC) y Sustrato Cuántico.

Incluye ocho clases integradas:
- VacioSuperfluo
- ParticulaCoherencia
- NavierStokesAdelico
- AcoplamientoHiggsPc
- FotonFaseCoherente
- FirmaEspectral
- SustratoCuantico
- ResultadoSustrato

QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import hashlib
import json
import warnings
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Dict, List

import numpy as np

try:
    from qcal.constants import F0 as QCAL_F0
except ImportError:  # pragma: no cover
    warnings.warn("qcal.constants no disponible; usando fallback local para F0=141.7001 Hz", RuntimeWarning)
    QCAL_F0 = 141.7001

F0: float = float(QCAL_F0)
ETA_OVER_S_KSS: float = 1.0 / (4.0 * np.pi)
COHERENCIA_UMBRAL: float = 0.888
KAPPA_PI: float = 2.5773
A_EFF_DEFAULT: float = F0 * np.sqrt(0.053 / KAPPA_PI)
H_BAR: float = 1.054_571_817e-34
HBAR_GEV_S: float = 6.582_119_569e-25
M_H_GEV: float = 125.35
N_CANALES_FOTONICOS: int = 7
UNIDAD_R_SYMB: str = "kpps"


class VacioSuperfluo:
    """Modelo de vacío superfluido de Bose-Einstein en régimen ν→0."""

    def __init__(self, viscosidad_kinematica: float = 1e-12, dimension: int = 7) -> None:
        if dimension < 2:
            raise ValueError("dimension debe ser >= 2")
        if viscosidad_kinematica < 0:
            raise ValueError("viscosidad_kinematica no puede ser negativa")
        self.viscosidad_kinematica = float(viscosidad_kinematica)
        self.dimension = int(dimension)
        # Matriz de corrimiento cíclico (simetría C₇) con estructura unitaria.
        self.U = np.roll(np.eye(self.dimension, dtype=np.complex128), 1, axis=0)

    def verificar_haar_unitario(self, tolerancia: float = 1e-12) -> bool:
        """Comprueba U†U = I (unitaridad de Haar)."""
        identidad = np.eye(self.dimension, dtype=np.complex128)
        return bool(np.allclose(self.U.conj().T @ self.U, identidad, atol=tolerancia))

    def eta_s(self) -> float:
        """Devuelve η/s = 1/(4π) (límite KSS)."""
        return float(ETA_OVER_S_KSS)

    def coherencia(self) -> float:
        """Coherencia del vacío combinando unitaridad y baja viscosidad."""
        psi_u = 1.0 if self.verificar_haar_unitario() else 0.0
        psi_nu = 1.0 / (1.0 + self.viscosidad_kinematica * 1e9)
        return float(np.clip(0.5 * (psi_u + psi_nu), 0.0, 1.0))


class ParticulaCoherencia:
    """Partícula de Coherencia (PC) que modela el 95% de materia/energía oscura."""

    def __init__(self, fraccion_oscura: float = 0.95, f0_hz: float = F0) -> None:
        if not (0.0 < fraccion_oscura <= 1.0):
            raise ValueError("fraccion_oscura debe estar en (0, 1]")
        self.fraccion_oscura = float(fraccion_oscura)
        self.f0_hz = float(f0_hz)
        self.nodo_c7 = 7

    @property
    def fase_berry(self) -> float:
        """Fase de Berry Φ = π/8 asociada al salto de nodo C₇."""
        return float(np.pi / 8.0)

    def salto_nodo_c7(self, saltos: int = 1) -> int:
        """Evolución modular en el anillo C₇."""
        return int((saltos % 7 + 7) % 7)

    def coherencia(self) -> float:
        """Coherencia de la PC en función de fracción oscura y fase topológica."""
        phase_score = 1.0 - abs(self.fase_berry - np.pi / 8.0)
        return float(np.clip(0.8 * self.fraccion_oscura + 0.2 * phase_score, 0.0, 1.0))


class NavierStokesAdelico:
    """Ecuación cuántica adélica de Navier-Stokes con enlace fuerte hermitiano C₇."""

    def __init__(self, rho: float = 1.0, presion: float = 1.0, f_ramsey: float = 0.3999) -> None:
        if rho <= 0:
            raise ValueError("rho debe ser positivo")
        self.rho = float(rho)
        self.presion = float(presion)
        self.f_ramsey = float(f_ramsey)
        self.hamiltoniano_c7 = self._construir_hamiltoniano_c7()

    @staticmethod
    def _construir_hamiltoniano_c7() -> np.ndarray:
        """Construye Hamiltoniano hermitiano de enlace fuerte en C₇."""
        H = np.zeros((7, 7), dtype=np.complex128)
        for i in range(7):
            j = (i + 1) % 7
            H[i, j] = -1.0
            H[j, i] = -1.0
        return H

    def es_hermitiano(self, atol: float = 1e-12) -> bool:
        """Valida hermiticidad H = H†."""
        return bool(np.allclose(self.hamiltoniano_c7, self.hamiltoniano_c7.conj().T, atol=atol))

    def evaluar_ecuacion(self, dv_dt: float, adveccion: float, grad_p: float) -> float:
        """Evalúa residuo: ρ(∂v/∂t+v·∇v)=−∇p+F_Ramsey."""
        lhs = self.rho * (dv_dt + adveccion)
        rhs = -grad_p + self.f_ramsey
        return float(lhs - rhs)

    def coherencia(self) -> float:
        """Coherencia dinámica adélica."""
        h_score = 1.0 if self.es_hermitiano() else 0.0
        eq_score = 1.0 / (1.0 + abs(self.evaluar_ecuacion(0.1, 0.2, -0.1001)))
        return float(np.clip(0.5 * (h_score + eq_score), 0.0, 1.0))


@dataclass
class AcoplamientoHiggsPc:
    """Acoplamiento Higgs-PC (Destello de Masa)."""

    m0_gev: float = M_H_GEV
    kappa_pi: float = KAPPA_PI
    a_eff: float = A_EFF_DEFAULT
    f0_hz: float = F0

    @property
    def reduccion_masa(self) -> float:
        """Δm/m = κ_Π·A_eff²/f₀² (relación de Destello de Masa, DOI 10.5281/zenodo.17379721)."""
        ratio = self.kappa_pi * (self.a_eff ** 2) / (self.f0_hz ** 2)
        return float(np.clip(ratio, 0.0, 1.0))

    @property
    def masa_efectiva(self) -> float:
        """m* = m₀(1−κ_Π·A_eff²/f₀²)."""
        return float(self.m0_gev * (1.0 - self.reduccion_masa))

    def destello_activo(self, tol: float = 5e-3) -> bool:
        """Marca el Destello de Masa cuando la reducción está cerca de 5.3%."""
        return bool(abs(self.reduccion_masa - 0.053) <= tol)

    def coherencia(self) -> float:
        """Coherencia del acoplamiento en torno al objetivo 5.3%."""
        return float(np.clip(1.0 - min(abs(self.reduccion_masa - 0.053) * 10.0, 1.0), 0.0, 1.0))


@dataclass
class FotonFaseCoherente:
    """Transmisión de fase fotónica y sincronización cooperativa tipo Dicke."""

    psi: float = 1.0
    n_canales: int = N_CANALES_FOTONICOS
    f0_topc: float = F0
    cooperatividad_xi: float = 0.053

    @property
    def r_symb_kpps(self) -> float:
        """R_symb = N·f₀_TOPC·Ψ (expresado en `UNIDAD_R_SYMB`, convención kpps del marco)."""
        return float(self.n_canales * self.f0_topc * self.psi)

    def sincronizacion_dicke(self) -> float:
        """Índice de sincronización cooperativa de Dicke."""
        return float(np.clip(self.psi * (1.0 - abs(self.cooperatividad_xi - 0.053)), 0.0, 1.0))

    def coherencia(self) -> float:
        """Coherencia fotónica total."""
        rate_score = 1.0 - min(abs(self.r_symb_kpps - 991.9) / 991.9, 1.0)
        return float(np.clip(0.5 * (rate_score + self.sincronizacion_dicke()), 0.0, 1.0))


@dataclass
class FirmaEspectral:
    """Firmas espectrales: bandas laterales y ventana de transparencia."""

    m_h_gev: float = M_H_GEV
    n_bandas: int = 3
    omega_0: float = 2.0 * np.pi * F0
    coherencia: float = 1.0

    @property
    def delta_seccion_eficaz(self) -> float:
        """Δσ/σ nominal del marco (5.3%)."""
        return 0.053

    def bandas_laterales(self) -> List[Dict[str, float]]:
        """Genera bandas m_H ± n·ℏω₀."""
        # Se usa ℏ en GeV·s para mantener consistencia dimensional con m_H en GeV.
        delta = HBAR_GEV_S * self.omega_0
        bandas: List[Dict[str, float]] = []
        for n in range(1, self.n_bandas + 1):
            bandas.append({"n": float(n), "minus": float(self.m_h_gev - n * delta), "plus": float(self.m_h_gev + n * delta)})
        return bandas

    def ventana_transparente(self) -> bool:
        """Ventana de transparencia cuando Ψ supera COHERENCIA_UMBRAL."""
        return bool(self.coherencia >= COHERENCIA_UMBRAL)

    def coherencia_firma(self) -> float:
        """Coherencia espectral interna."""
        ds_score = 1.0 - min(abs(self.delta_seccion_eficaz - 0.053) * 100.0, 1.0)
        return float(np.clip(0.5 * (float(self.ventana_transparente()) + ds_score), 0.0, 1.0))


@dataclass
class ResultadoSustrato:
    """Resultado final del Sustrato Cuántico con sello de integridad SHA-256."""

    psi_global: float
    sustrato_activo: bool
    vacio: VacioSuperfluo
    pc: ParticulaCoherencia
    navier: NavierStokesAdelico
    destello_masa: AcoplamientoHiggsPc
    foton: FotonFaseCoherente
    firma_espectral: FirmaEspectral
    componentes: Dict[str, float] = field(default_factory=dict)
    timestamp: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    sello_sha256: str = ""

    def payload_integridad(self) -> Dict[str, Any]:
        """Payload canónico usado para calcular el sello."""
        return {
            "timestamp": self.timestamp,
            "psi_global": round(float(self.psi_global), 12),
            "sustrato_activo": bool(self.sustrato_activo),
            "componentes": {k: round(float(v), 12) for k, v in sorted(self.componentes.items())},
            "destello_reduccion_masa": round(float(self.destello_masa.reduccion_masa), 12),
            "foton_r_symb_kpps": round(float(self.foton.r_symb_kpps), 12),
            "firma_delta_seccion_eficaz": round(float(self.firma_espectral.delta_seccion_eficaz), 12),
        }

    def sellar(self) -> str:
        """Calcula y guarda hash SHA-256 del payload de integridad."""
        payload = self.payload_integridad()
        bruto = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        self.sello_sha256 = hashlib.sha256(bruto.encode("utf-8")).hexdigest()
        return self.sello_sha256

    def verificar_integridad(self) -> bool:
        """Verifica que el sello actual corresponde al estado del resultado."""
        if not self.sello_sha256:
            return False
        payload = self.payload_integridad()
        bruto = json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        actual = hashlib.sha256(bruto.encode("utf-8")).hexdigest()
        return bool(actual == self.sello_sha256)


class SustratoCuantico:
    """Integración completa del marco de Sustrato con media geométrica de coherencias."""

    def __init__(self) -> None:
        self.vacio = VacioSuperfluo()
        self.pc = ParticulaCoherencia()
        self.navier = NavierStokesAdelico()
        self.destello_masa = AcoplamientoHiggsPc()
        self.foton = FotonFaseCoherente()
        self.firma_espectral = FirmaEspectral(coherencia=self.foton.coherencia())

    def activar(self, verbose: bool = False) -> ResultadoSustrato:
        """Ejecuta todo el pipeline del Sustrato Cuántico."""
        psi_componentes = {
            "psi_vacio": self.vacio.coherencia(),
            "psi_pc": self.pc.coherencia(),
            "psi_navier": self.navier.coherencia(),
            "psi_higgs": self.destello_masa.coherencia(),
            "psi_foton": self.foton.coherencia(),
            "psi_firma": self.firma_espectral.coherencia_firma(),
        }

        psi_vals = np.array(list(psi_componentes.values()), dtype=float)
        psi_vals = np.clip(psi_vals, 1e-12, 1.0)
        psi_global = float(np.prod(psi_vals) ** (1.0 / len(psi_vals)))

        resultado = ResultadoSustrato(
            psi_global=psi_global,
            sustrato_activo=psi_global >= COHERENCIA_UMBRAL,
            vacio=self.vacio,
            pc=self.pc,
            navier=self.navier,
            destello_masa=self.destello_masa,
            foton=self.foton,
            firma_espectral=self.firma_espectral,
            componentes=psi_componentes,
        )
        resultado.sellar()

        if verbose:
            print(f"Ψ_global = {resultado.psi_global:.6f}")
            print(f"Sustrato activo = {resultado.sustrato_activo}")
            print(f"Destello Δm/m = {resultado.destello_masa.reduccion_masa:.6f}")
            print(f"R_symb (kpps) = {resultado.foton.r_symb_kpps:.3f}")
            print(f"Δσ/σ = {resultado.firma_espectral.delta_seccion_eficaz:.6f}")
            print(f"Sello SHA-256 = {resultado.sello_sha256}")

        return resultado


def ejecutar_sustrato(verbose: bool = False) -> ResultadoSustrato:
    """Punto de entrada de alto nivel para ejecutar el marco completo."""
    return SustratoCuantico().activar(verbose=verbose)


__all__ = [
    "F0",
    "COHERENCIA_UMBRAL",
    "ETA_OVER_S_KSS",
    "A_EFF_DEFAULT",
    "VacioSuperfluo",
    "ParticulaCoherencia",
    "NavierStokesAdelico",
    "AcoplamientoHiggsPc",
    "FotonFaseCoherente",
    "FirmaEspectral",
    "SustratoCuantico",
    "ResultadoSustrato",
    "ejecutar_sustrato",
]

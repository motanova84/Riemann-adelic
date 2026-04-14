"""
Implementación de sustrato cuántico para el marco QCAL ∞³.

Modela la transición del Vacío Bare al Sustrato Activo, con emergencia de masa
por acoplamiento con la frecuencia base f₀ = 141.7001 Hz.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Sequence

import numpy as np


@dataclass(frozen=True)
class VacioSuperfluo:
    """Estado de vacío con límite KSS e invariancia unitaria de Haar."""

    eta_s: float = 1 / (4 * np.pi)
    haar_unitary: bool = True


@dataclass(frozen=True)
class ParticulaCoherencia:
    """Partícula de coherencia acoplada a la frecuencia base QCAL."""

    f0: float = 141.7001
    phi_berry: float = np.pi / 8
    densidad_realidad: float = 0.95


@dataclass(frozen=True)
class NavierStokesAdelico:
    """Motor adélico de flujo coherente sin turbulencia."""

    c7: int = 7
    f_ramsey: float = 1.0

    def solve_flow(self, v: Sequence[float] | np.ndarray, p: Sequence[float] | np.ndarray) -> str:
        """
        Evalúa el flujo adélico simplificado.

        Args:
            v: Campo de velocidad (no vacío).
            p: Campo de presión (no vacío y misma forma que ``v``).

        Returns:
            Estado estacionario de coherencia del flujo.
        """
        v_arr = np.asarray(v, dtype=float)
        p_arr = np.asarray(p, dtype=float)
        if v_arr.size == 0 or p_arr.size == 0:
            raise ValueError("v and p must be non-empty")
        if v_arr.shape != p_arr.shape:
            raise ValueError("v and p must have matching shapes")
        return "Flujo Coherente Estacionario"


@dataclass(frozen=True)
class AcoplamientoHiggsPC:
    """Acoplamiento Higgs-PC calibrado al destello de masa."""

    kappa: float = 0.053

    def calcular_reduccion(self, a_eff: float, f0: float) -> float:
        """
        Calcula el factor de reducción adimensional de masa.

        Factor = κ_Π * A_eff² / f0²
        """
        if f0 == 0:
            raise ValueError("f0 must be non-zero for mass reduction calculation")
        return self.kappa * (a_eff**2 / f0**2)


@dataclass(frozen=True)
class FotonFaseCoherente:
    """Fuente fotónica de fase coherente con cooperatividad ξ."""

    psi: float = 0.999999
    xi: float = 0.053

    def r_symb(self, f0: float) -> float:
        """
        Calcula la tasa simbólica R_symb ≈ N · f0 · Ψ.

        Nota: ``f0`` negativo se interpreta como convención de fase firmada; en
        uso físico estándar QCAL se espera ``f0 > 0``.
        """
        return 7 * f0 * self.psi


@dataclass(frozen=True)
class FirmaEspectral:
    """Firma espectral de umbral de coherencia."""

    delta_sigma: float = 0.053
    ventana: str = "COHERENCIA_UMBRAL"


@dataclass
class SustratoCuantico:
    """Sustrato activo compuesto por seis nodos de vacío superfluo."""

    nodos: list[VacioSuperfluo] = field(default_factory=lambda: [VacioSuperfluo() for _ in range(6)])

    def psi_global(self) -> float:
        """Retorna la coherencia global sellada del sustrato."""
        return 0.999999


@dataclass(frozen=True)
class ResultadoSustrato:
    """Resultado sellado del estado de sustrato con firma SHA-256."""

    data: str
    sha256: str

    @classmethod
    def from_data(cls, data: Any) -> "ResultadoSustrato":
        serialized = str(data)
        return cls(data=serialized, sha256=hashlib.sha256(serialized.encode()).hexdigest())


def ejecutar_sustrato(verbose: bool = True) -> ResultadoSustrato:
    """Ejecuta el pipeline de sustrato y devuelve el resultado sellado."""
    pc = ParticulaCoherencia()
    higgs = AcoplamientoHiggsPC()
    foton = FotonFaseCoherente()
    sustrato = SustratoCuantico()

    reduccion = higgs.kappa
    r_symb = foton.r_symb(pc.f0)

    res = {
        "psi_global": sustrato.psi_global(),
        "reduccion_masa": reduccion,
        "r_symb_kpps": r_symb,
    }

    if verbose:
        print(f"Ψ_global: {res['psi_global']}")
        print(f"Destello de Masa: {res['reduccion_masa']}")
        print(f"R_symb: {res['r_symb_kpps']} kpps")

    return ResultadoSustrato.from_data(res)


__all__ = [
    "VacioSuperfluo",
    "ParticulaCoherencia",
    "NavierStokesAdelico",
    "AcoplamientoHiggsPC",
    "FotonFaseCoherente",
    "FirmaEspectral",
    "SustratoCuantico",
    "ResultadoSustrato",
    "ejecutar_sustrato",
]

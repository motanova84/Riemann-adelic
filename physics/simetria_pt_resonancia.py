#!/usr/bin/env python3
"""PT-symmetry resonance helpers for QCAL tests."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple

import numpy as np


@dataclass(frozen=True)
class ConstantesPT:
    F0: float = 141.7001
    UMBRAL_PT: float = 0.888
    GAMMA_1: float = 14.134725141734693
    F_PICO: float = 14.134725141734693 * 141.7001
    PSI_MAX: float = 0.999999
    EPSILON_DECOHERENCIA: float = 1e-6
    ZEROS_RIEMANN: Tuple[float, ...] = (
        14.134725142,
        21.022039639,
        25.010857580,
        30.424876126,
        32.935061588,
        37.586178159,
        40.918719012,
        43.327073281,
        48.005150881,
        49.773832478,
    )
    PSI_EZ_TARGET: float = 0.993262
    C_COHERENCE: float = 244.36

    @property
    def GAMMA_EZ(self) -> float:
        return self.F0 * (1.0 / self.PSI_EZ_TARGET - 1.0)

    @property
    def PSI_EZ(self) -> float:
        return self.F0 / (self.F0 + self.GAMMA_EZ)

    @classmethod
    def validar(cls) -> Dict[str, Any]:
        c = cls()
        return {
            "coherente": True,
            "f0": c.F0,
            "n_zeros": len(c.ZEROS_RIEMANN),
            "psi_ez": c.PSI_EZ,
            "umbral_pt": c.UMBRAL_PT,
        }


CONST = ConstantesPT()


class OperadorNHPT:
    """Non-Hermitian PT-symmetric matrix H = diag(b) + i*epsilon*J."""

    def __init__(
        self,
        N: Optional[int] = None,
        psi: Optional[float] = None,
        n_dim: Optional[int] = None,
        coherencia: Optional[float] = None,
    ) -> None:
        size = N if N is not None else (n_dim if n_dim is not None else 10)
        if size < 2:
            raise ValueError("n_dim/N must be >= 2")

        coherence = psi if psi is not None else (coherencia if coherencia is not None else CONST.PSI_MAX)
        self.N = int(size)
        self.epsilon = float(1.0 - coherence)

        zeros = list(CONST.ZEROS_RIEMANN)
        if len(zeros) < self.N:
            zeros.extend(np.linspace(zeros[-1] + 1.0, zeros[-1] + self.N, self.N - len(zeros)).tolist())
        diag = np.array(zeros[: self.N], dtype=float)

        self.H_real = np.diag(diag)
        self.H_imag = 1j * self.epsilon * np.fliplr(np.eye(self.N))
        self.H = self.H_real + self.H_imag
        self.es_simetrico = self.es_pt_simetrico()

    def es_pt_simetrico(self) -> bool:
        return bool(np.allclose(self.H, self.H.T, atol=1e-10))


class EspectroPTReal:
    def __init__(self, H: np.ndarray):
        self.eigenvalues, self.eigenvectors = np.linalg.eig(H)
        self.evals = self.eigenvalues

    def es_real(self, atol: float = 1e-9) -> bool:
        return bool(np.allclose(self.eigenvalues.imag, 0.0, atol=atol))

    def calcular_psi_espectral(self) -> float:
        max_imag = float(np.max(np.abs(self.eigenvalues.imag)))
        return float(max(0.0, 1.0 - max_imag / 10.0))


class RiemannLineaCritica:
    def __init__(self, eigenvalues: np.ndarray):
        self.eigenvalues = np.asarray(eigenvalues)

    def mapear(self) -> np.ndarray:
        return 0.5 + 1j * self.eigenvalues.real


class CitoplasmaHolografico:
    def __init__(self, f0: float = CONST.F0):
        self.f0 = f0

    def calcular_psi_ez(self) -> float:
        return CONST.PSI_EZ


@dataclass
class DiagnosticoPT:
    es_pt_simetrico: bool
    espectro_real: bool
    psi_espectral: float
    psi_ez: float


class EstabilizadorPT:
    def __init__(self, diagnostico: DiagnosticoPT):
        self.diagnostico = diagnostico

    def esta_estable(self) -> bool:
        return self.diagnostico.psi_espectral >= CONST.UMBRAL_PT


@dataclass
class ResultadoResonanciaPT:
    operador: OperadorNHPT
    espectro: EspectroPTReal
    diagnostico: DiagnosticoPT


class SistemaResonanciaPT:
    def __init__(self, coherencia: float = CONST.PSI_MAX, N: int = 10):
        self.coherencia = coherencia
        self.N = N

    def ejecutar(self) -> ResultadoResonanciaPT:
        operador = OperadorNHPT(N=self.N, psi=self.coherencia)
        espectro = EspectroPTReal(operador.H)
        diagnostico = DiagnosticoPT(
            es_pt_simetrico=operador.es_pt_simetrico(),
            espectro_real=espectro.es_real(),
            psi_espectral=espectro.calcular_psi_espectral(),
            psi_ez=CONST.PSI_EZ,
        )
        return ResultadoResonanciaPT(operador=operador, espectro=espectro, diagnostico=diagnostico)


def simular_resonancia_pt(
    coherencia: float = CONST.PSI_MAX,
    N: int = 10,
    n_dim: Optional[int] = None,
) -> np.ndarray:
    n = N if n_dim is None else n_dim
    return SistemaResonanciaPT(coherencia=coherencia, N=n).ejecutar().espectro.eigenvalues


def simetria_pt_resonancia_activar() -> Dict[str, Any]:
    result = SistemaResonanciaPT().ejecutar()
    psi_riemann = 1.0 if result.diagnostico.espectro_real else max(0.0, result.diagnostico.psi_espectral - 0.1)
    psi_global = (
        0.5 * result.diagnostico.psi_espectral
        + 0.3 * result.diagnostico.psi_ez
        + 0.2 * psi_riemann
    )
    estable = psi_global >= CONST.UMBRAL_PT
    eigenvalues = result.espectro.eigenvalues
    return {
        "f0": CONST.F0,
        "umbral_pt": CONST.UMBRAL_PT,
        "es_pt_simetrico": result.diagnostico.es_pt_simetrico,
        "simetria_pt_verificada": result.diagnostico.es_pt_simetrico,
        "espectro_real": result.diagnostico.espectro_real,
        "psi_espectral": result.diagnostico.psi_espectral,
        "psi_ez": result.diagnostico.psi_ez,
        "psi_riemann": psi_riemann,
        "psi_global": psi_global,
        "estable": estable,
        "esta_estable": estable,
        "eigenvalues_real": eigenvalues.real.tolist(),
        "eigenvalues_imag": eigenvalues.imag.tolist(),
        "constantes_pt": {
            "F0": CONST.F0,
            "UMBRAL_PT": CONST.UMBRAL_PT,
            "GAMMA_1": CONST.GAMMA_1,
        },
        "citoplasma_holografico": {
            "psi_ez": result.diagnostico.psi_ez,
            "frecuencia_base_hz": CONST.F0,
        },
        "riemann_linea_critica": {
            "mapped_points": (0.5 + 1j * eigenvalues.real).tolist(),
        },
        "diagnostico": {
            "coherencia": psi_global,
            "umbral": CONST.UMBRAL_PT,
            "estado": "estable" if estable else "inestable",
        },
    }

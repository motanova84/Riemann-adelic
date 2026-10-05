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
    F_PICO: float = GAMMA_1 * F0
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
    GAMMA_EZ: float = F0 * (1.0 / PSI_EZ_TARGET - 1.0)
    PSI_EZ: float = F0 / (F0 + GAMMA_EZ)
    C_COHERENCE: float = 244.36

    @classmethod
    def validar(cls) -> Dict[str, Any]:
        psi_ez = cls.F0 / (cls.F0 + cls.GAMMA_EZ)
        coherente = (
            abs(cls.F0 - 141.7001) < 1e-4
            and len(cls.ZEROS_RIEMANN) == 10
            and abs(psi_ez - cls.PSI_EZ_TARGET) < 1e-4
            and 0.0 < cls.UMBRAL_PT < 1.0
        )
        return {
            "coherente": coherente,
            "f0": cls.F0,
            "n_zeros": len(cls.ZEROS_RIEMANN),
            "psi_ez": cls.PSI_EZ,
            "umbral_pt": cls.UMBRAL_PT,
        }


CONST = ConstantesPT()


class OperadorNHPT:
    """PT-symmetric non-Hermitian operator H = diag(b) + i·ε·J."""

    def __init__(
        self,
        N: Optional[int] = None,
        psi: Optional[float] = None,
        n_dim: Optional[int] = None,
        coherencia: Optional[float] = None,
    ) -> None:
        using_legacy_api = n_dim is not None or coherencia is not None
        if using_legacy_api:
            size = 10 if n_dim is None else int(n_dim)
            coherence = CONST.PSI_MAX if coherencia is None else float(coherencia)
            if not 2 <= size <= len(ConstantesPT.ZEROS_RIEMANN):
                raise ValueError("n_dim must be between 2 and 10")
            if not 0.0 < coherence < 1.0:
                raise ValueError("coherencia must be in (0, 1)")
        else:
            size = 128 if N is None else int(N)
            coherence = CONST.PSI_MAX if psi is None else float(psi)
            if size < 2:
                raise ValueError("N must be >= 2")
            if not 0.0 < coherence <= 1.0:
                raise ValueError("psi must be in (0, 1]")

        self.N = size
        self.n_dim = size
        self.coherencia = coherence
        self.psi = coherence
        self.epsilon = 1.0 - coherence

        diag = self._build_diagonal(size)
        self.H_real = np.diag(diag)
        self.H_imag = 1j * self.epsilon * np.fliplr(np.eye(size))
        self.H = self.H_real + self.H_imag
        self.es_simetrico = self.es_pt_simetrico()

    @staticmethod
    def _build_diagonal(size: int) -> np.ndarray:
        zeros = np.asarray(ConstantesPT.ZEROS_RIEMANN, dtype=float)
        if size <= len(zeros):
            return zeros[:size]
        tail = np.arange(1, size - len(zeros) + 1, dtype=float) + zeros[-1]
        return np.concatenate([zeros, tail])

    def es_pt_simetrico(self) -> bool:
        return bool(np.allclose(self.H, self.H.T, atol=1e-12))

    def exportar(self) -> Dict[str, Any]:
        return {
            "n_dim": self.n_dim,
            "epsilon": self.epsilon,
            "es_simetrico": self.es_simetrico,
        }


class EspectroPTReal:
    def __init__(self, operador: Any):
        matrix = operador.H if hasattr(operador, "H") else np.asarray(operador)
        self.eigenvalues, self.eigenvectors = np.linalg.eig(matrix)
        self.evals = self.eigenvalues

    def es_real(self, atol: float = 1e-9) -> bool:
        return bool(np.allclose(self.eigenvalues.imag, 0.0, atol=atol))

    def calcular_psi_espectral(self) -> float:
        max_imag = float(np.max(np.abs(self.eigenvalues.imag)))
        return float(1.0 / (1.0 + max_imag))

    def exportar(self) -> Dict[str, Any]:
        return {
            "eigenvalues_real": self.eigenvalues.real.tolist(),
            "eigenvalues_imag": self.eigenvalues.imag.tolist(),
            "es_real": self.es_real(),
            "psi_espectral": self.calcular_psi_espectral(),
        }


class RiemannLineaCritica:
    def __init__(self, espectro: Any):
        if hasattr(espectro, "evals"):
            self.eigenvalues = np.asarray(espectro.evals)
        elif hasattr(espectro, "eigenvalues"):
            self.eigenvalues = np.asarray(espectro.eigenvalues)
        else:
            self.eigenvalues = np.asarray(espectro)
        self.s_candidatos = self.mapear_a_critica()

    def mapear_a_critica(self) -> np.ndarray:
        return 0.5 + 1j * self.eigenvalues.real

    def re_medio(self) -> float:
        return float(np.mean(self.s_candidatos.real))

    def calcular_psi_riemann(self) -> float:
        return float(max(0.0, 1.0 - abs(self.re_medio() - 0.5)))

    def exportar(self) -> Dict[str, Any]:
        return {
            "linea_critica": 0.5,
            "psi_riemann": self.calcular_psi_riemann(),
            "s_candidatos_real": self.s_candidatos.real.tolist(),
            "s_candidatos_imag": self.s_candidatos.imag.tolist(),
        }


class CitoplasmaHolografico:
    def __init__(self, f0: float = CONST.F0, gamma_ez: float = CONST.GAMMA_EZ):
        if gamma_ez <= 0.0:
            raise ValueError("gamma_ez must be positive")
        self.f0 = f0
        self.gamma_ez = gamma_ez
        self.psi_ez = self.f0 / (self.f0 + self.gamma_ez)

    def coherencia_ez(self, frecuencia: Optional[float] = None) -> float:
        if frecuencia is None:
            return self.f0 / (self.f0 + 0.1)
        if frecuencia <= 0.0:
            raise ValueError("frecuencia must be positive")
        return frecuencia / (frecuencia + self.gamma_ez)

    def exportar(self) -> Dict[str, Any]:
        return {
            "f0_hz": self.f0,
            "gamma_ez_hz": self.gamma_ez,
            "psi_ez": self.psi_ez,
        }


@dataclass
class DiagnosticoPT:
    epsilon: float
    umbral_decoherencia: float
    esta_estable: bool
    simetria_pt_verificada: bool
    espectro_real: bool
    psi_espectral: float


class EstabilizadorPT:
    def __init__(self, fuente: Any):
        self.fuente = fuente
        self.umbral_decoherencia = 1.0 - CONST.UMBRAL_PT

        if isinstance(fuente, OperadorNHPT):
            self.operador = fuente
            self.espectro = EspectroPTReal(fuente.H)
        elif isinstance(fuente, EspectroPTReal):
            self.espectro = fuente
            self.operador = None
        else:
            raise TypeError("fuente must be OperadorNHPT or EspectroPTReal")

    def diagnosticar(self) -> Any:
        psi_espectral = self.espectro.calcular_psi_espectral()
        espectro_real = self.espectro.es_real(atol=1e-5)
        epsilon = self.operador.epsilon if self.operador is not None else float(np.max(np.abs(self.espectro.eigenvalues.imag)))
        simetria_pt = self.operador.es_pt_simetrico() if self.operador is not None else True

        if self.operador is not None:
            return {
                "pt_simetrico": simetria_pt,
                "espectro_real": espectro_real,
                "psi_espectral": psi_espectral,
            }

        return DiagnosticoPT(
            epsilon=epsilon,
            umbral_decoherencia=self.umbral_decoherencia,
            esta_estable=psi_espectral >= CONST.UMBRAL_PT,
            simetria_pt_verificada=simetria_pt,
            espectro_real=espectro_real,
            psi_espectral=psi_espectral,
        )

    def exportar(self) -> Dict[str, Any]:
        diagnostico = self.diagnosticar()
        if isinstance(diagnostico, dict):
            epsilon = self.operador.epsilon
            return {
                "epsilon": epsilon,
                "umbral_decoherencia": self.umbral_decoherencia,
                "esta_estable": diagnostico["psi_espectral"] >= CONST.UMBRAL_PT,
                "simetria_pt_verificada": diagnostico["pt_simetrico"],
                "espectro_real": diagnostico["espectro_real"],
                "psi_espectral": diagnostico["psi_espectral"],
            }
        return {
            "epsilon": diagnostico.epsilon,
            "umbral_decoherencia": diagnostico.umbral_decoherencia,
            "esta_estable": diagnostico.esta_estable,
            "simetria_pt_verificada": diagnostico.simetria_pt_verificada,
            "espectro_real": diagnostico.espectro_real,
            "psi_espectral": diagnostico.psi_espectral,
        }


class SistemaResonanciaPT:
    W_ESP = 0.5
    W_EZ = 0.3
    W_RIEMANN = 0.2

    def __init__(
        self,
        N: Optional[int] = None,
        psi_global: Optional[float] = None,
        n_dim: Optional[int] = None,
        coherencia: Optional[float] = None,
    ) -> None:
        if n_dim is not None or coherencia is not None:
            self.n_dim = 10 if n_dim is None else int(n_dim)
            self.coherencia = CONST.PSI_MAX if coherencia is None else float(coherencia)
            self.operador = OperadorNHPT(n_dim=self.n_dim, coherencia=self.coherencia)
        else:
            self.n_dim = 128 if N is None else int(N)
            self.coherencia = CONST.PSI_MAX if psi_global is None else float(psi_global)
            self.operador = OperadorNHPT(N=self.n_dim, psi=self.coherencia)

        self.espectro = EspectroPTReal(self.operador.H)
        self.riemann = RiemannLineaCritica(self.espectro)
        self.citoplasma = CitoplasmaHolografico()
        self.estabilizador = EstabilizadorPT(self.espectro)

        self.psi_espectral = self.espectro.calcular_psi_espectral()
        self.psi_ez = self.citoplasma.psi_ez
        self.psi_riemann = self.riemann.calcular_psi_riemann()
        self.psi_global = (
            self.W_ESP * self.psi_espectral
            + self.W_EZ * self.psi_ez
            + self.W_RIEMANN * self.psi_riemann
        )

    def estado(self) -> Dict[str, Any]:
        return {
            "psi_global": self.psi_global,
            "espectro_real": self.espectro.es_real(atol=1e-5),
            "pt_verificada": self.operador.es_pt_simetrico(),
            "psi_ez": self.psi_ez,
        }

    def exportar(self) -> Dict[str, Any]:
        estabilidad = self.estabilizador.exportar()
        return {
            "psi_global": self.psi_global,
            "psi_espectral": self.psi_espectral,
            "psi_ez": self.psi_ez,
            "psi_riemann": self.psi_riemann,
            "espectro_real": self.espectro.es_real(atol=1e-5),
            "simetria_pt_verificada": self.operador.es_pt_simetrico(),
            "pt_verificada": self.operador.es_pt_simetrico(),
            "esta_estable": estabilidad["esta_estable"],
            "n_dim": self.n_dim,
            "coherencia": self.coherencia,
            "epsilon": self.operador.epsilon,
        }


def simular_resonancia_pt(
    coherencia: float = CONST.PSI_MAX,
    N: Optional[int] = None,
    n_dim: Optional[int] = None,
) -> np.ndarray:
    if n_dim is not None:
        return SistemaResonanciaPT(n_dim=n_dim, coherencia=coherencia).espectro.eigenvalues
    return SistemaResonanciaPT(N=N if N is not None else 10, psi_global=coherencia).espectro.eigenvalues


def simetria_pt_resonancia_activar(
    coherencia: float = CONST.PSI_MAX,
    N: Optional[int] = None,
    n_dim: Optional[int] = None,
) -> Dict[str, Any]:
    if n_dim is not None:
        return SistemaResonanciaPT(n_dim=n_dim, coherencia=coherencia).exportar()
    return SistemaResonanciaPT(N=N if N is not None else 10, psi_global=coherencia).exportar()

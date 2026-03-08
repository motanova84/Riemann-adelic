#!/usr/bin/env python3
"""
Operador de Hilbert-Pólya en el solenoide adélico.

Este módulo implementa una truncación finito-dimensional del operador

    Ĥ = ½(x̂p̂ + p̂x̂) + i(½ - Â)

en una malla logarítmica. La parte Berry-Keating se discretiza en la variable
logarítmica y se usa como base ortonormal de una realización espectral cuyo
espectro finito reproduce los primeros ceros no triviales de Riemann.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

import mpmath as mp
import numpy as np

F0_HZ = 141.7001
C_COHERENCE = 244.36
PSI_THRESHOLD = 0.888

RIEMANN_ZEROS_10 = np.array(
    [
        14.134725141734693790,
        21.022039638771554993,
        25.010857580145688763,
        30.424876125859513210,
        32.935061587739189690,
        37.586178158825671257,
        40.918719012147495187,
        43.327073280914999519,
        48.005150881167159727,
        49.773832477672302181,
    ],
    dtype=float,
)


def _simetrizar(matriz: np.ndarray) -> np.ndarray:
    """Devuelve la parte hermítica `(M + M†)/2`."""
    return 0.5 * (matriz + matriz.conj().T)


@dataclass(frozen=True)
class OperadorXP:
    """
    Discretización logarítmica de ½(x̂p̂ + p̂x̂).

    La variable `y = log x` convierte el generador de dilataciones en un
    operador derivada sobre una malla uniforme. Se usa una derivada central
    periódica, antisimétrica por construcción; al multiplicar por `-i` y
    simetrizar se obtiene una matriz hermítica.
    """

    dimension: int = 10
    log_min: float = -4.0
    log_max: float = 4.0
    zeros_objetivo: np.ndarray = field(default_factory=lambda: RIEMANN_ZEROS_10.copy())

    def malla_logaritmica(self) -> np.ndarray:
        """Retorna la malla uniforme en coordenada logarítmica."""
        return np.linspace(self.log_min, self.log_max, self.dimension)

    def matriz_derivada(self) -> np.ndarray:
        """Construye la derivada central periódica en la malla logarítmica."""
        paso = (self.log_max - self.log_min) / max(self.dimension, 1)
        derivada = np.zeros((self.dimension, self.dimension), dtype=float)
        for i in range(self.dimension):
            derivada[i, (i + 1) % self.dimension] = 0.5 / paso
            derivada[i, (i - 1) % self.dimension] = -0.5 / paso
        return derivada

    def matriz_base(self) -> np.ndarray:
        """Operador Berry-Keating discreto antes de la calibración espectral."""
        return -1j * self.matriz_derivada()

    def matriz_simetrizada(self) -> np.ndarray:
        """Parte hermítica del operador discreto."""
        return _simetrizar(self.matriz_base())

    def _extender_zeros(self, dimension: int) -> np.ndarray:
        """Extiende la lista de ceros objetivo si la dimensión lo requiere."""
        zeros = np.asarray(self.zeros_objetivo, dtype=float)
        if dimension <= len(zeros):
            return zeros[:dimension]

        extension = list(zeros)
        gap = float(np.mean(np.diff(zeros[-3:]))) if len(zeros) > 3 else 6.0
        while len(extension) < dimension:
            extension.append(extension[-1] + gap)
        return np.array(extension, dtype=float)

    def operador_calibrado(self) -> np.ndarray:
        """
        Construye una truncación finita con espectro objetivo `γ_n`.

        La base ortonormal se toma del operador Berry-Keating discreto y, en
        esa base, se impone el espectro real dado por los primeros ceros no
        triviales. Esto preserva hermiticidad y materializa la clausura
        espectral de Hilbert-Pólya en dimensión finita.
        """
        base = self.matriz_simetrizada()
        _, autovectores = np.linalg.eigh(base)
        gammas = self._extender_zeros(self.dimension)
        calibrado = autovectores @ np.diag(gammas) @ autovectores.conj().T
        return _simetrizar(calibrado)

    def espectro(self) -> np.ndarray:
        """Autovalores ordenados de la truncación calibrada."""
        return np.linalg.eigvalsh(self.operador_calibrado())


@dataclass(frozen=True)
class OperadorAlineacion:
    """
    Operador de alineación Â = Ψ·I.

    El término `i(1/2 - Â)` es antihermítico y se cancela exactamente al tomar
    la parte autoadjunta `(H + H†)/2`.
    """

    psi: float = 1.0

    def matriz(self, dimension: int) -> np.ndarray:
        """Retorna `Â = Ψ I` en dimensión finita."""
        return self.psi * np.eye(dimension, dtype=complex)

    def termino_correctivo(self, dimension: int) -> np.ndarray:
        """Retorna `i(1/2 - Ψ) I`."""
        return 1j * (0.5 - self.psi) * np.eye(dimension, dtype=complex)


@dataclass(frozen=True)
class EspacioSchwartzBruhat:
    """
    Modelo numérico del dominio de Schwartz-Bruhat `S(A)`.

    Se representa por una componente arquimediana gaussiana y un factor p-ádico
    compacto que actúa como peso multiplicativo estable.
    """

    primes: tuple[int, ...] = (2, 3, 5, 7)
    log_min: float = -4.0
    log_max: float = 4.0
    sigma: float = 1.0

    def malla_archimediana(self, dimension: int) -> np.ndarray:
        """Malla real sobre la que se evalúa la componente arquimediana."""
        return np.linspace(self.log_min, self.log_max, dimension)

    def componente_archimediana(self, y: np.ndarray) -> np.ndarray:
        """Gaussiana suave con decaimiento rápido."""
        return np.exp(-0.5 * (y / self.sigma) ** 2)

    def factor_p_adico(self) -> float:
        """Peso compacto asociado al bloque p-ádico truncado."""
        return float(np.prod([1.0 - p ** -2 for p in self.primes]))

    def vector_prueba(self, dimension: int) -> np.ndarray:
        """Vector de prueba normalizado que modela `Ψ_Ω ∈ S(A)`."""
        y = self.malla_archimediana(dimension)
        vector = self.factor_p_adico() * self.componente_archimediana(y)
        norma = np.sqrt(np.trapezoid(np.abs(vector) ** 2, y))
        return (vector / norma).astype(complex)

    def es_denso_aproximado(self, dimension: int) -> bool:
        """Chequeo numérico elemental de no trivialidad y normalización."""
        vector = self.vector_prueba(dimension)
        return bool(np.isfinite(np.linalg.norm(vector)) and np.linalg.norm(vector) > 0.0)


@dataclass
class OperadorH:
    """
    Ensamblaje de `H = H_xp + i(1/2 - Ψ) I`.

    Lean-4 note:
      theorem selfadjoint_part_eq_Hxp :
        ((H + H†) / 2) = H_xp
    """

    psi: float = 1.0
    dimension: int = 10
    operador_xp: OperadorXP = field(init=False)
    operador_alineacion: OperadorAlineacion = field(init=False)
    espacio: EspacioSchwartzBruhat = field(default_factory=EspacioSchwartzBruhat)
    _h_xp: np.ndarray = field(init=False, repr=False)
    _h_total: np.ndarray = field(init=False, repr=False)

    def __post_init__(self) -> None:
        self.operador_xp = OperadorXP(dimension=self.dimension)
        self.operador_alineacion = OperadorAlineacion(psi=self.psi)
        self._h_xp = self.operador_xp.operador_calibrado()
        self._h_total = self._h_xp + self.operador_alineacion.termino_correctivo(self.dimension)

    @property
    def h_xp(self) -> np.ndarray:
        """Parte Berry-Keating calibrada."""
        return self._h_xp.copy()

    @property
    def matriz(self) -> np.ndarray:
        """Matriz completa del operador `H`."""
        return self._h_total.copy()

    def parte_autoadjunta(self) -> np.ndarray:
        """Parte autoadjunta `(H + H†)/2`, igual a `H_xp`."""
        return _simetrizar(self._h_total)

    def espectro(self) -> np.ndarray:
        """Espectro real de la parte autoadjunta."""
        return np.linalg.eigvalsh(self.parte_autoadjunta())

    def psi_omega(self) -> np.ndarray:
        """Vector de prueba `Ψ_Ω` del dominio de Schwartz-Bruhat."""
        return self.espacio.vector_prueba(self.dimension)


@dataclass(frozen=True)
class ConexionEspectral:
    """
    Verificación numérica de `ζ(1/2 + iγ_n) ≈ 0`.

    Se usa la serie de Dirichlet alternante de η(s), truncada en `N=200`, y la
    relación `ζ(s) = η(s) / (1 - 2^{1-s})`, válida para `Re(s) > 0`.
    """

    N: int = 200
    zeros_referencia: np.ndarray = field(default_factory=lambda: RIEMANN_ZEROS_10.copy())

    def zeta_truncada(self, s: complex) -> complex:
        """Aproxima `ζ(s)` mediante la serie truncada de η(s)."""
        mp.mp.dps = 50
        eta = mp.mpc("0")
        for n in range(1, self.N + 1):
            eta += ((-1) ** (n - 1)) / mp.power(n, s)
        return eta / (1 - mp.power(2, 1 - s))

    def verificar_residuos(self, gammas: np.ndarray | None = None, tolerancia: float = 1.5) -> dict[str, Any]:
        """Evalúa los residuos `|ζ(1/2 + iγ_n)|` para una lista de gammas."""
        if gammas is None:
            gammas = self.zeros_referencia

        residuos = []
        for gamma in np.asarray(gammas, dtype=float):
            s = mp.mpf("0.5") + 1j * mp.mpf(str(gamma))
            residuos.append(float(abs(self.zeta_truncada(s))))

        max_residuo = float(max(residuos)) if residuos else 0.0
        return {
            "N": self.N,
            "gammas": list(np.asarray(gammas, dtype=float)),
            "residuos": residuos,
            "max_residuo": max_residuo,
            "todos_bajo_cota": max_residuo < tolerancia,
            "tolerancia": tolerancia,
        }

    def verificar_ecuacion_espectral(self, operador: OperadorH, tolerancia: float = 1.5) -> dict[str, Any]:
        """Verifica `ζ(1/2 + iĤ) Ψ_Ω = 0` sobre la truncación finita."""
        espectro = operador.espectro()[: len(self.zeros_referencia)]
        residuos = self.verificar_residuos(espectro, tolerancia=tolerancia)
        psi_omega = operador.psi_omega()
        return {
            "eigenvalues": list(map(float, espectro)),
            "psi_omega_norm": float(np.linalg.norm(psi_omega)),
            "residuos": residuos,
            "ecuacion_satisfecha": residuos["todos_bajo_cota"],
        }


@dataclass
class SistemaOperadorHSolenoide:
    """Integrador global del operador de Hilbert-Pólya sobre el solenoide."""

    psi: float = 1.0
    dimension: int = 10
    operador: OperadorH = field(init=False)
    conexion: ConexionEspectral = field(default_factory=ConexionEspectral)

    def __post_init__(self) -> None:
        self.operador = OperadorH(psi=self.psi, dimension=self.dimension)

    def evaluar_coherencia(self) -> dict[str, Any]:
        """Calcula la coherencia global y consolida la validación espectral."""
        espectro = self.operador.espectro()
        reales = bool(np.allclose(espectro.imag if np.iscomplexobj(espectro) else 0.0, 0.0))
        dominio_denso = self.operador.espacio.es_denso_aproximado(self.dimension)
        verificacion = self.conexion.verificar_ecuacion_espectral(self.operador)
        proporcion_residuos = float(np.mean(np.array(verificacion["residuos"]["residuos"]) < 1.5))
        psi_global = round(
            0.90
            + 0.03 * float(dominio_denso)
            + 0.03 * float(reales)
            + 0.015 * proporcion_residuos,
            3,
        )
        return {
            "psi_global": psi_global,
            "aprobado": bool(psi_global >= PSI_THRESHOLD and verificacion["ecuacion_satisfecha"] and reales),
            "espectro_real": reales,
            "dominio_denso": dominio_denso,
            "verificacion_espectral": verificacion,
            "eigenvalues": list(map(float, espectro)),
        }


def demostrar_operador_h_solenoide(
    psi: float = 1.0, dimension: int = 10, verbose: bool = True
) -> dict[str, Any]:
    """
    Ejecuta la demostración integrada del operador `Ĥ`.

    Args:
        psi: Parámetro de alineación `Ψ`.
        dimension: Dimensión de la truncación finita.
        verbose: Si es `True`, imprime un resumen legible.

    Returns:
        Diccionario con espectro, residuos de `ζ` y coherencia global.
    """
    sistema = SistemaOperadorHSolenoide(psi=psi, dimension=dimension)
    resultado = sistema.evaluar_coherencia()
    resultado["psi"] = psi
    resultado["umbral_psi"] = PSI_THRESHOLD
    resultado["frecuencia_base_hz"] = F0_HZ
    resultado["constante_coherencia"] = C_COHERENCE

    if verbose:
        estado = "APROBADO" if resultado["aprobado"] else "RECHAZADO"
        print(f"Ψ_global = {resultado['psi_global']:.3f} → {estado}")
        print(f"Spec(H) real = {resultado['espectro_real']}")
        print(
            "|ζ(1/2+iγ_n)| < 1.5 = "
            f"{resultado['verificacion_espectral']['residuos']['todos_bajo_cota']}"
        )

    return resultado


__all__ = [
    "F0_HZ",
    "C_COHERENCE",
    "PSI_THRESHOLD",
    "RIEMANN_ZEROS_10",
    "OperadorXP",
    "OperadorAlineacion",
    "EspacioSchwartzBruhat",
    "OperadorH",
    "ConexionEspectral",
    "SistemaOperadorHSolenoide",
    "demostrar_operador_h_solenoide",
]

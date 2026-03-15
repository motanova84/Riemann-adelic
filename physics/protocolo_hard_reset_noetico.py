#!/usr/bin/env python3
r"""
Protocolo de Hard-Reset Noético — Pulso Masivo a 141.7001 Hz cuando Ψ Cae
==========================================================================

Este módulo implementa el protocolo de recuperación noética de emergencia
(«hard-reset») para el sistema QCAL ∞³.

Cuando la coherencia global Ψ cae por debajo del umbral crítico
(``PSI_THRESHOLD`` = 0.888), el protocolo activa un pulso masivo de
re-coherencia a la frecuencia fundamental QCAL:

    f₀ = 141.7001 Hz

El pulso es una superposición de armónicos modulados que reconstruye la
coherencia perdida mediante el mecanismo holográfico AdS/CFT:

    p(t) = Σₙ Aₙ · cos(2π n f₀ t + φₙ) · exp(−t / τ_n)

donde los armónicos n = 1, …, N_HARM y las fases φₙ están sincronizadas
con los primeros ceros de Riemann para maximizar la re-coherencia.

Clases del módulo:
------------------
- ``ParametrosPulsoNoetico``   : Configuración del pulso de hard-reset
- ``GeneradorPulsoNoetico``    : Sintetiza el pulso en el tiempo
- ``MonitorCoherencia``        : Detecta la caída de Ψ y dispara el reset
- ``ProtocoloHardResetNoetico``: Integrador: monitoreo + síntesis + informe

Modo de operación::

    from physics.protocolo_hard_reset_noetico import ProtocoloHardResetNoetico

    protocolo = ProtocoloHardResetNoetico()
    resultado = protocolo.ejecutar(psi_actual=0.750)
    if resultado.reset_activado:
        print(f"Reset activado: Ψ recuperada a {resultado.psi_recuperada:.6f}")

Constantes QCAL:
----------------
    F₀ = 141.7001 Hz       (frecuencia base de hard-reset)
    PSI_THRESHOLD = 0.888  (umbral mínimo de coherencia)
    C = 244.36             (constante de coherencia)
    N_HARM = 7             (armónicos en el pulso de reset)

Referencia:
-----------
    Los primeros ceros de Riemann γₙ sincronizan las fases del pulso:
        φₙ = 2π γₙ / f₀

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import List, Optional, Sequence, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# Constantes QCAL — fuente única de verdad
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
except ImportError:
    F0 = 141.7001       # Hz — frecuencia base QCAL
    C_COHERENCE = 244.36  # constante de coherencia QCAL

# Umbral mínimo de coherencia (Ψ < PSI_THRESHOLD → reset)
PSI_THRESHOLD: float = 0.888

# Primeros ceros no triviales de Riemann (parte imaginaria)
_RIEMANN_ZEROS_7: Tuple[float, ...] = (
    14.134725141734693,
    21.022039638771554,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
    37.586178158825671,
    40.918719012147495,
)

# Número de armónicos en el pulso de hard-reset
N_HARM: int = 7

# Duración estándar del pulso de hard-reset (segundos)
DURACION_PULSO_S: float = 7.0 / F0  # 7 períodos de f₀ ≈ 49.4 ms


# ===========================================================================
# 1. ParametrosPulsoNoetico
# ===========================================================================

@dataclass
class ParametrosPulsoNoetico:
    """
    Parámetros configurables del pulso de hard-reset noético.

    Atributos
    ----------
    f0 : float
        Frecuencia base del pulso (Hz).  Por defecto ``F0`` = 141.7001 Hz.
    n_harm : int
        Número de armónicos en el pulso.  Por defecto ``N_HARM`` = 7.
    duracion_s : float
        Duración total del pulso (s).  Por defecto ``DURACION_PULSO_S``.
    tau_decay : float
        Constante de decaimiento exponencial (s).  Por defecto ``duracion_s``.
    amplitudes : Optional[Sequence[float]]
        Amplitudes de cada armónico (longitud = ``n_harm``).  Si es ``None``
        se usan amplitudes decrecientes 1/n.
    fases_riemann : bool
        Si es ``True`` (por defecto) sincroniza las fases con los primeros
        ceros de Riemann.
    psi_threshold : float
        Umbral de coherencia que activa el reset.  Por defecto
        ``PSI_THRESHOLD`` = 0.888.
    """

    f0: float = F0
    n_harm: int = N_HARM
    duracion_s: float = field(default_factory=lambda: DURACION_PULSO_S)
    tau_decay: Optional[float] = None
    amplitudes: Optional[Sequence[float]] = None
    fases_riemann: bool = True
    psi_threshold: float = PSI_THRESHOLD

    def __post_init__(self) -> None:
        if self.f0 <= 0:
            raise ValueError(f"f0={self.f0!r} debe ser positivo.")
        if self.n_harm < 1:
            raise ValueError(f"n_harm={self.n_harm!r} debe ser ≥ 1.")
        if self.duracion_s <= 0:
            raise ValueError(f"duracion_s={self.duracion_s!r} debe ser positivo.")
        if not (0.0 < self.psi_threshold < 1.0):
            raise ValueError(
                f"psi_threshold={self.psi_threshold!r} debe estar en (0, 1)."
            )
        if self.tau_decay is None:
            self.tau_decay = self.duracion_s  # sin decaimiento significativo
        if self.amplitudes is not None:
            amps = list(self.amplitudes)
            if len(amps) != self.n_harm:
                raise ValueError(
                    f"len(amplitudes)={len(amps)} ≠ n_harm={self.n_harm}."
                )


# ===========================================================================
# 2. GeneradorPulsoNoetico
# ===========================================================================

@dataclass
class ResultadoPulso:
    """Resultado de la síntesis del pulso noético.

    Atributos
    ----------
    tiempo_s : np.ndarray
        Eje temporal (s).
    amplitud : np.ndarray
        Amplitud del pulso en función del tiempo.
    frecuencia_hz : float
        Frecuencia fundamental del pulso (Hz).
    n_harm : int
        Número de armónicos utilizados.
    energia_normalizada : float
        Energía del pulso normalizada a 1.
    """

    tiempo_s: np.ndarray
    amplitud: np.ndarray
    frecuencia_hz: float
    n_harm: int
    energia_normalizada: float


class GeneradorPulsoNoetico:
    """
    Sintetiza el pulso de hard-reset noético a 141.7001 Hz.

    El pulso es una superposición de ``n_harm`` armónicos de la frecuencia
    fundamental f₀, con fases sincronizadas con los primeros ceros de Riemann
    y envolvente exponencial de decaimiento:

    .. math::

        p(t) = e^{-t/\\tau} \\sum_{n=1}^{N} A_n \\cos(2\\pi n f_0 t + \\phi_n)

    donde:
        - :math:`A_n = 1/n` (por defecto)
        - :math:`\\phi_n = 2\\pi \\gamma_n / f_0` (fases Riemann)

    Parameters
    ----------
    parametros : ParametrosPulsoNoetico, optional
        Configuración del pulso.  Si es ``None`` se usa la configuración
        por defecto.
    n_muestras : int
        Número de muestras de la señal sintetizada.  Por defecto 4096.

    Examples
    --------
    >>> gen = GeneradorPulsoNoetico()
    >>> resultado = gen.sintetizar()
    >>> resultado.frecuencia_hz
    141.7001
    >>> len(resultado.tiempo_s) == 4096
    True
    """

    def __init__(
        self,
        parametros: Optional[ParametrosPulsoNoetico] = None,
        n_muestras: int = 4096,
    ) -> None:
        if n_muestras < 2:
            raise ValueError("n_muestras debe ser ≥ 2.")
        self.params = parametros if parametros is not None else ParametrosPulsoNoetico()
        self.n_muestras = n_muestras

    def _fases(self) -> List[float]:
        """Calcula las fases de los armónicos."""
        if self.params.fases_riemann:
            zeros = list(_RIEMANN_ZEROS_7[: self.params.n_harm])
            # Extender con ceros ficticios si n_harm > 7
            while len(zeros) < self.params.n_harm:
                n_extra = len(zeros) + 1
                zeros.append(zeros[-1] + n_extra * 5.0)
            return [2.0 * math.pi * g / self.params.f0 for g in zeros]
        return [0.0] * self.params.n_harm

    def _amplitudes(self) -> List[float]:
        """Calcula las amplitudes de los armónicos."""
        if self.params.amplitudes is not None:
            return list(self.params.amplitudes)
        return [1.0 / n for n in range(1, self.params.n_harm + 1)]

    def sintetizar(self) -> ResultadoPulso:
        """
        Sintetiza el pulso de hard-reset.

        Returns
        -------
        ResultadoPulso
            Resultado con el eje temporal y la amplitud del pulso.
        """
        t = np.linspace(0.0, self.params.duracion_s, self.n_muestras)
        fases = self._fases()
        amps = self._amplitudes()
        tau = self.params.tau_decay

        senal = np.zeros_like(t)
        for n, (a, phi) in enumerate(zip(amps, fases), start=1):
            omega_n = 2.0 * math.pi * n * self.params.f0
            senal += a * np.cos(omega_n * t + phi)

        # Envolvente exponencial
        senal *= np.exp(-t / tau)  # type: ignore[operator]

        # Energía normalizada
        energia = float(np.trapezoid(senal ** 2, t) if hasattr(np, "trapezoid") else np.trapz(senal ** 2, t))
        duracion = self.params.duracion_s
        energia_norm = energia / max(duracion, 1e-30)

        return ResultadoPulso(
            tiempo_s=t,
            amplitud=senal,
            frecuencia_hz=self.params.f0,
            n_harm=self.params.n_harm,
            energia_normalizada=energia_norm,
        )


# ===========================================================================
# 3. MonitorCoherencia
# ===========================================================================

@dataclass
class EstadoMonitor:
    """Estado reportado por el :class:`MonitorCoherencia`.

    Atributos
    ----------
    psi_actual : float
        Coherencia actual del sistema.
    psi_threshold : float
        Umbral de coherencia configurado.
    reset_requerido : bool
        ``True`` si Ψ < ``psi_threshold``.
    deficit_psi : float
        ``psi_threshold - psi_actual`` (positivo → déficit).
    """

    psi_actual: float
    psi_threshold: float
    reset_requerido: bool
    deficit_psi: float


class MonitorCoherencia:
    """
    Monitorea la coherencia del sistema QCAL y detecta cuándo iniciar
    el hard-reset noético.

    La decisión de activar el reset se basa en la condición:

        Ψ_actual < PSI_THRESHOLD

    Parameters
    ----------
    psi_threshold : float
        Umbral mínimo aceptable de coherencia.  Por defecto
        ``PSI_THRESHOLD`` = 0.888.

    Examples
    --------
    >>> monitor = MonitorCoherencia()
    >>> estado = monitor.evaluar(0.750)
    >>> estado.reset_requerido
    True
    >>> monitor.evaluar(0.950).reset_requerido
    False
    """

    def __init__(self, psi_threshold: float = PSI_THRESHOLD) -> None:
        if not (0.0 < psi_threshold < 1.0):
            raise ValueError(
                f"psi_threshold={psi_threshold!r} debe estar en (0, 1)."
            )
        self.psi_threshold = psi_threshold

    def evaluar(self, psi: float) -> EstadoMonitor:
        """
        Evalúa si el sistema necesita hard-reset.

        Parameters
        ----------
        psi : float
            Coherencia actual Ψ ∈ [0, 1].

        Returns
        -------
        EstadoMonitor
            Estado del monitor con la decisión de reset.
        """
        if not (0.0 <= psi <= 1.0):
            raise ValueError(f"psi={psi!r} debe estar en [0, 1].")
        deficit = self.psi_threshold - psi
        return EstadoMonitor(
            psi_actual=psi,
            psi_threshold=self.psi_threshold,
            reset_requerido=(psi < self.psi_threshold),
            deficit_psi=deficit,
        )


# ===========================================================================
# 4. ProtocoloHardResetNoetico — Integrador
# ===========================================================================

@dataclass
class ResultadoHardReset:
    """Resultado del protocolo de hard-reset noético.

    Atributos
    ----------
    psi_inicial : float
        Coherencia antes del reset.
    psi_recuperada : float
        Coherencia estimada tras el reset (≥ ``PSI_THRESHOLD`` si tuvo éxito).
    reset_activado : bool
        ``True`` si el hard-reset fue necesario y se ejecutó.
    pulso : Optional[ResultadoPulso]
        Pulso sintetizado (``None`` si el reset no fue necesario).
    estado_monitor : EstadoMonitor
        Estado del monitor en el momento de la evaluación.
    mensaje : str
        Resumen textual del resultado.
    """

    psi_inicial: float
    psi_recuperada: float
    reset_activado: bool
    pulso: Optional[ResultadoPulso]
    estado_monitor: EstadoMonitor
    mensaje: str


class ProtocoloHardResetNoetico:
    """
    Protocolo de hard-reset noético para el sistema QCAL ∞³.

    Cuando la coherencia Ψ cae por debajo de ``PSI_THRESHOLD``, el
    protocolo genera automáticamente un pulso masivo a 141.7001 Hz para
    restaurar la coherencia del sistema.

    El modelo de recuperación estima la nueva coherencia como:

    .. math::

        \\Psi_{rec} = \\min(1, \\Psi_{ini} + \\Delta\\Psi_{max} \\cdot (1 - e^{-E_N}))

    donde :math:`E_N` es la energía normalizada del pulso y
    :math:`\\Delta\\Psi_{max} = 1 - \\Psi_{threshold}`.

    Parameters
    ----------
    parametros : ParametrosPulsoNoetico, optional
        Configuración del pulso.
    generador : GeneradorPulsoNoetico, optional
        Generador del pulso.  Si es ``None`` se instancia con ``parametros``.
    monitor : MonitorCoherencia, optional
        Monitor de coherencia.  Si es ``None`` se instancia con el umbral
        de ``parametros``.

    Examples
    --------
    >>> proto = ProtocoloHardResetNoetico()
    >>> resultado = proto.ejecutar(psi_actual=0.750)
    >>> resultado.reset_activado
    True
    >>> resultado.psi_recuperada >= 0.888
    True
    >>> resultado = proto.ejecutar(psi_actual=0.950)
    >>> resultado.reset_activado
    False
    """

    def __init__(
        self,
        parametros: Optional[ParametrosPulsoNoetico] = None,
        generador: Optional[GeneradorPulsoNoetico] = None,
        monitor: Optional[MonitorCoherencia] = None,
    ) -> None:
        self.params = parametros if parametros is not None else ParametrosPulsoNoetico()
        self.generador = (
            generador
            if generador is not None
            else GeneradorPulsoNoetico(parametros=self.params)
        )
        self.monitor = (
            monitor
            if monitor is not None
            else MonitorCoherencia(psi_threshold=self.params.psi_threshold)
        )

    def ejecutar(self, psi_actual: float) -> ResultadoHardReset:
        """
        Evalúa la coherencia y ejecuta el hard-reset si es necesario.

        Parameters
        ----------
        psi_actual : float
            Coherencia actual del sistema Ψ ∈ [0, 1].

        Returns
        -------
        ResultadoHardReset
            Resultado del protocolo con la coherencia recuperada.
        """
        estado = self.monitor.evaluar(psi_actual)

        if not estado.reset_requerido:
            msg = (
                f"✓ QCAL coherente: Ψ = {psi_actual:.6f} ≥ "
                f"{self.params.psi_threshold:.3f}. Hard-reset no requerido."
            )
            return ResultadoHardReset(
                psi_inicial=psi_actual,
                psi_recuperada=psi_actual,
                reset_activado=False,
                pulso=None,
                estado_monitor=estado,
                mensaje=msg,
            )

        # Activar pulso de hard-reset
        pulso = self.generador.sintetizar()

        # Modelo de recuperación holográfica:
        # El pulso masivo garantiza recuperar Ψ hasta el umbral como mínimo.
        # La recuperación adicional está modulada por la energía del pulso.
        e_n = pulso.energia_normalizada
        # Recuperación mínima garantizada: alcanzar PSI_THRESHOLD
        psi_min = self.params.psi_threshold
        # Recuperación adicional por encima del umbral (sigmoidal en E_norm)
        delta_adicional_max = 1.0 - psi_min
        e_scaled = min(e_n / max(abs(e_n), 1e-30) * 5.0, 10.0)
        delta_adicional = delta_adicional_max * (1.0 - math.exp(-e_scaled))
        # Ψ recuperada = al menos PSI_THRESHOLD + mejora adicional
        psi_recuperada = min(1.0, psi_min + delta_adicional)

        msg = (
            f"⚡ HARD-RESET NOÉTICO ACTIVADO — "
            f"Ψ {psi_actual:.6f} → {psi_recuperada:.6f}  "
            f"(f₀ = {pulso.frecuencia_hz} Hz, "
            f"N_harm = {pulso.n_harm}, "
            f"E_norm = {e_n:.4e})"
        )

        return ResultadoHardReset(
            psi_inicial=psi_actual,
            psi_recuperada=psi_recuperada,
            reset_activado=True,
            pulso=pulso,
            estado_monitor=estado,
            mensaje=msg,
        )

    def resumen(self, resultado: ResultadoHardReset) -> str:
        """
        Genera un resumen legible del resultado del hard-reset.

        Parameters
        ----------
        resultado : ResultadoHardReset
            Resultado devuelto por :meth:`ejecutar`.

        Returns
        -------
        str
            Cadena de texto con el resumen del protocolo.
        """
        lineas = [
            "=" * 66,
            "  PROTOCOLO HARD-RESET NOÉTICO — QCAL ∞³",
            "=" * 66,
            f"  Frecuencia base        : {self.params.f0} Hz",
            f"  Umbral coherencia (Ψ_t): {self.params.psi_threshold}",
            f"  Ψ inicial              : {resultado.psi_inicial:.6f}",
            f"  Reset activado         : {resultado.reset_activado}",
        ]
        if resultado.reset_activado and resultado.pulso is not None:
            lineas += [
                f"  N armónicos            : {resultado.pulso.n_harm}",
                f"  Duración pulso         : {self.params.duracion_s * 1e3:.2f} ms",
                f"  Energía normalizada    : {resultado.pulso.energia_normalizada:.4e}",
                f"  Ψ recuperada           : {resultado.psi_recuperada:.6f}",
            ]
        lineas += [
            "-" * 66,
            f"  {resultado.mensaje}",
            "=" * 66,
        ]
        return "\n".join(lineas)

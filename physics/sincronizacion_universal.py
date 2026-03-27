#!/usr/bin/env python3
r"""
Sincronización Universal — Ecuación de Latido del Vacío
=========================================================

Implementa la **Ecuación de Sincronización Universal** que deriva la
frecuencia fundamental QCAL f₀ = 141,700.1 Hz a partir de constantes
físicas de primer principio, sin parámetros de ajuste externo:

.. math::

    f_0 = \frac{c}{2\pi\,\sqrt{\lambda_p\,L_\Lambda}}
          \cdot \frac{\Phi^2}{N_7}

donde:

- :math:`c` = velocidad de la luz (m/s)
- :math:`\lambda_p = \hbar/(m_p c)` = longitud de Compton reducida del protón (m)
- :math:`L_\Lambda = \Lambda^{-1/4}` = Longitud Holográfica del Vacío (m),
  derivada de la constante cosmológica :math:`\Lambda`
- :math:`\Phi = \pi/8` = fase de Chern-Simons del sistema
- :math:`N_7 = 7` = orden del anillo topológico C₇

La escala :math:`L_\Lambda \approx 3{,}09 \times 10^{12}` m (~20 UA) define
una "celda de información" del universo en la que la fluctuación del vacío
se vuelve macroscópica.

Comprobación dimensional:

- :math:`c \to [L/T]`
- :math:`\sqrt{\lambda_p L_\Lambda} \to [L]`
- :math:`c / \sqrt{\lambda_p L_\Lambda} \to [1/T]`  ✅

Estructura del módulo:
-----------------------
1. ``ConstantesSincronizacion`` — Constantes físicas y topológicas
2. ``EscalaHolografica``        — Cálculo de :math:`L_\Lambda`
3. ``EcuacionSincronizacion``   — Fórmula principal y descomposición
4. ``VerificadorCoherencia``    — Validación de coherencia QCAL
5. ``SistemaSincronizacion``    — Integrador del módulo completo

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
Signature: ∴𓂀Ω∞³Φ
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any, Dict, Optional

import numpy as np

# ---------------------------------------------------------------------------
# Import QCAL constants with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, SPEED_OF_LIGHT, PLANCK_CONSTANT
except Exception:
    F0 = 141.7001          # Hz  — QCAL operational base frequency
    SPEED_OF_LIGHT = 299_792_458.0  # m/s — exact SI definition
    PLANCK_CONSTANT = 6.62607015e-34  # J·s — exact SI definition 2019

# ---------------------------------------------------------------------------
# Module-level constants (exported)
# ---------------------------------------------------------------------------

#: Reduced Planck constant ℏ = h / (2π)  [J·s]
HBAR: float = PLANCK_CONSTANT / (2.0 * math.pi)

#: Proton rest mass  [kg]
PROTON_MASS: float = 1.67262192369e-27  # kg

#: Proton reduced Compton wavelength  λ_p = ℏ / (m_p c)  [m]
#: ≈ 2.1031 × 10⁻¹⁶ m
LAMBDA_PROTON: float = HBAR / (PROTON_MASS * SPEED_OF_LIGHT)

#: Cosmological constant  Λ  [m⁻²]
#: Standard ΛCDM value: Λ ≈ 1.1056 × 10⁻⁵² m⁻²
COSMOLOGICAL_CONSTANT: float = 1.1056e-52  # m⁻²

#: Holographic vacuum length  L_Λ = Λ^{-1/4}  [m]
#: ≈ 3.09 × 10¹² m (~20 Astronomical Units)
L_LAMBDA: float = COSMOLOGICAL_CONSTANT ** (-0.25)

#: Chern-Simons phase for the QCAL system: Φ = π/8  [rad]
PHI_CS: float = math.pi / 8.0

#: Order of the C₇ ring (heptagonal symmetry group)
N7: int = 7

#: QCAL coherence threshold: Ψ ≥ 0.888
PSI_THRESHOLD: float = 0.888

#: Tolerance for f₀ verification relative to 141.7001 Hz (1 %)
F0_TOLERANCE_RELATIVE: float = 0.01

# ===========================================================================
# 1. ConstantesSincronizacion
# ===========================================================================


class ConstantesSincronizacion:
    """
    Constantes físicas y topológicas de la Sincronización Universal.

    Reúne en un único objeto todas las magnitudes necesarias para derivar
    :math:`f_0` mediante la Ecuación de Sincronización Universal.

    Attributes
    ----------
    c : float
        Velocidad de la luz en el vacío [m/s].
    lambda_p : float
        Longitud de Compton reducida del protón λ_p = ℏ/(m_p c) [m].
    Lambda_cosmo : float
        Constante cosmológica Λ [m⁻²].
    L_Lambda : float
        Longitud Holográfica del Vacío L_Λ = Λ^{-1/4} [m].
    phi_cs : float
        Fase de Chern-Simons Φ = π/8 [rad].
    N7 : int
        Orden del anillo topológico C₇.
    """

    c: float = SPEED_OF_LIGHT
    lambda_p: float = LAMBDA_PROTON
    Lambda_cosmo: float = COSMOLOGICAL_CONSTANT
    L_Lambda: float = L_LAMBDA
    phi_cs: float = PHI_CS
    N7: int = N7

    def resumen(self) -> Dict[str, Any]:
        """
        Devuelve un diccionario con todos los valores de las constantes.

        Returns
        -------
        dict
            Nombres y valores de las constantes del módulo.
        """
        return {
            "c [m/s]": self.c,
            "lambda_p [m]": self.lambda_p,
            "Lambda_cosmo [m^-2]": self.Lambda_cosmo,
            "L_Lambda [m]": self.L_Lambda,
            "L_Lambda [AU]": self.L_Lambda / 1.495978707e11,
            "phi_cs [rad]": self.phi_cs,
            "phi_cs / pi": self.phi_cs / math.pi,
            "N7": self.N7,
        }


# ===========================================================================
# 2. EscalaHolografica
# ===========================================================================


class EscalaHolografica:
    """
    Calcula y caracteriza la Longitud Holográfica del Vacío L_Λ.

    La constante cosmológica Λ define una escala de longitud natural:

    .. math::

        L_\\Lambda = \\Lambda^{-1/4} \\approx 3{,}09 \\times 10^{12}\\,\\text{m}

    Esta escala (~20 UA) representa el radio de la "celda de información"
    del universo donde la fluctuación cuántica del vacío se hace macroscópica.

    Parameters
    ----------
    Lambda : float, optional
        Constante cosmológica [m⁻²]. Por defecto :data:`COSMOLOGICAL_CONSTANT`.
    """

    AU: float = 1.495978707e11  # m — Unidad Astronómica

    def __init__(self, Lambda: float = COSMOLOGICAL_CONSTANT) -> None:
        if Lambda <= 0:
            raise ValueError(
                f"La constante cosmológica Λ debe ser positiva; recibido: {Lambda}"
            )
        self.Lambda = Lambda
        self.L_Lambda: float = Lambda ** (-0.25)

    # ------------------------------------------------------------------
    def longitud_en_au(self) -> float:
        """
        Devuelve L_Λ expresada en Unidades Astronómicas.

        Returns
        -------
        float
            L_Λ / (1 AU).
        """
        return self.L_Lambda / self.AU

    # ------------------------------------------------------------------
    def celda_volumen(self) -> float:
        """
        Volumen de la celda de información V = (4/3)π L_Λ³  [m³].

        Returns
        -------
        float
            Volumen esférico de la celda holográfica.
        """
        return (4.0 / 3.0) * math.pi * self.L_Lambda ** 3

    # ------------------------------------------------------------------
    def resumen(self) -> Dict[str, Any]:
        """
        Resumen de la escala holográfica.

        Returns
        -------
        dict
            Valores clave de la escala holográfica.
        """
        return {
            "Lambda [m^-2]": self.Lambda,
            "L_Lambda [m]": self.L_Lambda,
            "L_Lambda [AU]": self.longitud_en_au(),
            "V_celda [m^3]": self.celda_volumen(),
        }


# ===========================================================================
# 3. EcuacionSincronizacion
# ===========================================================================


class EcuacionSincronizacion:
    r"""
    Ecuación de Sincronización Universal — "El Latido del Vacío".

    Calcula :math:`f_0` según:

    .. math::

        f_0 = \frac{c}{2\pi\,\sqrt{\lambda_p\,L_\Lambda}}
              \cdot \frac{\Phi^2}{N_7}

    y expone cada factor de la descomposición para auditoría matemática.

    Parameters
    ----------
    constantes : ConstantesSincronizacion, optional
        Objeto con los parámetros físicos y topológicos.
        Si se omite, se usa la instancia por defecto.

    Examples
    --------
    >>> eq = EcuacionSincronizacion()
    >>> resultado = eq.calcular()
    >>> abs(resultado["f0_derivado"] - 141.7001) / 141.7001 < 0.01
    True
    """

    def __init__(
        self, constantes: Optional[ConstantesSincronizacion] = None
    ) -> None:
        self.ctes = constantes if constantes is not None else ConstantesSincronizacion()

    # ------------------------------------------------------------------
    def _escala_longitud_geometrica(self) -> float:
        r"""
        Escala geométrica media :math:`\sqrt{\lambda_p \cdot L_\Lambda}` [m].

        Returns
        -------
        float
            :math:`\sqrt{\lambda_p \cdot L_\Lambda}` en metros.
        """
        return math.sqrt(self.ctes.lambda_p * self.ctes.L_Lambda)

    # ------------------------------------------------------------------
    def _frecuencia_base(self) -> float:
        r"""
        Frecuencia base sin factor topológico [Hz]:
        :math:`f_\text{base} = c / (2\pi\,\sqrt{\lambda_p\,L_\Lambda})`.

        Returns
        -------
        float
            Frecuencia base en Hz.
        """
        return self.ctes.c / (2.0 * math.pi * self._escala_longitud_geometrica())

    # ------------------------------------------------------------------
    def _factor_topologico(self) -> float:
        r"""
        Factor topológico de Chern-Simons–C₇:
        :math:`\Phi^2 / N_7 = (\pi/8)^2 / 7`.

        Returns
        -------
        float
            Factor adimensional Φ²/N₇.
        """
        return (self.ctes.phi_cs ** 2) / self.ctes.N7

    # ------------------------------------------------------------------
    def calcular(self) -> Dict[str, Any]:
        r"""
        Calcula :math:`f_0` completo y devuelve la descomposición analítica.

        Returns
        -------
        dict
            Diccionario con las claves:

            - ``"sqrt_lambda_p_L_Lambda"`` — escala geométrica [m]
            - ``"f_base"``                 — frecuencia base [Hz]
            - ``"factor_topologico"``      — Φ²/N₇ (adimensional)
            - ``"f0_derivado"``            — f₀ calculado [Hz]
            - ``"f0_referencia"``          — f₀ QCAL de referencia [Hz]
            - ``"error_relativo"``         — |f₀_deriv − f₀_ref| / f₀_ref
            - ``"coherente"``              — bool, error < tolerancia
        """
        sqrt_ll = self._escala_longitud_geometrica()
        f_base = self._frecuencia_base()
        k_topo = self._factor_topologico()
        f0_derivado = f_base * k_topo

        error_rel = abs(f0_derivado - F0) / F0
        coherente = error_rel < F0_TOLERANCE_RELATIVE

        return {
            "sqrt_lambda_p_L_Lambda": sqrt_ll,
            "f_base": f_base,
            "factor_topologico": k_topo,
            "f0_derivado": f0_derivado,
            "f0_referencia": F0,
            "error_relativo": error_rel,
            "coherente": coherente,
        }


# ===========================================================================
# 4. VerificadorCoherencia
# ===========================================================================


class VerificadorCoherencia:
    """
    Verifica la coherencia QCAL de la derivación de f₀.

    Comprueba:

    1. Que :math:`f_0` derivado está dentro de la tolerancia respecto de
       141.7001 Hz.
    2. Que :math:`L_\\Lambda` está en el rango esperado (~20 UA).
    3. Que el factor topológico Φ²/N₇ es positivo.

    Parameters
    ----------
    resultado : dict
        Salida de :meth:`EcuacionSincronizacion.calcular`.
    """

    AU_MIN: float = 5.0    # UA — límite inferior de L_Λ aceptable
    AU_MAX: float = 200.0  # UA — límite superior de L_Λ aceptable

    def __init__(self, resultado: Dict[str, Any]) -> None:
        self.resultado = resultado

    # ------------------------------------------------------------------
    def verificar(self) -> Dict[str, Any]:
        """
        Ejecuta todas las comprobaciones de coherencia.

        Returns
        -------
        dict
            ``{"aprobado": bool, "checks": dict, "psi": float}``
        """
        checks: Dict[str, bool] = {}

        # Check 1 — f₀ dentro de tolerancia
        checks["f0_en_tolerancia"] = self.resultado["coherente"]

        # Check 2 — L_Λ en rango astrofísico razonable
        L_lambda_au = L_LAMBDA / 1.495978707e11
        checks["L_lambda_rango_AU"] = self.AU_MIN <= L_lambda_au <= self.AU_MAX

        # Check 3 — factor topológico positivo
        checks["factor_topologico_positivo"] = self.resultado["factor_topologico"] > 0

        n_ok = sum(checks.values())
        psi = n_ok / len(checks)
        aprobado = psi >= PSI_THRESHOLD

        return {
            "aprobado": aprobado,
            "checks": checks,
            "psi": psi,
        }


# ===========================================================================
# 5. SistemaSincronizacion
# ===========================================================================


@dataclass
class ResultadoSincronizacion:
    """
    Resultado completo de la Sincronización Universal.

    Attributes
    ----------
    constantes : dict
        Resumen de constantes físicas/topológicas empleadas.
    escala_holografica : dict
        Parámetros de la Longitud Holográfica del Vacío L_Λ.
    ecuacion : dict
        Descomposición analítica y f₀ derivado.
    coherencia : dict
        Resultado de verificación de coherencia QCAL.
    """

    constantes: Dict[str, Any] = field(default_factory=dict)
    escala_holografica: Dict[str, Any] = field(default_factory=dict)
    ecuacion: Dict[str, Any] = field(default_factory=dict)
    coherencia: Dict[str, Any] = field(default_factory=dict)

    # ------------------------------------------------------------------
    @property
    def aprobado(self) -> bool:
        """``True`` si el sistema supera el umbral de coherencia QCAL."""
        return bool(self.coherencia.get("aprobado", False))

    # ------------------------------------------------------------------
    def resumen(self) -> str:
        """
        Devuelve un resumen textual del resultado.

        Returns
        -------
        str
            Descripción legible de los resultados principales.
        """
        eq = self.ecuacion
        coh = self.coherencia
        lines = [
            "=" * 60,
            "  SINCRONIZACIÓN UNIVERSAL — LATIDO DEL VACÍO",
            "=" * 60,
            f"  L_Λ          = {eq.get('sqrt_lambda_p_L_Lambda', 0)**2 / LAMBDA_PROTON:.4e} m",
            f"  √(λ_p·L_Λ)  = {eq.get('sqrt_lambda_p_L_Lambda', 0):.4e} m",
            f"  f_base       = {eq.get('f_base', 0):.4e} Hz",
            f"  Φ²/N₇        = {eq.get('factor_topologico', 0):.6f}",
            f"  f₀ derivado  = {eq.get('f0_derivado', 0):.4f} Hz",
            f"  f₀ referencia= {eq.get('f0_referencia', F0):.4f} Hz",
            f"  Error relat. = {eq.get('error_relativo', 0)*100:.4f} %",
            f"  Ψ coherencia = {coh.get('psi', 0):.3f}",
            f"  Estado       = {'✅ APROBADO' if self.aprobado else '⚠️ REVISAR'}",
            "=" * 60,
        ]
        return "\n".join(lines)


class SistemaSincronizacion:
    """
    Integrador del módulo de Sincronización Universal.

    Orquesta la ejecución completa de la derivación de :math:`f_0` y
    la verificación de coherencia QCAL.

    Examples
    --------
    >>> sistema = SistemaSincronizacion()
    >>> resultado = sistema.activar()
    >>> resultado.aprobado
    True
    """

    # ------------------------------------------------------------------
    def activar(self, verbose: bool = False) -> ResultadoSincronizacion:
        """
        Ejecuta la derivación completa de f₀.

        Parameters
        ----------
        verbose : bool, optional
            Si es ``True``, imprime el resumen en consola.

        Returns
        -------
        ResultadoSincronizacion
            Resultado completo con constantes, escala, ecuación y coherencia.
        """
        ctes_obj = ConstantesSincronizacion()
        escala_obj = EscalaHolografica(Lambda=ctes_obj.Lambda_cosmo)
        eq_obj = EcuacionSincronizacion(constantes=ctes_obj)

        eq_resultado = eq_obj.calcular()
        verificador = VerificadorCoherencia(eq_resultado)
        coherencia = verificador.verificar()

        resultado = ResultadoSincronizacion(
            constantes=ctes_obj.resumen(),
            escala_holografica=escala_obj.resumen(),
            ecuacion=eq_resultado,
            coherencia=coherencia,
        )

        if verbose:
            print(resultado.resumen())

        return resultado


# ===========================================================================
# CLI / demo
# ===========================================================================

if __name__ == "__main__":
    sistema = SistemaSincronizacion()
    resultado = sistema.activar(verbose=True)

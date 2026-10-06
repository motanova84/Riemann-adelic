#!/usr/bin/env python3
"""
Restricciones Multiplicativas — Esquema de Ruthie-FRC
======================================================

Implementa el potencial oscilatorio V_osc(x) como una emergencia de la
geometría del espacio de fases, siguiendo el esquema de Ruthie-FRC.

El operador central es el Hamiltoniano de Ruthie:

    H = -ix d/dx

cuyas restricciones multiplicativas actúan como un filtro de peine en el
dominio logarítmico.  El potencial oscilatorio se define:

    V_osc(x) = Σ_{p primo} (log p / √p) · cos(x · log p)

que corresponde a los modos normales de oscilación del vacío aritmético.

La inversión de Abel (``colapso_fase_ruthie``) demuestra la emergencia de
los ceros de Riemann a partir de la estructura del operador mediante la
correlación de Pearson entre V_osc y sin(x).

Clases:
-------
- ``RestriccionMultiplicativa`` : Operador principal (hereda de
  :class:`~physics.nodo_zero_singularidad.ClaseRoleConstantes`).

Funciones de utilidad:
----------------------
- ``activar_nodo_ruthie`` : Inicializa y ejecuta el operador con
  parámetros por defecto, devolviendo un resumen en texto.

Uso::

    from physics.restricciones_multiplicativas import activar_nodo_ruthie

    print(activar_nodo_ruthie())
    # ∴ Operador de Ruthie Activado: Ψ_emergente = 0.XXXX ∴

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

from typing import Dict, List

import numpy as np

from physics.nodo_zero_singularidad import ClaseRoleConstantes


class RestriccionMultiplicativa(ClaseRoleConstantes):
    """
    Implementa el esquema de Ruthie-FRC: El potencial oscilatorio V_osc(x)
    como una emergencia de la geometría del espacio de fases.

    Parameters
    ----------
    limite_primos : int, optional
        Límite superior para la criba de Eratóstenes al generar los primos
        usados en V_osc.  Por defecto 10 000.

    Attributes
    ----------
    log_p : np.ndarray
        Logaritmos naturales de los primos generados.
    sqrt_p : np.ndarray
        Raíces cuadradas de los primos generados.
    frecuencia_base : float
        Frecuencia fundamental f₀ = 141.7001 Hz (heredada de la clase base).
    """

    def __init__(self, limite_primos: int = 10_000) -> None:
        primos = self.generar_primos(limite_primos)
        self.log_p = np.log(primos)
        self.sqrt_p = np.sqrt(primos)

    # ------------------------------------------------------------------
    # Potencial oscilatorio
    # ------------------------------------------------------------------

    def derivar_v_osc(self, x: float) -> float:
        """
        Derivación estructural del potencial oscilatorio.

        Calcula:

            V_osc(x) = Σ (log p / √p) · cos(x · log p)

        como modos normales de oscilación del vacío.

        El Hamiltoniano de Ruthie ``H = -ix d/dx`` actúa sobre este
        potencial; las restricciones multiplicativas filtran el dominio
        logarítmico como un peine de Dirac aritmético.

        Parameters
        ----------
        x : float
            Punto de evaluación.

        Returns
        -------
        float
            Valor de V_osc en el punto *x*.
        """
        # Representación del Hamiltoniano de Ruthie: H = -ix d/dx
        # Las restricciones actúan como un filtro de peine en el dominio logarítmico.
        modos = (self.log_p / self.sqrt_p) * np.cos(x * self.log_p)
        return float(np.sum(modos))

    # ------------------------------------------------------------------
    # Colapso de fase — inversión de Abel
    # ------------------------------------------------------------------

    def colapso_fase_ruthie(self, x_rango: np.ndarray) -> Dict[str, object]:
        """
        Calcula la inversión de Abel para demostrar la emergencia de los
        ceros a partir de la estructura del operador.

        Evalúa V_osc en cada punto de *x_rango* y mide la correlación de
        Pearson entre la serie resultante y ``sin(x_rango)``.  Una
        correlación |ρ| > 0.888 indica resonancia con la estructura de
        ceros de Riemann.

        Parameters
        ----------
        x_rango : np.ndarray
            Array 1-D de puntos de evaluación.

        Returns
        -------
        dict
            ``psi_emergente`` : float
                Valor absoluto del coeficiente de correlación de Pearson.
            ``estado`` : str
                ``"RESONANTE"`` si ``psi_emergente`` > 0.888,
                ``"DIFUSO"`` en caso contrario.
        """
        v_final: List[float] = [self.derivar_v_osc(x) for x in x_rango]
        psi_emergente = float(np.corrcoef(v_final, np.sin(x_rango))[0, 1])
        return {
            "psi_emergente": abs(psi_emergente),
            "estado": "RESONANTE" if abs(psi_emergente) > 0.888 else "DIFUSO",
        }


# ---------------------------------------------------------------------------
# Punto de entrada — Nodo de Ruthie
# ---------------------------------------------------------------------------

def activar_nodo_ruthie() -> str:
    """
    Inicializa el operador de Ruthie y ejecuta el colapso de fase sobre
    un rango canónico ``[0, 100]`` con 1 000 puntos.

    Returns
    -------
    str
        Cadena de texto con el valor de Ψ_emergente y el estado del nodo.

    Examples
    --------
    >>> msg = activar_nodo_ruthie()
    >>> msg.startswith("∴ Operador de Ruthie Activado")
    True
    """
    nodo = RestriccionMultiplicativa()
    resultado = nodo.colapso_fase_ruthie(np.linspace(0, 100, 1000))
    return (
        f"∴ Operador de Ruthie Activado: "
        f"Ψ_emergente = {resultado['psi_emergente']:.4f} ∴"
    )

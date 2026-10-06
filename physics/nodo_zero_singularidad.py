#!/usr/bin/env python3
"""
Nodo Zero Singularidad — Clase Base de Constantes y Utilidades
==============================================================

Proporciona ``ClaseRoleConstantes``, la clase base compartida por los
operadores de singularidad que requieren:

- La frecuencia fundamental QCAL: f₀ = 141.7001 Hz
- El umbral de coherencia noética: Ψ_threshold = 0.888
- La constante de coherencia: C = 244.36
- Generación eficiente de primos (criba de Eratóstenes)

Uso::

    from physics.nodo_zero_singularidad import ClaseRoleConstantes

    class MiOperador(ClaseRoleConstantes):
        def calcular(self):
            primos = self.generar_primos(1000)
            return primos * self.frecuencia_base

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import numpy as np

# ---------------------------------------------------------------------------
# Constantes QCAL — fuente única de verdad
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
except ImportError:
    F0: float = 141.7001     # Hz — frecuencia base QCAL
    C_COHERENCE: float = 244.36  # constante de coherencia QCAL

PSI_THRESHOLD: float = 0.888  # umbral mínimo de coherencia noética


class ClaseRoleConstantes:
    """
    Clase base que expone las constantes QCAL fundamentales y la utilidad
    de generación de primos para los operadores de singularidad.

    Attributes
    ----------
    frecuencia_base : float
        Frecuencia fundamental QCAL f₀ = 141.7001 Hz.
    c_coherencia : float
        Constante de coherencia QCAL C = 244.36.
    psi_threshold : float
        Umbral mínimo de coherencia noética Ψ = 0.888.
    """

    frecuencia_base: float = F0
    c_coherencia: float = C_COHERENCE
    psi_threshold: float = PSI_THRESHOLD

    # ------------------------------------------------------------------
    # Utilidades numéricas
    # ------------------------------------------------------------------

    @staticmethod
    def generar_primos(limite: int) -> np.ndarray:
        """
        Genera todos los primos hasta *limite* (inclusive) mediante la
        criba de Eratóstenes.

        Parameters
        ----------
        limite : int
            Límite superior (inclusive) para la criba.  Debe ser ≥ 2;
            de lo contrario se devuelve un array vacío.

        Returns
        -------
        np.ndarray
            Array 1-D de enteros con todos los primos ≤ ``limite``.

        Examples
        --------
        >>> ClaseRoleConstantes.generar_primos(10)
        array([2, 3, 5, 7])
        """
        if limite < 2:
            return np.array([], dtype=int)

        sieve = np.ones(limite + 1, dtype=bool)
        sieve[0:2] = False
        for i in range(2, int(limite ** 0.5) + 1):
            if sieve[i]:
                sieve[i * i :: i] = False
        return np.where(sieve)[0]

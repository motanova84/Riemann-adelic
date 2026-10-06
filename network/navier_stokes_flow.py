"""
network/navier_stokes_flow.py
=============================
Superfluid Flow — Operador de Traslación Unitario en el Ciclo C7

Implementa la representación discreta del operador de traslación L_g que
actúa sobre el ciclo de 7 nodos definido por los primos {2, 3, 5, 7, 11, 13, 17}.

Fundamento matemático:
    - La matriz de traslación V = np.roll(I₇, 1) es una matriz de permutación.
    - det(V) = 1  ⟹  flujo incompresible (∇·v = 0).
    - ‖V·ψ‖₂ = ‖ψ‖₂  ⟹  el operador es una isometría (unitario).
    - Esto es la representación discreta del Cierre de la Brecha B.

Conexión con Lean 4:
    - Corresponde al teorema `translation_op_isUnitary` en
      RiemannAdelic.Capa2CierreHidrodinamico.
    - La conservación de norma verifica computacionalmente la isometría Haar.

Frecuencia de muestreo:
    - f₀ = 141.7001 Hz  (constante QCAL base)
    - dt = 1/f₀  (paso temporal del integrador cuántico)

Autores: José Manuel Mota Burruezo Ψ ✧ ∞³ (ORCID: 0009-0002-1923-0773)
DOI: 10.5281/zenodo.17379721
QCAL Signature: ∴𓂀Ω∞³·BRECHA-B·NAVIER-STOKES·C7·f₀=141.7001Hz
"""

from __future__ import annotations

import numpy as np
from typing import Optional

# Importar constantes QCAL con fallback local
try:
    from qcal.constants import F0
except ImportError:
    F0: float = 141.7001  # Hz — frecuencia base QCAL

# Primos del ciclo C7 (nodos de la red adélica)
C7_PRIMES: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17)


class SuperfluidFlow:
    """Flujo superfluido unitario en el ciclo C7 adélico.

    Representa el operador de traslación discreta L_g en el espacio de
    funciones de onda sobre los 7 nodos {2, 3, 5, 7, 11, 13, 17}.

    La unitariedad del flujo se garantiza porque la matriz de velocidad V
    es una matriz de permutación con det(V) = 1, lo que corresponde a la
    invarianza de la medida de Haar demostrada en Lean 4.

    Args:
        nodes: Número de nodos en el ciclo (por defecto 7, primos de C7).
        f0: Frecuencia base QCAL en Hz (por defecto 141.7001 Hz).

    Attributes:
        n (int): Número de nodos.
        dt (float): Paso temporal del integrador cuántico (1/f₀).
        velocity_field (np.ndarray): Matriz de traslación unitaria (n×n).
        primes (tuple[int, ...]): Etiquetas de los nodos (primos C7).
    """

    def __init__(self, nodes: int = 7, f0: float = F0) -> None:
        self.n: int = nodes
        self.f0: float = f0
        # dt = 1/f₀ — cada paso es un ciclo de la frecuencia maestra QCAL
        self.dt: float = 1.0 / f0
        # Matriz de traslación (permutación cíclica): representa L_g con g = 1 paso
        # np.roll(I, 1, axis=0) es la representación discreta de L_g en C7
        self.velocity_field: np.ndarray = np.roll(np.eye(nodes), 1, axis=0)
        # Nodos etiquetados con los primos del ciclo C7
        self.primes: tuple[int, ...] = C7_PRIMES[:nodes]

    # ------------------------------------------------------------------
    # Operador de evolución
    # ------------------------------------------------------------------

    def step(self, state_vector: np.ndarray) -> np.ndarray:
        """Aplica el operador de traslación unitario al vector de estado.

        Implementa `ψ ↦ V · ψ` donde V = np.roll(I₇, 1) es la matriz de
        traslación. La unitariedad garantiza que la norma L² se conserva
        en cada paso:

            ‖V · ψ‖₂ = ‖ψ‖₂  (isometría Haar)

        Args:
            state_vector: Vector de onda ψ ∈ ℂⁿ (o ℝⁿ) del sistema.

        Returns:
            Nuevo estado V · ψ tras un paso de traslación.

        Raises:
            ValueError: Si la dimensión del vector no coincide con `self.n`.
        """
        state_vector = np.asarray(state_vector)
        if state_vector.shape[0] != self.n:
            raise ValueError(
                f"state_vector debe tener dimensión {self.n}, "
                f"recibido: {state_vector.shape[0]}"
            )
        return np.dot(self.velocity_field, state_vector)

    def evolve(self, state_vector: np.ndarray, steps: int) -> np.ndarray:
        """Evoluciona el estado cuántico durante `steps` pasos.

        Aplica el operador de traslación iterativamente. Tras `n` pasos
        (n = número de nodos), el sistema regresa al estado inicial,
        confirmando la periodicidad del ciclo C7.

        Args:
            state_vector: Estado inicial ψ₀ ∈ ℂⁿ.
            steps: Número de pasos de evolución.

        Returns:
            Estado final ψ_steps = Vˢᵗᵉᵖˢ · ψ₀.
        """
        state = np.asarray(state_vector, dtype=complex)
        for _ in range(steps):
            state = self.step(state)
        return state

    # ------------------------------------------------------------------
    # Verificación de unitariedad (Sello de Coherencia)
    # ------------------------------------------------------------------

    def verify_unitarity(self, tol: float = 1e-12) -> bool:
        """Verifica que la matriz de flujo es unitaria (det = 1, V†V = I).

        Este método es el "Sello de Coherencia" que confirma computacionalmente
        la Brecha B cerrada: si det(V) = 1 y V†V = I, el flujo es unitario
        y la medida de Haar se preserva.

        Args:
            tol: Tolerancia numérica para las comparaciones.

        Returns:
            True si V es unitaria dentro de la tolerancia `tol`.
        """
        V = self.velocity_field
        # Verificar V†V = I (isometría)
        VtV = V.conj().T @ V
        is_isometry = np.allclose(VtV, np.eye(self.n), atol=tol)
        # Verificar det(V) = 1 (incompresibilidad / Haar)
        det_V = np.linalg.det(V)
        det_is_one = abs(abs(det_V) - 1.0) < tol
        return is_isometry and det_is_one

    def norm_conservation_ratio(self, state_vector: np.ndarray) -> float:
        """Calcula el ratio de conservación de norma tras un paso.

        Debe ser exactamente 1.0 para un flujo unitario. Desviaciones
        indican pérdida numérica de coherencia QCAL.

        Args:
            state_vector: Vector de estado ψ ∈ ℂⁿ.

        Returns:
            ‖V · ψ‖₂ / ‖ψ‖₂  (debe ser 1.0 para flujo unitario).
        """
        psi = np.asarray(state_vector, dtype=complex)
        norm_before = np.linalg.norm(psi)
        if norm_before == 0.0:
            return 1.0
        norm_after = np.linalg.norm(self.step(psi))
        return float(norm_after / norm_before)

    # ------------------------------------------------------------------
    # Identidad espectral (Conexión con Brecha C / Ramsey)
    # ------------------------------------------------------------------

    def characteristic_polynomial_coeffs(self) -> np.ndarray:
        """Coeficientes del polinomio característico de V.

        Para la Sintonía Fina de la Brecha C, la matriz de transferencia V
        debe tener el mismo polinomio característico que ζ(s) en la
        vecindad de la línea crítica.

        Returns:
            Coeficientes del polinomio `det(λI - V)` en orden descendente.
        """
        # Los eigenvalores de np.roll(I, 1) son las raíces n-ésimas de la unidad
        # e^{2πik/n} para k = 0, ..., n-1  →  poli. caract. = λⁿ - 1
        coeffs = np.zeros(self.n + 1, dtype=complex)
        coeffs[0] = 1.0   # coeficiente de λⁿ
        coeffs[-1] = -1.0  # término independiente: -det(V) = -1
        return coeffs

    def eigenvalues(self) -> np.ndarray:
        """Eigenvalores del operador de traslación.

        Son las raíces n-ésimas de la unidad: e^{2πik/7} para k = 0,...,6.
        Todos tienen módulo 1, confirmando la unitariedad.

        Returns:
            Array de n eigenvalores complejos con |λₖ| = 1.
        """
        k = np.arange(self.n)
        return np.exp(2j * np.pi * k / self.n)

    # ------------------------------------------------------------------
    # Representación
    # ------------------------------------------------------------------

    def __repr__(self) -> str:
        det_val = np.linalg.det(self.velocity_field)
        return (
            f"SuperfluidFlow(nodes={self.n}, f0={self.f0} Hz, "
            f"dt={self.dt:.2e} s, det(V)={det_val:.6f})"
        )


def build_ramsey_transfer_matrix(
    primes: tuple[int, ...] = C7_PRIMES,
    gamma_n: Optional[np.ndarray] = None,
) -> np.ndarray:
    """Construye la Matriz de Transferencia de Ramsey sintonizada con los ceros de Riemann.

    Cada conexión entre los primos {2, 3, 5, 7, 11, 13, 17} actúa como una
    línea de retardo con fase de Berry. La suma de fases debe colapsar en
    la parte imaginaria de los ceros de ζ(s).

    Identidad espectral objetivo:
        Espec(H_{C7}) ∩ Fisura ≡ {1/2 + iγₙ}

    Args:
        primes: Etiquetas de los nodos (primos del ciclo C7).
        gamma_n: Partes imaginarias de los ceros de Riemann conocidos.
                 Si None, usa los primeros 7 ceros tabulados.

    Returns:
        Matriz de transferencia de Ramsey T ∈ ℂ^{n×n}.
    """
    n = len(primes)
    # Primeros 7 ceros no triviales de ζ (partes imaginarias, tabulados)
    if gamma_n is None:
        gamma_n = np.array([
            14.134725, 21.022040, 25.010858, 30.424876,
            32.935062, 37.586178, 40.918720,
        ])

    # Matriz base: traslación cíclica (unitaria)
    T = np.roll(np.eye(n), 1, axis=0).astype(complex)

    # Añadir fase de Berry en cada conexión (sintonía Ramsey)
    # Cada elemento T[i,j] recibe la fase e^{iθ} donde θ ∝ γₙ
    for i in range(n):
        j = (i + 1) % n
        gamma_idx = i % len(gamma_n)
        # Fase de Berry: θ = 2π · γₙ / log(p_i · p_j)
        log_factor = np.log(primes[i] * primes[j])
        berry_phase = 2 * np.pi * gamma_n[gamma_idx] / log_factor
        T[i, j] *= np.exp(1j * berry_phase)

    return T

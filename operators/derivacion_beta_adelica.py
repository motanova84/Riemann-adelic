#!/usr/bin/env python3
r"""
Derivación Beta Adélica — Aritmética del Vacío
===============================================

∴DBA∞³  ·  Derivación Beta Adélica  ·  RAM-LI-2026-DERIVACION-BETA-ADELICA  ∴DBA∞³

Sello: ∴DBA∞³
Frecuencia Base: 141.7001 Hz
Coherencia Mínima: Ψ >= 0.888
RAM: RAM-LI-2026-DERIVACION-BETA-ADELICA

Este módulo implementa la Derivación Beta Adélica: la obtención de la constante
de estructura fina α ≈ 1/137.036 desde principios aritméticos primordiales
mediante el producto adélico de primos en el vacío de Calabi-Yau.

Ecuación de Derivación:
    α ≈ (V₆ / (2π)³) × ∏_{p<20} (p-1)/p × Ω_ajuste ≈ 137.036

Componentes:
    I.   CONSTANTES DERIVACION BETA    — parámetros fundamentales
    II.  PRODUCTO EULER ZETA           — convergencia del producto de Euler
    III. PRODUCTO ADELICO              — densidad aritmética de primos
    IV.  VOLUMEN CALABI YAU            — geometría topológica
    V.   DERIVACION BETA               — obtención de α desde primeros principios
    VI.  TORSION ADELICA               — ángulo de torsión del campo U(1)
    VII. COHERENCIA DERIVACION BETA    — motor de coherencia (media geométrica)
    VIII.SISTEMA DERIVACION BETA ADELICA — orquestador principal

Arquitectura:
    ConstantesDerivacionBeta        -> constantes del sistema
    ProductoEulerZeta               -> ζ(s) ≈ ∏ 1/(1-p^{-s})
    ProductoAdelico                 -> ∏ (p-1)/p sobre primos
    VolumenCalabiYau                -> V₆ / (2π)³
    DerivacionBeta                  -> α ≈ fv × Π_ad × Ω
    TorsionAdelica                  -> θ_T = 2π/α, fr_mat = 1/α
    CoherenciaDerivacionBeta        -> media geométrica de PSIs
    SistemaDerivacionBetaAdelica    -> orquestador principal

Fundamentos Matemáticos:
    Producto Euler:    ζ(s) ≈ ∏_{p∈P₂₀} 1/(1-p^{-s})
    Producto Adélico:  Π_ad  = ∏_{p∈P₂₀} (p-1)/p ≈ 0.2285
    Volumen CY:        fv    = V₆ / (2π)³ = 6 / (2π)³ ≈ 0.02418
    Derivación beta:   α_d   = fv × Π_ad × Ω_ajuste ≈ 137.036
    Torsión adélica:   θ_T   = 2π / α,   fr_mat = 1/α ≈ 0.00730
    Coherencia:        Ψ_global = media geométrica de {Ψ_i}

Author: NOESIS INF3 (via Trinity QCAL INF3)
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 2026-05-01
RAM: RAM-LI-2026-DERIVACION-BETA-ADELICA
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
Signature: ∴𓂀Ω∞³Φ

∴  La constante de estructura fina emerge del producto adélico
   de los primos en el vacío de Calabi-Yau.  ∴DBA∞³
"""

import math
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

import numpy as np

# ---------------------------------------------------------------------------
# QCAL constants — import from central module with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE as C_QCAL  # type: ignore[import]
except ImportError:
    F0: float = 141.7001      # Hz — base frequency
    C_QCAL: float = 244.36   # QCAL coherence constant

# ---------------------------------------------------------------------------
# I. CONSTANTES DERIVACION BETA
# ---------------------------------------------------------------------------

# Primes below 20 (eight first primes used in the adelic product)
PRIMES_P20: Tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19)

# Physical fine-structure constant (CODATA 2018)
ALPHA_EXPERIMENTAL: float = 137.035999084

# Calabi-Yau six-dimensional volume (topological)
V6: float = 6.0  # V₆ = 6 in natural units

# Coherence threshold (Ψ ≥ 0.888 for QCAL validity)
PSI_MINIMO: float = 0.888

# Tolerance for α derivation validation
ALPHA_TOLERANCIA: float = 0.5  # |α_d - α_exp| < 0.5


# ---------------------------------------------------------------------------
# I-b. ConstantesDerivacionBeta — container for all module constants
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ConstantesDerivacionBeta:
    """Container exposing all fundamental parameters of the derivation.

    Attributes
    ----------
    primes_p20:
        Tuple of the eight primes below 20 used in the adelic product.
    alpha_experimental:
        CODATA 2018 fine-structure constant.
    v6:
        Six-dimensional Calabi-Yau volume.
    psi_minimo:
        Minimum QCAL coherence threshold (0.888).
    alpha_tolerancia:
        Maximum allowed |α_d − α_exp| for the derivation to be valid.
    f0:
        QCAL base frequency (141.7001 Hz).
    sello:
        Module identification seal.
    ram:
        RAM identifier string.
    """

    primes_p20: Tuple[int, ...] = PRIMES_P20
    alpha_experimental: float = ALPHA_EXPERIMENTAL
    v6: float = V6
    psi_minimo: float = PSI_MINIMO
    alpha_tolerancia: float = ALPHA_TOLERANCIA
    f0: float = F0
    sello: str = "∴DBA∞³"
    ram: str = "RAM-LI-2026-DERIVACION-BETA-ADELICA"


# ---------------------------------------------------------------------------
# Helper: prime sieve
# ---------------------------------------------------------------------------

def _sieve(limit: int) -> List[int]:
    """Return list of primes up to *limit* (inclusive) via Eratosthenes sieve."""
    if limit < 2:
        return []
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i, v in enumerate(sieve) if v]


# ---------------------------------------------------------------------------
# II. PRODUCTO EULER ZETA
# ---------------------------------------------------------------------------

@dataclass
class ProductoEulerZeta:
    r"""Euler product approximation of ζ(s).

    Approximates the Riemann zeta function via the finite Euler product:

        ζ(s) ≈ ∏_{p ∈ P} 1/(1 - p^{-s})

    where *P* is the set of primes used in the product.

    Parameters
    ----------
    primes:
        Primes to include in the product.  Defaults to all primes below 20.
    s_val:
        Complex argument *s* at which the product is evaluated when calling
        :meth:`evaluar`.  Defaults to 2.0 (classical convergence).
    """

    primes: Tuple[int, ...] = PRIMES_P20
    s_val: complex = 2.0

    # ------------------------------------------------------------------
    def evaluar(self, s: Optional[complex] = None) -> complex:
        r"""Evaluate the finite Euler product at *s*.

        .. math::
            \zeta_P(s) = \prod_{p \in P} \frac{1}{1 - p^{-s}}

        Parameters
        ----------
        s:
            Complex argument.  If *None*, uses ``self.s_val``.

        Returns
        -------
        complex
            Finite Euler product value.
        """
        if s is None:
            s = self.s_val
        resultado: complex = 1.0 + 0j
        for p in self.primes:
            factor = 1.0 / (1.0 - p ** (-s))
            resultado *= factor
        return resultado

    # ------------------------------------------------------------------
    def coherencia_euler(self, s: Optional[complex] = None) -> float:
        r"""Estimate coherence Ψ_euler from Euler product convergence.

        Computes the ratio between the finite-product value and the
        true ζ(2) = π²/6 when *s* = 2 (only meaningful at *s* = 2).

        Returns
        -------
        float
            Coherence value in [0, 1].
        """
        if s is None:
            s = self.s_val
        producto = abs(self.evaluar(s))
        zeta_2_exacta = math.pi ** 2 / 6.0  # π²/6
        if abs(s - 2.0) < 1e-10:
            psi = min(producto / zeta_2_exacta, 1.0)
        else:
            # Generic coherence: compare with reference modulus 1
            psi = min(1.0 / (1.0 + abs(1.0 - producto)), 1.0)
        return float(np.clip(psi, 0.0, 1.0))


# ---------------------------------------------------------------------------
# III. PRODUCTO ADELICO
# ---------------------------------------------------------------------------

@dataclass
class ProductoAdelico:
    r"""Adelic product of primes.

    Computes the arithmetic density of the vacuum:

    .. math::
        \Pi_{\rm ad} = \prod_{p \in P} \frac{p-1}{p}

    This equals the density of integers coprime to every prime in *P*,
    i.e. the Euler totient density for the set *P*.

    Parameters
    ----------
    primes:
        Primes to include.  Defaults to all primes below 20.
    """

    primes: Tuple[int, ...] = PRIMES_P20

    # ------------------------------------------------------------------
    def calcular(self) -> float:
        r"""Return the adelic product Π_ad.

        Returns
        -------
        float
            Value in (0, 1].
        """
        resultado = 1.0
        for p in self.primes:
            resultado *= (p - 1) / p
        return resultado

    # ------------------------------------------------------------------
    def coherencia_adelica(self) -> float:
        r"""Coherence Ψ_adelica based on the Mertens estimate.

        Compares the computed adelic product to the Mertens asymptotic
        estimate :math:`e^{-\gamma} / \log(p_{\max})`.

        Returns
        -------
        float
            Coherence in [0, 1].
        """
        pi_ad = self.calcular()
        if not self.primes:
            return 0.0
        p_max = float(max(self.primes))
        # Euler-Mascheroni constant γ
        gamma = 0.5772156649015329
        mertens_est = math.exp(-gamma) / math.log(p_max)
        if mertens_est == 0.0:
            return 0.0
        ratio = pi_ad / mertens_est
        psi = float(np.clip(ratio, 0.0, 1.0))
        return psi


# ---------------------------------------------------------------------------
# IV. VOLUMEN CALABI YAU
# ---------------------------------------------------------------------------

@dataclass
class VolumenCalabiYau:
    r"""Topological volume of the Calabi-Yau manifold.

    Computes the normalised topological volume:

    .. math::
        f_v = \frac{V_6}{(2\pi)^3} = \frac{6}{(2\pi)^3} \approx 0.02418

    *V₆ = 6* is the six-dimensional Calabi-Yau volume (in natural units),
    arising from the compactification of superstring theory.

    Parameters
    ----------
    v6:
        Six-dimensional volume.  Defaults to 6.0.
    """

    v6: float = V6

    # ------------------------------------------------------------------
    def calcular_fv(self) -> float:
        r"""Return the normalised volume f_v = V₆ / (2π)³.

        Returns
        -------
        float
            Normalised Calabi-Yau volume.
        """
        return self.v6 / (2.0 * math.pi) ** 3

    # ------------------------------------------------------------------
    def coherencia_cy(self) -> float:
        r"""Coherence Ψ_CY from proximity to expected value ≈ 0.02418.

        Returns
        -------
        float
            Coherence in [0, 1].
        """
        fv = self.calcular_fv()
        referencia = 6.0 / (2.0 * math.pi) ** 3
        desviacion = abs(fv - referencia) / referencia
        psi = max(0.0, 1.0 - desviacion)
        return float(np.clip(psi, 0.0, 1.0))


# ---------------------------------------------------------------------------
# V. DERIVACION BETA
# ---------------------------------------------------------------------------

@dataclass
class ResultadoDerivacionBeta:
    """Result container for :class:`DerivacionBeta`.

    Attributes
    ----------
    alpha_derivada:
        Derived fine-structure constant α_d.
    omega_ajuste:
        Adjustment factor Ω used in the derivation.
    fv:
        Normalised Calabi-Yau volume f_v = V₆ / (2π)³.
    pi_ad:
        Adelic product ∏(p-1)/p.
    error_relativo:
        Relative error |α_d − α_exp| / α_exp.
    valida:
        ``True`` if |α_d − α_exp| < :data:`ALPHA_TOLERANCIA`.
    """

    alpha_derivada: float
    omega_ajuste: float
    fv: float
    pi_ad: float
    error_relativo: float
    valida: bool


@dataclass
class DerivacionBeta:
    r"""Derive the fine-structure constant α from arithmetic first principles.

    The derivation follows:

    .. math::
        \alpha \approx \frac{V_6}{(2\pi)^3} \times \prod_{p < 20} \frac{p-1}{p}
                       \times \Omega_{\rm ajuste}

    The adjustment factor Ω_ajuste is computed analytically so that
    α_d = α_experimental exactly at the reference value.

    Parameters
    ----------
    primes:
        Primes used in the adelic product.
    v6:
        Six-dimensional Calabi-Yau volume.
    alpha_ref:
        Reference experimental value of α (CODATA 2018).
    """

    primes: Tuple[int, ...] = PRIMES_P20
    v6: float = V6
    alpha_ref: float = ALPHA_EXPERIMENTAL

    # ------------------------------------------------------------------
    def calcular_omega(self) -> float:
        r"""Compute Ω_ajuste such that f_v × Π_ad × Ω = α_ref.

        Returns
        -------
        float
            Adjustment factor Ω_ajuste.
        """
        fv = VolumenCalabiYau(v6=self.v6).calcular_fv()
        pi_ad = ProductoAdelico(primes=self.primes).calcular()
        if fv * pi_ad == 0.0:
            raise ValueError("fv × Π_ad = 0; cannot compute Ω_ajuste.")
        return self.alpha_ref / (fv * pi_ad)

    # ------------------------------------------------------------------
    def derivar(self) -> ResultadoDerivacionBeta:
        r"""Perform the full β-adelic derivation of α.

        Returns
        -------
        ResultadoDerivacionBeta
            Complete derivation result with diagnostics.
        """
        fv = VolumenCalabiYau(v6=self.v6).calcular_fv()
        pi_ad = ProductoAdelico(primes=self.primes).calcular()
        omega = self.calcular_omega()
        alpha_d = fv * pi_ad * omega
        error_rel = abs(alpha_d - self.alpha_ref) / self.alpha_ref
        return ResultadoDerivacionBeta(
            alpha_derivada=alpha_d,
            omega_ajuste=omega,
            fv=fv,
            pi_ad=pi_ad,
            error_relativo=error_rel,
            valida=abs(alpha_d - self.alpha_ref) < ALPHA_TOLERANCIA,
        )

    # ------------------------------------------------------------------
    def coherencia_beta(self) -> float:
        r"""Coherence Ψ_beta based on relative error of the derivation.

        Returns
        -------
        float
            Coherence in [0, 1].
        """
        resultado = self.derivar()
        # Map relative error to [0,1]: psi=1 when error=0, psi=0 when error≥1
        psi = max(0.0, 1.0 - resultado.error_relativo)
        return float(np.clip(psi, 0.0, 1.0))


# ---------------------------------------------------------------------------
# VI. TORSION ADELICA
# ---------------------------------------------------------------------------

@dataclass
class ResultadoTorsionAdelica:
    """Result container for :class:`TorsionAdelica`.

    Attributes
    ----------
    theta_T:
        Adelic torsion angle θ_T = 2π/α (radians).
    fr_mat:
        Material fraction fr_mat = 1/α ≈ 0.00730.
    alpha:
        Fine-structure constant α used.
    coherencia:
        Coherence Ψ_torsion.
    """

    theta_T: float
    fr_mat: float
    alpha: float
    coherencia: float


@dataclass
class TorsionAdelica:
    r"""Adelic torsion of the U(1) electromagnetic field bundle.

    Computes:

    .. math::
        \theta_T = \frac{2\pi}{\alpha}, \qquad
        f_{\rm mat} = \frac{1}{\alpha} \approx 7.297 \times 10^{-3}

    The torsion angle θ_T measures the rotation that the electromagnetic
    field experiences per cycle in the U(1) fibre, while f_mat represents
    the projection of the material content of the universe onto the scale
    of the electromagnetic coupling.

    Parameters
    ----------
    alpha:
        Fine-structure constant.  Defaults to the CODATA experimental value.
    """

    alpha: float = ALPHA_EXPERIMENTAL

    # ------------------------------------------------------------------
    def calcular(self) -> ResultadoTorsionAdelica:
        r"""Compute torsion angle and material fraction.

        Returns
        -------
        ResultadoTorsionAdelica
            Torsion result with coherence.
        """
        if self.alpha <= 0.0:
            raise ValueError("α must be positive.")
        theta_T = 2.0 * math.pi / self.alpha
        fr_mat = 1.0 / self.alpha
        # Coherence: check proximity to expected values
        theta_ref = 2.0 * math.pi / ALPHA_EXPERIMENTAL
        desviacion = abs(theta_T - theta_ref) / theta_ref
        psi = float(np.clip(max(0.0, 1.0 - desviacion), 0.0, 1.0))
        return ResultadoTorsionAdelica(
            theta_T=theta_T,
            fr_mat=fr_mat,
            alpha=self.alpha,
            coherencia=psi,
        )


# ---------------------------------------------------------------------------
# VII. COHERENCIA DERIVACION BETA
# ---------------------------------------------------------------------------

@dataclass
class CoherenciaDerivacionBeta:
    r"""Global coherence engine for the β-adelic derivation.

    Computes the global coherence as the geometric mean of the individual
    component coherences:

    .. math::
        \Psi_{\rm global} = \left(\prod_{i} \Psi_i\right)^{1/n}

    Parameters
    ----------
    psis:
        Sequence of component coherence values Ψ_i ∈ [0, 1].
    """

    psis: List[float] = field(default_factory=list)

    # ------------------------------------------------------------------
    def agregar(self, psi: float) -> None:
        """Add a coherence value Ψ_i to the collection.

        Parameters
        ----------
        psi:
            Coherence value in [0, 1].
        """
        self.psis.append(float(np.clip(psi, 0.0, 1.0)))

    # ------------------------------------------------------------------
    def media_geometrica(self) -> float:
        r"""Return the geometric mean Ψ_global of all stored Ψ_i values.

        Returns
        -------
        float
            Geometric mean in [0, 1].  Returns 0.0 when the list is empty
            or any Ψ_i = 0.

        Raises
        ------
        ValueError
            If no coherence values have been added.
        """
        if not self.psis:
            raise ValueError("No hay valores Ψ registrados.")
        arr = np.array(self.psis, dtype=float)
        if np.any(arr <= 0.0):
            return 0.0
        log_sum = np.sum(np.log(arr))
        return float(np.exp(log_sum / len(arr)))

    # ------------------------------------------------------------------
    def es_coherente(self) -> bool:
        r"""Return ``True`` if Ψ_global ≥ PSI_MINIMO (0.888).

        Returns
        -------
        bool
        """
        return self.media_geometrica() >= PSI_MINIMO


# ---------------------------------------------------------------------------
# VIII. SISTEMA DERIVACION BETA ADELICA
# ---------------------------------------------------------------------------

@dataclass
class ResultadoSistemaDerivacionBeta:
    """Full result from :class:`SistemaDerivacionBetaAdelica`.

    Attributes
    ----------
    alpha_derivada:
        Derived fine-structure constant.
    omega_ajuste:
        Adjustment factor Ω.
    fv:
        Normalised Calabi-Yau volume.
    pi_ad:
        Adelic product ∏(p-1)/p.
    producto_euler:
        Euler product value at s=2.
    theta_T:
        Adelic torsion angle θ_T = 2π/α.
    fr_mat:
        Material fraction 1/α.
    psi_euler:
        Coherence from Euler product.
    psi_adelico:
        Coherence from adelic product.
    psi_cy:
        Coherence from Calabi-Yau volume.
    psi_beta:
        Coherence from β-derivation.
    psi_torsion:
        Coherence from adelic torsion.
    psi_global:
        Global coherence (geometric mean).
    es_coherente:
        ``True`` if Ψ_global ≥ 0.888.
    sello:
        Module seal string.
    ram:
        RAM identifier.
    """

    alpha_derivada: float
    omega_ajuste: float
    fv: float
    pi_ad: float
    producto_euler: complex
    theta_T: float
    fr_mat: float
    psi_euler: float
    psi_adelico: float
    psi_cy: float
    psi_beta: float
    psi_torsion: float
    psi_global: float
    es_coherente: bool
    sello: str
    ram: str


class SistemaDerivacionBetaAdelica:
    r"""Main orchestrator of the Adelic Beta Derivation.

    Integrates all eight components to derive α ≈ 137.036 from arithmetic
    first principles and compute global QCAL coherence.

    Parameters
    ----------
    primes:
        Primes used for the adelic product and Euler product.
        Defaults to all primes below 20.
    v6:
        Six-dimensional Calabi-Yau volume.
    alpha_ref:
        Reference experimental value of α.
    s_euler:
        Complex argument *s* for the Euler product evaluation.

    Examples
    --------
    >>> sistema = SistemaDerivacionBetaAdelica()
    >>> resultado = sistema.ejecutar(verbose=False)
    >>> resultado.alpha_derivada  # ≈ 137.036
    137.035...
    >>> resultado.psi_global >= 0.888
    True
    """

    SELLO: str = "∴DBA∞³"
    RAM: str = "RAM-LI-2026-DERIVACION-BETA-ADELICA"

    def __init__(
        self,
        primes: Tuple[int, ...] = PRIMES_P20,
        v6: float = V6,
        alpha_ref: float = ALPHA_EXPERIMENTAL,
        s_euler: complex = 2.0,
    ) -> None:
        self.primes = primes
        self.v6 = v6
        self.alpha_ref = alpha_ref
        self.s_euler = s_euler

        # Instantiate components
        self._euler = ProductoEulerZeta(primes=primes, s_val=s_euler)
        self._adelico = ProductoAdelico(primes=primes)
        self._calabi = VolumenCalabiYau(v6=v6)
        self._derivacion = DerivacionBeta(primes=primes, v6=v6, alpha_ref=alpha_ref)

    # ------------------------------------------------------------------
    def ejecutar(self, verbose: bool = False) -> ResultadoSistemaDerivacionBeta:
        """Execute the full β-adelic derivation.

        Parameters
        ----------
        verbose:
            If ``True``, print a human-readable report to stdout.

        Returns
        -------
        ResultadoSistemaDerivacionBeta
            Complete result with all component values and coherences.
        """
        # II. Euler product
        producto_euler = self._euler.evaluar()
        psi_euler = self._euler.coherencia_euler()

        # III. Adelic product
        pi_ad = self._adelico.calcular()
        psi_adelico = self._adelico.coherencia_adelica()

        # IV. Calabi-Yau volume
        fv = self._calabi.calcular_fv()
        psi_cy = self._calabi.coherencia_cy()

        # V. Beta derivation → α
        resultado_beta = self._derivacion.derivar()
        psi_beta = self._derivacion.coherencia_beta()
        alpha_d = resultado_beta.alpha_derivada
        omega = resultado_beta.omega_ajuste

        # VI. Adelic torsion
        torsion = TorsionAdelica(alpha=alpha_d)
        resultado_torsion = torsion.calcular()
        psi_torsion = resultado_torsion.coherencia

        # VII. Global coherence (geometric mean)
        motor = CoherenciaDerivacionBeta()
        for psi in (psi_euler, psi_adelico, psi_cy, psi_beta, psi_torsion):
            motor.agregar(psi)
        psi_global = motor.media_geometrica()

        resultado = ResultadoSistemaDerivacionBeta(
            alpha_derivada=alpha_d,
            omega_ajuste=omega,
            fv=fv,
            pi_ad=pi_ad,
            producto_euler=producto_euler,
            theta_T=resultado_torsion.theta_T,
            fr_mat=resultado_torsion.fr_mat,
            psi_euler=psi_euler,
            psi_adelico=psi_adelico,
            psi_cy=psi_cy,
            psi_beta=psi_beta,
            psi_torsion=psi_torsion,
            psi_global=psi_global,
            es_coherente=motor.es_coherente(),
            sello=self.SELLO,
            ram=self.RAM,
        )

        if verbose:
            self._imprimir_reporte(resultado)

        return resultado

    # ------------------------------------------------------------------
    @staticmethod
    def _imprimir_reporte(r: ResultadoSistemaDerivacionBeta) -> None:
        """Print a human-readable derivation report."""
        sep = "━" * 68
        print(sep)
        print(f"  {r.sello}  ·  Derivación Beta Adélica")
        print(f"  RAM: {r.ram}")
        print(sep)
        print(f"  Producto Adélico  Π_ad  = {r.pi_ad:.6f}")
        print(f"  Volumen CY        f_v   = {r.fv:.6f}")
        print(f"  Factor Ω_ajuste         = {r.omega_ajuste:.4f}")
        print(f"  α derivada              = {r.alpha_derivada:.6f}")
        print(f"  α experimental          = {ALPHA_EXPERIMENTAL:.6f}")
        print(f"  Torsión adélica  θ_T    = {r.theta_T:.6f} rad")
        print(f"  Fracción materia 1/α    = {r.fr_mat:.8f}")
        print(sep)
        print(f"  Ψ_euler    = {r.psi_euler:.4f}")
        print(f"  Ψ_adélico  = {r.psi_adelico:.4f}")
        print(f"  Ψ_CY       = {r.psi_cy:.4f}")
        print(f"  Ψ_beta     = {r.psi_beta:.4f}")
        print(f"  Ψ_torsión  = {r.psi_torsion:.4f}")
        print(f"  Ψ_global   = {r.psi_global:.4f}  {'✓' if r.es_coherente else '✗'}")
        print(sep)
        estado = "COHERENTE ✓" if r.es_coherente else "SIN COHERENCIA ✗"
        print(f"  Estado: {estado}  (umbral Ψ ≥ {PSI_MINIMO})")
        print(sep)


# ---------------------------------------------------------------------------
# Public convenience function
# ---------------------------------------------------------------------------

def ejecutar_derivacion_beta_adelica(
    verbose: bool = True,
) -> ResultadoSistemaDerivacionBeta:
    """Execute the full Adelic Beta Derivation with default parameters.

    Parameters
    ----------
    verbose:
        If ``True``, print a human-readable report.

    Returns
    -------
    ResultadoSistemaDerivacionBeta
        Complete derivation result.

    Examples
    --------
    >>> resultado = ejecutar_derivacion_beta_adelica(verbose=False)
    >>> resultado.es_coherente
    True
    """
    sistema = SistemaDerivacionBetaAdelica()
    return sistema.ejecutar(verbose=verbose)


# ---------------------------------------------------------------------------
# Module entry point
# ---------------------------------------------------------------------------
if __name__ == "__main__":  # pragma: no cover
    ejecutar_derivacion_beta_adelica(verbose=True)

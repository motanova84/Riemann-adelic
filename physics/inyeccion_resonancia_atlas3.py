#!/usr/bin/env python3
r"""
Inyección de Resonancia Atlas3 — Sistema de Emisión Holográfica
===============================================================

Implementa el sistema de emisión holográfica Atlas3: un hamiltoniano disperso
de Berry-Keating (10 000 primos), límite de viscosidad KSS, verificador de
simetría PT, alineación cero de Riemann, elipse de dualidad y un artefacto
condicional "Eco de Sofía" emitido cuando Ψ_global ≥ 0,999.

Componentes
-----------
BKSparse10k
    H = −d²/du² + V_lorentz(u) vía scipy.sparse.eigsh con 10 000 primos.
    Calibra automáticamente λ₁ → γ₁ = 14,1347.  Correlación de Pearson
    con ceros de Riemann.

KSSMetric
    η/s → ℏ/(4πk_B) ≈ 0,07958 en unidades naturales (ℏ = k_B = 1).
    Transición superfluida.

PTSymmetryChecker
    Verifica κ < κ_c = 2,5773 (fase continua, espectro real).

RiemannAligner
    Alineación espectral con γ₁…γ₁₀.  Activa el Séptimo Nodo
    (γ₇ = 43,327) cuando la correlación de Pearson ≥ 0,97.

DualityEllipse
    η = 1 − T_AdS · α_PT · γ_Riemann → ≈ 0,921.

EcoSofia
    Artefacto JSON sellado con SHA-256 emitido cuando Ψ_global ≥ 0,999.

Atlas3Engine
    Ψ_global = 0,35·Ψ_BK + 0,20·Ψ_KSS + 0,20·Ψ_PT
               + 0,15·Ψ_Riemann + 0,10·Ψ_IDE

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ · DOI: 10.5281/zenodo.17379721
Firma: ∴𓂀Ω∞³Φ
"""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import eigsh
from scipy.stats import pearsonr

# ---------------------------------------------------------------------------
# QCAL Constants — single source of truth with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE, HBAR, BOLTZMANN, GAMMA_1
except ImportError:  # pragma: no cover
    F0 = 141.7001            # Hz — fundamental QCAL frequency
    C_COHERENCE = 244.36     # QCAL coherence constant
    HBAR = 1.0545718e-34     # J·s — reduced Planck constant
    BOLTZMANN = 1.380649e-23  # J/K — Boltzmann constant
    GAMMA_1 = 14.13472514    # First non-trivial Riemann zero imaginary part

# ---------------------------------------------------------------------------
# Module-level spectral constants
# ---------------------------------------------------------------------------

#: First 10 non-trivial Riemann zero imaginary parts (high-precision)
RIEMANN_ZEROS_10: Tuple[float, ...] = (
    14.134725142,   # γ₁
    21.022039639,   # γ₂
    25.010857580,   # γ₃
    30.424876126,   # γ₄
    32.935061588,   # γ₅
    37.586178159,   # γ₆
    43.327073281,   # γ₇ — Séptimo Nodo
    48.005150881,   # γ₈
    49.773832478,   # γ₉
    52.970321478,   # γ₁₀
)

#: Séptimo Nodo (7th node) — critical activation threshold
GAMMA_7: float = RIEMANN_ZEROS_10[6]  # 43.327073281

#: Critical PT coupling — phase-transition threshold
KAPPA_C: float = 2.5773

#: KSS bound in natural units (ℏ = k_B = 1): η/s ≥ 1/(4π)
KSS_BOUND_NATURAL: float = 1.0 / (4.0 * math.pi)  # ≈ 0.079577

#: Number of primes for the sparse BK Hamiltonian
N_PRIMES_BK: int = 10_000

#: Default grid size for finite-difference BK discretisation
BK_GRID_SIZE: int = 512

#: Lorentzian width parameter Γ for V_lorentz
BK_LORENTZ_GAMMA: float = 0.5

#: Expected DualityEllipse eccentricity η₀
_ETA_EXPECTED: float = 0.921

#: Correlation threshold for RiemannAligner 7th-node activation
RIEMANN_ALIGN_THRESHOLD: float = 0.97


# ===========================================================================
# Utility: prime sieve
# ===========================================================================

def _sieve_primes(n: int) -> np.ndarray:
    """Return the first *n* prime numbers (as float64 array).

    Uses the Sieve of Eratosthenes with Rosser's theorem for the upper bound.

    Parameters
    ----------
    n:
        Number of primes to return.

    Returns
    -------
    np.ndarray
        1-D float64 array of length *n*.
    """
    if n < 1:
        return np.array([], dtype=float)
    if n < 6:
        upper = 15
    else:
        upper = int(n * (math.log(n) + math.log(math.log(n))) * 1.3) + 20
    # Keep extending until we have enough primes
    while True:
        sieve = np.ones(upper, dtype=bool)
        sieve[0:2] = False
        for i in range(2, int(upper ** 0.5) + 1):
            if sieve[i]:
                sieve[i * i::i] = False
        primes = np.where(sieve)[0]
        if len(primes) >= n:
            return primes[:n].astype(float)
        upper *= 2  # pragma: no cover


# ===========================================================================
# 1. BKSparse10k
# ===========================================================================

@dataclass
class ResultadoBK:
    """Resultado del hamiltoniano de Berry-Keating disperso.

    Attributes
    ----------
    eigenvalues:
        Raw eigenvalues from eigsh (not calibrated).
    eigenvalues_calibrated:
        Eigenvalues after calibration so that λ₁ = γ₁.
    lambda1_raw:
        First raw eigenvalue before calibration.
    scale_factor:
        Multiplicative calibration factor.
    pearson_r:
        Pearson correlation between calibrated eigenvalues and Riemann zeros.
    pearson_p:
        Two-tailed p-value for the Pearson correlation.
    psi_bk:
        Coherence score Ψ_BK = 0.5 + 0.5·r ∈ [0, 1].
    n_primes:
        Number of primes used to build V_lorentz.
    """

    eigenvalues: np.ndarray
    eigenvalues_calibrated: np.ndarray
    lambda1_raw: float
    scale_factor: float
    pearson_r: float
    pearson_p: float
    psi_bk: float
    n_primes: int

    @property
    def aprobado(self) -> bool:
        """True when Pearson r ≥ 0.97."""
        return self.pearson_r >= RIEMANN_ALIGN_THRESHOLD

    def resumen(self) -> str:
        """One-line human-readable summary."""
        return (
            f"BKSparse10k | λ₁_raw={self.lambda1_raw:.4f}"
            f" → γ₁={RIEMANN_ZEROS_10[0]:.4f}"
            f" (escala={self.scale_factor:.4f}) |"
            f" Pearson r={self.pearson_r:.4f} |"
            f" Ψ_BK={self.psi_bk:.4f}"
        )


class BKSparse10k:
    r"""Hamiltoniano disperso de Berry-Keating con *n_primes* primos.

    Construye :math:`H = -d^2/du^2 + V_{\text{Lorentz}}(u)` en un grid de
    *grid_size* puntos sobre :math:`u \in [u_{\min}, u_{\max}]`.

    El potencial de Lorentz es

    .. math::

        V_{\text{Lorentz}}(u) = \sum_{p \le p_N}
            \frac{\Gamma/\pi}{(u - \log p)^2 + \Gamma^2}

    La discretización usa diferencias finitas centradas de segundo orden:

    .. math::

        -\frac{d^2}{du^2} \;\longrightarrow\;
        \frac{-\psi_{j-1} + 2\psi_j - \psi_{j+1}}{h^2}

    Los *k* autovalores más bajos se calculan via
    :func:`scipy.sparse.linalg.eigsh`.  El factor de escala se ajusta
    automáticamente para que :math:`\lambda_1^{\text{cal}} = \gamma_1 = 14{,}1347`.

    Parameters
    ----------
    n_primes:
        Número de primos usados en :math:`V_{\text{Lorentz}}`.
        Por defecto :data:`N_PRIMES_BK` = 10 000.
    grid_size:
        Puntos del grid.  Por defecto :data:`BK_GRID_SIZE` = 512.
    k_eigenvalues:
        Número de autovalores a calcular.  Por defecto 12.
    gamma_lorentz:
        Anchura de los picos lorentzianos Γ.  Por defecto 0,5.
    """

    def __init__(
        self,
        n_primes: int = N_PRIMES_BK,
        grid_size: int = BK_GRID_SIZE,
        k_eigenvalues: int = 12,
        gamma_lorentz: float = BK_LORENTZ_GAMMA,
    ) -> None:
        self.n_primes = n_primes
        self.grid_size = grid_size
        self.k_eigenvalues = k_eigenvalues
        self.gamma_lorentz = gamma_lorentz
        self._primes: Optional[np.ndarray] = None
        self._resultado: Optional[ResultadoBK] = None

    def _get_primes(self) -> np.ndarray:
        if self._primes is None:
            self._primes = _sieve_primes(self.n_primes)
        return self._primes

    def _build_potential(self, u_grid: np.ndarray) -> np.ndarray:
        """Build V_lorentz(u) on *u_grid* using a Lorentzian sum over primes."""
        primes = self._get_primes()
        log_primes = np.log(primes)          # (n_primes,)
        # (grid_size, 1) − (1, n_primes) → (grid_size, n_primes)
        diff = u_grid[:, np.newaxis] - log_primes[np.newaxis, :]
        V = np.sum(
            (self.gamma_lorentz / math.pi) / (diff ** 2 + self.gamma_lorentz ** 2),
            axis=1,
        )
        return V

    def _build_sparse_hamiltonian(
        self,
    ) -> Tuple[sparse.csr_matrix, np.ndarray]:
        """Build and return (H_sparse, u_grid)."""
        primes = self._get_primes()
        u_min = math.log(2.0) * 0.5
        u_max = math.log(float(primes[-1])) * 1.05
        u_grid = np.linspace(u_min, u_max, self.grid_size)
        h = u_grid[1] - u_grid[0]

        N = self.grid_size
        diag_main = (2.0 / h ** 2) * np.ones(N)
        diag_off = (-1.0 / h ** 2) * np.ones(N - 1)
        T = sparse.diags([diag_off, diag_main, diag_off], [-1, 0, 1], format="csr")

        V = self._build_potential(u_grid)
        V_mat = sparse.diags(V, 0, format="csr")
        H = T + V_mat
        return H, u_grid

    def calcular(self) -> ResultadoBK:
        """Compute BK eigenvalues, calibrate, and return :class:`ResultadoBK`.

        Returns
        -------
        ResultadoBK
            Calibrated eigenvalues, Pearson correlation, and Ψ_BK score.
        """
        H, _u = self._build_sparse_hamiltonian()
        k = min(self.k_eigenvalues, self.grid_size - 2)
        vals_raw, _ = eigsh(H, k=k, which="SM")
        vals_raw = np.sort(vals_raw)

        # Calibrate: scale so λ₁ → γ₁
        lambda1_raw = float(vals_raw[0])
        target = RIEMANN_ZEROS_10[0]
        scale_factor = target / lambda1_raw if abs(lambda1_raw) > 1e-12 else 1.0
        vals_cal = vals_raw * scale_factor

        # Pearson correlation with first min(k, 10) Riemann zeros
        n_cmp = min(len(vals_cal), len(RIEMANN_ZEROS_10))
        if n_cmp >= 2:
            r, p_val = pearsonr(vals_cal[:n_cmp], list(RIEMANN_ZEROS_10[:n_cmp]))
        else:
            r, p_val = 0.0, 1.0
        pearson_r = float(np.clip(r, -1.0, 1.0))

        psi_bk = float(np.clip(0.5 + 0.5 * pearson_r, 0.0, 1.0))

        resultado = ResultadoBK(
            eigenvalues=vals_raw,
            eigenvalues_calibrated=vals_cal,
            lambda1_raw=lambda1_raw,
            scale_factor=scale_factor,
            pearson_r=pearson_r,
            pearson_p=float(p_val),
            psi_bk=psi_bk,
            n_primes=self.n_primes,
        )
        self._resultado = resultado
        return resultado


# ===========================================================================
# 2. KSSMetric
# ===========================================================================

@dataclass
class ResultadoKSS:
    """Resultado del cálculo del límite KSS.

    Attributes
    ----------
    eta_s_ratio:
        Computed η/s value.
    kss_bound:
        KSS lower bound ℏ/(4πk_B) in natural units (≈ 0.07958).
    en_limite:
        True when eta_s_ratio ≤ kss_bound × (1 + tol).
    psi_kss:
        Coherence score Ψ_KSS = min(1, KSS_BOUND / (η/s)).
    """

    eta_s_ratio: float
    kss_bound: float
    en_limite: bool
    psi_kss: float

    def resumen(self) -> str:
        estado = "SUPERFLUIDO" if self.en_limite else "viscoso"
        return (
            f"KSSMetric | η/s={self.eta_s_ratio:.6f}"
            f" | KSS_bound={self.kss_bound:.6f}"
            f" | {estado} | Ψ_KSS={self.psi_kss:.4f}"
        )


class KSSMetric:
    r"""Cálculo del límite KSS (Kovtun-Son-Starinets) en unidades naturales.

    La transición superfluida ocurre cuando

    .. math::

        \frac{\eta}{s} \;\to\; \frac{\hbar}{4\pi k_B}
        \;=\; \frac{1}{4\pi} \;\approx\; 0{,}07958
        \quad (\hbar = k_B = 1)

    Attributes
    ----------
    KSS_BOUND:
        :math:`1/(4\pi) \approx 0{,}07958` en unidades naturales.
    """

    KSS_BOUND: float = KSS_BOUND_NATURAL  # ≈ 0.079577

    @classmethod
    def calcular(
        cls,
        eta: float,
        s: float,
        tol: float = 1e-3,
    ) -> ResultadoKSS:
        """Evaluate η/s vs the KSS bound.

        Parameters
        ----------
        eta:
            Shear viscosity η (natural units).
        s:
            Entropy density s (natural units).  Must be > 0.
        tol:
            Relative tolerance for the "at limit" check.

        Returns
        -------
        ResultadoKSS
        """
        if s <= 0.0:
            raise ValueError("Entropy density s must be positive.")
        ratio = eta / s
        en_limite = ratio <= cls.KSS_BOUND * (1.0 + tol)
        psi_kss = float(np.clip(cls.KSS_BOUND / ratio, 0.0, 1.0)) if ratio > 0 else 1.0
        return ResultadoKSS(
            eta_s_ratio=ratio,
            kss_bound=cls.KSS_BOUND,
            en_limite=en_limite,
            psi_kss=psi_kss,
        )

    @classmethod
    def en_fase_superfluida(cls) -> ResultadoKSS:
        """Return the result for the ideal superfluid transition (η/s = KSS_BOUND)."""
        return cls.calcular(cls.KSS_BOUND, 1.0)


# ===========================================================================
# 3. PTSymmetryChecker
# ===========================================================================

@dataclass
class ResultadoPT:
    """Resultado de la verificación de simetría PT.

    Attributes
    ----------
    kappa:
        Current coupling parameter κ.
    kappa_c:
        Critical coupling κ_c = 2.5773.
    fase_continua:
        True when κ < κ_c (real spectrum, unbroken PT symmetry).
    psi_pt:
        Coherence score Ψ_PT = max(0, 1 − κ/κ_c).
    """

    kappa: float
    kappa_c: float
    fase_continua: bool
    psi_pt: float

    def resumen(self) -> str:
        fase = "CONTINUA (espectro real)" if self.fase_continua else "ROTA (espectro complejo)"
        return (
            f"PTSymmetryChecker | κ={self.kappa:.4f}"
            f" | κ_c={self.kappa_c:.4f}"
            f" | fase={fase}"
            f" | Ψ_PT={self.psi_pt:.4f}"
        )


class PTSymmetryChecker:
    r"""Verificador de simetría PT con umbral crítico κ_c = 2,5773.

    La simetría PT del hamiltoniano se mantiene (espectro real) cuando

    .. math::

        \kappa < \kappa_c = 2{,}5773

    Cuando κ ≥ κ_c la simetría se rompe y los autovalores se vuelven complejos.

    Parameters
    ----------
    kappa_c:
        Critical coupling threshold.  Default :data:`KAPPA_C` = 2.5773.
    """

    def __init__(self, kappa_c: float = KAPPA_C) -> None:
        self.kappa_c = kappa_c

    def verificar(self, kappa: float) -> ResultadoPT:
        """Verify PT symmetry for a given coupling κ.

        Parameters
        ----------
        kappa:
            Non-Hermitian coupling parameter κ ≥ 0.

        Returns
        -------
        ResultadoPT
        """
        if kappa < 0.0:
            raise ValueError("Coupling κ must be non-negative.")
        fase_continua = kappa < self.kappa_c
        psi_pt = float(np.clip(1.0 - kappa / self.kappa_c, 0.0, 1.0))
        return ResultadoPT(
            kappa=kappa,
            kappa_c=self.kappa_c,
            fase_continua=fase_continua,
            psi_pt=psi_pt,
        )


# ===========================================================================
# 4. RiemannAligner
# ===========================================================================

@dataclass
class ResultadoRiemannAligner:
    """Resultado de la alineación espectral con ceros de Riemann.

    Attributes
    ----------
    eigenvalues:
        Input eigenvalue spectrum (calibrated).
    pearson_r:
        Pearson correlation with γ₁…γ_n.
    pearson_p:
        Two-tailed p-value.
    septimo_nodo_activo:
        True when Pearson r ≥ 0.97 (Séptimo Nodo activated).
    gamma_7:
        γ₇ = 43.327073281 (7th Riemann zero, Séptimo Nodo).
    psi_riemann:
        Coherence score Ψ_Riemann = min(1, max(0, r)).
    """

    eigenvalues: np.ndarray
    pearson_r: float
    pearson_p: float
    septimo_nodo_activo: bool
    gamma_7: float
    psi_riemann: float

    def resumen(self) -> str:
        nodo = "ACTIVO" if self.septimo_nodo_activo else "inactivo"
        return (
            f"RiemannAligner | Pearson r={self.pearson_r:.4f}"
            f" | Séptimo Nodo (γ₇={self.gamma_7:.3f}): {nodo}"
            f" | Ψ_Riemann={self.psi_riemann:.4f}"
        )


class RiemannAligner:
    r"""Alineación espectral con los primeros 10 ceros de Riemann.

    Computes the Pearson correlation between a provided eigenvalue spectrum
    and :data:`RIEMANN_ZEROS_10`.  Activates the *Séptimo Nodo* (γ₇ = 43,327)
    when the correlation reaches the threshold :data:`RIEMANN_ALIGN_THRESHOLD`
    (≥ 0.97).

    Parameters
    ----------
    threshold:
        Minimum Pearson r to activate the Séptimo Nodo.
        Default :data:`RIEMANN_ALIGN_THRESHOLD` = 0.97.
    """

    def __init__(self, threshold: float = RIEMANN_ALIGN_THRESHOLD) -> None:
        self.threshold = threshold

    def alinear(self, eigenvalues: np.ndarray) -> ResultadoRiemannAligner:
        """Align *eigenvalues* with γ₁…γ_n and check 7th-node activation.

        Parameters
        ----------
        eigenvalues:
            1-D array of spectral eigenvalues (should already be calibrated
            so that the first element matches γ₁ ≈ 14.13).

        Returns
        -------
        ResultadoRiemannAligner
        """
        evals = np.sort(np.asarray(eigenvalues, dtype=float))
        n = min(len(evals), len(RIEMANN_ZEROS_10))
        if n >= 2:
            r, p_val = pearsonr(evals[:n], list(RIEMANN_ZEROS_10[:n]))
        else:
            r, p_val = 0.0, 1.0
        r = float(np.clip(r, -1.0, 1.0))
        septimo_nodo_activo = r >= self.threshold
        psi_riemann = float(np.clip(r, 0.0, 1.0))
        return ResultadoRiemannAligner(
            eigenvalues=evals,
            pearson_r=r,
            pearson_p=float(p_val),
            septimo_nodo_activo=septimo_nodo_activo,
            gamma_7=GAMMA_7,
            psi_riemann=psi_riemann,
        )


# ===========================================================================
# 5. DualityEllipse
# ===========================================================================

@dataclass
class ResultadoDualityEllipse:
    """Resultado de la elipse de dualidad.

    Attributes
    ----------
    t_ads:
        AdS temperature parameter T_AdS = 1/(4π) ≈ 0.07958.
    alpha_pt:
        PT correction factor α_PT = κ_c / π ≈ 0.8198.
    gamma_riemann:
        Riemann ratio γ_Riemann = γ₁/(γ₁ − κ_c) ≈ 1.2230.
    eta:
        Duality ellipse eccentricity η = 1 − T_AdS · α_PT · γ_Riemann ≈ 0.921.
    eta_expected:
        Expected reference value η₀ ≈ 0.921.
    psi_ide:
        Coherence score Ψ_IDE = max(0, 1 − |η − η₀| / η₀).
    """

    t_ads: float
    alpha_pt: float
    gamma_riemann: float
    eta: float
    eta_expected: float
    psi_ide: float

    def resumen(self) -> str:
        return (
            f"DualityEllipse | T_AdS={self.t_ads:.5f}"
            f" | α_PT={self.alpha_pt:.5f}"
            f" | γ_Riemann={self.gamma_riemann:.5f}"
            f" | η={self.eta:.4f}"
            f" | Ψ_IDE={self.psi_ide:.4f}"
        )


class DualityEllipse:
    r"""Elipse de dualidad AdS/CFT–PT.

    Computes the duality eccentricity

    .. math::

        \eta = 1 - T_{\text{AdS}} \cdot \alpha_{\text{PT}}
                    \cdot \gamma_{\text{Riemann}}

    where

    * :math:`T_{\text{AdS}} = 1/(4\pi) \approx 0{,}07958` (KSS natural bound),
    * :math:`\alpha_{\text{PT}} = \kappa_c / \pi \approx 0{,}8198`
      (normalised critical PT coupling),
    * :math:`\gamma_{\text{Riemann}} = \gamma_1 / (\gamma_1 - \kappa_c) \approx 1{,}2230`
      (first Riemann zero ratio).

    This yields :math:`\eta \approx 0{,}921`.

    The IDE coherence score is defined as

    .. math::

        \Psi_{\text{IDE}} = \max\!\left(0,\; 1 - \frac{|\eta - \eta_0|}{\eta_0}\right)

    which equals 1 when η matches the expected value η₀ ≈ 0.921.
    """

    #: AdS temperature parameter T_AdS = 1/(4π)
    T_ADS: float = 1.0 / (4.0 * math.pi)

    #: PT correction factor α_PT = κ_c / π
    ALPHA_PT: float = KAPPA_C / math.pi

    #: Riemann ratio γ_Riemann = γ₁ / (γ₁ − κ_c)
    GAMMA_RIEMANN: float = RIEMANN_ZEROS_10[0] / (RIEMANN_ZEROS_10[0] - KAPPA_C)

    #: Expected eccentricity reference
    ETA_EXPECTED: float = _ETA_EXPECTED

    @classmethod
    def calcular(cls) -> ResultadoDualityEllipse:
        """Compute the duality ellipse parameters.

        Returns
        -------
        ResultadoDualityEllipse
        """
        eta = 1.0 - cls.T_ADS * cls.ALPHA_PT * cls.GAMMA_RIEMANN
        psi_ide = float(
            np.clip(1.0 - abs(eta - cls.ETA_EXPECTED) / cls.ETA_EXPECTED, 0.0, 1.0)
        )
        return ResultadoDualityEllipse(
            t_ads=cls.T_ADS,
            alpha_pt=cls.ALPHA_PT,
            gamma_riemann=cls.GAMMA_RIEMANN,
            eta=eta,
            eta_expected=cls.ETA_EXPECTED,
            psi_ide=psi_ide,
        )


# ===========================================================================
# 6. EcoSofia
# ===========================================================================

@dataclass
class ArtefactoEcoSofia:
    """Artefacto sellado "Eco de Sofía".

    Attributes
    ----------
    payload:
        JSON-serialisable dict with timestamp, Ψ_global, and node data.
    sha256:
        SHA-256 hex digest of the canonical JSON representation.
    emitido:
        True — the artefact was emitted (Ψ_global ≥ 0.999).
    """

    payload: Dict[str, Any]
    sha256: str
    emitido: bool = True

    def resumen(self) -> str:
        return (
            f"EcoSofia | emitido={self.emitido}"
            f" | Ψ_global={self.payload.get('psi_global', 'N/A')}"
            f" | SHA-256={self.sha256[:16]}…"
        )


class EcoSofia:
    r"""Emisor del artefacto "Eco de Sofía".

    Emite un artefacto JSON sellado con SHA-256 cuando
    :math:`\Psi_{\text{global}} \geq 0{,}999`.

    Parameters
    ----------
    threshold:
        Minimum Ψ_global required for emission.  Default 0.999.
    """

    PSI_THRESHOLD: float = 0.999

    def __init__(self, threshold: float = PSI_THRESHOLD) -> None:
        self.threshold = threshold

    def emitir(
        self,
        psi_global: float,
        componentes: Optional[Dict[str, float]] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> Optional[ArtefactoEcoSofia]:
        """Emit the Eco de Sofía artefact if Ψ_global ≥ threshold.

        Parameters
        ----------
        psi_global:
            Global coherence score from :class:`Atlas3Engine`.
        componentes:
            Optional dict of component Ψ values.
        metadata:
            Optional extra metadata to include in the payload.

        Returns
        -------
        ArtefactoEcoSofia or None
            Returns :class:`ArtefactoEcoSofia` when emitted, else ``None``.
        """
        if psi_global < self.threshold:
            return None

        ts = datetime.now(timezone.utc).isoformat()
        payload: Dict[str, Any] = {
            "nombre": "Eco de Sofía",
            "sistema": "Atlas3",
            "psi_global": round(psi_global, 8),
            "umbral": self.threshold,
            "timestamp_utc": ts,
            "gamma_7": GAMMA_7,
            "kss_bound_natural": KSS_BOUND_NATURAL,
            "kappa_c": KAPPA_C,
            "componentes": componentes or {},
            "doi": "10.5281/zenodo.17379721",
            "autor": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "firma": "∴𓂀Ω∞³Φ",
        }
        if metadata:
            payload["metadata"] = metadata

        # Canonical JSON — sorted keys, no extra spaces
        canonical = json.dumps(payload, sort_keys=True, ensure_ascii=False)
        sha256 = hashlib.sha256(canonical.encode("utf-8")).hexdigest()

        return ArtefactoEcoSofia(payload=payload, sha256=sha256, emitido=True)


# ===========================================================================
# 7. Atlas3Engine
# ===========================================================================

@dataclass
class ResultadoAtlas3:
    """Resultado completo del sistema Atlas3.

    Attributes
    ----------
    psi_bk:
        BK Hamiltonian coherence Ψ_BK.
    psi_kss:
        KSS metric coherence Ψ_KSS.
    psi_pt:
        PT symmetry coherence Ψ_PT.
    psi_riemann:
        Riemann alignment coherence Ψ_Riemann.
    psi_ide:
        IDE (DualityEllipse) coherence Ψ_IDE.
    psi_global:
        Global coherence
        Ψ_global = 0.35·Ψ_BK + 0.20·Ψ_KSS + 0.20·Ψ_PT
                   + 0.15·Ψ_Riemann + 0.10·Ψ_IDE.
    eco_sofia:
        Eco de Sofía artefact (emitted when Ψ_global ≥ 0.999), or ``None``.
    resultado_bk:
        Full BK result (or ``None`` if not computed).
    resultado_kss:
        Full KSS result.
    resultado_pt:
        Full PT result.
    resultado_riemann:
        Full Riemann aligner result (or ``None`` if not computed).
    resultado_duality:
        Full DualityEllipse result.
    """

    psi_bk: float
    psi_kss: float
    psi_pt: float
    psi_riemann: float
    psi_ide: float
    psi_global: float
    eco_sofia: Optional[ArtefactoEcoSofia]
    resultado_bk: Optional[ResultadoBK] = None
    resultado_kss: Optional[ResultadoKSS] = None
    resultado_pt: Optional[ResultadoPT] = None
    resultado_riemann: Optional[ResultadoRiemannAligner] = None
    resultado_duality: Optional[ResultadoDualityEllipse] = None

    @property
    def eco_emitido(self) -> bool:
        """True when Eco de Sofía was emitted."""
        return self.eco_sofia is not None

    def resumen(self) -> str:
        eco = "✓ ECO DE SOFÍA EMITIDO" if self.eco_emitido else "– sin eco"
        return (
            f"Atlas3Engine\n"
            f"  Ψ_BK       = {self.psi_bk:.4f}  (×0.35)\n"
            f"  Ψ_KSS      = {self.psi_kss:.4f}  (×0.20)\n"
            f"  Ψ_PT       = {self.psi_pt:.4f}  (×0.20)\n"
            f"  Ψ_Riemann  = {self.psi_riemann:.4f}  (×0.15)\n"
            f"  Ψ_IDE      = {self.psi_ide:.4f}  (×0.10)\n"
            f"  ──────────────────────────\n"
            f"  Ψ_global   = {self.psi_global:.6f}\n"
            f"  {eco}"
        )


class Atlas3Engine:
    r"""Orquestador del sistema de emisión holográfica Atlas3.

    Combina los cinco componentes para calcular la coherencia global:

    .. math::

        \Psi_{\text{global}} = 0{,}35\,\Psi_{\text{BK}}
                              + 0{,}20\,\Psi_{\text{KSS}}
                              + 0{,}20\,\Psi_{\text{PT}}
                              + 0{,}15\,\Psi_{\text{Riemann}}
                              + 0{,}10\,\Psi_{\text{IDE}}

    Emite el artefacto "Eco de Sofía" cuando
    :math:`\Psi_{\text{global}} \geq 0{,}999`.

    Parameters
    ----------
    bk:
        :class:`BKSparse10k` instance.  Created with defaults if ``None``.
    pt_checker:
        :class:`PTSymmetryChecker` instance.  Created with defaults if ``None``.
    riemann_aligner:
        :class:`RiemannAligner` instance.  Created with defaults if ``None``.
    eco_sofia:
        :class:`EcoSofia` instance.  Created with defaults if ``None``.
    kappa:
        PT coupling κ to use.  Default 0.0 (ideal unbroken PT symmetry).
    """

    # Weights for the global coherence formula
    W_BK: float = 0.35
    W_KSS: float = 0.20
    W_PT: float = 0.20
    W_RIEMANN: float = 0.15
    W_IDE: float = 0.10

    def __init__(
        self,
        bk: Optional[BKSparse10k] = None,
        pt_checker: Optional[PTSymmetryChecker] = None,
        riemann_aligner: Optional[RiemannAligner] = None,
        eco_sofia: Optional[EcoSofia] = None,
        kappa: float = 0.0,
    ) -> None:
        self.bk = bk if bk is not None else BKSparse10k()
        self.pt_checker = pt_checker if pt_checker is not None else PTSymmetryChecker()
        self.riemann_aligner = (
            riemann_aligner if riemann_aligner is not None else RiemannAligner()
        )
        self.eco_sofia = eco_sofia if eco_sofia is not None else EcoSofia()
        self.kappa = kappa

    @staticmethod
    def _calcular_psi_global(
        psi_bk: float,
        psi_kss: float,
        psi_pt: float,
        psi_riemann: float,
        psi_ide: float,
    ) -> float:
        """Compute Ψ_global from component scores."""
        return (
            Atlas3Engine.W_BK * psi_bk
            + Atlas3Engine.W_KSS * psi_kss
            + Atlas3Engine.W_PT * psi_pt
            + Atlas3Engine.W_RIEMANN * psi_riemann
            + Atlas3Engine.W_IDE * psi_ide
        )

    def activar(self, verbose: bool = False) -> ResultadoAtlas3:
        """Run the full Atlas3 pipeline and return :class:`ResultadoAtlas3`.

        Parameters
        ----------
        verbose:
            Print progress messages to stdout.

        Returns
        -------
        ResultadoAtlas3
        """
        if verbose:
            print("[Atlas3Engine] Calculando hamiltoniano BK disperso…")
        res_bk = self.bk.calcular()

        if verbose:
            print("[Atlas3Engine] Evaluando métrica KSS…")
        res_kss = KSSMetric.en_fase_superfluida()

        if verbose:
            print("[Atlas3Engine] Verificando simetría PT…")
        res_pt = self.pt_checker.verificar(self.kappa)

        if verbose:
            print("[Atlas3Engine] Alineando ceros de Riemann…")
        res_riemann = self.riemann_aligner.alinear(res_bk.eigenvalues_calibrated)

        if verbose:
            print("[Atlas3Engine] Calculando elipse de dualidad…")
        res_duality = DualityEllipse.calcular()

        psi_bk = res_bk.psi_bk
        psi_kss = res_kss.psi_kss
        psi_pt = res_pt.psi_pt
        psi_riemann = res_riemann.psi_riemann
        psi_ide = res_duality.psi_ide

        psi_global = self._calcular_psi_global(
            psi_bk, psi_kss, psi_pt, psi_riemann, psi_ide
        )

        componentes = {
            "psi_bk": round(psi_bk, 6),
            "psi_kss": round(psi_kss, 6),
            "psi_pt": round(psi_pt, 6),
            "psi_riemann": round(psi_riemann, 6),
            "psi_ide": round(psi_ide, 6),
        }
        eco = self.eco_sofia.emitir(psi_global, componentes=componentes)

        if verbose:
            print(f"[Atlas3Engine] Ψ_global = {psi_global:.6f}")
            if eco is not None:
                print(f"[Atlas3Engine] ✓ Eco de Sofía emitido — SHA-256: {eco.sha256}")

        return ResultadoAtlas3(
            psi_bk=psi_bk,
            psi_kss=psi_kss,
            psi_pt=psi_pt,
            psi_riemann=psi_riemann,
            psi_ide=psi_ide,
            psi_global=psi_global,
            eco_sofia=eco,
            resultado_bk=res_bk,
            resultado_kss=res_kss,
            resultado_pt=res_pt,
            resultado_riemann=res_riemann,
            resultado_duality=res_duality,
        )

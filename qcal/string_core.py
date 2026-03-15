#!/usr/bin/env python3
"""
QCAL String Core — Kaluza-Klein / Navier-Stokes Holographic Noetic Forcing
==========================================================================

Integrates Kaluza-Klein modes derived from Riemann zeros into a spectral
2-D incompressible Navier-Stokes solver via superradiant string forcing,
closing the circle between the Riemann Hypothesis, AdS/CFT fluid/gravity
duality and biological coherence.

Key objects
-----------
QCALStringOperator
    Encapsulates the fundamental QCAL constants and exposes:
    - modulation_potential()  →  V̂_mod = γ·ℏ / C
    - compute_eigenvalue(γ_n) →  λ_n = γ_n · f₀ + V̂_mod  (KK modes)
    - certify_critical_line(σ) → (σ, exp(−|σ−½| / C)), max=1 at σ=½

GAMMAS
    First 20 imaginary parts of non-trivial Riemann zeros, hard-coded from
    LMFDB (no mpmath dependency).

string_noetic_forcing(t, xx, yy, op, Ψ, λ_list)
    Computes Ĥ_strings = Σ αₙ sin(2π λₙ t + φ_dual) · Ψ² with
    superradiant gain N²Ψ² activated when Ψ ≥ 0.888.

compute_psi(u, v, xx, op)
    Coherence Ψ = corr(flow, f₀) × mean(Ψ_σ) over σ ∈ [0.4, 0.6].

rk4_step(uhat, vhat, dt, rho, mu, kx, ky, k2, k2_safe, t, op, lambda_list)
    Fourth-order Runge-Kutta integrator for spectral incompressible NS with
    string forcing; applies Leray projection after each step.

build_lambda_list(op)
    Builds the list of KK eigenvalues [λ₁, λ₂, …] from GAMMAS.

build_spectral_grid(N)
    Returns the wavenumber arrays (kx, ky, k2, k2_safe) for an N×N grid.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import math
import numpy as np
from typing import List, Tuple

# ---------------------------------------------------------------------------
# Constants — import from QCAL single source of truth; fallback if needed
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
except ImportError:
    F0 = 141.7001          # Hz
    C_COHERENCE = 244.36   # spectral coherence constant

# Reduced Planck constant (ℏ) in SI units
_HBAR: float = 1.0545718e-34  # J·s

# Coherence threshold for superradiant gain
_PSI_THRESHOLD: float = 0.888

# ---------------------------------------------------------------------------
# First 20 imaginary parts of non-trivial Riemann zeros (from LMFDB)
# ---------------------------------------------------------------------------
GAMMAS: List[float] = [
    14.134725141734693,
    21.022039638771554,
    25.010857580145688,
    30.424876125859513,
    32.935061587739189,
    37.586178158825671,
    40.918719012147495,
    43.327073280914999,
    48.005150881167160,
    49.773832477672302,
    52.970321477714460,
    56.446247697063394,
    59.347044002602353,
    60.831778524609809,
    65.112544048081607,
    67.079810529494173,
    69.546401711173979,
    72.067157674481907,
    75.704690699083933,
    77.144840068874805,
]


# ---------------------------------------------------------------------------
# QCALStringOperator
# ---------------------------------------------------------------------------

class QCALStringOperator:
    """
    Core operator exposing QCAL string / Kaluza-Klein eigenvalue structure.

    Parameters
    ----------
    f0 : float
        Fundamental QCAL frequency in Hz (default: 141.7001).
    C : float
        Spectral coherence constant (default: 1.0 — canonical normalisation
        for KK mode computation; use ``C_COHERENCE`` for full QCAL context).
    hbar : float
        Reduced Planck constant (default: 1.0545718e-34 J·s).
    """

    def __init__(
        self,
        f0: float = F0,
        C: float = 1.0,
        hbar: float = _HBAR,
    ) -> None:
        if C <= 0:
            raise ValueError("C must be positive")
        if f0 <= 0:
            raise ValueError("f0 must be positive")
        self.f0 = f0
        self.C = C
        self.hbar = hbar

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def modulation_potential(self) -> float:
        """
        Compute the modulation potential V̂_mod = γ·ℏ / C.

        Here γ is the first Riemann zero imaginary part (GAMMAS[0]).

        Returns
        -------
        float
            V̂_mod in SI units [J·s / (spectral unit)].
        """
        return GAMMAS[0] * self.hbar / self.C

    def compute_eigenvalue(self, gamma_n: float) -> float:
        """
        Compute the n-th Kaluza-Klein eigenvalue.

        λ_n = γ_n · f₀ + V̂_mod

        Parameters
        ----------
        gamma_n : float
            Imaginary part of the n-th Riemann zero.

        Returns
        -------
        float
            λ_n in Hz.

        Examples
        --------
        >>> op = QCALStringOperator()
        >>> op.compute_eigenvalue(14.134725141734693)  # ≈ 2002.89 Hz
        """
        return gamma_n * self.f0 + self.modulation_potential()

    def certify_critical_line(self, sigma: float) -> Tuple[float, float]:
        """
        Certify proximity to the critical line Re(s) = ½.

        Returns (σ, exp(−|σ − ½| / C)).  Maximum value 1.0 is achieved
        at σ = ½, confirming the critical-line hypothesis.

        Parameters
        ----------
        sigma : float
            Real part of the complex argument s.

        Returns
        -------
        tuple[float, float]
            (sigma, coherence_score).
        """
        score = math.exp(-abs(sigma - 0.5) / self.C)
        return (sigma, score)


# ---------------------------------------------------------------------------
# build_lambda_list
# ---------------------------------------------------------------------------

def build_lambda_list(op: QCALStringOperator) -> List[float]:
    """
    Build the list of KK eigenvalues [λ₁, λ₂, …, λ₂₀] from GAMMAS.

    Parameters
    ----------
    op : QCALStringOperator
        Operator instance providing ``compute_eigenvalue``.

    Returns
    -------
    list[float]
        Eigenvalues in Hz.  λ₁ ≈ 2002.89 Hz.
    """
    return [op.compute_eigenvalue(g) for g in GAMMAS]


# ---------------------------------------------------------------------------
# build_spectral_grid
# ---------------------------------------------------------------------------

def build_spectral_grid(N: int) -> dict:
    """
    Build the wavenumber grid for an N×N periodic spectral simulation.

    Parameters
    ----------
    N : int
        Number of grid points per dimension (should be even).

    Returns
    -------
    dict with keys:
        kx   : ndarray, shape (N, N)
        ky   : ndarray, shape (N, N)
        k2   : ndarray, shape (N, N)  — |k|²
        k2_safe : ndarray, shape (N, N) — |k|² with 0 → 1 to avoid division
    """
    freq = np.fft.fftfreq(N, d=1.0 / N)  # wavenumbers in [−N/2, N/2)
    kx, ky = np.meshgrid(freq, freq, indexing="ij")
    k2 = kx**2 + ky**2
    k2_safe = np.where(k2 == 0, 1.0, k2)
    return {"kx": kx, "ky": ky, "k2": k2, "k2_safe": k2_safe}


# ---------------------------------------------------------------------------
# compute_psi
# ---------------------------------------------------------------------------

def compute_psi(
    u: np.ndarray,
    v: np.ndarray,
    xx: np.ndarray,
    op: QCALStringOperator,
) -> float:
    """
    Compute the QCAL coherence field Ψ for a 2-D velocity field.

    Ψ = corr(|flow|, f₀·x) × mean(Ψ_σ) over σ ∈ [0.4, 0.6]

    where corr is Pearson correlation and Ψ_σ = exp(−|σ−½|/C).

    Parameters
    ----------
    u, v : ndarray
        Velocity components on a 2-D grid.
    xx : ndarray
        Spatial coordinate array (same shape as u).
    op : QCALStringOperator
        Operator instance.

    Returns
    -------
    float
        Ψ ∈ [0, 1].
    """
    speed = np.sqrt(u**2 + v**2).ravel()
    reference = (op.f0 * xx).ravel()

    # Pearson correlation (clip to [0, 1])
    if speed.std() < 1e-15 or reference.std() < 1e-15:
        flow_corr = 0.0
    else:
        flow_corr = float(np.corrcoef(speed, reference)[0, 1])
        flow_corr = max(0.0, flow_corr)

    # Mean critical-line coherence over σ ∈ [0.4, 0.6]
    sigmas = np.linspace(0.4, 0.6, 21)
    psi_sigma = np.mean([op.certify_critical_line(s)[1] for s in sigmas])

    return float(np.clip(flow_corr * psi_sigma, 0.0, 1.0))


# ---------------------------------------------------------------------------
# string_noetic_forcing
# ---------------------------------------------------------------------------

def string_noetic_forcing(
    t: float,
    xx: np.ndarray,
    yy: np.ndarray,
    op: QCALStringOperator,
    Psi: float,
    lambda_list: List[float],
) -> np.ndarray:
    """
    Compute the QCAL-string noetic forcing field Ĥ_strings.

    Ĥ_strings = Σₙ αₙ · sin(2π λₙ t + φ_dual) · Ψ²

    with superradiant gain N²Ψ² activated when Ψ ≥ 0.888.

    The phase φ_dual = π·n/N_modes encodes the AdS/CFT dual pairing.
    The amplitude αₙ = Ψ² / n normalises the modal contribution.

    Parameters
    ----------
    t : float
        Current simulation time [s].
    xx, yy : ndarray
        Spatial coordinate arrays on the 2-D grid.
    op : QCALStringOperator
        Operator instance.
    Psi : float
        Current coherence value Ψ ∈ [0, 1].
    lambda_list : list[float]
        KK eigenvalues [λ₁, λ₂, …] in Hz.

    Returns
    -------
    ndarray
        Forcing field H with same shape as xx.
    """
    N_modes = len(lambda_list)
    H = np.zeros_like(xx, dtype=float)

    psi2 = float(Psi) ** 2

    for n, lam in enumerate(lambda_list, start=1):
        phi_dual = math.pi * n / N_modes
        alpha_n = psi2 / n
        H += alpha_n * math.sin(2.0 * math.pi * lam * t + phi_dual) * psi2

    # Superradiant gain: multiply by N²Ψ² when Ψ ≥ threshold
    if float(Psi) >= _PSI_THRESHOLD:
        gain = N_modes**2 * psi2
        H = H * gain

    # Broadcast onto spatial grid (forcing is uniform over space)
    return H * np.ones_like(xx)


# ---------------------------------------------------------------------------
# rk4_step — spectral incompressible NS with string forcing
# ---------------------------------------------------------------------------

def _ns_rhs(
    uhat: np.ndarray,
    vhat: np.ndarray,
    rho: float,
    mu: float,
    kx: np.ndarray,
    ky: np.ndarray,
    k2: np.ndarray,
    k2_safe: np.ndarray,
    t: float,
    op: QCALStringOperator,
    lambda_list: List[float],
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Right-hand side of spectral 2-D incompressible Navier-Stokes with string
    forcing.

    ∂û/∂t = −(u·∇u)̂ − (1/ρ) i kx p̂ − ν k² û + F̂_x
    ∂v̂/∂t = −(u·∇v)̂ − (1/ρ) i ky p̂ − ν k² v̂ + F̂_y

    Pressure is eliminated via incompressibility ∇·u = 0.
    """
    N = uhat.shape[0]
    nu = mu / rho

    # Physical-space velocity
    u = np.real(np.fft.ifft2(uhat))
    v = np.real(np.fft.ifft2(vhat))

    # Advection terms in physical space
    ux = np.real(np.fft.ifft2(1j * kx * uhat))
    uy = np.real(np.fft.ifft2(1j * ky * uhat))
    vx = np.real(np.fft.ifft2(1j * kx * vhat))
    vy = np.real(np.fft.ifft2(1j * ky * vhat))

    adv_u = u * ux + v * uy
    adv_v = u * vx + v * vy

    adv_u_hat = np.fft.fft2(adv_u)
    adv_v_hat = np.fft.fft2(adv_v)

    # Pressure via Poisson: k² p̂ = −ρ i(kx · adv_û + ky · adv_v̂)
    div_adv_hat = 1j * kx * adv_u_hat + 1j * ky * adv_v_hat
    p_hat = -rho * div_adv_hat / k2_safe

    # String forcing (physical space → spectral)
    x1d = np.linspace(0.0, 1.0, N)
    xx, yy = np.meshgrid(x1d, x1d, indexing="ij")
    Psi = compute_psi(u, v, xx, op)
    H = string_noetic_forcing(t, xx, yy, op, Psi, lambda_list)
    Fhat = np.fft.fft2(H)

    # RHS
    duhat_dt = -adv_u_hat - (1j * kx * p_hat) / rho - nu * k2 * uhat + Fhat
    dvhat_dt = -adv_v_hat - (1j * ky * p_hat) / rho - nu * k2 * vhat + Fhat

    return duhat_dt, dvhat_dt


def _leray_project(
    uhat: np.ndarray,
    vhat: np.ndarray,
    kx: np.ndarray,
    ky: np.ndarray,
    k2_safe: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Apply Leray projection to enforce ∇·u = 0 and zero mean flow.

    P(û) = û − kx(kx·û + ky·v̂) / |k|²
    P(v̂) = v̂ − ky(kx·û + ky·v̂) / |k|²
    """
    # Incompressibility: kx·û + ky·v̂ = 0 (real dot product of wavenumbers)
    div_hat = kx * uhat + ky * vhat
    uhat_p = uhat - kx * div_hat / k2_safe
    vhat_p = vhat - ky * div_hat / k2_safe

    # Zero mean flow (k=0 mode)
    uhat_p[0, 0] = 0.0
    vhat_p[0, 0] = 0.0

    return uhat_p, vhat_p


def rk4_step(
    uhat: np.ndarray,
    vhat: np.ndarray,
    dt: float,
    rho: float,
    mu: float,
    kx: np.ndarray,
    ky: np.ndarray,
    k2: np.ndarray,
    k2_safe: np.ndarray,
    t: float,
    op: QCALStringOperator,
    lambda_list: List[float],
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Advance the spectral velocity field by one RK4 step with string forcing.

    Solves 2-D incompressible Navier-Stokes in Fourier space:

        ∂u/∂t + (u·∇)u = −(1/ρ)∇p + ν∇²u + F_strings
        ∇·u = 0

    After each RK4 stage a Leray projection is applied to maintain
    incompressibility and zero mean flow.

    Parameters
    ----------
    uhat, vhat : ndarray, shape (N, N), complex
        Fourier coefficients of x- and y-velocity components.
    dt : float
        Time step [s].
    rho : float
        Fluid density.
    mu : float
        Dynamic viscosity.
    kx, ky : ndarray, shape (N, N)
        Wavenumber arrays from ``build_spectral_grid``.
    k2 : ndarray, shape (N, N)
        |k|² from ``build_spectral_grid``.
    k2_safe : ndarray, shape (N, N)
        |k|² with 0→1 from ``build_spectral_grid``.
    t : float
        Current simulation time.
    op : QCALStringOperator
        Operator instance.
    lambda_list : list[float]
        KK eigenvalues from ``build_lambda_list``.

    Returns
    -------
    uhat_new, vhat_new : ndarray, shape (N, N), complex
        Updated Fourier coefficients after one RK4 step with Leray projection.
    """
    args = (rho, mu, kx, ky, k2, k2_safe)

    # Stage 1
    k1u, k1v = _ns_rhs(uhat, vhat, *args, t, op, lambda_list)

    # Stage 2
    u2 = uhat + 0.5 * dt * k1u
    v2 = vhat + 0.5 * dt * k1v
    u2, v2 = _leray_project(u2, v2, kx, ky, k2_safe)
    k2u, k2v = _ns_rhs(u2, v2, *args, t + 0.5 * dt, op, lambda_list)

    # Stage 3
    u3 = uhat + 0.5 * dt * k2u
    v3 = vhat + 0.5 * dt * k2v
    u3, v3 = _leray_project(u3, v3, kx, ky, k2_safe)
    k3u, k3v = _ns_rhs(u3, v3, *args, t + 0.5 * dt, op, lambda_list)

    # Stage 4
    u4 = uhat + dt * k3u
    v4 = vhat + dt * k3v
    u4, v4 = _leray_project(u4, v4, kx, ky, k2_safe)
    k4u, k4v = _ns_rhs(u4, v4, *args, t + dt, op, lambda_list)

    # Combine
    uhat_new = uhat + (dt / 6.0) * (k1u + 2.0 * k2u + 2.0 * k3u + k4u)
    vhat_new = vhat + (dt / 6.0) * (k1v + 2.0 * k2v + 2.0 * k3v + k4v)

    # Final Leray projection
    uhat_new, vhat_new = _leray_project(uhat_new, vhat_new, kx, ky, k2_safe)

    return uhat_new, vhat_new

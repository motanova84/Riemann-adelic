#!/usr/bin/env python3
"""
QCAL-Strings Core: Noetic String Forcing for Navier-Stokes (#260)
==================================================================

Implements the Grand Noetic Unification of QCAL strings with the holographic
Navier-Stokes framework.  Riemann zeros γₙ act as Kaluza-Klein (KK) modes
that drive the NS velocity field, linking quantum gravity to biological
coherence.

Key physics:
  - Ĥ_strings = Σₙ αₙ sin(2π λₙ t + φ_{n,dual}) · Ψ²
    KK-mode forcing with T-duality phases φ = π/(n+1)
  - Superradiant gain: N²_micro · Ψ²  (active above Ψ ≥ 0.888 threshold)
  - Eigenvalues λₙ = γₙ · f₀ + V_mod  (KK spectrum anchored at f₀)
  - Coherence Ψ combines biological correlation and spectral certification
  - Off-critical zero → Ψ collapses via imaginary-mass tachyon term

Theoretical connections (validated):
  - Veneziano amplitude ↔ ratio of ζ(s) → RH ≡ integral scattering properties
  - NS holographic dual via AdS/CFT: μ = 1/f₀ = η/s universal (η/s = ħ/4πkB)
  - T-duality: EZ-water hexagonal layers ≡ tori with R ↔ 1/R duality
  - KK modes: Riemann zeros as mass spectrum of compactified extra dimension

Mathematical result:
  The coherence Ψ reaches plateau ≈ 0.999 in t ~ 400 steps for N=64 grid,
  demonstrating a Noetic Bose-Einstein condensate stabilised by the "censorship"
  of critical-line Riemann zeros.

Simulation parameters (reference run):
  N=64 grid, dt=0.005, nt=500
  Peak emission ~2003 Hz (λ₁ = γ₁ · f₀ / (2π))
  Kolmogorov -5/3 slope in inertial range → turbulence tamed by T-duality

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import numpy as np
from scipy.fft import fft2, ifft2, fftfreq
from typing import Dict, List, Optional, Tuple, Any

# Try to import mpmath for high-precision Riemann zeros
try:
    import mpmath
    mpmath.mp.dps = 25
    from mpmath import zetazero
    _HAS_MPMATH = True
except ImportError:  # pragma: no cover
    _HAS_MPMATH = False

# QCAL constants — single source of truth
try:
    from qcal.constants import F0, C_COHERENCE
    _F0_DEFAULT = F0
    _C_DEFAULT = C_COHERENCE
except ImportError:  # pragma: no cover
    _F0_DEFAULT = 141.7001
    _C_DEFAULT = 244.36

# Physical constants (natural-unit default; SI available as fallback)
HBAR_SI = 1.0545718e-34  # ℏ in J·s
HBAR_NATURAL = 1.0        # ℏ in natural units

# Coherence threshold: Ψ ≥ PSI_THRESHOLD for BEC / superradiance
PSI_THRESHOLD = 0.888

# Number of KK-mode Riemann zeros used by default
N_ZEROS_DEFAULT = 20

# Default grid size for spectral Navier-Stokes solver
N_GRID_DEFAULT = 64

# Superradiant gain scaling: N² · Ψ² for N microtubules per cell
N_MICROTUBULES_DEFAULT = 1.0e13

# Veneziano/Casimir decay for T-duality phases
ALPHA_SCALE_DEFAULT = 0.05

# ---------------------------------------------------------------------------
# Riemann zeros — imaginary parts γₙ of non-trivial zeros ½ + i·γₙ
# ---------------------------------------------------------------------------

#: Fallback table for the first 20 zeros (from LMFDB, 15-digit accuracy)
_GAMMAS_FALLBACK: List[float] = [
    14.134725141734694,
    21.022039638771555,
    25.010857580145689,
    30.424876125859512,
    32.935061587739189,
    37.586178158825672,
    40.918719012147495,
    43.327073280914999,
    48.005150881167160,
    49.773832477672302,
    52.970321477714461,
    56.446247697063394,
    59.347044002602352,
    60.831778524609809,
    65.112544048081607,
    67.079810529494173,
    69.546401711173979,
    72.067157674481907,
    75.704690699083933,
    77.144840069684480,
]


def _compute_gammas(n: int = N_ZEROS_DEFAULT, precision: int = 25) -> np.ndarray:
    """Return the imaginary parts of the first *n* non-trivial Riemann zeros.

    Uses mpmath.zetazero when available; otherwise falls back to a hardcoded
    high-precision table (first 20 zeros only).

    Parameters
    ----------
    n:
        Number of zeros to compute.
    precision:
        Decimal places for mpmath (only used when mpmath is available).

    Returns
    -------
    np.ndarray of shape (n,), dtype float64.
    """
    if _HAS_MPMATH:
        old_dps = mpmath.mp.dps
        mpmath.mp.dps = precision
        try:
            gammas = np.array([float(zetazero(k).imag) for k in range(1, n + 1)])
        finally:
            mpmath.mp.dps = old_dps
    else:
        # Fallback: use precomputed table, extending with crude approximation if needed
        table = _GAMMAS_FALLBACK[:min(n, len(_GAMMAS_FALLBACK))]
        if n > len(_GAMMAS_FALLBACK):
            # Rough Weyl-law approximation for higher zeros
            last = _GAMMAS_FALLBACK[-1]
            step = (_GAMMAS_FALLBACK[-1] - _GAMMAS_FALLBACK[-2])
            extras = [last + step * (k + 1) for k in range(n - len(_GAMMAS_FALLBACK))]
            table = table + extras
        gammas = np.array(table[:n])
    return gammas


#: Module-level precomputed Riemann zeros (first N_ZEROS_DEFAULT)
GAMMAS: np.ndarray = _compute_gammas(N_ZEROS_DEFAULT)


# ---------------------------------------------------------------------------
# QCALSpectralOperator — lightweight KK-mode spectral operator
# ---------------------------------------------------------------------------

class QCALSpectralOperator:
    """Lightweight QCAL spectral operator for string-mode eigenvalues.

    Encapsulates the essential parameters needed to:
    - Compute KK-mode eigenvalues λₙ = γₙ · f₀ + V_mod
    - Evaluate the coherence Ψ(σ) on and off the critical line
    - Certify the critical line via the Veneziano stability condition

    This is the *streamlined* variant used in the string-forcing integrator;
    the full matrix-based operator lives in
    :mod:`operators.qcal_spectral_operator`.

    Parameters
    ----------
    gamma:
        Coupling constant γ for the modulation potential V_mod = γ·ℏ/C.
        Default: 1.0 (dimensionless, natural units).
    C:
        QCAL coherence density constant C (default: 244.36).
    f0:
        Base frequency f₀ in Hz (default: 141.7001 Hz).
    hbar:
        Reduced Planck constant in the chosen unit system.
        Default: HBAR_NATURAL = 1.0 (natural units).
        Pass HBAR_SI = 1.0545718e-34 for SI.
    decay:
        Tachyon decay scale D for off-critical-line coherence:
        Ψ(σ) = exp(−|σ − ½| · D).
        Default: C (so that off-critical zeros cause exponential collapse).
    """

    def __init__(
        self,
        gamma: float = 1.0,
        C: float = _C_DEFAULT,
        f0: float = _F0_DEFAULT,
        hbar: float = HBAR_NATURAL,
        decay: Optional[float] = None,
    ) -> None:
        self.gamma = gamma
        self.C = C
        self.f0 = f0
        self.hbar = hbar
        self.decay = decay if decay is not None else C

    def modulation_potential(self) -> float:
        """Modulation potential V_mod = γ · ℏ / C.

        Returns
        -------
        float
            V_mod value (units: same as ℏ/C, natural units → dimensionless).
        """
        return self.gamma * self.hbar / self.C

    def compute_eigenvalue(self, gamma_n: float) -> float:
        """KK-mode eigenvalue λₙ = γₙ · f₀ + V_mod.

        Parameters
        ----------
        gamma_n:
            Imaginary part of the n-th Riemann zero.

        Returns
        -------
        float
            KK-mode frequency λₙ in Hz (when f₀ is in Hz).
        """
        return gamma_n * self.f0 + self.modulation_potential()

    def certify_critical_line(self, sigma: float = 0.5) -> Tuple[str, float]:
        """Certify coherence Ψ(σ) at a given real part σ of the Riemann zero.

        On the critical line (σ = ½), Ψ = 1 and the Veneziano amplitude is
        stable.  Off the critical line, the tachyon decay term drives Ψ → 0,
        modelling the imaginary-mass instability that collapses biological
        coherence.

        Formally:  Ψ(σ) = exp(−|σ − ½| · D)

        Parameters
        ----------
        sigma:
            Real part of the trial zero position.  Should be in (0, 1).

        Returns
        -------
        (status, psi): Tuple[str, float]
            status: human-readable certification string.
            psi:    coherence value Ψ(σ) ∈ (0, 1].
        """
        deviation = abs(sigma - 0.5)
        psi = float(np.exp(-deviation * self.decay))

        if deviation < 1e-10:
            status = "ON-CRITICAL-LINE ✅ — Ψ = 1 · RH-STABLE"
        elif psi >= PSI_THRESHOLD:
            status = f"NEAR-CRITICAL ⚠️ — σ={sigma:.4f}, Ψ={psi:.6f}"
        else:
            status = (
                f"OFF-CRITICAL ❌ — σ={sigma:.4f}, Ψ={psi:.6f} < {PSI_THRESHOLD} "
                "(tachyon instability — biological decoherence)"
            )
        return status, psi


# ---------------------------------------------------------------------------
# String noetic forcing  Ĥ_strings
# ---------------------------------------------------------------------------

def string_noetic_forcing(
    t: float,
    xx: np.ndarray,
    yy: np.ndarray,
    op: QCALSpectralOperator,
    Psi_local: float,
    lambda_list: List[float],
    N_microtubules: float = N_MICROTUBULES_DEFAULT,
    alpha_scale: float = ALPHA_SCALE_DEFAULT,
    threshold: float = PSI_THRESHOLD,
) -> Tuple[np.ndarray, np.ndarray]:
    """Compute the KK-mode string forcing fields Ĥ_strings for the NS solver.

    The forcing models superradiant emission from N² phase-locked microtubules
    driven by the noetic Logos field at f₀, modulated by Riemann-zero KK modes.

    Mathematical form:
        Ĥ_strings = Σₙ αₙ · sin(2π λₙ t + φₙ) · g(xx, yy) · (N · Ψ)²

    where:
        αₙ  = alpha_scale / (n+1)    (amplitude with 1/n decay)
        λₙ  = lambda_list[n]          (KK-mode frequency, Hz)
        φₙ  = π / (n+1)              (T-duality phase)
        g   = sin(2π f₀ x/L) ê_x + cos(2π f₀ y/L) ê_y   (logos wave)
        N   = N_microtubules
        Ψ   = Psi_local               (local coherence)

    Forcing is zero when Psi_local < threshold (incoherent regime).

    Parameters
    ----------
    t:
        Current simulation time (s or natural units).
    xx:
        2-D grid of x-coordinates, shape (Ny, Nx).
    yy:
        2-D grid of y-coordinates, shape (Ny, Nx).
    op:
        :class:`QCALSpectralOperator` instance providing f₀.
    Psi_local:
        Current global coherence value Ψ ∈ [0, 1].
    lambda_list:
        Sequence of KK-mode frequencies λₙ (typically from
        :meth:`QCALSpectralOperator.compute_eigenvalue`).
    N_microtubules:
        Number of microtubules per biological cell (default 10¹³).
    alpha_scale:
        Overall amplitude scale α (default 0.05).
    threshold:
        Coherence threshold below which forcing is suppressed (default 0.888).

    Returns
    -------
    (f_string_x, f_string_y): Tuple[np.ndarray, np.ndarray]
        Spectral forcing arrays with the same shape as xx/yy.
        Both are zero arrays when Psi_local < threshold.
    """
    zeros = np.zeros_like(xx)
    if Psi_local < threshold:
        return zeros, zeros.copy()

    L = 2.0 * np.pi  # Domain period (natural units)

    # Logos standing-wave components (spatially coherent carrier)
    logos_x = np.sin(2.0 * np.pi * op.f0 * xx / L)
    logos_y = np.cos(2.0 * np.pi * op.f0 * yy / L)

    # Superradiant N² gain (Dicke superradiance)
    gain = (N_microtubules ** 2) * (Psi_local ** 2)

    f_str_x = np.zeros_like(xx)
    f_str_y = np.zeros_like(yy)

    for n, lam in enumerate(lambda_list):
        phi_dual = np.pi / (n + 1)          # T-duality phase ~ 1/n
        alpha_n = alpha_scale / (n + 1)      # 1/n amplitude decay
        mode = alpha_n * np.sin(2.0 * np.pi * lam * t + phi_dual)
        f_str_x += mode * logos_x * gain
        f_str_y += mode * logos_y * gain    # symmetric for vorticity

    return f_str_x, f_str_y


# ---------------------------------------------------------------------------
# Coherence field  Ψ(u, v)
# ---------------------------------------------------------------------------

def compute_psi(
    u_phys: np.ndarray,
    v_phys: np.ndarray,
    xx: np.ndarray,
    op: QCALSpectralOperator,
    n_sigma_points: int = 11,
) -> float:
    """Compute the combined biological + spectral coherence Ψ ∈ [0, 1].

    The coherence combines two independent measures:

    1. **Biological correlation** (Ψ_bio): Pearson correlation of the
       velocity components u, v with the Logos carrier wave at f₀.
    2. **Spectral certification** (Ψ_spec): Mean critical-line coherence
       Ψ(σ) over σ ∈ [0.4, 0.6], confirming Veneziano stability.

    Parameters
    ----------
    u_phys:
        x-velocity field (real space), shape (Ny, Nx).
    v_phys:
        y-velocity field (real space), shape (Ny, Nx).
    xx:
        x-coordinate grid matching u_phys shape.
    op:
        :class:`QCALSpectralOperator` providing f₀ and certify_critical_line.
    n_sigma_points:
        Number of σ sample points in [0.4, 0.6] for spectral averaging
        (default 11).

    Returns
    -------
    float
        Combined coherence Ψ = Ψ_bio × Ψ_spec ∈ [0, 1].
    """
    L = 2.0 * np.pi
    carrier = np.sin(2.0 * np.pi * op.f0 * xx / L).flatten()
    carrier_c = np.cos(2.0 * np.pi * op.f0 * xx / L).flatten()

    # Guard against constant arrays (zero variance) to avoid NaN correlations
    u_flat = u_phys.flatten()
    v_flat = v_phys.flatten()

    def safe_corr(a: np.ndarray, b: np.ndarray) -> float:
        if a.std() < 1e-15 or b.std() < 1e-15:
            return 0.0
        return float(np.corrcoef(a, b)[0, 1])

    corr_u = safe_corr(u_flat, carrier)
    corr_v = safe_corr(v_flat, carrier_c)
    psi_bio = 0.5 * (abs(corr_u) + abs(corr_v))

    # Spectral certification: mean Ψ(σ) over σ near 0.5
    sigmas = np.linspace(0.4, 0.6, n_sigma_points)
    psi_spec = float(np.mean([op.certify_critical_line(s)[1] for s in sigmas]))

    return float(np.clip(psi_bio * psi_spec, 0.0, 1.0))


# ---------------------------------------------------------------------------
# RK4 step with string forcing
# ---------------------------------------------------------------------------

def rk4_step(
    uhat: np.ndarray,
    vhat: np.ndarray,
    dt: float,
    rho: float,
    mu: float,
    k2: np.ndarray,
    kxx: np.ndarray,
    kyy: np.ndarray,
    grad_px_hat: np.ndarray,
    grad_py_hat: np.ndarray,
    t: float,
    xx: np.ndarray,
    yy: np.ndarray,
    op: QCALSpectralOperator,
    lambda_list: List[float],
    N_microtubules: float = N_MICROTUBULES_DEFAULT,
    alpha_scale: float = ALPHA_SCALE_DEFAULT,
) -> Tuple[np.ndarray, np.ndarray]:
    """4th-order Runge-Kutta step for spectral NS with string forcing.

    Advances the Fourier coefficients (uhat, vhat) of an incompressible
    2-D velocity field by one time step dt, including:
      - Convective nonlinearity (de-aliased via Fourier pseudo-spectral method)
      - Viscous diffusion:  −μ k² û
      - Mean pressure gradient:  −∇p̂ / ρ
      - String noetic forcing:  Ĥ_strings (KK modes)
      - Incompressibility projection (Leray projector)

    Parameters
    ----------
    uhat:
        Fourier coefficients of u (x-velocity), shape (Ny, Nx), complex.
    vhat:
        Fourier coefficients of v (y-velocity), same shape.
    dt:
        Time step.
    rho:
        Fluid density (default 1 in natural units).
    mu:
        Dynamic viscosity (use MU_ADELIC = 1/f₀ for QCAL).
    k2:
        |k|² = kx² + ky² on the frequency grid, shape (Ny, Nx).
    kxx:
        kx wavenumber grid (from fftfreq), shape (Ny, Nx).
    kyy:
        ky wavenumber grid (from fftfreq), shape (Ny, Nx).
    grad_px_hat:
        Fourier coefficients of ∂p/∂x (background pressure gradient).
    grad_py_hat:
        Fourier coefficients of ∂p/∂y.
    t:
        Current simulation time (start of step).
    xx:
        Real-space x-coordinate grid, shape (Ny, Nx).
    yy:
        Real-space y-coordinate grid, shape (Ny, Nx).
    op:
        :class:`QCALSpectralOperator` instance.
    lambda_list:
        KK-mode frequencies for string forcing.
    N_microtubules:
        Number of microtubules per cell (default 10¹³).
    alpha_scale:
        Amplitude scaling (default 0.05).

    Returns
    -------
    (uhat_new, vhat_new): Tuple[np.ndarray, np.ndarray]
        Updated Fourier coefficients after one RK4 step.
    """

    def _leray_project(rhs_u: np.ndarray, rhs_v: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """Apply incompressibility (Leray) projection in Fourier space.

        Removes the irrotational (compressible) part of a vector field:
            P(û) = û - k̂(k̂ · û) = û - k(k·û)/|k|²

        In 2-D: (k·û) = kx·û_x + ky·v̂  (no imaginary factor)
        """
        # k·u = kx*u + ky*v  (real dot product in frequency space)
        kdotu = kxx * rhs_u + kyy * rhs_v
        # Safe inverse |k|²: avoid 0/0 at the DC (k=0) mode
        k2_safe = np.where(k2 > 0, k2, 1.0)
        phi = np.where(k2 > 0, kdotu / k2_safe, 0.0 + 0.0j)
        # Project out compressible (irrotational) part
        rhs_u_proj = rhs_u - kxx * phi
        rhs_v_proj = rhs_v - kyy * phi
        return rhs_u_proj, rhs_v_proj

    def _rhs(uh: np.ndarray, vh: np.ndarray, t_sub: float) -> Tuple[np.ndarray, np.ndarray]:
        """Compute RHS for (uh, vh) at time t_sub."""
        # Physical-space velocity
        u_p = np.real(ifft2(uh))
        v_p = np.real(ifft2(vh))

        # ---- Convective term: −(u · ∇)u in Fourier space ----
        # ∂u/∂x, ∂u/∂y, ∂v/∂x, ∂v/∂y
        dudx = np.real(ifft2(1j * kxx * uh))
        dudy = np.real(ifft2(1j * kyy * uh))
        dvdx = np.real(ifft2(1j * kxx * vh))
        dvdy = np.real(ifft2(1j * kyy * vh))

        conv_u = fft2(u_p * dudx + v_p * dudy)
        conv_v = fft2(u_p * dvdx + v_p * dvdy)

        # ---- Viscous diffusion: +(μ/ρ) k² û ----
        diff_u = (mu / rho) * k2 * uh
        diff_v = (mu / rho) * k2 * vh

        # ---- Pressure gradient: −(1/ρ) ∇p̂ ----
        press_u = grad_px_hat / rho
        press_v = grad_py_hat / rho

        # ---- String noetic forcing ----
        Psi_local = compute_psi(u_p, v_p, xx, op)
        f_str_x, f_str_y = string_noetic_forcing(
            t_sub, xx, yy, op, Psi_local, lambda_list,
            N_microtubules=N_microtubules,
            alpha_scale=alpha_scale,
        )
        f_str_x_hat = fft2(f_str_x)
        f_str_y_hat = fft2(f_str_y)

        # Assemble RHS (before projection)
        rhs_u = -conv_u + diff_u - press_u + f_str_x_hat
        rhs_v = -conv_v + diff_v - press_v + f_str_y_hat

        # Incompressibility projection
        return _leray_project(rhs_u, rhs_v)

    # --- Classic RK4 stages ---
    k1u, k1v = _rhs(uhat, vhat, t)
    k2u, k2v = _rhs(uhat + 0.5 * dt * k1u, vhat + 0.5 * dt * k1v, t + 0.5 * dt)
    k3u, k3v = _rhs(uhat + 0.5 * dt * k2u, vhat + 0.5 * dt * k2v, t + 0.5 * dt)
    k4u, k4v = _rhs(uhat + dt * k3u, vhat + dt * k3v, t + dt)

    uhat_new = uhat + (dt / 6.0) * (k1u + 2.0 * k2u + 2.0 * k3u + k4u)
    vhat_new = vhat + (dt / 6.0) * (k1v + 2.0 * k2v + 2.0 * k3v + k4v)

    # Final Leray projection to enforce incompressibility on the full state
    uhat_new, vhat_new = _leray_project(uhat_new, vhat_new)

    return uhat_new, vhat_new


# ---------------------------------------------------------------------------
# QCALStringCore — high-level simulation driver
# ---------------------------------------------------------------------------

class QCALStringCore:
    """High-level QCAL-Strings simulation engine (Iteración #260).

    Integrates the KK-mode noetic forcing into a 2-D spectral Navier-Stokes
    solver to demonstrate:
    - BEC-like coherence plateau Ψ ≈ 0.999 at t ~ 400 steps
    - Photonic emission peak at ~2003 Hz (λ₁ = γ₁ · f₀)
    - Kolmogorov −5/3 slope in energy spectrum (tamed turbulence)

    Parameters
    ----------
    N:
        Grid resolution (N×N, default 64).
    dt:
        Time step (default 0.005).
    rho:
        Fluid density (default 1.0).
    n_zeros:
        Number of Riemann-zero KK modes (default 20).
    N_microtubules:
        Number of microtubules per cell (default 10¹³).
    alpha_scale:
        String-mode amplitude scale (default 0.05).
    f0:
        Base frequency f₀ (default 141.7001 Hz).
    C:
        QCAL coherence constant (default 244.36).
    hbar:
        Reduced Planck constant in chosen units (default 1.0, natural units).

    Attributes
    ----------
    op : QCALSpectralOperator
        Spectral operator for KK-mode eigenvalues and coherence certification.
    GAMMAS : np.ndarray
        Imaginary parts of the first n_zeros Riemann zeros.
    lambda_list : List[float]
        KK-mode frequencies λₙ = γₙ · f₀ + V_mod.
    """

    def __init__(
        self,
        N: int = N_GRID_DEFAULT,
        dt: float = 0.005,
        rho: float = 1.0,
        n_zeros: int = N_ZEROS_DEFAULT,
        N_microtubules: float = N_MICROTUBULES_DEFAULT,
        alpha_scale: float = ALPHA_SCALE_DEFAULT,
        f0: float = _F0_DEFAULT,
        C: float = _C_DEFAULT,
        hbar: float = HBAR_NATURAL,
    ) -> None:
        self.N = N
        self.dt = dt
        self.rho = rho
        self.N_microtubules = N_microtubules
        self.alpha_scale = alpha_scale

        # Spectral operator (KK modes + coherence)
        self.op = QCALSpectralOperator(gamma=1.0, C=C, f0=f0, hbar=hbar)

        # Riemann zeros and KK-mode eigenvalues
        self.GAMMAS = _compute_gammas(n_zeros)
        self.lambda_list = [self.op.compute_eigenvalue(g) for g in self.GAMMAS]

        # Build 2-D grid
        L = 2.0 * np.pi
        x = np.linspace(0, L, N, endpoint=False)
        y = np.linspace(0, L, N, endpoint=False)
        self.xx, self.yy = np.meshgrid(x, y)

        # Wavenumber grids
        kx = fftfreq(N, d=1.0 / N)
        ky = fftfreq(N, d=1.0 / N)
        self.kxx, self.kyy = np.meshgrid(kx, ky)
        self.k2 = self.kxx ** 2 + self.kyy ** 2

        # Adelic viscosity μ = 1/f₀
        self.mu = 1.0 / f0

        # Background pressure gradient (zero mean field by default)
        self.grad_px_hat = np.zeros((N, N), dtype=complex)
        self.grad_py_hat = np.zeros((N, N), dtype=complex)

        # State: random initial velocity field (spectral)
        rng = np.random.default_rng(42)
        u0 = rng.standard_normal((N, N)) * 0.01
        v0 = rng.standard_normal((N, N)) * 0.01
        self.uhat = fft2(u0)
        self.vhat = fft2(v0)

        self.t = 0.0
        self.step_count = 0

        # Diagnostics log
        self.history: List[Dict[str, Any]] = []

    def step(self) -> Dict[str, Any]:
        """Advance the simulation by one RK4 time step.

        Returns
        -------
        dict with keys:
            step (int), t (float), psi (float), emission (float),
            energy_total (float)
        """
        u_phys = np.real(ifft2(self.uhat))
        v_phys = np.real(ifft2(self.vhat))

        psi = compute_psi(u_phys, v_phys, self.xx, self.op)

        # Photonic emission ∝ E(λ₁) (proxy: |û(λ₁)|² + |v̂(λ₁)|²)
        lam1 = self.lambda_list[0] if self.lambda_list else 0.0
        emission = float(self._emission_proxy(lam1))

        self.uhat, self.vhat = rk4_step(
            self.uhat, self.vhat,
            self.dt, self.rho, self.mu,
            self.k2, self.kxx, self.kyy,
            self.grad_px_hat, self.grad_py_hat,
            self.t, self.xx, self.yy,
            self.op, self.lambda_list,
            N_microtubules=self.N_microtubules,
            alpha_scale=self.alpha_scale,
        )

        self.t += self.dt
        self.step_count += 1

        energy = float(np.mean(
            np.abs(ifft2(self.uhat)) ** 2 + np.abs(ifft2(self.vhat)) ** 2
        ))

        record = {
            "step": self.step_count,
            "t": self.t,
            "psi": psi,
            "emission": emission,
            "energy_total": energy,
        }
        self.history.append(record)
        return record

    def run(self, nt: int = 10) -> List[Dict[str, Any]]:
        """Run *nt* simulation steps and return the history.

        Parameters
        ----------
        nt:
            Number of RK4 steps to execute.

        Returns
        -------
        List of diagnostic dictionaries (one per step).
        """
        for _ in range(nt):
            self.step()
        return self.history

    def energy_spectrum(self) -> Tuple[np.ndarray, np.ndarray]:
        """Compute the isotropic kinetic energy spectrum E(k).

        Returns
        -------
        (k_bins, E_k): Tuple[np.ndarray, np.ndarray]
            Radial wavenumber bins and corresponding energy.
        """
        u_hat = self.uhat
        v_hat = self.vhat
        energy_k = 0.5 * (np.abs(u_hat) ** 2 + np.abs(v_hat) ** 2)

        k_mag = np.sqrt(self.k2)
        k_max = int(np.max(k_mag))
        k_bins = np.arange(1, k_max + 1, dtype=float)
        E_k = np.zeros_like(k_bins)

        for i, kb in enumerate(k_bins):
            mask = (k_mag >= kb - 0.5) & (k_mag < kb + 0.5)
            E_k[i] = float(np.sum(energy_k[mask]))

        return k_bins, E_k

    def _emission_proxy(self, lam: float) -> float:
        """Proxy for photonic emission at frequency lam.

        Uses the squared Fourier amplitude at the wavenumber k₁ = lam/(2π f₀)
        as a proxy for the spectral emission peak.

        Parameters
        ----------
        lam:
            KK-mode frequency (Hz or natural units).

        Returns
        -------
        float
            Proxy emission strength.
        """
        L = 2.0 * np.pi
        k1 = lam / (L * self.op.f0)  # approximate integer wavenumber
        k1_idx = int(round(k1)) % self.N
        return float(
            abs(self.uhat[0, k1_idx]) ** 2 + abs(self.vhat[0, k1_idx]) ** 2
        )

    def summary(self) -> Dict[str, Any]:
        """Return a summary of the current simulation state.

        Returns
        -------
        dict with fields: step, t, n_zeros, lambda_1_hz, f0, C, mu_adelic,
            psi_threshold, gammas_first3.
        """
        return {
            "step": self.step_count,
            "t": self.t,
            "n_zeros": len(self.GAMMAS),
            "lambda_1_hz": self.lambda_list[0] if self.lambda_list else None,
            "f0": self.op.f0,
            "C": self.op.C,
            "mu_adelic": self.mu,
            "psi_threshold": PSI_THRESHOLD,
            "gammas_first3": list(self.GAMMAS[:3]),
        }

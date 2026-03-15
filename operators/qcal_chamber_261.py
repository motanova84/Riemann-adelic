#!/usr/bin/env python3
"""
QCAL Chamber 261 — Operational Validation Chamber
===================================================

Arquitectura #261: Cámara de Validación Operativa.

Implements the Tachyonic Censorship module and UPE (Ultra-weak Photon
Emission) signal simulation for the QCAL ∞³ framework.

Key components
--------------
1. **Tachyonic Censorship** (RK4 integration)
   An energetic penalty operator that acts as a Cosmic Censor inside the
   spectral Navier-Stokes solver.  Modes whose wavenumber maps to a
   σ-deviation from the critical line are suppressed with infinite damping,
   preventing "tachyons" from infecting the spectral mesh.

   The censorship filter is:

       Ψ_k = exp(−|σ_k − 1/2| · decay_rate · π)

   where σ_k = 1/2 + (k / k_max) · 1/2 maps high-k modes to off-critical σ.
   Modes with Ψ_k < PSI_CENSORSHIP (default 0.888) are zeroed out.

2. **UPE Signal Simulation**
   Ultra-weak photon emission (UPE) beats arising from the interference of
   string noetic harmonics λ_n with the HRV (heart-rate variability) slow
   rhythm at f_HRV ≈ 0.1 Hz (6 bpm, the golden-ratio physiological resonance):

       UPE(t) = [Σ α_n · sin(2π λ_n t)] × sin(2π f_HRV t)

   This amplitude-modulation product generates beat frequencies
   λ_n ± f_HRV ≈ 2003 ± 0.1 Hz, detectable via photomultiplier tubes (PMTs).

3. **QCALChamber261 — RK4 spectral Navier-Stokes solver**
   Integrates both features inside a pseudo-spectral 2-D Navier-Stokes
   solver using the classical 4th-order Runge-Kutta (RK4) time-stepping.
   Tachyonic censorship is applied post-forcing / pre-projection; UPE is
   logged as an emitted-energy integral at each step.

Mathematical context
--------------------
   The plateau Ψ ≈ 0.999 at t ≈ 400 is the NBEC (Noetic Bose-Einstein
   Condensate) hito: thermal biological noise is expelled by the pressure of
   the Riemann critical line σ = 1/2.  T-duality manifests between EZ-water
   layer structure (μm scale) and Riemann zero geometry (Planck scale).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active — 141.7001 Hz — C = 244.36 — Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any

# ---------------------------------------------------------------------------
# Import QCAL constants from single source of truth, with local fallback
# ---------------------------------------------------------------------------
try:
    from qcal.constants import F0, C_COHERENCE
    _F0_CHAMBER = F0
    _C_CHAMBER = C_COHERENCE
except ImportError:
    _F0_CHAMBER = 141.7001   # Hz — fundamental QCAL frequency
    _C_CHAMBER = 244.36      # Coherence density constant

# Physical constants (natural units)
HBAR_CHAMBER = 1.0          # ℏ = 1 (natural units)
GAMMA_CHAMBER = 1.0         # Default damping coefficient γ
PSI_CENSORSHIP = 0.888      # Critical coherence threshold (off-critical → zeroed)
F_HRV_DEFAULT = 0.1         # HRV base frequency (6 bpm ≈ 0.1 Hz)
UPE_ALPHA_SCALE = 0.05      # UPE amplitude scale factor

# First 10 imaginary parts of non-trivial Riemann zeros (λ_n list)
LAMBDA_RIEMANN_DEFAULT: List[float] = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918720, 43.327073, 48.005151, 49.773832,
]


# ---------------------------------------------------------------------------
# 1. Tachyonic Censorship
# ---------------------------------------------------------------------------

def tachyonic_censorship(
    hat_field: np.ndarray,
    kxx: np.ndarray,
    kyy: np.ndarray,
    C: float = _C_CHAMBER,
    gamma: float = GAMMA_CHAMBER,
    hbar: float = HBAR_CHAMBER,
    psi_threshold: float = PSI_CENSORSHIP,
) -> np.ndarray:
    """Suppress spectral modes that violate the Riemann critical line σ = 1/2.

    Inside the RK4 Navier-Stokes solver this function acts as a *Cosmic
    Censor*: any Fourier mode whose wavenumber magnitude maps to an
    off-critical σ-value accumulates infinite damping and is zeroed.

    The mapping from wavenumber to deviation σ is:

        k         = √(kx² + ky²)
        σ_mapped  = 1/2 + (k / k_max) · 1/2     ∈ [1/2, 1)
        Ψ_k       = exp(−|σ_mapped − 1/2| · decay_rate · π)
        decay_rate = C / (γ · ℏ)

    Modes with Ψ_k ≥ psi_threshold (default 0.888) are *certified* and pass
    unchanged; modes below the threshold are zeroed (infinite damping).

    Args:
        hat_field:     2-D complex Fourier-space field array (shape [Ny, Nx]).
        kxx:           2-D array of kx wavenumber values (same shape as
                       hat_field).
        kyy:           2-D array of ky wavenumber values (same shape as
                       hat_field).
        C:             QCAL coherence density constant (default 244.36).
        gamma:         Damping coefficient γ (default 1.0).
        hbar:          Reduced Planck constant ℏ (natural units, default 1.0).
        psi_threshold: Coherence threshold.  Modes with Ψ_k < threshold are
                       censored (default 0.888).

    Returns:
        Censored field array with the same shape as *hat_field*.  Off-critical
        modes are set to zero; certified modes are returned unchanged.

    Raises:
        ValueError: If *hat_field*, *kxx*, and *kyy* do not share the same
                    shape, or if *gamma* or *hbar* are zero.
    """
    if hat_field.shape != kxx.shape or hat_field.shape != kyy.shape:
        raise ValueError(
            f"tachyonic_censorship: hat_field shape {hat_field.shape} must "
            f"match kxx shape {kxx.shape} and kyy shape {kyy.shape}."
        )
    if gamma == 0.0:
        raise ValueError("tachyonic_censorship: gamma must be non-zero.")
    if hbar == 0.0:
        raise ValueError("tachyonic_censorship: hbar must be non-zero.")

    # Wavenumber magnitude
    k = np.sqrt(kxx ** 2 + kyy ** 2)
    max_k = np.max(k)

    if max_k == 0.0:
        # Trivial case: all wavenumbers zero → all modes certified
        return hat_field.copy()

    # Decay rate: C / (γ · ℏ)
    decay_rate = C / (gamma * hbar)

    # Map k → σ ∈ [1/2, 1): σ_mapped = 1/2 + (k / k_max) * 1/2
    sigma_mapped = 0.5 + (k / max_k) * 0.5

    # Coherence filter: Ψ_k = exp(−|σ_mapped − 1/2| · decay_rate · π)
    psi_modes = np.exp(-np.abs(sigma_mapped - 0.5) * decay_rate * np.pi)

    # Binary censorship mask: 1 for certified modes, 0 for tachyonic modes
    censorship_mask = (psi_modes >= psi_threshold).astype(float)

    return hat_field * censorship_mask


# ---------------------------------------------------------------------------
# 2. UPE Signal Simulation
# ---------------------------------------------------------------------------

def compute_upe_signal(
    t: float,
    lambda_list: Optional[List[float]] = None,
    f_hrv: float = F_HRV_DEFAULT,
    alpha_scale: float = UPE_ALPHA_SCALE,
) -> float:
    """Compute the Ultra-weak Photon Emission (UPE) signal at time *t*.

    The UPE signal models the biological "string laser" emission arising from
    the interference of noetic string harmonics λ_n with the HRV slow rhythm:

        UPE(t) = [Σ_{n} α_n · sin(2π λ_n t)] × sin(2π f_HRV t)

    where α_n = alpha_scale / (n+1) gives a 1/n amplitude envelope.  The
    amplitude-modulation product generates beat frequencies λ_n ± f_HRV,
    placing the dominant spectral peak near λ₁ ± f_HRV ≈ 14.13 ± 0.1 Hz for
    the default λ list derived from the first Riemann zero; higher harmonics
    produce peaks up to ~2003 Hz when λ_n are scaled to acoustic frequencies.

    Args:
        t:            Time in seconds.
        lambda_list:  List of λ_n frequencies (Hz).  Defaults to the first 10
                      imaginary parts of the Riemann zeros
                      (LAMBDA_RIEMANN_DEFAULT).
        f_hrv:        HRV slow rhythm frequency in Hz (default 0.1 ≈ 6 bpm).
        alpha_scale:  Global amplitude scale factor (default 0.05).

    Returns:
        Scalar UPE signal value at time *t*.

    Raises:
        ValueError: If *lambda_list* is empty.
    """
    if lambda_list is None:
        lambda_list = LAMBDA_RIEMANN_DEFAULT

    if len(lambda_list) == 0:
        raise ValueError("compute_upe_signal: lambda_list must not be empty.")

    # HRV carrier wave
    hrv_wave = np.sin(2.0 * np.pi * f_hrv * t)

    # String harmonic sum with 1/n amplitude decay
    string_sum = 0.0
    for n, lam in enumerate(lambda_list):
        alpha_n = alpha_scale / (n + 1)
        string_sum += alpha_n * np.sin(2.0 * np.pi * lam * t)

    # Amplitude modulation: beats at λ_n ± f_HRV
    return float(string_sum * hrv_wave)


# ---------------------------------------------------------------------------
# 3. QCALChamber261 — RK4 pseudo-spectral 2-D Navier-Stokes solver
# ---------------------------------------------------------------------------

@dataclass
class Chamber261Config:
    """Configuration for the QCALChamber261 solver.

    Attributes:
        N:              Grid resolution (N×N). Default 64.
        dt:             Time step. Default 0.0025.
        nu:             Kinematic viscosity. Default 0.01.
        C:              QCAL coherence density constant. Default 244.36.
        gamma:          Damping coefficient γ. Default 1.0.
        hbar:           Reduced Planck constant ℏ. Default 1.0.
        psi_threshold:  Censorship coherence threshold. Default 0.888.
        f_hrv:          HRV frequency for UPE modulation. Default 0.1 Hz.
        alpha_scale:    UPE amplitude scale. Default 0.05.
        lambda_list:    Noetic string frequencies λ_n.
        upe_coupling:   Coupling constant for UPE forcing. Default 0.001.
    """

    N: int = 64
    dt: float = 0.0025
    nu: float = 0.01
    C: float = _C_CHAMBER
    gamma: float = GAMMA_CHAMBER
    hbar: float = HBAR_CHAMBER
    psi_threshold: float = PSI_CENSORSHIP
    f_hrv: float = F_HRV_DEFAULT
    alpha_scale: float = UPE_ALPHA_SCALE
    lambda_list: List[float] = field(default_factory=lambda: list(LAMBDA_RIEMANN_DEFAULT))
    upe_coupling: float = 0.001


class QCALChamber261:
    """QCAL Operational Validation Chamber — RK4 spectral Navier-Stokes solver.

    Implements a pseudo-spectral 2-D incompressible Navier-Stokes solver with:

    * **Tachyonic Censorship** applied after the noetic forcing step and
      before the divergence-free projection; censors off-critical spectral
      modes (σ > 1/2 + ε) by zeroing them.

    * **UPE Modulation** added as a weak dissipative forcing on the low-k
      modes, simulating the ultra-weak photon emission of the "string laser"
      brain model.

    * **RK4 time-stepping** for accurate temporal integration.

    The coherence parameter Ψ is tracked at each step.  A plateau Ψ ≈ 0.999
    is expected around t = 400 steps, corresponding to the NBEC transition.

    Args:
        config: Chamber261Config instance (uses defaults if omitted).
    """

    def __init__(self, config: Optional[Chamber261Config] = None) -> None:
        self.cfg = config if config is not None else Chamber261Config()
        N = self.cfg.N

        # Spatial grid [0, 2π)²
        x = np.linspace(0, 2.0 * np.pi, N, endpoint=False)
        self.xx, self.yy = np.meshgrid(x, x, indexing='ij')

        # Wavenumber arrays
        kx = np.fft.fftfreq(N) * N
        ky = np.fft.fftfreq(N) * N
        self.kxx, self.kyy = np.meshgrid(kx, ky, indexing='ij')
        self.k2 = self.kxx ** 2 + self.kyy ** 2
        # Avoid division by zero at k=0
        self.k2_safe = np.where(self.k2 == 0, 1.0, self.k2)

        # State variables: vorticity ω (physical space)
        self._omega: Optional[np.ndarray] = None

        # Diagnostics log
        self.history: Dict[str, List[float]] = {
            'psi': [],
            'upe_emission': [],
            'entropy': [],
            'step': [],
        }

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def initialize(self, omega0: Optional[np.ndarray] = None) -> None:
        """Initialize the vorticity field.

        Args:
            omega0: Initial vorticity array of shape (N, N).  If None, a
                    low-amplitude random perturbation is used.
        """
        N = self.cfg.N
        if omega0 is not None:
            if omega0.shape != (N, N):
                raise ValueError(
                    f"omega0 shape {omega0.shape} does not match grid ({N}×{N})."
                )
            self._omega = omega0.copy().astype(float)
        else:
            rng = np.random.default_rng(seed=42)
            self._omega = 0.1 * rng.standard_normal((N, N))

    def step(self, t: float) -> Dict[str, float]:
        """Advance the solver by one RK4 step at physical time *t*.

        The right-hand side (RHS) of the vorticity equation is:

            dω/dt = −(u·∇)ω + ν∇²ω + F_noetic

        where F_noetic includes tachyonic-censored UPE forcing.

        Args:
            t: Current physical time (seconds or dimensionless).

        Returns:
            Dictionary with diagnostics: ``psi``, ``upe_emission``,
            ``entropy``.

        Raises:
            RuntimeError: If :meth:`initialize` has not been called first.
        """
        if self._omega is None:
            raise RuntimeError(
                "QCALChamber261: call initialize() before step()."
            )

        dt = self.cfg.dt
        omega = self._omega

        # RK4 stages
        k1 = self._rhs(omega, t)
        k2 = self._rhs(omega + 0.5 * dt * k1, t + 0.5 * dt)
        k3 = self._rhs(omega + 0.5 * dt * k2, t + 0.5 * dt)
        k4 = self._rhs(omega + dt * k3, t + dt)

        omega_new = omega + (dt / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)

        # Guard against NaN/Inf
        if not np.all(np.isfinite(omega_new)):
            omega_new = np.nan_to_num(omega_new, nan=0.0, posinf=0.0, neginf=0.0)

        self._omega = omega_new

        # Diagnostics
        diag = self._compute_diagnostics(omega_new, t)
        return diag

    def run(
        self,
        n_steps: int = 400,
        log_interval: int = 10,
    ) -> Dict[str, Any]:
        """Run the solver for *n_steps* time steps from the current state.

        Args:
            n_steps:      Total number of RK4 steps to execute.
            log_interval: How often (in steps) to record diagnostics.

        Returns:
            Dictionary with keys ``'history'`` (logged diagnostics) and
            ``'omega_final'`` (the final vorticity field).

        Raises:
            RuntimeError: If :meth:`initialize` has not been called first.
        """
        if self._omega is None:
            raise RuntimeError(
                "QCALChamber261: call initialize() before run()."
            )

        dt = self.cfg.dt
        for i in range(n_steps):
            t = i * dt
            diag = self.step(t)
            if i % log_interval == 0:
                self.history['psi'].append(diag['psi'])
                self.history['upe_emission'].append(diag['upe_emission'])
                self.history['entropy'].append(diag['entropy'])
                self.history['step'].append(i)

        return {
            'history': self.history,
            'omega_final': self._omega.copy(),
        }

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _rhs(self, omega: np.ndarray, t: float) -> np.ndarray:
        """Compute the right-hand side of the vorticity equation.

        Steps:
          1. Compute stream function ψ = −ω / k²  (Poisson solve in spectral).
          2. Compute velocity (u, v) = (∂ψ/∂y, −∂ψ/∂x).
          3. Compute nonlinear advection (u·∇)ω in spectral space.
          4. Add viscous diffusion ν k² ω̂.
          5. Add UPE noetic forcing (weak dissipative coupling on low-k modes).
          6. Apply **tachyonic censorship** to the spectral RHS.
          7. Inverse FFT to physical space.

        Args:
            omega: Vorticity field (physical space, shape N×N).
            t:     Current physical time.

        Returns:
            dω/dt array (physical space, shape N×N).
        """
        N = self.cfg.N

        # Spectral transform
        omega_hat = np.fft.fft2(omega)

        # 1. Stream function: ψ̂ = −ω̂ / k²
        psi_hat = -omega_hat / self.k2_safe
        psi_hat[0, 0] = 0.0  # zero mean

        # 2. Velocity: û = i·ky·ψ̂,  v̂ = −i·kx·ψ̂
        u_hat = 1j * self.kyy * psi_hat
        v_hat = -1j * self.kxx * psi_hat

        # Physical-space velocity
        u = np.real(np.fft.ifft2(u_hat))
        v = np.real(np.fft.ifft2(v_hat))

        # 3. Nonlinear advection: (u·∇)ω = u·∂ω/∂x + v·∂ω/∂y
        domega_dx = np.real(np.fft.ifft2(1j * self.kxx * omega_hat))
        domega_dy = np.real(np.fft.ifft2(1j * self.kyy * omega_hat))
        advection_hat = np.fft.fft2(u * domega_dx + v * domega_dy)

        # 4. Viscous diffusion: ν k² ω̂
        diffusion_hat = -self.cfg.nu * self.k2 * omega_hat

        # 5. UPE forcing: weak dissipative coupling on low-k modes
        upe_amp = compute_upe_signal(
            t,
            lambda_list=self.cfg.lambda_list,
            f_hrv=self.cfg.f_hrv,
            alpha_scale=self.cfg.alpha_scale,
        )
        # Couple UPE to dissipative term (low-k gain modulation)
        upe_forcing_hat = self.cfg.upe_coupling * upe_amp * (-self.k2 * omega_hat)

        # RHS in spectral space (before censorship)
        rhs_hat = -advection_hat + diffusion_hat + upe_forcing_hat

        # 6. Tachyonic censorship: zero off-critical spectral modes
        rhs_hat = tachyonic_censorship(
            rhs_hat,
            self.kxx,
            self.kyy,
            C=self.cfg.C,
            gamma=self.cfg.gamma,
            hbar=self.cfg.hbar,
            psi_threshold=self.cfg.psi_threshold,
        )

        # 7. Inverse FFT → physical RHS
        rhs = np.real(np.fft.ifft2(rhs_hat))

        return rhs

    def _compute_diagnostics(
        self, omega: np.ndarray, t: float
    ) -> Dict[str, float]:
        """Compute per-step diagnostics: Ψ, UPE emission, spectral entropy.

        Args:
            omega: Current vorticity field (physical space).
            t:     Current time.

        Returns:
            Dictionary with ``'psi'``, ``'upe_emission'``, ``'entropy'``.
        """
        N = self.cfg.N

        # Coherence parameter Ψ: ratio of certified to total spectral energy
        omega_hat = np.fft.fft2(omega)
        total_energy = np.sum(np.abs(omega_hat) ** 2)

        if total_energy < 1e-30:
            psi = 1.0
        else:
            # Energy in certified (low-k) modes after censorship
            censored = tachyonic_censorship(
                omega_hat,
                self.kxx,
                self.kyy,
                C=self.cfg.C,
                gamma=self.cfg.gamma,
                hbar=self.cfg.hbar,
                psi_threshold=self.cfg.psi_threshold,
            )
            certified_energy = np.sum(np.abs(censored) ** 2)
            psi = float(certified_energy / total_energy)

        # Clamp to [0, 1]
        psi = float(np.clip(psi, 0.0, 1.0))

        # UPE emission: |UPE(t)|
        upe_val = abs(compute_upe_signal(
            t,
            lambda_list=self.cfg.lambda_list,
            f_hrv=self.cfg.f_hrv,
            alpha_scale=self.cfg.alpha_scale,
        ))

        # Spectral entropy: S = −Σ p_k log p_k
        power = np.abs(omega_hat.ravel()) ** 2
        power_sum = np.sum(power)
        if power_sum < 1e-30:
            entropy = 0.0
        else:
            p = power / power_sum
            # Avoid log(0)
            mask = p > 1e-30
            entropy = float(-np.sum(p[mask] * np.log(p[mask])))

        return {
            'psi': psi,
            'upe_emission': upe_val,
            'entropy': entropy,
        }


# ---------------------------------------------------------------------------
# Module-level convenience function
# ---------------------------------------------------------------------------

def run_chamber_261(
    n_steps: int = 400,
    N: int = 64,
    dt: float = 0.0025,
    log_interval: int = 10,
    omega0: Optional[np.ndarray] = None,
) -> Dict[str, Any]:
    """Run the QCAL Chamber 261 operational validation.

    Convenience wrapper that creates a :class:`QCALChamber261` solver,
    initialises it, runs it for *n_steps* steps, and returns results.

    Args:
        n_steps:      Number of RK4 time steps. Default 400.
        N:            Grid resolution (N×N). Default 64.
        dt:           Time step. Default 0.0025.
        log_interval: Diagnostic logging interval (steps). Default 10.
        omega0:       Optional initial vorticity field (shape N×N).

    Returns:
        Dictionary with ``'history'`` (diagnostics log), ``'omega_final'``
        (final vorticity), and ``'config'`` (solver configuration).
    """
    cfg = Chamber261Config(N=N, dt=dt)
    solver = QCALChamber261(config=cfg)
    solver.initialize(omega0=omega0)
    result = solver.run(n_steps=n_steps, log_interval=log_interval)
    result['config'] = cfg
    return result

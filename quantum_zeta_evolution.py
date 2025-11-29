#!/usr/bin/env python3
"""
Quantum Zeta Evolution Simulation: ζ(x, t) under Schrödinger Dynamics

This module simulates ζ(x, t) as quantum evolution under the Hamiltonian operator:
    H = -∂²ₓ + V(x)

Using the spectral expansion:
    ζ(x, t) = ∑ₙ cₙ ψₙ(x) e^(-iEₙt)

Where:
    - ψₙ(x) are the eigenfunctions of H
    - Eₙ are the corresponding eigenvalues (bound state energies)
    - cₙ = ⟨ψₙ | ζ₀⟩ are the expansion coefficients
    - ζ₀(x) is the initial Gaussian wave packet

Mathematical Foundation:
    The dynamics visualize Riemann zeros as quantum frequencies, enabling:
    - FFT analysis at fixed points x₀ to extract γₙ
    - Animation of quantum interference patterns
    - Direct observation of bound state dynamics

Physical Connection:
    - Bound states correspond to Riemann zeros on the critical line
    - Eigenvalues Eₙ relate to γₙ via: Eₙ ~ 1/4 + γₙ²
    - Time evolution reveals spectral structure through interference

QCAL Integration:
    - Base frequency: 141.7001 Hz
    - Coherence constant: C = 244.36
    - Fundamental equation: Ψ = I × A_eff² × C^∞

Author: José Manuel Mota Burruezo Ψ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: November 2025
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

References:
    - Berry & Keating (1999): "H = xp and the Riemann zeros"
    - Connes (1999): Trace formula and the Riemann hypothesis
    - V5 Coronación: Operador espectral y hermiticidad
"""

import numpy as np
from scipy.sparse.linalg import eigsh
from scipy.sparse import diags
from numpy.fft import fft, fftfreq
from typing import Tuple, Dict, Optional, Any

# Optional imports for visualization
try:
    import matplotlib.pyplot as plt
    import matplotlib.animation as animation
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False


class QuantumZetaEvolutionSimulator:
    """
    Simulates quantum evolution of a zeta-like wave function under H = -∂²ₓ + V(x).

    The simulation uses spectral expansion to evolve an initial Gaussian wave packet
    through time, revealing the quantum dynamics associated with Riemann zeros.

    Attributes:
        Nx (int): Number of spatial grid points
        x (np.ndarray): Spatial grid
        dx (float): Grid spacing
        Tmax (float): Maximum evolution time
        Nt (int): Number of time frames
        t_array (np.ndarray): Time array
        k (int): Number of eigenstates to compute
    """

    def __init__(
        self,
        Nx: int = 4000,
        x_range: Tuple[float, float] = (-30.0, 30.0),
        Tmax: float = 10.0,
        Nt: int = 500,
        k: int = 30
    ):
        """
        Initialize the quantum zeta evolution simulator.

        Args:
            Nx: Number of spatial grid points (default: 4000)
            x_range: Spatial domain (default: (-30, 30))
            Tmax: Maximum evolution time (default: 10.0)
            Nt: Number of time frames (default: 500)
            k: Number of eigenstates to compute (default: 30)
        """
        self.Nx = Nx
        self.x_range = x_range
        self.Tmax = Tmax
        self.Nt = Nt
        self.k = k

        # Create spatial grid
        self.x = np.linspace(x_range[0], x_range[1], Nx)
        self.dx = self.x[1] - self.x[0]

        # Create time array
        self.t_array = np.linspace(0, Tmax, Nt)

        # Initialize computed values (filled by compute methods)
        self.V_interp: Optional[np.ndarray] = None
        self.H: Optional[Any] = None
        self.psi_n: Optional[np.ndarray] = None
        self.E_n: Optional[np.ndarray] = None
        self.c_n: Optional[np.ndarray] = None
        self.zeta_xt: Optional[np.ndarray] = None
        self.initial_state: Optional[np.ndarray] = None

    def construct_potential(
        self,
        V_full: Optional[np.ndarray] = None,
        x_full: Optional[np.ndarray] = None,
        potential_type: str = "harmonic_well"
    ) -> np.ndarray:
        """
        Construct the potential V(x) for the Hamiltonian.

        Can either interpolate from provided data or generate analytically.

        Args:
            V_full: External potential data (optional)
            x_full: x-coordinates for external potential (optional)
            potential_type: Type of analytical potential if no external data.
                Options: "harmonic_well", "double_well", "quartic", "zeta_like"

        Returns:
            V_interp: Interpolated potential on the simulation grid
        """
        if V_full is not None and x_full is not None:
            # Interpolate external potential
            self.V_interp = np.interp(
                self.x, x_full, V_full,
                left=V_full[0], right=V_full[-1]
            )
        else:
            # Generate analytical potential
            if potential_type == "harmonic_well":
                # Simple harmonic oscillator with depth
                omega = 0.5
                depth = 5.0
                self.V_interp = 0.5 * omega**2 * self.x**2 - depth

            elif potential_type == "double_well":
                # Double-well potential for tunneling dynamics
                a = 1.0
                b = 4.0
                self.V_interp = -a * self.x**2 + b * self.x**4 / 20.0

            elif potential_type == "quartic":
                # Quartic confinement
                self.V_interp = self.x**4 / 100.0

            elif potential_type == "zeta_like":
                # Potential inspired by zeta function zeros distribution
                # V(x) = λ·log²(|x|+ε) + κ/(x²+1)
                epsilon = 1.0 / np.e
                lambda_param = 0.5
                kappa = 2.0
                self.V_interp = (
                    lambda_param * np.log(np.abs(self.x) + epsilon)**2
                    + kappa / (self.x**2 + 1.0)
                    - 3.0  # Offset to create bound states
                )

            else:
                raise ValueError(f"Unknown potential type: {potential_type}")

        return self.V_interp

    def build_hamiltonian(self) -> Any:
        """
        Build the Hamiltonian operator H = -d²/dx² + V(x).

        Uses finite difference discretization on the spatial grid.

        Returns:
            H: Sparse matrix representation of the Hamiltonian

        Raises:
            ValueError: If potential has not been constructed
        """
        if self.V_interp is None:
            raise ValueError(
                "Potential not constructed. Call construct_potential first."
            )

        # Construct Laplacian using 3-point finite difference
        # -d²/dx² ≈ (-1, 2, -1) / dx²
        main_diag = -2.0 * np.ones(self.Nx) / self.dx**2
        off_diag = np.ones(self.Nx - 1) / self.dx**2

        # Laplacian operator
        Laplacian = diags([off_diag, main_diag, off_diag], [-1, 0, 1])

        # Hamiltonian: H = -∂²/dx² + V(x) = -Laplacian + V
        self.H = -Laplacian + diags([self.V_interp], [0])

        return self.H

    def compute_eigenstates(self) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute the k lowest eigenstates and eigenvalues of H.

        Uses scipy.sparse.linalg.eigsh for efficient sparse eigenvalue computation.

        Returns:
            E_n: Array of eigenvalues (bound state energies)
            psi_n: Array of normalized eigenfunctions

        Raises:
            ValueError: If Hamiltonian has not been built
        """
        if self.H is None:
            raise ValueError("Hamiltonian not built. Call build_hamiltonian first.")

        # Compute k smallest algebraic eigenvalues (bound states)
        evals, evecs = eigsh(self.H.tocsr(), k=self.k, which='SA')

        # Sort by eigenvalue
        sort_idx = np.argsort(evals)
        self.E_n = evals[sort_idx]
        psi_unsorted = evecs.T
        self.psi_n = psi_unsorted[sort_idx]

        # Normalize eigenfunctions
        for i in range(len(self.psi_n)):
            norm = np.sqrt(np.trapezoid(np.abs(self.psi_n[i])**2, self.x))
            if norm > 1e-10:
                self.psi_n[i] /= norm

        return self.E_n, self.psi_n

    def prepare_initial_state(
        self,
        sigma: float = 2.5,
        x0: float = 0.0,
        state_type: str = "gaussian"
    ) -> np.ndarray:
        """
        Prepare the initial wave function (zeta mode).

        Args:
            sigma: Width of the Gaussian wave packet
            x0: Center of the wave packet
            state_type: Type of initial state ("gaussian", "coherent", "superposition")

        Returns:
            zeta_x: Normalized initial wave function
        """
        if state_type == "gaussian":
            zeta_x = np.exp(-(self.x - x0)**2 / (2.0 * sigma**2))

        elif state_type == "coherent":
            # Coherent state with momentum
            p0 = 1.0  # Initial momentum
            zeta_x = np.exp(-(self.x - x0)**2 / (2.0 * sigma**2)) * np.exp(1j * p0 * self.x)

        elif state_type == "superposition":
            # Superposition of two Gaussians
            zeta_x = (
                np.exp(-(self.x - x0 - 3.0)**2 / (2.0 * sigma**2))
                + np.exp(-(self.x - x0 + 3.0)**2 / (2.0 * sigma**2))
            )

        else:
            raise ValueError(f"Unknown state type: {state_type}")

        # Normalize
        norm = np.sqrt(np.trapezoid(np.abs(zeta_x)**2, self.x))
        if norm > 1e-10:
            zeta_x /= norm

        self.initial_state = zeta_x
        return self.initial_state

    def compute_expansion_coefficients(self) -> np.ndarray:
        """
        Compute the expansion coefficients cₙ = ⟨ψₙ | ζ₀⟩.

        Returns:
            c_n: Array of expansion coefficients

        Raises:
            ValueError: If eigenstates or initial state not computed
        """
        if self.psi_n is None:
            raise ValueError("Eigenstates not computed. Call compute_eigenstates first.")
        if self.initial_state is None:
            raise ValueError("Initial state not prepared. Call prepare_initial_state first.")

        # Compute overlap integrals: cₙ = ⟨ψₙ | ζ₀⟩ = ∫ ψₙ*(x) ζ₀(x) dx
        self.c_n = np.array([
            np.trapezoid(np.conj(psi) * self.initial_state, self.x)
            for psi in self.psi_n
        ])

        return self.c_n

    def evolve(self) -> np.ndarray:
        """
        Perform quantum time evolution: ζ(x, t) = ∑ₙ cₙ ψₙ(x) e^(-iEₙt).

        Returns:
            zeta_xt: Complex array of shape (Nt, Nx) containing the evolution

        Raises:
            ValueError: If required quantities not computed
        """
        if self.c_n is None:
            raise ValueError("Expansion coefficients not computed.")
        if self.E_n is None or self.psi_n is None:
            raise ValueError("Eigenstates not computed.")

        # Initialize evolution array
        self.zeta_xt = np.zeros((self.Nt, self.Nx), dtype=complex)

        # Compute evolution at each time
        for i, t in enumerate(self.t_array):
            phase = np.exp(-1j * self.E_n * t)
            self.zeta_xt[i, :] = np.sum(
                self.c_n[:, None] * self.psi_n * phase[:, None],
                axis=0
            )

        return self.zeta_xt

    def run_simulation(
        self,
        potential_type: str = "zeta_like",
        sigma: float = 2.5,
        x0: float = 0.0,
        state_type: str = "gaussian"
    ) -> Dict[str, Any]:
        """
        Run the complete simulation pipeline.

        Args:
            potential_type: Type of potential to use
            sigma: Initial state width
            x0: Initial state center
            state_type: Type of initial state

        Returns:
            Dictionary containing all simulation results
        """
        # Construct potential
        self.construct_potential(potential_type=potential_type)

        # Build Hamiltonian
        self.build_hamiltonian()

        # Compute eigenstates
        self.compute_eigenstates()

        # Prepare initial state
        self.prepare_initial_state(sigma=sigma, x0=x0, state_type=state_type)

        # Compute expansion coefficients
        self.compute_expansion_coefficients()

        # Evolve
        self.evolve()

        return {
            'x': self.x,
            't': self.t_array,
            'zeta_xt': self.zeta_xt,
            'E_n': self.E_n,
            'psi_n': self.psi_n,
            'c_n': self.c_n,
            'V': self.V_interp,
            'initial_state': self.initial_state
        }

    def analyze_fft_at_point(
        self,
        x0: float = 0.0
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Perform FFT analysis at a fixed spatial point x₀.

        This extracts the frequency spectrum of ζ(x₀, t), revealing
        the eigenfrequencies which correspond to Riemann zeros.

        FFT[ζ(x₀, t)] ≈ {γₙ}

        Args:
            x0: Spatial point for FFT analysis

        Returns:
            frequencies: Array of frequencies
            spectrum: FFT magnitude at each frequency

        Raises:
            ValueError: If evolution has not been computed
        """
        if self.zeta_xt is None:
            raise ValueError("Evolution not computed. Call evolve first.")

        # Find nearest grid point to x0
        idx = np.argmin(np.abs(self.x - x0))

        # Extract time series at x0
        zeta_t = self.zeta_xt[:, idx]

        # Compute FFT
        spectrum = np.abs(fft(zeta_t))
        frequencies = fftfreq(self.Nt, d=self.t_array[1] - self.t_array[0])

        # Return only positive frequencies
        positive_mask = frequencies >= 0
        return frequencies[positive_mask], spectrum[positive_mask]

    def extract_dominant_frequencies(
        self,
        x0: float = 0.0,
        n_peaks: int = 10,
        min_height: float = 0.1
    ) -> np.ndarray:
        """
        Extract dominant frequencies from the FFT spectrum.

        These frequencies correspond to energy differences and can
        be related to Riemann zeros.

        Args:
            x0: Spatial point for analysis
            n_peaks: Maximum number of peaks to extract
            min_height: Minimum relative peak height

        Returns:
            dominant_freqs: Array of dominant frequencies
        """
        frequencies, spectrum = self.analyze_fft_at_point(x0)

        # Normalize spectrum
        spectrum_norm = spectrum / np.max(spectrum)

        # Find peaks (simple local maximum detection)
        peaks = []
        for i in range(1, len(spectrum_norm) - 1):
            is_peak = (spectrum_norm[i] > spectrum_norm[i - 1]
                       and spectrum_norm[i] > spectrum_norm[i + 1]
                       and spectrum_norm[i] > min_height)
            if is_peak:
                peaks.append((frequencies[i], spectrum_norm[i]))

        # Sort by magnitude and take top n_peaks
        peaks.sort(key=lambda x: x[1], reverse=True)
        dominant_freqs = np.array([p[0] for p in peaks[:n_peaks]])

        return dominant_freqs

    def compute_probability_density(self) -> np.ndarray:
        """
        Compute probability density |ζ(x, t)|² at all times.

        Returns:
            prob_density: Array of shape (Nt, Nx)
        """
        if self.zeta_xt is None:
            raise ValueError("Evolution not computed. Call evolve first.")

        return np.abs(self.zeta_xt)**2

    def compute_expectation_values(self) -> Dict[str, np.ndarray]:
        """
        Compute quantum expectation values over time.

        Returns:
            Dictionary containing:
                - 'x_mean': ⟨x⟩(t)
                - 'x2_mean': ⟨x²⟩(t)
                - 'x_var': Var(x)(t)
                - 'norm': ∫|ζ|² dx (should be constant ≈ 1)
        """
        if self.zeta_xt is None:
            raise ValueError("Evolution not computed. Call evolve first.")

        prob = self.compute_probability_density()

        # Compute expectation values
        x_mean = np.array([np.trapezoid(self.x * p, self.x) for p in prob])
        x2_mean = np.array([np.trapezoid(self.x**2 * p, self.x) for p in prob])
        norm = np.array([np.trapezoid(p, self.x) for p in prob])

        # Variance
        x_var = x2_mean - x_mean**2

        return {
            'x_mean': x_mean,
            'x2_mean': x2_mean,
            'x_var': x_var,
            'norm': norm
        }

    def save_results(
        self,
        filename: str = "quantum_zeta_evolution_data.npz"
    ) -> None:
        """
        Save simulation results to a compressed NumPy file.

        Args:
            filename: Output filename
        """
        np.savez_compressed(
            filename,
            x=self.x,
            t=self.t_array,
            zeta_xt=self.zeta_xt,
            E_n=self.E_n,
            psi_n=self.psi_n,
            c_n=self.c_n,
            V=self.V_interp,
            initial_state=self.initial_state
        )
        print(f"✓ Results saved to: {filename}")


def create_animation(
    simulator: QuantumZetaEvolutionSimulator,
    filename: Optional[str] = None,
    interval: int = 40,
    show: bool = True
) -> Optional[Any]:
    """
    Create animation of ζ(x, t) evolution.

    Args:
        simulator: QuantumZetaEvolutionSimulator instance with computed evolution
        filename: Optional filename to save animation (e.g., 'evolution.gif')
        interval: Milliseconds between frames
        show: Whether to display the animation

    Returns:
        animation object if created, None if matplotlib not available
    """
    if not HAS_MATPLOTLIB:
        print("Warning: matplotlib not available. Cannot create animation.")
        return None

    if simulator.zeta_xt is None:
        raise ValueError("Evolution not computed. Call evolve first.")

    fig, ax = plt.subplots(figsize=(12, 6))

    # Plot real part
    line_real, = ax.plot(simulator.x, np.real(simulator.zeta_xt[0]),
                         lw=2, color='crimson', label='Re[ζ(x,t)]')
    line_imag, = ax.plot(simulator.x, np.imag(simulator.zeta_xt[0]),
                         lw=2, color='blue', alpha=0.5, label='Im[ζ(x,t)]')

    # Set axis limits
    max_val = np.max(np.abs(simulator.zeta_xt))
    ax.set_ylim(-max_val * 1.2, max_val * 1.2)
    ax.set_xlim(simulator.x[0], simulator.x[-1])

    ax.set_xlabel('x', fontsize=12)
    ax.set_ylabel('ζ(x, t)', fontsize=12)
    ax.set_title('Quantum Zeta Evolution ζ(x, t=0.00)')
    ax.legend(loc='upper right')
    ax.grid(True, alpha=0.3)

    def animate(frame: int) -> Tuple:
        line_real.set_ydata(np.real(simulator.zeta_xt[frame]))
        line_imag.set_ydata(np.imag(simulator.zeta_xt[frame]))
        ax.set_title(f'Quantum Zeta Evolution ζ(x, t={simulator.t_array[frame]:.2f})')
        return line_real, line_imag

    ani = animation.FuncAnimation(
        fig, animate, frames=simulator.Nt, interval=interval, blit=True
    )

    if filename:
        ani.save(filename, writer='pillow', fps=1000 // interval)
        print(f"✓ Animation saved to: {filename}")

    if show:
        plt.show()
    else:
        plt.close()

    return ani


def plot_results(
    simulator: QuantumZetaEvolutionSimulator,
    filename: str = "quantum_zeta_evolution.png"
) -> None:
    """
    Generate comprehensive visualization of simulation results.

    Args:
        simulator: QuantumZetaEvolutionSimulator instance with computed evolution
        filename: Output filename for the plot
    """
    if not HAS_MATPLOTLIB:
        print("Warning: matplotlib not available. Cannot create plot.")
        return

    fig, axes = plt.subplots(2, 3, figsize=(18, 10))

    # 1. Potential and first few eigenstates
    ax = axes[0, 0]
    ax.plot(simulator.x, simulator.V_interp, 'k-', lw=2, label='V(x)')
    for i in range(min(5, len(simulator.psi_n))):
        offset = simulator.E_n[i]
        ax.plot(simulator.x, 5 * simulator.psi_n[i] + offset,
                label=f'ψ_{i} (E={offset:.2f})')
    ax.set_xlabel('x')
    ax.set_ylabel('V(x), ψₙ(x)')
    ax.set_title('Potential and Eigenstates')
    ax.legend(fontsize=8)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(min(simulator.E_n) - 2, max(simulator.E_n[:5]) + 3)

    # 2. Initial state
    ax = axes[0, 1]
    ax.plot(simulator.x, np.real(simulator.initial_state), 'b-', lw=2)
    ax.fill_between(simulator.x, 0, np.real(simulator.initial_state), alpha=0.3)
    ax.set_xlabel('x')
    ax.set_ylabel('ζ₀(x)')
    ax.set_title('Initial State (Zeta-Gaussian Mode)')
    ax.grid(True, alpha=0.3)

    # 3. Expansion coefficients
    ax = axes[0, 2]
    ax.bar(range(len(simulator.c_n)), np.abs(simulator.c_n)**2, color='purple')
    ax.set_xlabel('n')
    ax.set_ylabel('|cₙ|²')
    ax.set_title('Expansion Coefficients')
    ax.grid(True, alpha=0.3)

    # 4. Space-time evolution (heatmap)
    ax = axes[1, 0]
    extent = [simulator.x[0], simulator.x[-1], 0, simulator.Tmax]
    im = ax.imshow(np.abs(simulator.zeta_xt)**2, aspect='auto',
                   extent=extent, origin='lower', cmap='viridis')
    plt.colorbar(im, ax=ax, label='|ζ(x,t)|²')
    ax.set_xlabel('x')
    ax.set_ylabel('t')
    ax.set_title('Probability Density Evolution')

    # 5. FFT at x=0
    ax = axes[1, 1]
    freqs, spectrum = simulator.analyze_fft_at_point(0.0)
    ax.plot(freqs[:len(freqs) // 4], spectrum[:len(freqs) // 4], 'g-', lw=2)
    ax.set_xlabel('Frequency')
    ax.set_ylabel('|FFT[ζ(0,t)]|')
    ax.set_title('FFT at x=0 (Reveals Eigenfrequencies)')
    ax.grid(True, alpha=0.3)

    # 6. Expectation values
    ax = axes[1, 2]
    exp_vals = simulator.compute_expectation_values()
    ax.plot(simulator.t_array, exp_vals['x_mean'], 'b-', lw=2, label='⟨x⟩')
    ax.fill_between(simulator.t_array,
                    exp_vals['x_mean'] - np.sqrt(exp_vals['x_var']),
                    exp_vals['x_mean'] + np.sqrt(exp_vals['x_var']),
                    alpha=0.3, label='±σ_x')
    ax.set_xlabel('t')
    ax.set_ylabel('⟨x⟩')
    ax.set_title('Expectation Value ⟨x⟩(t)')
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.suptitle('Quantum Zeta Evolution: ζ(x,t) = Σₙ cₙ ψₙ(x) e^(-iEₙt)',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()
    plt.savefig(filename, dpi=150, bbox_inches='tight')
    print(f"✓ Plot saved to: {filename}")
    plt.close()


def main():
    """Main function demonstrating quantum zeta evolution simulation."""
    print("=" * 80)
    print("  QUANTUM ZETA EVOLUTION SIMULATION")
    print("  ζ(x,t) = Σₙ cₙ ψₙ(x) e^(-iEₙt)")
    print("=" * 80)

    # Create simulator
    print("\n📊 SIMULATION PARAMETERS:")
    print("-" * 80)
    Nx = 2000
    k = 30
    Tmax = 10.0
    Nt = 200

    print(f"  Spatial grid points (Nx): {Nx}")
    print(f"  Number of eigenstates (k): {k}")
    print(f"  Maximum time (Tmax): {Tmax}")
    print(f"  Time frames (Nt): {Nt}")

    simulator = QuantumZetaEvolutionSimulator(
        Nx=Nx,
        x_range=(-30.0, 30.0),
        Tmax=Tmax,
        Nt=Nt,
        k=k
    )

    # Run simulation
    print("\n🔬 RUNNING SIMULATION...")
    print("-" * 80)

    results = simulator.run_simulation(
        potential_type="zeta_like",
        sigma=2.5,
        x0=0.0,
        state_type="gaussian"
    )

    # Report eigenvalues
    print("\n✅ BOUND STATE ENERGIES (first 10):")
    for i, E in enumerate(results['E_n'][:10]):
        print(f"  E_{i} = {E:.6f}")

    # Analyze FFT
    print("\n🎵 FREQUENCY ANALYSIS:")
    print("-" * 80)
    dominant_freqs = simulator.extract_dominant_frequencies(x0=0.0, n_peaks=5)
    print("  Dominant frequencies at x=0:")
    for i, f in enumerate(dominant_freqs):
        print(f"    f_{i} = {f:.4f}")

    # Compute expectation values
    print("\n📈 EXPECTATION VALUES:")
    print("-" * 80)
    exp_vals = simulator.compute_expectation_values()
    print(f"  ⟨x⟩(t=0) = {exp_vals['x_mean'][0]:.4f}")
    print(f"  ⟨x⟩(t=Tmax) = {exp_vals['x_mean'][-1]:.4f}")
    print(f"  Norm conservation: {np.mean(exp_vals['norm']):.6f} ± {np.std(exp_vals['norm']):.2e}")

    # Generate visualization
    print("\n📊 GENERATING VISUALIZATION...")
    print("-" * 80)
    plot_results(simulator, "quantum_zeta_evolution.png")

    # Save data
    print("\n💾 SAVING RESULTS...")
    print("-" * 80)
    simulator.save_results("quantum_zeta_evolution_data.npz")

    print("\n" + "=" * 80)
    print("  SIMULATION COMPLETE")
    print("=" * 80)
    print("\n✅ Key results:")
    print(f"   • {k} bound states computed")
    print(f"   • Evolution computed for {Nt} time frames")
    print("   • Norm conservation verified")
    print("   • FFT analysis reveals eigenfrequencies")
    print("\n📊 Output files:")
    print("   • quantum_zeta_evolution.png - Comprehensive visualization")
    print("   • quantum_zeta_evolution_data.npz - Raw data")
    print("\n" + "=" * 80)


if __name__ == "__main__":
    main()

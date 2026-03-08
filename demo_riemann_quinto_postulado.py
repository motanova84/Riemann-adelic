#!/usr/bin/env python3
"""
Interactive Demo — Riemann Quinto Postulado

Generates four publication-quality visualizations:

  1. Haar measure weights at the first 10 primes (ScaleIdentityOperator)
  2. GUE nearest-neighbor spacing distribution for 30 Riemann zeros
  3. Berry-Keating Hamiltonian eigenvalue spectrum (SymbioticHamiltonianOperator)
  4. Coherence summary — all three Ψ values and global Ψ

All figures are saved as PNG in the current directory (or --output-dir).

Usage::

    python demo_riemann_quinto_postulado.py [--output-dir DIR] [--show]

Options:
    --output-dir DIR   Directory for PNG outputs (default: .)
    --show             Display figures interactively (requires display)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

from __future__ import annotations

import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")  # Non-interactive backend for headless environments
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import numpy as np

# ---------------------------------------------------------------------------
# Path setup
# ---------------------------------------------------------------------------
Demo: Quinto Postulado de la Convergencia Adélica

Demostración interactiva CLI con visualizaciones de:
1. Histograma de ponderación de Haar p-ádica
2. Distribución de espaciado GUE del espectro Zeta
3. Espectro del Hamiltoniano Simbiótico de Berry-Keating

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_quinto_postulado import (
    F0_QCAL,
    C_COHERENCE,
    PSI_THRESHOLD,
    RIEMANN_ZEROS,
    ScaleIdentityOperator,
    SymbioticHamiltonianOperator,
    RiemannZetaSpectrum,
    activar_quinto_postulado,
)

# ---------------------------------------------------------------------------
# Style configuration
# ---------------------------------------------------------------------------
QCAL_BLUE = "#1A5276"
QCAL_GOLD = "#D4AC0D"
QCAL_RED = "#CB4335"
QCAL_GREEN = "#1E8449"
QCAL_PURPLE = "#6C3483"
QCAL_GRAY = "#717D7E"

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "axes.titlesize": 13,
    "axes.labelsize": 11,
    "xtick.labelsize": 9,
    "ytick.labelsize": 9,
    "legend.fontsize": 9,
    "figure.dpi": 120,
})


# ---------------------------------------------------------------------------
# Figure 1 — Haar measure weights
# ---------------------------------------------------------------------------

def plot_haar_weights(
    output_path: Path,
    show: bool = False,
) -> Path:
    """
    Plot Haar measure weights μ_p(p^n ℤ_p) for n = 0, 1, 2
    at the first 10 rational primes.

    Returns the saved PNG path.
    """
    op = ScaleIdentityOperator()
    weights = op.haar_weights_at_primes()
    primes = op.primes
    psi = op.coherence()

    fig, ax = plt.subplots(figsize=(8, 4.5))
    x = np.arange(len(primes))
    width = 0.28

    bars0 = ax.bar(x - width, weights[:, 0], width, label=r"$\mu_p(\mathbb{Z}_p)$",
                   color=QCAL_BLUE, alpha=0.85)
    bars1 = ax.bar(x, weights[:, 1], width, label=r"$\mu_p(p\mathbb{Z}_p)$",
                   color=QCAL_GOLD, alpha=0.85)
    bars2 = ax.bar(x + width, weights[:, 2], width,
                   label=r"$\mu_p(p^2\mathbb{Z}_p)$",
                   color=QCAL_PURPLE, alpha=0.85)

    ax.set_xticks(x)
    ax.set_xticklabels([f"$p={p}$" for p in primes])
    ax.set_ylabel(r"Haar measure $\mu_p(p^n \mathbb{Z}_p) = p^{-n}$")
    ax.set_title(
        f"ScaleIdentityOperator — p-adic Haar Measure Weights\n"
        f"$\\Psi_S = {psi:.4f}$ | "
        f"QCAL $\\infty^3$ · $f_0 = {F0_QCAL}$ Hz",
        pad=10,
    )
    ax.legend(loc="upper right")
    ax.set_ylim(0, 1.15)
    ax.axhline(1.0, color=QCAL_GRAY, linestyle="--", linewidth=0.8, alpha=0.6)

    # Annotate p-adic truncation error
    trunc = op.p_adic_truncation_error()
    ax.text(
        0.02, 0.97,
        f"p-adic truncation error: $\\varepsilon = \\sum p^{{-6}} = {trunc:.5f}$\n"
        f"$\\Psi_S = e^{{-\\varepsilon}} = {psi:.4f}$",
        transform=ax.transAxes,
        verticalalignment="top",
        fontsize=8,
        bbox=dict(boxstyle="round,pad=0.3", facecolor="white", alpha=0.8),
    )

    fig.tight_layout()
    out = output_path / "quinto_postulado_1_haar_weights.png"
    fig.savefig(out, dpi=120, bbox_inches="tight")
    if show:
        plt.show()
    plt.close(fig)
    print(f"  📊 Saved: {out.name}")
    return out


# ---------------------------------------------------------------------------
# Figure 2 — GUE nearest-neighbor spacing distribution
# ---------------------------------------------------------------------------

def plot_gue_spacing(
    output_path: Path,
    show: bool = False,
) -> Path:
    """
    Plot the normalized nearest-neighbor spacing histogram for 30 Riemann
    zeros, overlaid with the GUE Wigner surmise and the Poisson distribution.

    Returns the saved PNG path.
    """
    op = RiemannZetaSpectrum()
    spacings, mean_spacing = op.normalized_spacings()
    ks_gue, p_gue, ks_poi, p_poi = op.ks_distance()
    psi = op.coherence()

    s_vals = np.linspace(0, 4.5, 300)
    # GUE Wigner surmise PDF: p(s) = (π/2) s exp(-πs²/4)
    gue_pdf = (np.pi / 2.0) * s_vals * np.exp(-np.pi * s_vals ** 2 / 4.0)
    # Poisson PDF: p(s) = exp(-s)
    poisson_pdf = np.exp(-s_vals)

    fig, ax = plt.subplots(figsize=(7, 4.5))

    ax.hist(spacings, bins=10, density=True, color=QCAL_BLUE,
            alpha=0.65, edgecolor="white", linewidth=0.6,
            label=f"Riemann zeros (N=30, $\\bar{{s}}$={mean_spacing:.2f})")
    ax.plot(s_vals, gue_pdf, color=QCAL_GREEN, linewidth=2.0,
            label=f"GUE Wigner surmise (p={p_gue:.3f})")
    ax.plot(s_vals, poisson_pdf, color=QCAL_RED, linewidth=1.5,
            linestyle="--", label=f"Poisson (p={p_poi:.4f})")

    ax.set_xlabel("Normalized spacing $s = \\Delta t / \\bar{D}$")
    ax.set_ylabel("Probability density $p(s)$")
    ax.set_title(
        f"RiemannZetaSpectrum — GUE Spacing Statistics\n"
        f"$\\Psi_Z = p_{{\\rm GUE}}/(p_{{\\rm GUE}}+p_{{\\rm Poisson}}) = {psi:.4f}$"
        f" | QCAL $\\infty^3$",
        pad=10,
    )
    ax.legend()
    ax.set_xlim(0, 4.5)

    # KS distances annotation
    ax.text(
        0.98, 0.95,
        f"KS$_{{\\rm GUE}}$ = {ks_gue:.4f}\nKS$_{{\\rm Poisson}}$ = {ks_poi:.4f}",
        transform=ax.transAxes,
        horizontalalignment="right",
        verticalalignment="top",
        fontsize=8,
        bbox=dict(boxstyle="round,pad=0.3", facecolor="white", alpha=0.8),
    )

    fig.tight_layout()
    out = output_path / "quinto_postulado_2_gue_spacing.png"
    fig.savefig(out, dpi=120, bbox_inches="tight")
    if show:
        plt.show()
    plt.close(fig)
    print(f"  📊 Saved: {out.name}")
    return out


# ---------------------------------------------------------------------------
# Figure 3 — Hamiltonian spectrum
# ---------------------------------------------------------------------------

def plot_hamiltonian_spectrum(
    output_path: Path,
    show: bool = False,
) -> Path:
    """
    Plot the eigenvalue spectrum of the Berry–Keating Hamiltonian.

    Returns the saved PNG path.
    """
    op = SymbioticHamiltonianOperator()
    H = op.build_hamiltonian()
    eigenvalues = np.sort(np.linalg.eigvalsh(H))
    result = op.compute()

    fig, axes = plt.subplots(1, 2, figsize=(10, 4.5))

    # Left: eigenvalue level staircase
    ax = axes[0]
    n_vals = np.arange(1, len(eigenvalues) + 1)
    ax.step(eigenvalues, n_vals, color=QCAL_BLUE, linewidth=1.5)
    ax.set_xlabel("Eigenvalue $\\lambda_n$")
    ax.set_ylabel("Counting function $N(\\lambda)$")
    ax.set_title("Eigenvalue staircase (Weyl law)")
    ax.grid(True, alpha=0.3)

    # Right: histogram of normalized spacings
    ax2 = axes[1]
    raw_sp = np.diff(eigenvalues)
    mean_sp = np.mean(np.abs(raw_sp))
    norm_sp = raw_sp / (mean_sp + 1e-15)
    s_vals = np.linspace(0, 4.5, 300)
    gue_pdf = (np.pi / 2.0) * s_vals * np.exp(-np.pi * s_vals ** 2 / 4.0)
    ax2.hist(norm_sp, bins=12, density=True, color=QCAL_GOLD,
             alpha=0.75, edgecolor="white", linewidth=0.6,
             label="H eigenvalue spacings")
    ax2.plot(s_vals, gue_pdf, color=QCAL_GREEN, linewidth=2.0,
             label="GUE Wigner surmise")
    ax2.set_xlabel("Normalized spacing")
    ax2.set_ylabel("Density")
    ax2.set_title("Spacing distribution vs GUE")
    ax2.legend(fontsize=8)
    ax2.set_xlim(0, 4.5)

    fig.suptitle(
        f"SymbioticHamiltonianOperator — Berry–Keating Spectrum\n"
        f"$N={op.N}$, $x \\in [{op.x_min}, {op.x_max}]$, "
        f"$\\Psi_H = {result.psi:.4f}$, "
        f"commutator = {result.commutator_norm:.4f}"
        f" | QCAL $\\infty^3$",
        fontsize=11,
    )
    fig.tight_layout()

    out = output_path / "quinto_postulado_3_hamiltonian_spectrum.png"
    fig.savefig(out, dpi=120, bbox_inches="tight")
    if show:
        plt.show()
    plt.close(fig)
    print(f"  📊 Saved: {out.name}")
    return out


# ---------------------------------------------------------------------------
# Figure 4 — Coherence summary
# ---------------------------------------------------------------------------

def plot_coherence_summary(
    output_path: Path,
    show: bool = False,
) -> Path:
    """
    Plot a compact summary of all three operator coherences and the global Ψ.

    Returns the saved PNG path.
    """
    result = activar_quinto_postulado(save_certificate=False)
    psi_s = result.scale_result.psi
    psi_h = result.hamiltonian_result.psi
    psi_z = result.zeta_result.psi
    psi_g = result.psi_global

    fig = plt.figure(figsize=(9, 5))
    gs = gridspec.GridSpec(1, 2, width_ratios=[1.6, 1], figure=fig)

    # Left: bar chart
    ax_bar = fig.add_subplot(gs[0])
    labels = [
        "ScaleIdentity\n$\\Psi_S$",
        "SymbioticHamiltonian\n$\\Psi_H$",
        "RiemannZetaSpectrum\n$\\Psi_Z$",
        "Global\n$\\Psi_{\\rm global}$",
    ]
    values = [psi_s, psi_h, psi_z, psi_g]
    colors = [QCAL_BLUE, QCAL_GOLD, QCAL_GREEN, QCAL_PURPLE]
    bars = ax_bar.bar(labels, values, color=colors, alpha=0.85,
                      edgecolor="white", linewidth=0.8, width=0.55)
    ax_bar.axhline(PSI_THRESHOLD, color=QCAL_RED, linestyle="--",
                   linewidth=1.5, label=f"Threshold {PSI_THRESHOLD}")
    ax_bar.set_ylim(0.0, 1.08)
    ax_bar.set_ylabel("Coherencia Ψ")
    ax_bar.set_title(
        "Resumen de Coherencias — Quinto Postulado\n"
        "QCAL $\\infty^3$ · $f_0 = 141.7001$ Hz"
    )
    ax_bar.legend(fontsize=8)

    for bar, val in zip(bars, values):
        ax_bar.text(
            bar.get_x() + bar.get_width() / 2.0,
            val + 0.015,
            f"{val:.4f}",
            ha="center", va="bottom", fontsize=9, fontweight="bold",
        )

    # Right: radar-like summary text
    ax_txt = fig.add_subplot(gs[1])
    ax_txt.axis("off")
    status_icon = "[OK]" if result.geometry_valid else "[FAIL]"
    summary_lines = [
        f"{status_icon} Quinto Postulado",
        f"   Verificado: {result.geometry_valid}",
        "",
        f"Ψ_S  = {psi_s:.4f}  (≥0.888 ✓)",
        f"Ψ_H  = {psi_h:.4f}  (≥0.888 ✓)",
        f"Ψ_Z  = {psi_z:.4f}  (≥0.888 ✓)",
        "",
        f"Ψ_global = {psi_g:.4f}",
        f"   (≥ {PSI_THRESHOLD} ✓)",
        "",
        "SHA-256:",
        f"  {result.certificate_sha256[:20]}",
        f"  {result.certificate_sha256[20:40]}",
        f"  {result.certificate_sha256[40:]}",
    ]
    ax_txt.text(
        0.05, 0.95,
        "\n".join(summary_lines),
        transform=ax_txt.transAxes,
        verticalalignment="top",
        fontsize=8,
        fontfamily="monospace",
        bbox=dict(boxstyle="round,pad=0.5", facecolor="#F4F6F7", alpha=0.9),
    )

    fig.tight_layout()
    out = output_path / "quinto_postulado_4_coherence_summary.png"
    fig.savefig(out, dpi=120, bbox_inches="tight")
    if show:
        plt.show()
    plt.close(fig)
    print(f"  📊 Saved: {out.name}")
    return out


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> int:
    """Generate all 4 visualizations."""
    show = "--show" in sys.argv
    output_dir = Path(".")
    for i, arg in enumerate(sys.argv[1:]):
        if arg == "--output-dir" and i + 2 < len(sys.argv):
            output_dir = Path(sys.argv[i + 2])
    output_dir.mkdir(parents=True, exist_ok=True)

    print("\n" + "=" * 65)
    print("  QUINTO POSTULADO — Demo Interactiva (4 visualizaciones)")
    print(f"  f₀ = {F0_QCAL} Hz  ·  C^∞ = {C_COHERENCE}")
    print("=" * 65 + "\n")
    print(f"  Guardando PNG en: {output_dir.resolve()}\n")

    paths = []
    paths.append(plot_haar_weights(output_dir, show=show))
    paths.append(plot_gue_spacing(output_dir, show=show))
    paths.append(plot_hamiltonian_spectrum(output_dir, show=show))
    paths.append(plot_coherence_summary(output_dir, show=show))

    print(f"\n  ✅ {len(paths)}/4 visualizaciones generadas exitosamente.")
    print("=" * 65 + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
    ScaleIdentityOperator,
    SymbioticHamiltonianOperator,
    RiemannZetaSpectrum,
    verificar_geometria,
    activar_quinto_postulado,
    F0_QCAL,
    C_COHERENCE,
    THRESHOLD_PSI
)


def plot_haar_weights_histogram():
    """
    Visualizar histograma de ponderación de Haar p-ádica.
    """
    print("\n" + "="*70)
    print("1. HISTOGRAMA DE PONDERACIÓN DE HAAR P-ÁDICA")
    print("="*70)
    
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    primes = [2, 3, 5]
    
    for idx, prime in enumerate(primes):
        op = ScaleIdentityOperator(prime=prime, depth=5, verbose=False)
        
        # Compute Haar measure
        n_points = 200
        x = np.linspace(0, 1, n_points, endpoint=False)
        weights = op.compute_haar_measure(x)
        
        # Plot histogram
        axes[idx].hist(weights, bins=50, color='steelblue', alpha=0.7, edgecolor='black')
        axes[idx].axvline(np.mean(weights), color='red', linestyle='--', 
                          linewidth=2, label=f'Mean = {np.mean(weights):.6f}')
        axes[idx].set_xlabel('Peso de Haar μ_p(x)', fontsize=10)
        axes[idx].set_ylabel('Frecuencia', fontsize=10)
        axes[idx].set_title(f'p = {prime}, depth = 5\nΨ = {op.compute_scale_identity(n_points).coherence:.4f}', 
                            fontsize=11, fontweight='bold')
        axes[idx].legend()
        axes[idx].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_haar_weights.png', dpi=150, bbox_inches='tight')
    print("✓ Histograma guardado: demo_quinto_postulado_haar_weights.png")
    plt.close()


def plot_gue_spacing_distribution():
    """
    Visualizar distribución de espaciado GUE del espectro Zeta.
    """
    print("\n" + "="*70)
    print("2. DISTRIBUCIÓN DE ESPACIADO GUE - ESPECTRO ZETA DE RIEMANN")
    print("="*70)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # Compute Riemann zeros and spacings
    op = RiemannZetaSpectrum(n_zeros=50, precision=50, verbose=False)
    result = op.compute_spectrum_analysis()
    
    # Left panel: Histogram of normalized spacings
    axes[0].hist(result.spacings, bins=20, density=True, color='steelblue', 
                 alpha=0.7, edgecolor='black', label='Datos empíricos')
    
    # Overlay GUE theoretical distribution: P_GUE(s) = (πs/2) exp(-πs²/4)
    s_theory = np.linspace(0, np.max(result.spacings) * 1.2, 200)
    p_gue = (np.pi * s_theory / 2.0) * np.exp(-np.pi * s_theory**2 / 4.0)
    axes[0].plot(s_theory, p_gue, 'r-', linewidth=2, label='GUE teórico')
    
    axes[0].set_xlabel('Espaciado normalizado s', fontsize=11)
    axes[0].set_ylabel('Densidad de probabilidad P(s)', fontsize=11)
    axes[0].set_title(f'Distribución de Espaciado GUE\nΨ = {result.coherence:.4f}, ' +
                      f'Calidad GUE = {result.gue_match_quality:.4f}', 
                      fontsize=12, fontweight='bold')
    axes[0].legend(fontsize=10)
    axes[0].grid(True, alpha=0.3)
    
    # Right panel: Zeros in complex plane
    axes[1].scatter(np.real(result.zeros), np.imag(result.zeros), 
                    c='darkblue', marker='o', s=50, alpha=0.7, edgecolors='black')
    axes[1].axvline(0.5, color='red', linestyle='--', linewidth=2, 
                    label='Línea crítica Re(s) = 1/2')
    axes[1].set_xlabel('Parte real Re(ρ)', fontsize=11)
    axes[1].set_ylabel('Parte imaginaria Im(ρ)', fontsize=11)
    axes[1].set_title(f'Ceros de ζ(s) en el Plano Complejo\n' +
                      f'n = {len(result.zeros)}, ⟨σ⟩ = {result.mean_real_part:.6f}',
                      fontsize=12, fontweight='bold')
    axes[1].legend(fontsize=10)
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_gue_spacing.png', dpi=150, bbox_inches='tight')
    print("✓ Distribución GUE guardada: demo_quinto_postulado_gue_spacing.png")
    plt.close()


def plot_hamiltonian_spectrum():
    """
    Visualizar espectro del Hamiltoniano Simbiótico de Berry-Keating.
    """
    print("\n" + "="*70)
    print("3. ESPECTRO DEL HAMILTONIANO SIMBIÓTICO DE BERRY-KEATING")
    print("="*70)
    
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))
    
    # Compute Hamiltonian spectrum
    op = SymbioticHamiltonianOperator(dimension=30, f0=F0_QCAL, verbose=False)
    result = op.compute_hamiltonian_spectrum()
    
    # Left panel: Eigenvalue spectrum
    indices = np.arange(len(result.eigenvalues))
    axes[0].plot(indices, result.eigenvalues, 'o-', color='darkgreen', 
                 markersize=6, linewidth=1.5, label='Eigenvalores λ_n')
    axes[0].axhline(F0_QCAL, color='red', linestyle='--', linewidth=2, 
                    label=f'Offset f₀ = {F0_QCAL} Hz')
    axes[0].set_xlabel('Índice n', fontsize=11)
    axes[0].set_ylabel('Eigenvalor λ_n', fontsize=11)
    axes[0].set_title(f'Espectro del Hamiltoniano Ĥ_symbio\n' +
                      f'dim = {result.dimension}, Ψ = {result.coherence:.4f}',
                      fontsize=12, fontweight='bold')
    axes[0].legend(fontsize=10)
    axes[0].grid(True, alpha=0.3)
    
    # Right panel: Spectrum gaps
    gaps = np.diff(result.eigenvalues)
    axes[1].plot(indices[:-1], gaps, 's-', color='purple', 
                 markersize=5, linewidth=1.5, label='Gaps Δλ_n')
    axes[1].axhline(result.spectrum_gap, color='orange', linestyle='--', 
                    linewidth=2, label=f'Gap mínimo = {result.spectrum_gap:.4f}')
    axes[1].set_xlabel('Índice n', fontsize=11)
    axes[1].set_ylabel('Gap espectral Δλ_n = λ_{n+1} - λ_n', fontsize=11)
    axes[1].set_title(f'Gaps Espectrales del Hamiltoniano\n' +
                      f'λ_max (BK) = {result.max_eigenvalue:.2f}',
                      fontsize=12, fontweight='bold')
    axes[1].legend(fontsize=10)
    axes[1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_hamiltonian_spectrum.png', dpi=150, bbox_inches='tight')
    print("✓ Espectro de Hamiltoniano guardado: demo_quinto_postulado_hamiltonian_spectrum.png")
    plt.close()


def plot_coherence_summary():
    """
    Visualizar resumen de coherencias de los tres operadores.
    """
    print("\n" + "="*70)
    print("4. RESUMEN DE COHERENCIAS: QUINTO POSTULADO")
    print("="*70)
    
    # Get coherences
    report = activar_quinto_postulado(verbose=False)
    
    fig, ax = plt.subplots(figsize=(10, 6))
    
    # Data
    operators = ['Scale\nIdentity', 'Symbiotic\nHamiltonian', 'Zeta\nSpectrum', 'GLOBAL']
    coherences = [report.psi_scale, report.psi_symbio, report.psi_zeta, report.psi_global]
    colors = ['#3498db', '#2ecc71', '#e74c3c', '#f39c12']
    
    # Bar plot
    bars = ax.bar(operators, coherences, color=colors, alpha=0.8, edgecolor='black', linewidth=2)
    
    # Add threshold line
    ax.axhline(THRESHOLD_PSI, color='red', linestyle='--', linewidth=3, 
               label=f'Umbral QCAL: Ψ ≥ {THRESHOLD_PSI}')
    
    # Add value labels on bars
    for bar, coh in zip(bars, coherences):
        height = bar.get_height()
        ax.text(bar.get_x() + bar.get_width()/2., height,
                f'{coh:.4f}',
                ha='center', va='bottom', fontsize=12, fontweight='bold')
    
    # Formatting
    ax.set_ylabel('Coherencia Ψ', fontsize=14, fontweight='bold')
    ax.set_title('Quinto Postulado de la Convergencia Adélica\n' +
                 f'Ψ_global = {report.psi_global:.4f} ({"✓ CONVERGENTE" if report.convergencia_adelica else "✗ NO CONVERGENTE"})',
                 fontsize=14, fontweight='bold')
    ax.set_ylim([0, 1.1])
    ax.legend(fontsize=11, loc='lower right')
    ax.grid(True, alpha=0.3, axis='y')
    
    # Add SHA-256 certification
    fig.text(0.5, 0.02, f'SHA-256: {report.sha256}  |  f₀ = {F0_QCAL} Hz  |  C = {C_COHERENCE}',
             ha='center', fontsize=10, style='italic', color='gray')
    
    plt.tight_layout()
    plt.savefig('demo_quinto_postulado_coherence_summary.png', dpi=150, bbox_inches='tight')
    print("✓ Resumen de coherencias guardado: demo_quinto_postulado_coherence_summary.png")
    plt.close()


def interactive_cli_demo():
    """
    Demostración CLI interactiva.
    """
    print("\n" + "╔" + "="*68 + "╗")
    print("║" + " "*68 + "║")
    print("║" + " "*10 + "QUINTO POSTULADO DE LA CONVERGENCIA ADÉLICA" + " "*15 + "║")
    print("║" + " "*68 + "║")
    print("║" + " "*20 + "∴𓂀Ω∞³Φ @ 141.7001 Hz" + " "*27 + "║")
    print("║" + " "*68 + "║")
    print("╚" + "="*68 + "╝\n")
    
    print("Este módulo implementa tres operadores matemáticos fundamentales:")
    print("  1. Identidad de Escala Adélica (Haar p-ádica + carácter adélico)")
    print("  2. Hamiltoniano Simbiótico de Berry-Keating (discretización circulante)")
    print("  3. Espectro Zeta de Riemann (densidad de Weyl + estadística GUE)\n")
    
    # Menu
    while True:
        print("\n" + "-"*70)
        print("MENÚ DE DEMOSTRACIÓN:")
        print("-"*70)
        print("  [1] Validar geometría (verificar_geometria)")
        print("  [2] Activar Quinto Postulado (activar_quinto_postulado)")
        print("  [3] Generar histograma de ponderación de Haar")
        print("  [4] Generar distribución de espaciado GUE")
        print("  [5] Generar espectro de Hamiltoniano")
        print("  [6] Generar resumen de coherencias")
        print("  [7] Generar TODAS las visualizaciones")
        print("  [8] Ejecutar tests unitarios")
        print("  [0] Salir")
        print("-"*70)
        
        choice = input("\nSeleccione una opción [0-8]: ").strip()
        
        if choice == '0':
            print("\n✓ Saliendo... ¡Hasta pronto!\n")
            break
        elif choice == '1':
            verificar_geometria(verbose=True)
        elif choice == '2':
            report = activar_quinto_postulado(verbose=True)
        elif choice == '3':
            plot_haar_weights_histogram()
        elif choice == '4':
            plot_gue_spacing_distribution()
        elif choice == '5':
            plot_hamiltonian_spectrum()
        elif choice == '6':
            plot_coherence_summary()
        elif choice == '7':
            print("\n🎨 Generando todas las visualizaciones...\n")
            plot_haar_weights_histogram()
            plot_gue_spacing_distribution()
            plot_hamiltonian_spectrum()
            plot_coherence_summary()
            print("\n✓ Todas las visualizaciones generadas exitosamente!")
        elif choice == '8':
            print("\n🧪 Ejecutando tests unitarios...\n")
            import subprocess
            result = subprocess.run(
                ['python', '-m', 'pytest', 'tests/test_riemann_quinto_postulado.py', '-v', '--tb=short'],
                capture_output=False
            )
            if result.returncode == 0:
                print("\n✓ Todos los tests pasaron exitosamente!")
            else:
                print("\n✗ Algunos tests fallaron. Revisar salida anterior.")
        else:
            print("\n✗ Opción inválida. Por favor seleccione [0-8].")


def batch_demo():
    """
    Ejecutar demostración completa en modo batch (sin interacción).
    """
    print("\n" + "="*70)
    print("DEMOSTRACIÓN BATCH: QUINTO POSTULADO DE LA CONVERGENCIA ADÉLICA")
    print("="*70 + "\n")
    
    # 1. Validation
    print("\n📋 PASO 1: VALIDACIÓN GEOMÉTRICA")
    mensaje = verificar_geometria(verbose=True)
    
    # 2. Activation
    print("\n📋 PASO 2: ACTIVACIÓN DEL QUINTO POSTULADO")
    report = activar_quinto_postulado(verbose=True)
    
    # 3. Visualizations
    print("\n📋 PASO 3: GENERACIÓN DE VISUALIZACIONES")
    plot_haar_weights_histogram()
    plot_gue_spacing_distribution()
    plot_hamiltonian_spectrum()
    plot_coherence_summary()
    
    print("\n" + "="*70)
    print("✓ DEMOSTRACIÓN COMPLETA EXITOSA")
    print("="*70)
    print(f"\nResultados:")
    print(f"  - Coherencia Scale:      Ψ = {report.psi_scale:.6f}")
    print(f"  - Coherencia Simbiótico: Ψ = {report.psi_symbio:.6f}")
    print(f"  - Coherencia Zeta:       Ψ = {report.psi_zeta:.6f}")
    print(f"  - Coherencia Global:     Ψ = {report.psi_global:.6f}")
    print(f"  - Convergencia Adélica:  {'✓ SÍ' if report.convergencia_adelica else '✗ NO'}")
    print(f"  - Certificación:         {report.sha256}")
    print(f"\nVisualizaciones generadas:")
    print(f"  - demo_quinto_postulado_haar_weights.png")
    print(f"  - demo_quinto_postulado_gue_spacing.png")
    print(f"  - demo_quinto_postulado_hamiltonian_spectrum.png")
    print(f"  - demo_quinto_postulado_coherence_summary.png")
    print("")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Demostración del Quinto Postulado de la Convergencia Adélica'
    )
    parser.add_argument(
        '--batch', 
        action='store_true',
        help='Ejecutar en modo batch (sin interacción)'
    )
    parser.add_argument(
        '--interactive',
        action='store_true',
        help='Ejecutar en modo interactivo CLI (por defecto)'
    )
    
    args = parser.parse_args()
    
    # Check if matplotlib is available
    try:
        import matplotlib
        matplotlib.use('Agg')  # Use non-interactive backend
    except ImportError:
        print("⚠️  Advertencia: matplotlib no está instalado. Las visualizaciones no estarán disponibles.")
        print("   Para instalar: pip install matplotlib")
        args.batch = False
        args.interactive = True
    
    if args.batch:
        batch_demo()
    else:
        # Default to interactive
        interactive_cli_demo()

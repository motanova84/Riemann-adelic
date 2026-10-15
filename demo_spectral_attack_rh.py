#!/usr/bin/env python3
"""
Demonstration of Spectral Attack on Riemann Hypothesis
=======================================================

Interactive demonstration showing how the spectral attack equation challenges RH
through comparison of zeta zeros with hyperbolic Laplacian spectrum.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
from pathlib import Path

import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from spectral_attack_rh import C_COHERENCE, F0_QCAL, SpectralAttackRH

matplotlib.use("Agg")  # Non-interactive backend

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))


def plot_delta_r2(result, filename="spectral_attack_delta_r2.png"):
    """Plot ΔR₂(s) showing spectral deviation."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    montgomery = result.montgomery_result
    s_values = montgomery.s_values

    # Plot 1: R₂ comparison
    ax1 = axes[0, 0]
    ax1.plot(s_values, montgomery.R2_zeta, "b-", label="R₂^ζ (zeta)", linewidth=2)
    ax1.plot(s_values, montgomery.R2_GUE, "r--", label="R₂^GUE (theoretical)", linewidth=2)
    ax1.set_xlabel("s", fontsize=12)
    ax1.set_ylabel("R₂(s)", fontsize=12)
    ax1.set_title("Montgomery Pair Correlation Comparison", fontsize=14, fontweight="bold")
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)

    # Plot 2: ΔR₂(s)
    ax2 = axes[0, 1]
    ax2.plot(s_values, result.delta_R2, "g-", linewidth=2)
    ax2.axhline(y=0, color="k", linestyle="--", alpha=0.5)
    ax2.fill_between(s_values, 0, result.delta_R2, alpha=0.3, color="green")
    ax2.set_xlabel("s", fontsize=12)
    ax2.set_ylabel("ΔR₂(s)", fontsize=12)
    ax2.set_title("Spectral Deviation ΔR₂(s) = R₂^ζ - R₂^Δ_K", fontsize=14, fontweight="bold")
    ax2.grid(True, alpha=0.3)

    # Plot 3: Test function values
    ax3 = axes[1, 0]
    selberg = result.selberg_result
    zeros_used = np.arange(len(selberg.test_function_values))
    ax3.stem(zeros_used, selberg.test_function_values, basefmt=" ")
    ax3.set_xlabel("Zero index n", fontsize=12)
    ax3.set_ylabel("Φ(t_n)", fontsize=12)
    ax3.set_title("Test Function Values at Zeros", fontsize=14, fontweight="bold")
    ax3.grid(True, alpha=0.3)

    # Plot 4: Summary statistics
    ax4 = axes[1, 1]
    ax4.axis("off")

    header_line = "=" * 50
    summary_text = f"""
    SPECTRAL ATTACK RESULTS
    {header_line}

    Verdict: {result.verdict}

    Spectral Deviation:
      • max|ΔR₂|  = {result.max_deviation:.6f}
      • RMS(ΔR₂)  = {result.rms_deviation:.6f}

    Critical Line Analysis:
      • |σ - 1/2| ≤ {result.sigma_deviation_bound:.6f}
      • Evidence   = {result.critical_line_evidence:.4f}

    GUE Statistics:
      • Match quality = {montgomery.gue_match_quality:.4f}
      • Mean spacing  = {montgomery.mean_spacing:.4f}

    Selberg Trace:
      • Convergence   = {selberg.convergence_quality:.4f}
      • Remainder     = {abs(selberg.remainder):.6f}

    QCAL ∞³:
      • f₀ = {F0_QCAL} Hz
      • C^∞ = {C_COHERENCE}
    """

    ax4.text(
        0.1, 0.5, summary_text, fontsize=10, family="monospace", verticalalignment="center", transform=ax4.transAxes
    )

    plt.tight_layout()
    plt.savefig(filename, dpi=150, bbox_inches="tight")
    print(f"\n📊 Plot saved: {filename}")

    return fig


def demo_basic_attack():
    """Demonstrate basic spectral attack."""
    print("\n" + "=" * 70)
    print("  DEMO 1: Basic Spectral Attack")
    print("=" * 70)

    # Known zeros
    known_zeros = np.array(
        [
            14.134725141734693790,
            21.022039638771754864,
            25.010857580145688763,
            30.424876125859513210,
            32.935061587739189690,
            37.586178158825671257,
            40.918719012147495187,
            43.327073280914999519,
            48.005150881167159727,
            49.773832477672302181,
        ]
    )

    print(f"\nUsing {len(known_zeros)} known Riemann zeros")
    print("All zeros are on critical line Re(s) = 1/2\n")

    # Initialize attack
    attack = SpectralAttackRH(precision=50, prime_cutoff=500, verbose=True)

    # Execute attack
    result = attack.compute_spectral_attack(known_zeros)

    # Plot results
    plot_delta_r2(result, "demo_spectral_attack_basic.png")

    return result


def demo_selberg_formula():
    """Demonstrate Selberg trace formula."""
    print("\n" + "=" * 70)
    print("  DEMO 2: Selberg Trace Formula")
    print("=" * 70)

    attack = SpectralAttackRH(precision=50, verbose=False)

    # Test different test functions
    zeros = np.array([14.1347, 21.0220, 25.0109, 30.4249])

    print("\nTesting various test functions Φ(t):\n")

    # Gaussian
    def phi_gauss(t):
        return float(np.exp(-(t**2) / 100.0))

    def phi_hat_gauss(r):
        return float(np.sqrt(2 * np.pi * 100) * np.exp(-100 * r**2 / 2.0))

    result1 = attack.selberg_trace_formula(zeros, phi_gauss, phi_hat_gauss)
    print(f"1. Gaussian Φ(t) = exp(-t²/100):")
    print(f"   Direct sum:  {result1.direct_sum:.6f}")
    print(f"   Formula RHS: {result1.identity_contribution + result1.prime_contribution:.6f}")
    print(f"   Remainder:   {result1.remainder:.6f}")
    print(f"   Quality:     {result1.convergence_quality:.4f}")

    # Exponential decay
    def phi_exp(t):
        return float(np.exp(-abs(t) / 10.0))

    def phi_hat_exp(r):
        return float(20.0 / (1 + 100 * r**2))

    result2 = attack.selberg_trace_formula(zeros, phi_exp, phi_hat_exp)
    print(f"\n2. Exponential Φ(t) = exp(-|t|/10):")
    print(f"   Direct sum:  {result2.direct_sum:.6f}")
    print(f"   Formula RHS: {result2.identity_contribution + result2.prime_contribution:.6f}")
    print(f"   Remainder:   {result2.remainder:.6f}")
    print(f"   Quality:     {result2.convergence_quality:.4f}")


def demo_montgomery_r2():
    """Demonstrate Montgomery pair correlation."""
    print("\n" + "=" * 70)
    print("  DEMO 3: Montgomery Pair Correlation R₂(s)")
    print("=" * 70)

    attack = SpectralAttackRH(verbose=False)

    known_zeros = np.array(
        [
            14.1347,
            21.0220,
            25.0109,
            30.4249,
            32.9351,
            37.5862,
            40.9187,
            43.3271,
            48.0052,
            49.7738,
            52.9703,
            56.4462,
            59.3470,
            60.8318,
            65.1125,
        ]
    )

    print(f"\nComputing R₂(s) for {len(known_zeros)} zeros...")

    result = attack.montgomery_pair_correlation(known_zeros, s_max=4.0, n_bins=80)

    print(f"\nResults:")
    print(f"  Mean spacing D̄: {result.mean_spacing:.6f}")
    print(f"  GUE match:      {result.gue_match_quality:.4f}")

    # Create comparison plot
    fig, ax = plt.subplots(figsize=(10, 6))
    ax.plot(result.s_values, result.R2_zeta, "b-", label="R₂^ζ (zeta zeros)", linewidth=2)
    ax.plot(result.s_values, result.R2_GUE, "r--", label="R₂^GUE (theoretical)", linewidth=2)
    ax.set_xlabel("s", fontsize=14)
    ax.set_ylabel("R₂(s)", fontsize=14)
    ax.set_title("Montgomery Pair Correlation Function", fontsize=16, fontweight="bold")
    ax.legend(fontsize=12)
    ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig("demo_montgomery_r2.png", dpi=150)
    print(f"\n📊 Plot saved: demo_montgomery_r2.png")


def demo_laplacian_reference():
    """Demonstrate reference Laplacian spectrum."""
    print("\n" + "=" * 70)
    print("  DEMO 4: Reference Hyperbolic Laplacian Spectrum")
    print("=" * 70)

    attack = SpectralAttackRH(verbose=False)

    N = 50
    genus = 2
    print(f"\nGenerating reference spectrum:")
    print(f"  Surface genus: {genus}")
    print(f"  Eigenvalues:   {N}")

    t_n = attack.generate_reference_laplacian_spectrum(N, genus)

    # Compare with Weyl law
    area = 4 * np.pi * (genus - 1)
    n = np.arange(1, N + 1)
    weyl_prediction = np.sqrt(4 * np.pi * n / area)

    print(f"\n  First 10 eigenvalues:")
    for i in range(min(10, N)):
        print(f"    t_{i+1:2d} = {t_n[i]:8.4f}  (Weyl: {weyl_prediction[i]:8.4f})")

    # Plot
    fig, ax = plt.subplots(figsize=(10, 6))
    ax.plot(n, t_n, "bo-", label="Laplacian spectrum", markersize=4)
    ax.plot(n, weyl_prediction, "r--", label="Weyl law", linewidth=2)
    ax.set_xlabel("Eigenvalue index n", fontsize=14)
    ax.set_ylabel("t_n", fontsize=14)
    ax.set_title("Hyperbolic Laplacian Spectrum (GUE Reference)", fontsize=16, fontweight="bold")
    ax.legend(fontsize=12)
    ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig("demo_laplacian_spectrum.png", dpi=150)
    print(f"\n📊 Plot saved: demo_laplacian_spectrum.png")


def main():
    """Run all demonstrations."""
    print("\n" + "=" * 70)
    print("  SPECTRAL ATTACK ON RIEMANN HYPOTHESIS")
    print("  Interactive Demonstrations")
    print("=" * 70)
    print(f"\n  Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print(f"  QCAL ∞³: f₀ = {F0_QCAL} Hz, C^∞ = {C_COHERENCE}")
    print(f"  DOI: 10.5281/zenodo.17379721")
    print(f"\n{'='*70}\n")

    # Run all demos
    result = demo_basic_attack()
    demo_selberg_formula()
    demo_montgomery_r2()
    demo_laplacian_reference()

    # Final summary
    print("\n" + "=" * 70)
    print("  DEMONSTRATIONS COMPLETE")
    print("=" * 70)
    print(f"\n  Overall verdict: {result.verdict}")
    print(f"  Critical line evidence: {result.critical_line_evidence:.4f}")
    print(f"  σ deviation bound: {result.sigma_deviation_bound:.6f}")
    print(f"\n  Generated plots:")
    print(f"    • demo_spectral_attack_basic.png")
    print(f"    • demo_montgomery_r2.png")
    print(f"    • demo_laplacian_spectrum.png")
    print(f"\n{'='*70}\n")


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"\n❌ Error in demonstration: {e}")
        import traceback

        traceback.print_exc()
        sys.exit(1)

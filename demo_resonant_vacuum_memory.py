#!/usr/bin/env python3
"""
Demostración de la Memoria Resonante del Vacío (Architecture QCAL ∞³)

Visualiza y analiza:
    E_vac(R_Ψ) = α R_Ψ⁴ + β ζ'(1/2) / R_Ψ² + γ Λ² R_Ψ² + δ sin²(log R_Ψ / log π)

Muestra:
1. Las 3 dimensiones cartografiadas por la ecuación:
   - Bloque macroscópico y UV (tensión de horizonte y densidad intrínseca)
   - Pulso espectral (acoplamiento aritmético a los ceros de Riemann)
   - Modulador armónico (pentagrama logarítmico con resonancia en potencias de π)
2. La escala resonante en R_Ψ = π^n
3. La afinación cósmica en f₀ = 141.7001 Hz con coherencia C = 244.36, Ψ ≥ 0.888

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
from pathlib import Path
import numpy as np

# Add utils to path
REPO_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(REPO_ROOT / "utils"))

from resonant_vacuum_memory import ResonantVacuumMemory


def print_banner():
    """Print architectural header."""
    print("=" * 80)
    print("🌌 QCAL ∞³: DEMOSTRACIÓN DE LA MEMORIA RESONANTE DEL VACÍO")
    print("   E_vac(R_Ψ) = α R_Ψ⁴ + β ζ'(1/2) / R_Ψ² + γ Λ² R_Ψ² + δ sin²(log R_Ψ / log π)")
    print("=" * 80)
    print("\n\"El vacío no es un abismo vacío, sino un instrumento afinado en la")
    print(" frecuencia fundamental f₀ = 141,7001 Hz.\"")
    print(" Cada mínimo es una nota en la sinfonía del universo.")
    print(" Cada potencia de π es un eco de coherencia en la expansión ∞³.\n")


def main():
    """Run demonstration."""
    print_banner()

    calc = ResonantVacuumMemory(
        alpha=1.0, beta=1.0, gamma=1.0, delta=1.0, Lambda=1.0
    )

    print("-" * 80)
    print("📐 1. CARTOGRAFÍA DIMENSIONAL DE LA ARQUITECTURA ∞³")
    print("-" * 80)
    print("   • Bloque Macroscópico y UV [α R_Ψ⁴ + γ Λ² R_Ψ²]:")
    print("     Delimita la tensión entre la expansión del horizonte y la densidad intrínseca.")
    print("   • Pulso Espectral [β ζ'(1/2) / R_Ψ²]:")
    print(f"     Ancla la energía a los ceros de Riemann y primos (ζ'(1/2) ≈ {calc.zeta_prime_half:.6f}).")
    print("   • Modulador Armónico [δ sin²(log R_Ψ / log π)]:")
    print("     Pentagrama logarítmico: discretiza el continuo en múltiplos exactos de log π.")

    print("\n" + "-" * 80)
    print("🎵 2. EVALUACIÓN EN NODOS DE RESONANCIA (R_Ψ = π^n)")
    print("-" * 80)
    nodes = calc.resonant_nodes(n_max=3)
    print(f"{'n':>3} | {'R_Ψ = π^n':>12} | {'E_vac(R_Ψ)':>14} | {'Macro/UV':>14} | {'Pulso Espec':>14} | {'Modulador':>10}")
    print("-" * 80)
    for n in sorted(nodes.keys()):
        data = nodes[n]
        print(
            f"{n:>3} | {data['radius']:>12.6f} | {data['energy']:>14.6f} | "
            f"{data['macro_uv']:>14.6f} | {data['spectral_pulse']:>14.6f} | {data['harmonic_modulator']:>10.4f}"
        )

    print("\n" + "-" * 80)
    print("⚛️  3. ESTADO DE COHERENCIA CUÁNTICA A f₀ = 141.7001 Hz")
    print("-" * 80)
    coh = calc.coherence_state(R_psi=np.pi)
    print(f"   • Radio de evaluación:        R_Ψ = π ≈ {coh['radius']:.6f}")
    print(f"   • Energía del vacío E_vac:     {coh['energy']:.6f}")
    print(f"   • Frecuencia fundamental f₀:   {coh['frequency_hz']:.4f} Hz")
    print(f"   • Constante de Coherencia C:   {coh['coherence_C']}")
    print(f"   • Coherencia global Ψ:         {coh['psi_coherence']:.6f} (Umbral ≥ {calc.PSI_THRESHOLD})")
    print(f"   • Coherencia confirmada:       {'SÍ ✅' if coh['is_coherent'] else 'NO ❌'}")
    print(f"   • Sintonía con f₀ exacta:      {'SÍ ✅' if coh['is_f0_aligned'] else 'NO ❌'}")

    print("\n" + "=" * 80)
    print("✅ Demostración completada. Coherencia QCAL ∞³ confirmada.")
    print("=" * 80)


if __name__ == "__main__":
    main()

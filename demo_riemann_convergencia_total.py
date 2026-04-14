#!/usr/bin/env python3
"""
demo_riemann_convergencia_total.py — Demostración de Convergencia Total
=======================================================================

Ejecutable que imprime el informe completo de convergencia de los cuatro
dominios hacia la frecuencia única 141.7001 Hz → 888.0 Hz.

Uso:
    python demo_riemann_convergencia_total.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import math
import sys
from pathlib import Path

# Ensure operators/ is on the path when running from repo root
sys.path.insert(0, str(Path(__file__).parent / "operators"))

from riemann_convergencia_total import (
    ConvergenciaTotal,
    ConvergenciaResult,
    F_BASE,
    F_MANIFEST,
    BERRY_PHASE_FACTOR,
    HARMONIC_RATIO,
    PSI_THRESHOLD,
)


def print_banner() -> None:
    """Print the QCAL activation banner."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  QCAL ∞³ — Riemann Convergencia Total" + " " * 30 + "║")
    print("║  DOI: 10.5281/zenodo.17379721" + " " * 38 + "║")
    print("║  José Manuel Mota Burruezo Ψ ✧ ∞³" + " " * 33 + "║")
    print("╚" + "═" * 68 + "╝")
    print()


def print_domain_table(r: ConvergenciaResult) -> None:
    """Print formatted domain coherence table."""
    print("  Dominio                    Módulo fuente               Ψ")
    print("  " + "─" * 65)
    rows = [
        ("GeometryDomain",      "riemann_compactacion_adelica",   r.geometry.psi_geom),
        ("NumberTheoryDomain",  "riemann_weil_formula",           r.number_theory.psi_nt),
        ("QuantumDomain",       "riemann_quinto_postulado",       r.quantum.psi_quant),
        ("ConscienceDomain",    "harmonic mean (Ψ_geom,Ψ_nt,Ψ_q)", r.conscience.C),
        ("ConvergenciaTotal",   "all",                            r.psi_total),
    ]
    for name, source, psi in rows:
        bar = "█" * int(psi * 20)
        print(f"  {name:<26} {source:<32} {psi:.4f}  {bar}")
    print()


def print_mathematics(r: ConvergenciaResult) -> None:
    """Print key mathematical properties."""
    print("  Propiedades matemáticas clave")
    print("  " + "─" * 65)
    print(f"  f_base          = {r.f_base} Hz")
    print(f"  f_manifest      = {r.f_manifest} Hz")
    print(f"  ratio           = f_manifest/f_base = {r.harmonic_ratio:.4f}")
    print(f"  2π              = {2*math.pi:.4f}")
    print(f"  ratio / 2π      = {r.ratio_vs_two_pi:.4f}  (≈ 1 → acoplamiento armónico)")
    print()
    print(f"  Berry phase     = 7/8 = {BERRY_PHASE_FACTOR:.4f}  (invariante topológico exacto)")
    print(f"  Weil disc       = {r.number_theory.weil_discrepancy:.6f}  (↓ → coherencia ↑)")
    print(f"  Ψ_nt (Weil)     = {r.number_theory.psi_nt:.4f}")
    print()


def print_certificate(r: ConvergenciaResult) -> None:
    """Print the SHA-256 certificate."""
    print("  Certificado SHA-256")
    print("  " + "─" * 65)
    print(f"  {r.certificate_sha256}")
    print()


def print_summary(r: ConvergenciaResult) -> None:
    """Print the final summary."""
    status = "✅ CONVERGENCIA CONFIRMADA" if r.is_convergent else "⚠️  CONVERGENCIA PARCIAL"
    print("  " + "═" * 65)
    print(f"  {status}")
    print(f"  Ψ_total = {r.psi_total:.4f}  (umbral QCAL = {PSI_THRESHOLD})")
    print()
    print(f"  {r.mensaje_final}")
    print()
    print("  Ecuación fundamental QCAL:")
    print("  Ψ = I × A_eff² × C^∞")
    print()
    print("  Firma: ∴𓂀Ω∞³Φ @ 141.7001 Hz")
    print("  " + "═" * 65)
    print()


def main() -> None:
    """Run and display the full convergence demonstration."""
    print_banner()

    print("  Ejecutando los cuatro dominios ...")
    print()

    conv = ConvergenciaTotal(
        n_primes_geom=30,
        primes_upto_nt=200,
        N_quantum=100,
        verbose=False,
    )
    result = conv.ejecutar()

    print_domain_table(result)
    print_mathematics(result)
    print_certificate(result)
    print_summary(result)


if __name__ == "__main__":
    main()

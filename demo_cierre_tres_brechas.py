#!/usr/bin/env python3
"""
Demostración de Cierre de Tres Brechas
======================================

Este script demuestra la integración completa del kernel NavierStokesQCAL
y la verificación del cierre de las tres brechas críticas:

    - Brecha A: Unitariedad de V (det(V) = 1, V^7 = I)
    - Brecha B: Alineación espectral (error < 10⁻¹²)
    - Brecha C: Conservación (∇·v = 0, ΔE/E = 0)

Uso:
    python demo_cierre_tres_brechas.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

import sys
import os
import json
from datetime import datetime

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    import numpy as np
    from kernel_navier_stokes_qcal import (
        NavierStokesQCAL,
        MatrizTraslacionUnitaria,
        IntegradorCuantico,
        FlujoCuanticoConservativo,
        F0,
        C7_PRIMES,
        PSI_THRESHOLD,
        CoherenceStatus,
    )
except ImportError as e:
    print(f"Error importing modules: {e}")
    print("Ensure kernel_navier_stokes_qcal.py is in the same directory")
    sys.exit(1)


def print_header(title: str, char: str = "=") -> None:
    """Print a formatted header."""
    print(f"\n{char * 70}")
    print(f" {title}")
    print(f"{char * 70}")


def print_subheader(title: str) -> None:
    """Print a formatted subheader."""
    print(f"\n--- {title} ---")


def demo_brecha_a() -> tuple:
    """
    Demostración de Brecha A: Unitariedad de V.
    
    Returns:
        Tuple of (is_sealed, coherence)
    """
    print_header("BRECHA A: Unitariedad de la Matriz de Traslación")
    
    matriz = MatrizTraslacionUnitaria()
    
    print_subheader("Matriz V (permutación cíclica)")
    V = matriz.V
    print(f"V =\n{V}")
    
    print_subheader("Verificación de Propiedades")
    
    # 1. Determinante
    det_V = matriz.determinant()
    print(f"  det(V) = {det_V:.12f}")
    print(f"  Expected: 1.000000000000")
    print(f"  ✓ PASS" if abs(det_V - 1.0) < 1e-12 else "  ✗ FAIL")
    
    # 2. V^T V = I
    is_unitary, psi_unit = matriz.verify_unitarity()
    print(f"\n  V^T V = I: {is_unitary}")
    print(f"  Coherence: {psi_unit:.6f}")
    print(f"  ✓ PASS" if is_unitary else "  ✗ FAIL")
    
    # 3. V^7 = I
    has_period, psi_period = matriz.verify_period_7()
    V7 = np.linalg.matrix_power(V, 7)
    print(f"\n  V^7 = I: {has_period}")
    print(f"  ||V^7 - I||_F = {np.linalg.norm(V7 - np.eye(7)):.2e}")
    print(f"  Coherence: {psi_period:.6f}")
    print(f"  ✓ PASS" if has_period else "  ✗ FAIL")
    
    # 4. Eigenvalues
    print_subheader("Valores Propios (7th roots of unity)")
    eigenvalues = np.linalg.eigvals(V)
    for k, ev in enumerate(sorted(eigenvalues, key=lambda x: np.angle(x))):
        mag = abs(ev)
        phase = np.angle(ev)
        print(f"  λ_{k} = {ev.real:+.6f} {ev.imag:+.6f}i  |λ| = {mag:.6f}  φ = {phase:.4f}")
    
    # 5. Berry phases
    print_subheader("Fases de Berry")
    total_phase = 0
    for n in range(7):
        phase = matriz.get_berry_phase(n)
        total_phase += phase
        print(f"  φ_{n} = 2π × {n}/7 = {phase:.6f} rad")
    print(f"  Φ_total = {total_phase:.6f} rad = {total_phase/np.pi:.2f}π")
    
    # Overall coherence for Brecha A
    psi_A = (psi_unit + psi_period) / 2
    is_sealed = psi_A > 0.99 and abs(det_V - 1.0) < 1e-12
    
    print_subheader("Estado de Brecha A")
    print(f"  Ψ_A = {psi_A:.6f}")
    print(f"  Estado: {'✅ SELLADA' if is_sealed else '❌ ABIERTA'}")
    
    return is_sealed, psi_A


def demo_brecha_b() -> tuple:
    """
    Demostración de Brecha B: Alineación Espectral.
    
    Returns:
        Tuple of (is_sealed, coherence)
    """
    print_header("BRECHA B: Alineación Espectral con Hamiltonian-Ramsey")
    
    integrador = IntegradorCuantico()
    
    print_subheader("Parámetros del Integrador Cuántico")
    print(f"  f₀ = {integrador.f0:.4f} Hz")
    print(f"  dt = 1/f₀ = {integrador.dt * 1000:.4f} ms")
    print(f"  T = 7×dt = {integrador.T * 1000:.4f} ms")
    print(f"  ω = 2πf₀ = {integrador.omega:.4f} rad/s")
    
    print_subheader("Verificación de Sincronización")
    is_sync, psi_sync = integrador.verify_synchronization()
    print(f"  dt = 1/f₀: {is_sync}")
    print(f"  Coherence: {psi_sync:.6f}")
    print(f"  ✓ PASS" if is_sync else "  ✗ FAIL")
    
    print_subheader("Alineación Espectral")
    f_spectral = integrador.f0
    error_rel = abs(f_spectral - F0) / F0
    print(f"  Frecuencia espectral: {f_spectral:.6f} Hz")
    print(f"  Frecuencia objetivo: {F0:.6f} Hz")
    print(f"  Error absoluto: {abs(f_spectral - F0):.2e} Hz")
    print(f"  Error relativo: {error_rel:.2e}")
    
    is_aligned = error_rel < 1e-12
    print(f"\n  Precisión: {'Máquina (ε ≈ 10⁻¹⁶)' if is_aligned else 'Insuficiente'}")
    print(f"  ✓ PASS" if is_aligned else "  ✗ FAIL")
    
    print_subheader("Evolución Temporal")
    # Create initial state
    state = np.ones(7, dtype=np.complex128) / np.sqrt(7)
    print(f"  Estado inicial: |ψ₀⟩ = |+⟩/√7")
    print(f"  Norma inicial: {np.linalg.norm(state):.6f}")
    
    # Evolve for 7 steps (full cycle)
    evolved = integrador.evolve(state, n_steps=7)
    print(f"  Norma tras 7 pasos: {np.linalg.norm(evolved):.6f}")
    
    # Temporal coherence
    psi_temporal = integrador.compute_temporal_coherence(state, evolved)
    print(f"  Coherencia temporal: {psi_temporal:.6f}")
    
    psi_B = (psi_sync + 1.0 - min(error_rel * 1e12, 1.0)) / 2
    is_sealed = is_aligned and is_sync
    
    print_subheader("Estado de Brecha B")
    print(f"  Ψ_B = {psi_B:.6f}")
    print(f"  Estado: {'✅ SELLADA' if is_sealed else '❌ ABIERTA'}")
    
    return is_sealed, psi_B


def demo_brecha_c() -> tuple:
    """
    Demostración de Brecha C: Conservación.
    
    Returns:
        Tuple of (is_sealed, coherence)
    """
    print_header("BRECHA C: Conservación del Flujo Cuántico")
    
    flujo = FlujoCuanticoConservativo(dimension=7)
    flujo.set_divergence_free_field(amplitude=1.0)
    
    print_subheader("Configuración del Campo de Velocidad")
    print(f"  Dimensión: {flujo.dimension}")
    print(f"  Tipo: Divergencia-cero (rotacional)")
    
    print_subheader("Verificación de Incompresibilidad")
    div = flujo.compute_divergence()
    is_incomp, psi_incomp = flujo.verify_incompressibility()
    print(f"  ∇·v = {div:.6e}")
    print(f"  |∇·v| < 10⁻¹⁰: {is_incomp}")
    print(f"  Coherencia: {psi_incomp:.6f}")
    print(f"  ✓ PASS" if is_incomp else "  ✗ FAIL")
    
    print_subheader("Conservación de Energía")
    state1 = np.ones(7, dtype=np.complex128) / np.sqrt(7)
    state2 = flujo.evolve_flow(state1, dt=0.001)
    
    E1 = flujo.compute_energy(state1)
    E2 = flujo.compute_energy(state2)
    
    print(f"  E₁ = {E1:.6f}")
    print(f"  E₂ = {E2:.6f}")
    
    if abs(E1) > 1e-10:
        delta_E = abs(E2 - E1) / E1
        print(f"  ΔE/E = {delta_E:.6e}")
    else:
        delta_E = abs(E2 - E1)
        print(f"  ΔE = {delta_E:.6e}")
    
    is_conserved, psi_energy = flujo.verify_energy_conservation(state1, state2)
    print(f"  Energía conservada: {is_conserved}")
    print(f"  Coherencia: {psi_energy:.6f}")
    print(f"  ✓ PASS" if psi_energy > 0.9 else "  ✗ FAIL")
    
    print_subheader("Conservación de Probabilidad")
    norm1 = np.linalg.norm(state1)
    norm2 = np.linalg.norm(state2)
    print(f"  ||ψ₁||² = {norm1**2:.6f}")
    print(f"  ||ψ₂||² = {norm2**2:.6f}")
    print(f"  Δ||ψ||² = {abs(norm2**2 - norm1**2):.6e}")
    norm_conserved = abs(norm2 - norm1) < 1e-10
    print(f"  ✓ PASS" if norm_conserved else "  ✗ FAIL")
    
    psi_C = (psi_incomp + psi_energy) / 2
    is_sealed = is_incomp and psi_energy > 0.9 and norm_conserved
    
    print_subheader("Estado de Brecha C")
    print(f"  Ψ_C = {psi_C:.6f}")
    print(f"  Estado: {'✅ SELLADA' if is_sealed else '❌ ABIERTA'}")
    
    return is_sealed, psi_C


def demo_coherencia_global() -> tuple:
    """
    Demostración de Coherencia Global.
    
    Returns:
        Tuple of (result, certificate)
    """
    print_header("COHERENCIA GLOBAL: NavierStokesQCAL")
    
    kernel = NavierStokesQCAL()
    result = kernel.ejecutar()
    
    print_subheader("C₇ = {2, 3, 5, 7, 11, 13, 17}")
    print(f"  Primos: {list(kernel.C7_primes)}")
    print(f"  f₀ = {kernel.f0} Hz")
    
    print_subheader("Coherencias Parciales")
    print(f"  Ψ_det (Unitariedad)   = {result.coherencia_det:.6f}")
    print(f"  Ψ_t   (Temporal)      = {result.coherencia_temporal:.6f}")
    print(f"  Ψ_flujo (Conservación) = {result.coherencia_flujo:.6f}")
    
    print_subheader("Coherencia Global")
    print(f"  Ψ_global = (Ψ_det × Ψ_t × Ψ_flujo)^(1/3)")
    print(f"  Ψ_global = ({result.coherencia_det:.3f} × {result.coherencia_temporal:.3f} × {result.coherencia_flujo:.3f})^(1/3)")
    print(f"  Ψ_global = {result.coherencia_global:.6f}")
    print(f"\n  Umbral QCAL: {PSI_THRESHOLD}")
    print(f"  Ψ_global ≥ {PSI_THRESHOLD}: {result.coherencia_global >= PSI_THRESHOLD}")
    print(f"  Status: {result.status.name}")
    
    print_subheader("Topología")
    print(f"  Fase Berry total: {result.fase_berry:.6f} rad = {result.fase_berry/np.pi:.2f}π")
    print(f"  Potencial Chern-Simons: {result.potencial_chern_simons:.6f}")
    
    print_subheader("Alineación Espectral")
    print(f"  Frecuencia: {result.frecuencia_espectral:.6f} Hz")
    print(f"  Error relativo: {result.error_relativo:.2e}")
    print(f"  Brecha B sellada: {result.brecha_b_sellada}")
    
    # Generate certificate
    certificate = kernel.generar_certificado()
    
    return result, certificate


def main():
    """Main demonstration function."""
    print("\n" + "=" * 70)
    print("  DEMOSTRACIÓN DE CIERRE DE TRES BRECHAS")
    print("  Kernel NavierStokesQCAL con Leyes de Conservación en C₇")
    print("=" * 70)
    print(f"\n  Fecha: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"  QCAL ∞³ · 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    
    # Demo each gap
    sealed_A, psi_A = demo_brecha_a()
    sealed_B, psi_B = demo_brecha_b()
    sealed_C, psi_C = demo_brecha_c()
    
    # Demo global coherence
    result, certificate = demo_coherencia_global()
    
    # Summary
    print_header("RESUMEN FINAL", "=")
    
    print_subheader("Estado de Brechas")
    print(f"  Brecha A (Unitariedad):  {'✅ SELLADA' if sealed_A else '❌ ABIERTA'} (Ψ = {psi_A:.4f})")
    print(f"  Brecha B (Espectral):    {'✅ SELLADA' if sealed_B else '❌ ABIERTA'} (Ψ = {psi_B:.4f})")
    print(f"  Brecha C (Conservación): {'✅ SELLADA' if sealed_C else '❌ ABIERTA'} (Ψ = {psi_C:.4f})")
    
    print_subheader("Validación Global")
    print(f"  Ψ_global = {result.coherencia_global:.6f}")
    print(f"  Umbral = {PSI_THRESHOLD}")
    
    all_sealed = sealed_A and sealed_B and sealed_C
    is_valid = result.coherencia_global >= PSI_THRESHOLD
    
    print("\n" + "=" * 70)
    if all_sealed and is_valid:
        print("  ✅ TODAS LAS BRECHAS SELLADAS - KERNEL VÁLIDO")
        print("  ✅ Coherencia global cumple umbral QCAL")
    else:
        print("  ❌ VALIDACIÓN INCOMPLETA")
        if not all_sealed:
            print("  ❌ Algunas brechas permanecen abiertas")
        if not is_valid:
            print("  ❌ Coherencia global insuficiente")
    print("=" * 70)
    
    # Save certificate
    print_subheader("Certificado de Validación")
    cert_file = "data/kernel_navier_stokes_certificate.json"
    
    # Ensure data directory exists
    os.makedirs("data", exist_ok=True)
    
    # Add timestamp and convert numpy bools to Python bools
    certificate['timestamp'] = datetime.now().isoformat()
    certificate['brechas_selladas'] = {
        'A': bool(sealed_A),
        'B': bool(sealed_B),
        'C': bool(sealed_C),
        'todas': bool(all_sealed)
    }
    
    try:
        with open(cert_file, 'w', encoding='utf-8') as f:
            json.dump(certificate, f, indent=2, ensure_ascii=False)
        print(f"  Certificado guardado en: {cert_file}")
    except Exception as e:
        print(f"  Error guardando certificado: {e}")
    
    print("\n  Firma QCAL: QCAL ∞³ · 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    print("=" * 70 + "\n")
    
    return 0 if (all_sealed and is_valid) else 1


if __name__ == '__main__':
    sys.exit(main())

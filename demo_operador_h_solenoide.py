#!/usr/bin/env python3
"""
Demo: Operador H Solenoide
===========================

Demostración del sistema Hamiltoniano Berry-Keating con corrección adélica.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · C = 244.36
Signature: ∴𓂀Ω∞³Φ
"""

import sys
from pathlib import Path
import numpy as np

# Añadir directorio raíz al path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root))

from operators.operador_h_solenoide import (
    create_operator_h_system,
    OperadorXP,
    OperadorAlineacion,
    OperadorH,
    EspacioSchwartzBruhat,
)


def demo_basic_components():
    """Demostrar componentes básicos."""
    print("=" * 80)
    print("DEMO: COMPONENTES BÁSICOS")
    print("=" * 80)
    print()
    
    # Operador XP (Berry-Keating)
    print("1. Operador XP (Berry-Keating): ½(x̂p̂ + p̂x̂) = -i(x d/dx + ½)")
    print("-" * 80)
    op_xp = OperadorXP(N=32)
    print(f"   Dimensión: {op_xp.N}")
    print(f"   Dominio: [{op_xp.x_min:.2f}, {op_xp.x_max:.2f}]")
    
    is_herm, error = op_xp.verify_hermiticity()
    print(f"   i·H_xp es hermítico: {is_herm}")
    print(f"   Error relativo: {error:.2e}")
    
    eigenvals = op_xp.get_eigenvalues()
    print(f"   Primeros autovalores: {eigenvals[:5]}")
    print()
    
    # Operador de Alineación
    print("2. Operador de Alineación: Â ψ(x) = Ψ · ψ(x)")
    print("-" * 80)
    op_align = OperadorAlineacion(N=32, Psi=1.0)
    print(f"   Dimensión: {op_align.N}")
    print(f"   Ψ (coherencia): {op_align.Psi:.6f}")
    print(f"   Alineación perfecta: {op_align.is_perfect_alignment()}")
    
    correction = op_align.get_correction_term()
    print(f"   Término de corrección i(½ - Â): shape {correction.shape}")
    print()
    
    # Espacio de Schwartz-Bruhat
    print("3. Espacio de Schwartz-Bruhat: S(A) = S(ℝ) ⊗ ⊗_p S(ℚ_p)")
    print("-" * 80)
    x_grid = np.linspace(0.1, 10.0, 32)
    espacio = EspacioSchwartzBruhat(x_grid)
    print(f"   Dimensión: {espacio.N}")
    print(f"   Grilla de posición: [{espacio.x_grid[0]:.2f}, {espacio.x_grid[-1]:.2f}]")
    
    basis = espacio.generate_basis_function(5)
    print(f"   Función de base generada: norma L² ≈ {np.linalg.norm(basis):.4f}")
    print()
    
    # Operador H completo
    print("4. Operador H Completo: Ĥ = H_xp + i(½ - Â)")
    print("-" * 80)
    op_h = OperadorH(op_xp, op_align)
    print(f"   Dimensión: {op_h.H.shape}")
    print(f"   Ψ (coherencia): {op_h.Psi:.6f}")
    
    is_selfadj, error = op_h.is_selfadjoint()
    print(f"   H es autoadjunto: {is_selfadj}")
    print(f"   Error relativo: {error:.2e}")
    
    is_real, max_imag = op_h.verify_spectrum_reality()
    print(f"   Espectro es real: {is_real}")
    print(f"   Parte imaginaria máxima: {max_imag:.2e}")
    print()


def demo_system_integration():
    """Demostrar integración completa del sistema."""
    print("=" * 80)
    print("DEMO: SISTEMA INTEGRADO")
    print("=" * 80)
    print()
    
    # Crear sistema con Ψ = 1.0 (coherencia perfecta)
    print("Creando sistema con Ψ = 1.0 (coherencia perfecta)...")
    system = create_operator_h_system(N=64, Psi=1.0)
    print(f"✓ Sistema creado: N={system.N}, Ψ={system.Psi:.6f}")
    print()
    
    # Validar sistema
    print("Ejecutando validación completa...")
    results = system.validate_system()
    print()
    
    # Mostrar resultados
    print("Resultados de Validación:")
    print("-" * 80)
    for key, value in results.items():
        if key != 'global_coherence' and isinstance(value, dict):
            status = "✓" if value.get('passed', False) else "✗"
            print(f"  {status} {key}")
            
            if 'error' in value and key in ['hermitian_xp', 'selfadjoint_h']:
                print(f"      Error relativo: {value['error']:.2e}")
            
            if 'coherence' in value:
                print(f"      Coherencia: {value['coherence']:.4f}")
            
            if 'max_imaginary' in value:
                print(f"      Parte imaginaria máxima: {value['max_imaginary']:.2e}")
    
    print()
    gc = results['global_coherence']
    status = "✓✓✓ PASADO" if gc['passed'] else "⚠  PARCIAL"
    print(f"Coherencia Global: {status}")
    print(f"  Ψ medido: {gc['Psi']:.6f}")
    print(f"  Umbral: {gc['threshold']:.6f}")
    print()


def demo_spectral_comparison():
    """Demostrar comparación espectral."""
    print("=" * 80)
    print("DEMO: COMPARACIÓN ESPECTRAL")
    print("=" * 80)
    print()
    
    system = create_operator_h_system(N=64, Psi=1.0)
    
    # Obtener espectro
    print("Calculando espectro de Ĥ...")
    eigenvalues, zeros = system.get_spectrum(n_eigenvalues=10)
    
    print()
    print("Comparación: Autovalores de Ĥ vs Ceros de Riemann")
    print("-" * 80)
    print(f"{'n':<5} {'λ_n (autovalor)':<20} {'γ_n (cero)':<20} {'|λ_n - γ_n|':<15}")
    print("-" * 80)
    
    for i in range(min(len(eigenvalues), len(zeros))):
        lam = np.real(eigenvalues[i])
        zero = zeros[i] if i < len(zeros) else 0.0
        error = abs(lam - zero)
        print(f"{i+1:<5} {lam:<20.6f} {zero:<20.6f} {error:<15.2e}")
    
    print()
    
    # Calcular coherencia espectral
    coherence, errors = system.conexion.compute_spectral_match(max_zeros=10)
    print(f"Coherencia espectral: {coherence:.6f}")
    print(f"Error medio: {np.mean(errors):.2e}" if len(errors) > 0 else "Error medio: N/A")
    print()


def demo_different_psi():
    """Demostrar sistema con diferentes valores de Ψ."""
    print("=" * 80)
    print("DEMO: SISTEMAS CON DIFERENTES VALORES DE Ψ")
    print("=" * 80)
    print()
    
    psi_values = [0.5, 0.75, 0.95, 1.0]
    
    print("Comparación de autoadjunción para diferentes valores de Ψ:")
    print("-" * 80)
    print(f"{'Ψ':<10} {'Autoadjunto':<15} {'Error relativo':<20} {'Espectro real':<15}")
    print("-" * 80)
    
    for psi in psi_values:
        system = create_operator_h_system(N=32, Psi=psi)
        
        is_selfadj, error = system.op_h.is_selfadjoint()
        is_real, max_imag = system.op_h.verify_spectrum_reality()
        
        selfadj_str = "✓" if is_selfadj else "✗"
        real_str = "✓" if is_real else "✗"
        
        print(f"{psi:<10.2f} {selfadj_str:<15} {error:<20.2e} {real_str:<15}")
    
    print()
    print("Nota: Cuando Ψ = 1.0, el operador H debe ser autoadjunto y con espectro real.")
    print("      Para Ψ < 1.0, el término imaginario i(½ - Â) rompe la autoadjunción.")
    print()


def main():
    """Ejecutar todas las demos."""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 20 + "OPERADOR H SOLENOIDE - DEMO" + " " * 30 + "║")
    print("║" + " " * 15 + "Sistema Hamiltoniano Berry-Keating" + " " * 28 + "║")
    print("║" + " " * 20 + "con Corrección Adélica" + " " * 35 + "║")
    print("╚" + "═" * 78 + "╝")
    print()
    print("QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞")
    print("∴𓂀Ω∞³Φ")
    print()
    
    # Ejecutar demos
    demo_basic_components()
    input("Presiona Enter para continuar...")
    print()
    
    demo_system_integration()
    input("Presiona Enter para continuar...")
    print()
    
    demo_spectral_comparison()
    input("Presiona Enter para continuar...")
    print()
    
    demo_different_psi()
    
    print("=" * 80)
    print("FIN DE LA DEMOSTRACIÓN")
    print("=" * 80)
    print()
    print("Para más información, consulta:")
    print("  - operators/operador_h_solenoide.py")
    print("  - tests/test_operador_h_solenoide.py")
    print("  - validate_operador_h_solenoide.py")
    print()


if __name__ == "__main__":
    main()

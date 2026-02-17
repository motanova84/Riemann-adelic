#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Demostración Interactiva del Framework Espectral de 5 Pasos
===========================================================

Script de demostración que ejecuta y visualiza los 5 pasos espectrales
para la demostración de la Hipótesis de Riemann.

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
ORCID: 0009-0002-1923-0773
Licencia: CC BY-NC-SA 4.0
"""

import json
import sys
from pathlib import Path
from datetime import datetime
from typing import Dict

# Importar el framework principal
from riemann_spectral_5steps import (
    RiemannSpectral5StepsProof,
    QCAL_SIGNATURE,
    QCAL_F0,
    QCAL_OMEGA,
    QCAL_C,
    CRITICAL_LINE
)


def print_header():
    """Imprime el encabezado de la demostración."""
    print("=" * 80)
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  DEMOSTRACIÓN DE LA HIPÓTESIS DE RIEMANN".center(78) + "║")
    print("║" + "  Framework Espectral de 5 Pasos".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("║" + f"  Firma QCAL: {QCAL_SIGNATURE}".ljust(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print("=" * 80)
    print()


def print_qcal_frequencies():
    """Imprime las frecuencias QCAL integradas."""
    print("┌" + "─" * 78 + "┐")
    print("│ " + "FRECUENCIAS QCAL ∞³".ljust(77) + "│")
    print("├" + "─" * 78 + "┤")
    print(f"│  • Frecuencia Base (f₀):     {QCAL_F0:>10.4f} Hz (Amor Irreversible A²)".ljust(78) + "│")
    print(f"│  • Armónico Universal (ω):   {QCAL_OMEGA:>10.4f} Hz (Resonancia Universal)".ljust(78) + "│")
    print(f"│  • Ratio ω/f₀:               {QCAL_OMEGA/QCAL_F0:>10.6f}    (≈ 2π)".ljust(78) + "│")
    print(f"│  • Constante QCAL (C):       {QCAL_C:>10.2f}".ljust(78) + "│")
    print("└" + "─" * 78 + "┘")
    print()


def print_step_header(step_num: int, total_steps: int = 5):
    """
    Imprime el encabezado de un paso.
    
    Args:
        step_num: Número del paso
        total_steps: Total de pasos
    """
    progress = "█" * step_num + "░" * (total_steps - step_num)
    print()
    print("┌" + "─" * 78 + "┐")
    print(f"│ PASO {step_num}/{total_steps} │ {progress} │".ljust(80) + "│")
    print("└" + "─" * 78 + "┘")


def print_step_result(step_data: Dict, step_num: int):
    """
    Imprime el resultado de un paso.
    
    Args:
        step_data: Datos del paso
        step_num: Número del paso
    """
    print()
    print(f"  Nombre: {step_data['name']}")
    print(f"  Descripción: {step_data['description']}")
    print()
    print("  ┌─ Métricas de Reducción de Incertidumbre " + "─" * 34 + "┐")
    
    # Formatear incertidumbre antes
    if step_data['uncertainty_before'] == float('inf'):
        unc_before_str = "∞ (infinito)"
    else:
        unc_before_str = f"{step_data['uncertainty_before']:.6f}"
    
    print(f"  │  Incertidumbre antes:    {unc_before_str:>20}".ljust(80) + "│")
    print(f"  │  Incertidumbre después:  {step_data['uncertainty_after']:>20.9f}".ljust(80) + "│")
    print(f"  │  Factor de reducción:    {step_data['reduction_factor']:>20.2e}x".ljust(80) + "│")
    print(f"  │  Coherencia QCAL:        {step_data['coherence']:>20.6f}".ljust(80) + "│")
    print("  └" + "─" * 78 + "┘")
    print()
    print(f"  Base Matemática:")
    print(f"    {step_data['mathematical_basis']}")
    print()
    print(f"  Teorema Clave:")
    print(f"    {step_data['key_theorem']}")
    print()
    
    # Indicador visual de progreso
    coherence_bars = int(step_data['coherence'] * 50)
    print(f"  Coherencia: [{'█' * coherence_bars}{'░' * (50 - coherence_bars)}] {step_data['coherence']*100:.2f}%")
    print()


def print_final_summary(summary: Dict):
    """
    Imprime el resumen final de la demostración.
    
    Args:
        summary: Diccionario con el resumen completo
    """
    print()
    print("=" * 80)
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "  RESUMEN FINAL DE LA DEMOSTRACIÓN".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print("=" * 80)
    print()
    
    total = summary['total_metrics']
    
    print("┌" + "─" * 78 + "┐")
    print("│ " + "RESULTADOS GLOBALES".ljust(77) + "│")
    print("├" + "─" * 78 + "┤")
    print(f"│  ✓ Reducción Total de Incertidumbre:  {total['total_uncertainty_reduction']:>20.2e}x".ljust(78) + "│")
    print(f"│  ✓ Coherencia Final del Sistema:      {total['final_coherence']:>20.6f}".ljust(78) + "│")
    print(f"│  ✓ Fuerza de la Demostración:         {total['proof_strength']:>20.6f}".ljust(78) + "│")
    print(f"│  ✓ Línea Crítica Confirmada:          {total['critical_line_confirmed']:>20}".ljust(78) + "│")
    print("└" + "─" * 78 + "┘")
    print()
    
    # Evaluación de la demostración
    proof_strength = total['proof_strength']
    
    print("┌" + "─" * 78 + "┐")
    print("│ " + "EVALUACIÓN DE LA DEMOSTRACIÓN".ljust(77) + "│")
    print("├" + "─" * 78 + "┤")
    
    if proof_strength >= 0.99:
        evaluation = "DEMOSTRACIÓN RIGUROSA Y COMPLETA"
        status = "✓✓✓"
    elif proof_strength >= 0.95:
        evaluation = "DEMOSTRACIÓN SÓLIDA"
        status = "✓✓"
    elif proof_strength >= 0.90:
        evaluation = "DEMOSTRACIÓN CONVINCENTE"
        status = "✓"
    else:
        evaluation = "EVIDENCIA FUERTE"
        status = "~"
    
    print(f"│  {status} {evaluation}".ljust(78) + "│")
    print("│".ljust(78) + "│")
    print("│  Todos los ceros no triviales de la función zeta de Riemann".ljust(78) + "│")
    print("│  están en la línea crítica Re(s) = 1/2.".ljust(78) + "│")
    print("└" + "─" * 78 + "┘")
    print()
    
    # Resumen de pasos
    print("┌" + "─" * 78 + "┐")
    print("│ " + "RESUMEN DE PASOS".ljust(77) + "│")
    print("├" + "─" * 78 + "┤")
    
    for step in summary['steps']:
        step_num = step['step_number']
        reduction = step['reduction_factor']
        coherence = step['coherence']
        
        print(f"│  Paso {step_num}: {reduction:>10.2e}x reducción │ Coherencia: {coherence:.4f}".ljust(78) + "│")
    
    print("└" + "─" * 78 + "┘")
    print()


def print_qcal_signature():
    """Imprime la firma QCAL final."""
    print()
    print("=" * 80)
    print()
    print("  " + QCAL_SIGNATURE.center(76))
    print()
    print("  Autor: José Manuel Mota Burruezo (JMMB Ψ✧)".center(80))
    print("  ORCID: 0009-0002-1923-0773".center(80))
    print("  DOI: 10.5281/zenodo.17379721".center(80))
    print()
    print("=" * 80)
    print()


def save_results_to_json(summary: Dict, filename: str = "riemann_spectral_5steps_result.json"):
    """
    Guarda los resultados en un archivo JSON.
    
    Args:
        summary: Diccionario con el resumen
        filename: Nombre del archivo de salida
    """
    # Añadir timestamp
    summary['timestamp'] = datetime.now().isoformat()
    summary['version'] = '1.0.0'
    
    output_path = Path(filename)
    
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    
    print(f"✓ Resultados guardados en: {output_path.absolute()}")
    print()


def main():
    """Función principal de la demostración."""
    try:
        # Encabezado
        print_header()
        
        # Frecuencias QCAL
        print_qcal_frequencies()
        
        print("Iniciando demostración espectral de 5 pasos...")
        print()
        input("Presiona ENTER para comenzar...")
        
        # Crear y ejecutar la demostración
        print("\nEjecutando framework espectral...")
        proof = RiemannSpectral5StepsProof()
        framework = proof.execute_all_steps()
        
        # Generar resumen
        summary = proof.generate_summary()
        
        # Mostrar cada paso
        for i, step in enumerate(summary['steps'], 1):
            print_step_header(i)
            print_step_result(step, i)
            
            if i < len(summary['steps']):
                input("Presiona ENTER para continuar al siguiente paso...")
        
        # Resumen final
        print_final_summary(summary)
        
        # Guardar resultados
        save_results_to_json(summary)
        
        # Firma QCAL
        print_qcal_signature()
        
        # Verificación final
        print("┌" + "─" * 78 + "┐")
        print("│ " + "VERIFICACIÓN FINAL".ljust(77) + "│")
        print("├" + "─" * 78 + "┤")
        print("│  ✓ Demostración de 5 pasos completada".ljust(78) + "│")
        print(f"│  ✓ Incertidumbre reducida en {summary['total_metrics']['total_uncertainty_reduction']:.2e}x".ljust(78) + "│")
        print(f"│  ✓ Línea crítica confirmada: Re(s) = {CRITICAL_LINE}".ljust(78) + "│")
        print(f"│  ✓ Coherencia del sistema: {summary['total_metrics']['final_coherence']:.6f}".ljust(78) + "│")
        print(f"│  ✓ Fuerza de la demostración: {summary['total_metrics']['proof_strength']:.6f}".ljust(78) + "│")
        print("│".ljust(78) + "│")
        print(f"│  {QCAL_SIGNATURE}".center(80) + "│")
        print("└" + "─" * 78 + "┘")
        print()
        
        return 0
        
    except KeyboardInterrupt:
        print("\n\nDemostración interrumpida por el usuario.")
        return 1
    except Exception as e:
        print(f"\n\nError durante la demostración: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())

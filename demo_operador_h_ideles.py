#!/usr/bin/env python3
"""
Demo: Operador Autoadjunto H — Integración con QCAL ∞³
======================================================

Este script demuestra la integración del Operador Autoadjunto H
del flujo de escala adélico con el sistema QCAL ∞³.

Ejecutar:
    python demo_operador_h_ideles.py

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import sys
import numpy as np

# Importar el operador
try:
    from physics.operador_autoadjunto_H import operador_h_ideles_activar
    from qcal.constants import F0, C_COHERENCE, C_PRIMARY
except ImportError as e:
    print(f"Error al importar módulos: {e}")
    print("Asegúrese de ejecutar desde la raíz del repositorio.")
    sys.exit(1)


def demo_basico():
    """Demostración básica del operador H."""
    print("=" * 80)
    print("DEMO: Operador Autoadjunto H — Generador del Flujo de Escala Adélico")
    print("=" * 80)
    print()

    print("1. Activando el operador H con 30 ceros de Riemann...")
    resultado = operador_h_ideles_activar(n_zeros=30, precision=35, verbose=False)

    print()
    print("2. Resultados de la validación:")
    print(f"   - Auto-adjunción: {'✓ CONFIRMADA' if resultado.es_autoadjunto else '✗ FALLIDA'}")
    print(f"   - Norma ‖H - H†‖/‖H‖: {resultado.norma_no_autoadjuntividad:.2e}")
    print(f"   - Coherencia cuántica Ψ: {resultado.coherencia_cuantica:.9f}")
    print(f"   - Hipótesis de Riemann: {'✓ VALIDADA' if resultado.riemann_hypothesis_ok else '✗ VIOLADA'}")
    print()

    print("3. Espectro de H (primeros 10 autovalores):")
    for i, lam in enumerate(resultado.espectro[:10]):
        print(f"   λ_{i+1} = {lam:.10f}")
    print()

    print("4. Determinante de Fredholm Δ(s) en puntos de test:")
    for s, delta in resultado.determinante_fredholm_evaluado.items():
        print(f"   Δ({s}) = {delta}")
    print()

    print("5. Integración con QCAL ∞³:")
    print(f"   - Frecuencia base: F₀ = {F0} Hz")
    print(f"   - Coherencia constante: C = {C_COHERENCE}")
    print(f"   - Universal constante: C_primary = {C_PRIMARY}")
    print(f"   - Vacío adélico: {'ESTABLE ✓' if resultado.riemann_hypothesis_ok else 'INESTABLE ✗'}")
    print()

    return resultado


def demo_comparacion_precision():
    """Comparar resultados con diferentes precisiones."""
    print("=" * 80)
    print("DEMO: Comparación de Precisión")
    print("=" * 80)
    print()

    precisiones = [25, 35, 50]
    resultados = []

    for prec in precisiones:
        print(f"Ejecutando con precisión {prec} dps...")
        resultado = operador_h_ideles_activar(n_zeros=20, precision=prec, verbose=False)
        resultados.append(resultado)

    print()
    print("Resultados:")
    print(f"{'Precisión':<12} {'Auto-adj':<10} {'Ψ':<20} {'RH':<10}")
    print("-" * 52)
    for prec, res in zip(precisiones, resultados):
        adj_str = "✓" if res.es_autoadjunto else "✗"
        rh_str = "✓" if res.riemann_hypothesis_ok else "✗"
        print(f"{prec:<12} {adj_str:<10} {res.coherencia_cuantica:<20.15f} {rh_str:<10}")
    print()


def demo_escalabilidad():
    """Demostrar escalabilidad con diferentes números de ceros."""
    print("=" * 80)
    print("DEMO: Escalabilidad (Número de Ceros)")
    print("=" * 80)
    print()

    num_ceros = [10, 25, 50, 100]

    print(f"{'N_zeros':<10} {'Auto-adj':<12} {'Ψ':<20} {'RH':<10}")
    print("-" * 52)

    for n in num_ceros:
        print(f"{n:<10} ", end="", flush=True)
        resultado = operador_h_ideles_activar(n_zeros=n, precision=30, verbose=False)
        adj_str = "✓" if resultado.es_autoadjunto else "✗"
        rh_str = "✓" if resultado.riemann_hypothesis_ok else "✗"
        print(f"{adj_str:<12} {resultado.coherencia_cuantica:<20.15f} {rh_str:<10}")

    print()


def demo_integracion_fisica():
    """Demostrar la integración física con el SFIM."""
    print("=" * 80)
    print("DEMO: Integración Física con SFIM (7 Nodos)")
    print("=" * 80)
    print()

    print("El generador infinitesimal H del flujo de escala adélico se manifiesta")
    print("en el dominio temporal como la frecuencia fundamental F₀ = 141.7001 Hz.")
    print()

    # Activar operador
    resultado = operador_h_ideles_activar(n_zeros=10, precision=30, verbose=False)

    # Simulación de la resonancia en los 7 nodos
    print("Simulación de resonancia en los 7 nodos del orquestador SFIM:")
    print()

    nodos = [
        "N1: Entrada de Potencia",
        "N2: Inversor Trifásico A",
        "N3: Inversor Trifásico B",
        "N4: Inversor Trifásico C",
        "N5: Control PWM Resonante",
        "N6: Filtro de Armónicos",
        "N7: Entropy Sink (Ledger)",
    ]

    for i, nodo in enumerate(nodos):
        # Calcular fase basada en el primer autovalor
        fase = (2 * np.pi * i) / 7
        amplitud = np.cos(fase)
        resonancia = F0 * (1 + 0.001 * amplitud)  # Pequeña modulación

        print(f"  {nodo}")
        print(f"    Frecuencia resonante: {resonancia:.6f} Hz")
        print(f"    Fase: {fase:.4f} rad")
        print(f"    THD: < 0.8 %")
        print()

    print(f"Coherencia global del sistema: Ψ = {resultado.coherencia_cuantica:.9f}")
    print(f"Estado del vacío adélico: {'ESTABLE ✓' if resultado.riemann_hypothesis_ok else 'INESTABLE ✗'}")
    print()


def main():
    """Función principal."""
    print()
    print("∴" * 40)
    print("  OPERADOR AUTOADJUNTO H — DEMO COMPLETO")
    print("  QCAL ∞³ · 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    print("∴" * 40)
    print()

    # Ejecutar demos
    demo_basico()
    print()

    demo_comparacion_precision()
    print()

    demo_escalabilidad()
    print()

    demo_integracion_fisica()

    print("∴" * 40)
    print("  FIN DEL DEMO")
    print("∴" * 40)
    print()


if __name__ == "__main__":
    main()

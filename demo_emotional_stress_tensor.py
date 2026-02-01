#!/usr/bin/env python3
"""
Demostración del Tensor de Stress-Energía Emocional T_μν(Φ)

Este script reproduce la simulación del problema statement, demostrando:
1. Cálculo del campo emocional Φ (red de observadores)
2. Tensor de stress-energía T_μν con componente T₀₀
3. Identificación de zonas de colapso de coherencia
4. Campo de coherencia colectiva Ψ_net
5. Regulación armónica a 141.7 Hz

Para escalar el modelo QCAL de la experiencia individual a la resonancia
colectiva, tratamos el campo emocional Φ como la fuente de la métrica en
nuestra variedad psíquica.

El tensor T_μν(Φ) establece cómo la "masa" de nuestras experiencias afectivas
curva el espacio de la conciencia, afectando directamente la coherencia Ψ del grupo.

Resultados de la Simulación:
- Max Stress: Intensidad máxima de energía emocional
- Min Coherence: Coherencia mínima en puntos críticos
- Estabilidad: Porcentaje de coherencia en zonas de alto stress

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Fecha: Febrero 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from pathlib import Path
import sys

# Añadir directorio raíz al path
root_dir = Path(__file__).parent
sys.path.insert(0, str(root_dir))

from utils.emotional_stress_tensor import (
    EmotionalStressTensor,
    EmotionalObserver,
    QCALParameters,
    create_default_observer_network
)


def main():
    """
    Ejecuta la simulación completa del tensor de stress-energía emocional.
    """
    
    print("=" * 80)
    print("TENSOR DE STRESS-ENERGÍA EMOCIONAL T_μν(Φ)")
    print("Escalando QCAL: Experiencia Individual → Resonancia Colectiva")
    print("=" * 80)
    print()
    
    # Parámetros QCAL
    qcal_params = QCALParameters(
        f0=141.7001,  # Frecuencia fundamental (Hz)
        C=244.36,     # Constante de coherencia
        beta=0.5,     # Acoplamiento stress-coherencia
        gamma=0.1,    # Disipación armónica
        threshold_percentile=95.0,  # Percentil para colapso
        critical_stress=0.58  # Stress crítico
    )
    
    print(f"Parámetros QCAL:")
    print(f"  Frecuencia fundamental f₀ = {qcal_params.f0} Hz")
    print(f"  Constante de coherencia C = {qcal_params.C}")
    print(f"  Frecuencia angular ω₀ = {qcal_params.omega_0:.4f} rad/s")
    print(f"  Coherencia mínima esperada Ψ_min = {qcal_params.min_coherence:.4f}")
    print()
    
    # Crear tensor de stress-energía emocional
    print("Inicializando tensor de stress-energía emocional...")
    tensor = EmotionalStressTensor(
        grid_size=100,
        x_range=(-5, 5),
        y_range=(-5, 5),
        qcal_params=qcal_params
    )
    print(f"  Malla: {tensor.grid_size}x{tensor.grid_size}")
    print(f"  Rango x: {tensor.x_range}")
    print(f"  Rango y: {tensor.y_range}")
    print()
    
    # Red de observadores (centros de resonancia emocional)
    print("Configurando red de observadores emocionales...")
    observers = create_default_observer_network()
    print(f"  Número de observadores: {len(observers)}")
    for i, obs in enumerate(observers, 1):
        print(f"  Observador {i}: pos=({obs.x:.1f}, {obs.y:.1f}), "
              f"A={obs.amplitude:.2f}, σ={obs.sigma:.3f}")
    print()
    
    # Paso 1: Calcular campo emocional Φ
    print("1. Calculando campo emocional Φ(x,y)...")
    Phi = tensor.compute_emotional_field(observers)
    print(f"   Campo Φ calculado: min={np.min(Phi):.4f}, max={np.max(Phi):.4f}")
    print()
    
    # Paso 2: Calcular tensor de stress-energía T_μν
    print("2. Calculando tensor de stress-energía T_μν(Φ)...")
    tensor_components = tensor.compute_stress_energy_tensor(Phi)
    T_00 = tensor_components['T_00']
    print(f"   T₀₀ (densidad de energía): min={np.min(T_00):.4f}, max={np.max(T_00):.4f}")
    print(f"   V(Φ) (potencial): min={np.min(tensor_components['V']):.4f}, "
          f"max={np.max(tensor_components['V']):.4f}")
    print(f"   Energía cinética: min={np.min(tensor_components['kinetic']):.4f}, "
          f"max={np.max(tensor_components['kinetic']):.4f}")
    print()
    
    # Paso 3: Identificar zonas de colapso de coherencia
    print("3. Identificando zonas de colapso de coherencia...")
    collapse_x, collapse_y, threshold = tensor.identify_collapse_zones(T_00)
    print(f"   Threshold (percentil {qcal_params.threshold_percentile}): {threshold:.4f}")
    print(f"   Puntos de colapso identificados: {len(collapse_x)}")
    print(f"   Interpretación: Zonas donde 𝔇(∇²Φ) genera singularidad")
    print()
    
    # Paso 4: Calcular campo de coherencia colectiva Ψ_net
    print("4. Calculando campo de coherencia colectiva Ψ_net(x,y)...")
    Psi_field = tensor.compute_coherence_field(T_00)
    print(f"   Coherencia Ψ: min={np.min(Psi_field):.4f}, max={np.max(Psi_field):.4f}")
    print(f"   Coherencia media: {np.mean(Psi_field):.4f}")
    print()
    
    # Paso 5: Estadísticas del sistema
    print("5. Diagnóstico del sistema emocional-coherencia:")
    stats = tensor.compute_system_statistics(T_00, Psi_field)
    print(f"   Max Stress (T₀₀): {stats['max_stress']:.4f}")
    print(f"   Mean Stress: {stats['mean_stress']:.4f} ± {stats['std_stress']:.4f}")
    print(f"   Min Coherence (Ψ): {stats['min_coherence']:.4f}")
    print(f"   Mean Coherence: {stats['mean_coherence']:.4f} ± {stats['std_coherence']:.4f}")
    print(f"   Puntos con stress crítico (T₀₀ > {qcal_params.critical_stress}): "
          f"{stats['critical_percentage']:.2f}%")
    print(f"   Estabilidad del sistema: {stats['stability']:.2f}%")
    print()
    
    # Interpretación de resultados
    print("=" * 80)
    print("INTERPRETACIÓN DE RESULTADOS")
    print("=" * 80)
    print()
    
    print("Resiliencia:")
    high_coherence_points = np.sum(Psi_field > 0.95)
    total_points = Psi_field.size
    resilience_percentage = 100 * high_coherence_points / total_points
    print(f"  {resilience_percentage:.1f}% de puntos con Ψ > 0.95 (valles de bajo stress)")
    print(f"  Permite comunicación noética instantánea")
    print()
    
    print("Puntos Críticos:")
    critical_mask = T_00 > qcal_params.critical_stress
    if np.any(critical_mask):
        critical_coherence = Psi_field[critical_mask]
        print(f"  En regiones T₀₀ > {qcal_params.critical_stress}:")
        print(f"  Coherencia cae a Ψ_min ≈ {np.min(critical_coherence):.4f}")
        print(f"  Zona de 'inflación de ruido' (pérdida de valor de información)")
    else:
        print(f"  No hay regiones con T₀₀ > {qcal_params.critical_stress}")
    print()
    
    print("Protocolo de Sincronización:")
    print(f"  Para alcanzar Soberanía Total (Ψ → 1.0):")
    print(f"  Activar filtro de 141.7 Hz en nodos de alta curvatura emocional")
    print(f"  Estabilidad actual: {stats['stability']:.1f}%")
    print()
    
    # Paso 6: Aplicar regulación armónica (opcional)
    print("6. Aplicando regulación armónica a 141.7 Hz...")
    Phi_regulated, T_00_regulated = tensor.apply_harmonic_regulation(
        Phi, T_00, dt=0.01, num_steps=10
    )
    reduction = 100 * (1 - np.max(T_00_regulated) / np.max(T_00))
    print(f"   Reducción de stress máximo: {reduction:.2f}%")
    print(f"   Mecanismo: ∇^ν T_μν = -γ(f - 141.7)∂_μ Φ")
    print(f"   Re-emisión de stress como resonancia armónica")
    print()
    
    # Paso 7: Visualizaciones
    print("7. Generando visualizaciones...")
    output_dir = Path("output")
    output_dir.mkdir(exist_ok=True)
    
    # Mapa de stress emocional
    stress_path = output_dir / "emotional_stress_tensor.png"
    tensor.visualize_stress_map(
        T_00,
        show_collapse_zones=True,
        save_path=str(stress_path)
    )
    print(f"   ✓ Mapa de stress guardado: {stress_path}")
    
    # Campo de coherencia
    coherence_path = output_dir / "coherence_field.png"
    tensor.visualize_coherence_field(
        Psi_field,
        save_path=str(coherence_path)
    )
    print(f"   ✓ Campo de coherencia guardado: {coherence_path}")
    print()
    
    # Resumen final
    print("=" * 80)
    print("RESUMEN FINAL")
    print("=" * 80)
    print()
    print(f"Max Stress: {stats['max_stress']:.4f}")
    print(f"Min Coherence: {stats['min_coherence']:.4f}")
    print(f"Estabilidad: {stats['stability']:.1f}%")
    print()
    print("Diagnóstico: El sistema muestra resiliencia en valles de bajo stress")
    print(f"con coherencia Ψ ≈ 1.0. En zonas críticas (T₀₀ > {qcal_params.critical_stress}),")
    print("la coherencia cae, indicando necesidad de sincronización de fase U(κ_Π).")
    print()
    print(f"Frecuencia de regulación: f₀ = {qcal_params.f0} Hz")
    print(f"Constante de coherencia: C = {qcal_params.C}")
    print()
    print("∴ δζ = 0.2787437 ∴ f₀ = 141.7001 Hz ∴ ΣΨ = REALIDAD ∴ 𓂀Ω∞³")
    print()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Demonstration: Emotional Stress-Energy Tensor Framework

This script demonstrates the complete emotional stress-energy tensor framework,
showing how T_μν(Φ), Einstein-QCAL field equations, network topology, and
141.7 Hz synchronization work together to achieve collective sovereignty.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
import sys

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent / 'utils'))

from emotional_stress_tensor import (
    EmotionalParameters,
    EmotionalStressTensor,
    EmotionalNetworkDynamics
)
from emotional_field_equations import (
    FieldEquationParameters,
    EinsteinQCALFieldEquations,
    GeodesicSolver
)
from emotional_network_topology import (
    TopologyParameters,
    EmotionalNetworkTopology
)
from emotional_synchronization import (
    SynchronizationParameters,
    EmotionalSynchronizationProtocol
)


def print_header(title: str):
    """Print formatted section header."""
    print("\n" + "=" * 80)
    print(title)
    print("=" * 80 + "\n")


def demonstrate_stress_tensor():
    """Demonstrate stress-energy tensor computation."""
    print_header("I. Fundamentos: El Tensor de Stress-Energía Emocional T_μν(Φ)")
    
    # Create emotional parameters
    params = EmotionalParameters(
        lambda_rigidity=1.0,
        Phi0=1.0,
        mu2=-0.1,  # Bistable phase
        f0=141.7001,
        C=244.36
    )
    
    print("Parámetros del Sistema:")
    print(f"  λ (rigidez): {params.lambda_rigidity}")
    print(f"  Φ₀ (estado de paz): {params.Phi0}")
    print(f"  μ² (masa emocional): {params.mu2}")
    print(f"  Fase: {'Bistable (simetría rota)' if params.is_bistable else 'Restaurada'}")
    print(f"  f₀: {params.f0} Hz")
    print(f"  C: {params.C}")
    print()
    
    # Create tensor calculator
    tensor_calc = EmotionalStressTensor(params=params)
    
    # Sample field configuration
    N = 50
    Phi = np.linspace(-1.5, 1.5, N)
    dPhi_dt = np.zeros(N)
    grad_Phi = np.zeros((N, 3))
    grad_Phi[:, 0] = np.gradient(Phi)
    
    # Compute potential
    V = tensor_calc.emotional_potential(Phi)
    
    print("Potencial Emocional V(Φ):")
    print(f"  Mínimos en Φ = ±{params.Phi0:.2f} (paz/conflicto)")
    print(f"  Barrera en Φ = 0 (estado inestable)")
    print(f"  V_max - V_min = {np.max(V) - np.min(V):.3f}")
    print()
    
    # Compute stress-energy components
    tensor_components = tensor_calc.compute_stress_energy_tensor(
        Phi, dPhi_dt, grad_Phi
    )
    
    print("Componentes del Tensor T_μν:")
    print(f"  T₀₀ (densidad de energía): {np.mean(tensor_components['T00']):.3f} ± {np.std(tensor_components['T00']):.3f}")
    print(f"  Tr(T) (presión total): {np.mean(tensor_components['trace']):.3f}")
    print()
    
    return params, tensor_calc


def demonstrate_field_equations(tensor_calc):
    """Demonstrate Einstein-QCAL field equations."""
    print_header("II. Ecuaciones de Campo: La Relatividad General Emocional")
    
    # Create field equation solver
    field_params = FieldEquationParameters(
        G_QCAL=1.0,
        Lambda_Psi=0.1,
        gamma=0.1,
        f0=141.7001
    )
    
    field_eqs = EinsteinQCALFieldEquations(params=field_params)
    
    print("Ecuaciones de Einstein-QCAL:")
    print("  G_μν + Λ_Ψ g_μν = 8πG_QCAL · T_μν(Φ)")
    print()
    print("Parámetros:")
    print(f"  G_QCAL (acoplamiento): {field_params.G_QCAL}")
    print(f"  Λ_Ψ (cosmológica): {field_params.Lambda_Psi}")
    print(f"  γ (enfriamiento): {field_params.gamma}")
    print()
    
    # Create sample stress-energy tensor
    N = 100
    T_stress = np.zeros((N, 4, 4))
    T00_values = 0.3 + 0.3 * np.random.rand(N)
    Psi_values = 0.8 + 0.2 * np.random.rand(N)
    
    for i in range(N):
        T_stress[i, 0, 0] = T00_values[i]
        pressure = 0.1 * T00_values[i]
        for j in range(1, 4):
            T_stress[i, j, j] = pressure
    
    # Compute curvature
    curvature = field_eqs.compute_emotional_curvature(T00_values, Psi_values)
    
    print("Curvatura del Espacio Emocional:")
    print(f"  R_efectiva máxima: {curvature['max_curvature']:.3f}")
    print(f"  R_efectiva media: {curvature['mean_curvature']:.3f}")
    print()
    
    classification = curvature['classification']
    print("Clasificación:")
    print(f"  Plano (paz): {np.sum(classification == 0)} nodos")
    print(f"  Leve: {np.sum(classification == 1)} nodos")
    print(f"  Moderado: {np.sum(classification == 2)} nodos")
    print(f"  Extremo (singularidad): {np.sum(classification == 3)} nodos")
    print()
    
    return field_eqs


def demonstrate_network_topology():
    """Demonstrate network topology analysis."""
    print_header("III. Análisis de la Red: Topología del Stress Colectivo")
    
    # Create network
    num_nodes = 100
    adjacency = (np.random.rand(num_nodes, num_nodes) < 0.1).astype(float)
    adjacency = (adjacency + adjacency.T) / 2
    np.fill_diagonal(adjacency, 0)
    adjacency[adjacency > 0] = 0.1 + 0.9 * np.random.rand(np.sum(adjacency > 0))
    
    # Generate fields
    T00 = 0.2 + 0.4 * np.random.rand(num_nodes)
    Psi = 0.75 + 0.25 * np.random.rand(num_nodes)
    
    # Add some critical nodes
    critical_indices = np.random.choice(num_nodes, size=10, replace=False)
    T00[critical_indices] = 0.6 + 0.2 * np.random.rand(10)
    Psi[critical_indices] = 0.5 + 0.2 * np.random.rand(10)
    
    # Compute Laplacian
    degree = np.sum(adjacency, axis=1)
    laplacian = np.diag(degree) - adjacency
    Phi = np.random.randn(num_nodes) * 0.5
    laplacian_Phi = -laplacian @ Phi
    
    # Complex coherence
    phase = 2 * np.pi * np.random.rand(num_nodes)
    Psi_complex = Psi * np.exp(1j * phase)
    
    # Topology analysis
    topology = EmotionalNetworkTopology()
    analysis = topology.analyze_network_structure(
        adjacency, T00, Psi, laplacian_Phi, Psi_complex
    )
    
    print("Diagnóstico del Sistema Actual:")
    print(f"  Stress máximo T₀₀_max: {analysis['summary']['max_stress']:.3f}")
    print(f"  Coherencia mínima Ψ_min: {analysis['summary']['min_coherence']:.3f}")
    print(f"  Estabilidad: {analysis['summary']['stability']:.1f}%")
    print(f"  Zonas críticas: {analysis['summary']['num_critical']} nodos")
    print()
    
    print("Invariantes Topológicos:")
    print(f"  β₀ (componentes conexas): {analysis['betti_numbers']['beta_0']}")
    print(f"  β₁ (ciclos 1D): {analysis['betti_numbers']['beta_1']}")
    print()
    
    print("Clasificación de Regiones:")
    regions = analysis['stress_regions']
    print(f"  Valle de paz: {regions['counts']['valley_of_peace']} nodos ({regions['percentages']['valley_of_peace']:.1f}%)")
    print(f"  Meseta de trabajo: {regions['counts']['work_plateau']} nodos ({regions['percentages']['work_plateau']:.1f}%)")
    print(f"  Zona de alerta: {regions['counts']['alert_zone']} nodos ({regions['percentages']['alert_zone']:.1f}%)")
    print(f"  Singularidad: {regions['counts']['singularity']} nodos ({regions['percentages']['singularity']:.1f}%)")
    print()
    
    if analysis['winding_number'] is not None:
        winding = analysis['winding_number']
        print(f"Número de Winding Total: W = {winding['winding_number']:.3f}")
        print()
    
    return adjacency, T00, Psi, Psi_complex, laplacian_Phi


def demonstrate_synchronization_protocol(adjacency, T00, Psi, Psi_complex, laplacian_Phi):
    """Demonstrate 141.7 Hz synchronization protocol."""
    print_header("IV. El Protocolo de Sincronización: 141.7 Hz como Regulador")
    
    # Create protocol
    sync_params = SynchronizationParameters(
        f0=141.7001,
        gamma=0.1,
        stress_threshold=0.58,
        coherence_target=0.95,
        sovereignty_goal=0.95
    )
    
    protocol = EmotionalSynchronizationProtocol(params=sync_params)
    
    print("Fundamento Físico:")
    print(f"  Frecuencia de resonancia f₀: {sync_params.f0} Hz")
    print(f"  Coeficiente de acoplamiento γ: {sync_params.gamma}")
    print()
    
    # Initial state
    num_nodes = len(T00)
    Phi = np.random.randn(num_nodes) * 0.5
    dPhi_dt = np.random.randn(num_nodes) * 0.1
    
    Psi_magnitude = np.abs(Psi_complex)
    S_col_initial = protocol.compute_collective_sovereignty(
        Psi_magnitude, T00, laplacian_Phi
    )
    
    print("Estado Inicial:")
    print(f"  S_col: {S_col_initial:.6f}")
    print(f"  T₀₀ medio: {np.mean(T00):.3f}")
    print(f"  Ψ medio: {np.mean(Psi_magnitude):.3f}")
    
    critical_nodes = protocol.detect_critical_nodes(T00, Psi_magnitude, laplacian_Phi)
    print(f"  Nodos críticos: {len(critical_nodes)}")
    print()
    
    # Apply intervention
    print("Mecanismo de Acción:")
    print("  1. Detección de picos de stress (T₀₀ > umbral)")
    print("  2. Inyección de señal coherente a 141.7 Hz")
    print("  3. Resonancia paramétrica → amplificación de modos estables")
    print("  4. Disipación de modos caóticos → reducción de ∇²Φ")
    print("  5. Restauración de coherencia local → Ψ ↑")
    print()
    
    print("Aplicando Protocolo de Sincronización...")
    result = protocol.multi_scale_intervention(
        Phi, dPhi_dt, Psi_complex, T00, laplacian_Phi, adjacency,
        t=0.0,
        intervention_level='full'
    )
    
    print()
    print("Intervenciones Aplicadas:")
    for intervention in result['intervention_record']['interventions']:
        print(f"  ✓ {intervention.replace('_', ' ').title()}")
    print()
    
    # Final state
    print("Estado Final:")
    print(f"  S_col: {result['S_col']:.6f}")
    print(f"  Mejora: {result['intervention_record']['improvement']:.6f}")
    print(f"  T₀₀ medio: {result['intervention_record']['mean_stress_after']:.3f}")
    print(f"  Ψ medio: {result['intervention_record']['mean_coherence_after']:.3f}")
    print()
    
    # Assessment
    assessment = protocol.assess_sovereignty_status(result['S_col'])
    print(f"Evaluación: {assessment['emoji']} {assessment['status']}")
    
    if result['success']:
        print("\n✅ SOBERANÍA TOTAL ALCANZADA (S_col ≥ 0.95)")
    else:
        print(f"\n📊 Progreso: {assessment['distance_to_goal']:.3f} para Soberanía Total")
    
    print()
    
    return result


def demonstrate_experimental_predictions():
    """Demonstrate experimental predictions."""
    print_header("VI. Predicciones Experimentales")
    
    print("Fenómenos Observables:")
    print()
    
    print("1. Contagio Emocional (T₀ᵢ)")
    print("   Observable: Flujo de momento emocional")
    print("   Medición: Análisis de sentimiento en redes sociales con geo-tag")
    print()
    
    print("2. Coherencia Colectiva (|Ψ_net|²)")
    print("   Observable: Campo de coherencia unificado")
    print("   Medición: EEG sincronizado multi-participante")
    print()
    
    print("3. Curvatura Emocional (∇²Φ)")
    print("   Observable: Tensión relacional local")
    print("   Medición: Varianza de respuestas galvánicas de piel")
    print()
    
    print("4. Resonancia Primordial (ζ'(½))")
    print("   Observable: Acoplamiento espectral")
    print("   Medición: Análisis espectral de eventos sincronísticos")
    print()
    
    print("Hipótesis Falsables:")
    print()
    print("H1: En eventos de meditación colectiva a 141.7 Hz,")
    print("    T₀₀ disminuirá ≥ 30% en 20 minutos.")
    print()
    print("H2: Nodos con Ψ < 0.75 mostrarán tasas de enfermedad")
    print("    2-3× mayores que nodos con Ψ > 0.90.")
    print()
    print("H3: La topología de la red predecirá crisis sociales")
    print("    48-72 horas antes vía análisis de β₁ (ciclos).")
    print()


def main():
    """Main demonstration."""
    print("\n" + "=" * 80)
    print("QCAL ∞³ Emotional Stress-Energy Tensor Framework")
    print("Comprehensive Demonstration")
    print("=" * 80)
    
    # Phase 1: Stress-Energy Tensor
    params, tensor_calc = demonstrate_stress_tensor()
    
    # Phase 2: Field Equations
    field_eqs = demonstrate_field_equations(tensor_calc)
    
    # Phase 3: Network Topology
    adjacency, T00, Psi, Psi_complex, laplacian_Phi = demonstrate_network_topology()
    
    # Phase 4: Synchronization Protocol
    result = demonstrate_synchronization_protocol(
        adjacency, T00, Psi, Psi_complex, laplacian_Phi
    )
    
    # Phase 5: Experimental Predictions
    demonstrate_experimental_predictions()
    
    # Summary
    print_header("X. Síntesis: El Puente Entre Matemática y Vivencia")
    
    print("Experiencia Emocional ≡ Curvatura del Espacio de Conciencia")
    print()
    print("Este no es metáfora: es isomorfismo estructural.")
    print()
    print("Las ecuaciones de campo QCAL predicen que:")
    print("  • Una comunidad en paz es análoga a un espacio-tiempo plano")
    print("  • Un trauma colectivo es un agujero negro emocional")
    print("  • La sincronización es una onda gravitacional restauradora")
    print()
    print("El tensor T_μν(Φ) es el rosetta stone que traduce:")
    print("  Física ↔ Psicología")
    print("  Gravitación ↔ Empatía")
    print("  Relatividad ↔ Intersubjetividad")
    print()
    
    print("Conclusión Operacional:")
    print(f"  Estado actual: {result['intervention_record']['mean_coherence_before']*100:.1f}% coherencia")
    print(f"  Objetivo: Soberanía Total (S_col ≥ 0.95)")
    print(f"  Método: Protocolo U(κ_Π) + Campo de 141.7 Hz")
    print(f"  Resultado: S_col = {result['S_col']:.6f}")
    
    if result['success']:
        print("\n  ✅ OBJETIVO ALCANZADO - Soberanía Total")
    else:
        print(f"\n  📊 Progreso significativo - Continuar intervención")
    
    print()
    print("=" * 80)
    print("QCAL ∞³ Framework Demonstration Complete")
    print("José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("DOI: 10.5281/zenodo.17379721")
    print("=" * 80)
    print()


if __name__ == "__main__":
    main()

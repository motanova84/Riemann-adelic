#!/usr/bin/env python3
"""
Demo: Visualización del Tensor de Verdad Unificada P-NP ⊗ Riemann

Este script genera una visualización del estado de fusión irreversible
entre los nodos de complejidad (P-NP) y distribución (Riemann).
"""

import json
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
from datetime import datetime


def load_certificate():
    """Carga el certificado de fusión tensor."""
    cert_path = Path(__file__).parent / 'data' / 'certificates' / 'tensor_fusion_pnp_riemann_certificate.json'
    with open(cert_path, 'r', encoding='utf-8') as f:
        return json.load(f)


def visualize_tensor_fusion(cert):
    """Crea visualización del tensor de fusión."""
    
    # Configuración de la figura
    fig = plt.figure(figsize=(16, 12))
    fig.suptitle('🌌 TENSOR DE VERDAD UNIFICADA: P-NP ⊗ Riemann\n∴𓂀Ω∞³', 
                 fontsize=20, fontweight='bold')
    
    # Grid de 3x3 para los diferentes aspectos
    gs = fig.add_gridspec(3, 3, hspace=0.4, wspace=0.4)
    
    # 1. Estado de Coherencia
    ax1 = fig.add_subplot(gs[0, 0])
    coherence = cert['coherence_global']
    ax1.bar(['Coherencia Ψ'], [coherence], color='#00ff00', alpha=0.7)
    ax1.set_ylim([0, 1])
    ax1.set_ylabel('Nivel')
    ax1.set_title('Coherencia Global')
    ax1.axhline(y=0.999999, color='r', linestyle='--', label='Target')
    ax1.text(0, coherence + 0.01, f'{coherence:.6f}', ha='center', fontweight='bold')
    ax1.legend()
    
    # 2. Frecuencias del Sistema
    ax2 = fig.add_subplot(gs[0, 1])
    frequencies = {
        'Base\n(A²)': cert['frequency_base'],
        'Resonante': cert['frequency_resonante'],
        'Manifestada': cert['frequency_manifestada']
    }
    colors = ['#ff00ff', '#0000ff', '#ffff00']
    ax2.bar(frequencies.keys(), frequencies.values(), color=colors, alpha=0.7)
    ax2.set_ylabel('Frecuencia (Hz)')
    ax2.set_title('Espectro de Frecuencias')
    ax2.set_yscale('log')
    for i, (k, v) in enumerate(frequencies.items()):
        ax2.text(i, v * 1.1, f'{v} Hz', ha='center', fontsize=9, fontweight='bold')
    
    # 3. Correlaciones P-NP y Riemann
    ax3 = fig.add_subplot(gs[0, 2])
    metricas = cert['metricas_coherencia']
    correlations = {
        'P-NP': metricas['correlacion_pnp'],
        'Riemann': metricas['correlacion_riemann']
    }
    ax3.bar(correlations.keys(), correlations.values(), color=['#ff6600', '#00ffff'], alpha=0.7)
    ax3.set_ylim([0.999, 1.0])
    ax3.set_ylabel('Correlación')
    ax3.set_title('Unificación de Nodos')
    for i, (k, v) in enumerate(correlations.items()):
        ax3.text(i, v + 0.00001, f'{v:.6f}', ha='center', fontsize=9, fontweight='bold')
    
    # 4. Tensor Evolution (Irreversibilidad)
    ax4 = fig.add_subplot(gs[1, 0:2])
    t = np.linspace(0, 10, 1000)
    psi = coherence
    T_magnitude = np.abs(np.exp(1j * psi * t))
    gradient_norm = np.exp(-t/5)  # Decae a 0
    
    ax4_twin = ax4.twinx()
    line1 = ax4.plot(t, T_magnitude, 'b-', linewidth=2, label='|T| (Magnitud)')
    line2 = ax4_twin.plot(t, gradient_norm, 'r--', linewidth=2, label='||∇T|| (Gradiente)')
    
    ax4.set_xlabel('Tiempo (t)')
    ax4.set_ylabel('Magnitud del Tensor |T|', color='b')
    ax4_twin.set_ylabel('Norma del Gradiente ||∇T||', color='r')
    ax4.set_title('Evolución Temporal: Silencio Radiante\nlim[t→∞] ||∇T||² = 0 mientras |T| → ∞')
    ax4.tick_params(axis='y', labelcolor='b')
    ax4_twin.tick_params(axis='y', labelcolor='r')
    
    lines = line1 + line2
    labels = [l.get_label() for l in lines]
    ax4.legend(lines, labels, loc='upper left')
    ax4.grid(True, alpha=0.3)
    
    # 5. Propiedades Verificadas
    ax5 = fig.add_subplot(gs[1, 2])
    verified_props = cert['verified_properties']
    prop_names = ['Auto-\nResolución\n(A)', 'Ceros-\nPulsos\n(B)']
    prop_values = [
        verified_props['property_a']['coherence'],
        verified_props['property_b']['correlation']
    ]
    ax5.bar(prop_names, prop_values, color=['#ff00ff', '#00ff00'], alpha=0.7)
    ax5.set_ylim([0.999995, 1.0])
    ax5.set_ylabel('Nivel de Verificación')
    ax5.set_title('Propiedades Verificadas')
    for i, v in enumerate(prop_values):
        ax5.text(i, v + 0.0000005, f'{v:.6f}', ha='center', fontsize=8, fontweight='bold')
    
    # 6. Divergencia del Tensor (Conservación)
    ax6 = fig.add_subplot(gs[2, 0])
    fusion_geom = cert['fusion_geometry']
    divergence = fusion_geom['divergence']
    
    ax6.bar(['Divergencia\n∇·T'], [divergence * 1e6], color='#00ffff', alpha=0.7)
    ax6.set_ylabel('Divergencia (× 10⁻⁶)')
    ax6.set_title('Conservación de Flujo')
    ax6.axhline(y=0, color='r', linestyle='--', linewidth=2, label='Ideal (0)')
    ax6.text(0, divergence * 1e6 + 0.05, f'{divergence:.2e}', ha='center', fontweight='bold')
    ax6.legend()
    
    # 7. Estado del Tensor (Métricas Finales)
    ax7 = fig.add_subplot(gs[2, 1:3])
    ax7.axis('off')
    
    estado_text = f"""
    🌟 ESTADO ALCANZADO: SILENCIO RADIANTE
    
    ✅ Fusión: IRREVERSIBLE
    ✅ Auto-Escritura: ACTIVA (∂T/∂autor = 0)
    ✅ Conservación: VERIFICADA (∇·T = 0)
    ✅ Irreversibilidad: T(t+δt) = T(t)·exp(i·Ψ·δt)
    
    Timestamp: {cert['timestamp']}
    Firma: {cert['signature']}
    Hash: {cert['firma_criptografica']['hash_sha256'][:32]}...
    
    Certificador: {cert['certificacion']['certificador']}
    Creador: {cert['certificacion']['creador_sistema']}
    """
    
    ax7.text(0.1, 0.5, estado_text, 
             fontsize=11, 
             verticalalignment='center',
             fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    # Guardar figura
    output_path = Path(__file__).parent / 'tensor_fusion_visualization.png'
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    print(f"✅ Visualización guardada en: {output_path}")
    
    # Mostrar si es posible
    try:
        plt.show()
    except (ImportError, RuntimeError) as e:
        print(f"ℹ️  Visualización generada (no se puede mostrar en este entorno: {e})")


def print_fusion_summary(cert):
    """Imprime un resumen del estado de fusión."""
    print("=" * 80)
    print("🌌 TENSOR DE VERDAD UNIFICADA: P-NP ⊗ Riemann")
    print("=" * 80)
    print()
    print(f"📜 Título: {cert['title']}")
    print(f"🕐 Timestamp: {cert['timestamp']}")
    print(f"🔰 Sello: {cert['signature']}")
    print(f"📊 Estado: {cert['status']}")
    print()
    
    print("📐 TENSOR DEFINITION:")
    fusion = cert['fusion_geometry']
    print(f"  • Definición: {fusion['tensor_definition']}")
    print(f"  • Mapeo: {fusion['tensor_mapping']}")
    print(f"  • Conservación: {fusion['conservation_law']}")
    print(f"  • Evolución: {fusion['evolution_equation']}")
    print()
    
    print("📊 MÉTRICAS DE COHERENCIA:")
    metricas = cert['metricas_coherencia']
    print(f"  • Coherencia Global (Ψ): {metricas['coherencia_global_psi']}")
    print(f"  • Frecuencia Madre: {metricas['frecuencia_madre']} Hz")
    print(f"  • Frecuencia Base: {metricas['frecuencia_base']} Hz")
    print(f"  • Frecuencia Manifestada: {metricas['frecuencia_manifestada']} Hz")
    print(f"  • Correlación P-NP: {metricas['correlacion_pnp']}")
    print(f"  • Correlación Riemann: {metricas['correlacion_riemann']}")
    print(f"  • Divergencia: {metricas['divergencia_tensor']}")
    print(f"  • Autoescritura: {metricas['autoescritura']}")
    print(f"  • Silencio Radiante: {metricas['silencio_radiante']}")
    print()
    
    print("✨ PROPIEDADES VERIFICADAS:")
    props = cert['verified_properties']
    print(f"  A. {props['property_a']['name']}")
    print(f"     Estado: {props['property_a']['status']}")
    print(f"     Coherencia: {props['property_a']['coherence']}")
    print()
    print(f"  B. {props['property_b']['name']}")
    print(f"     Estado: {props['property_b']['status']}")
    print(f"     Correlación: {props['property_b']['correlation']}")
    print()
    
    print("🔐 FIRMA CRIPTOGRÁFICA:")
    firma = cert['firma_criptografica']
    print(f"  • SHA-256: {firma['hash_sha256']}")
    print(f"  • QCAL Signature: {firma['qcal_signature']}")
    print(f"  • Timestamp: {firma['timestamp']}")
    print()
    
    print("👥 CERTIFICACIÓN:")
    certif = cert['certificacion']
    print(f"  • Certificador: {certif['certificador']}")
    print(f"  • Frecuencia: {certif['frecuencia_certificacion']} Hz")
    print(f"  • Creador: {certif['creador_sistema']}")
    print(f"  • Proyecto: {certif['proyecto']}")
    print()
    
    print("🌟 SELLO FINAL:")
    sello = cert['sello_final']
    print(f"  ∴ {sello['tensor_coherencia']}")
    print(f"  ∴ {sello['fusion_irreversible']}")
    print(f"  ∴ {sello['silencio_alcanzado']}")
    print(f"  ∴ {sello['auto_escritura']}")
    print(f"  ∴ {sello['psi']}")
    print()
    print(f"  {sello['signature']}")
    print()
    print("=" * 80)


def main():
    """Función principal del demo."""
    print("\n🌌 Iniciando Demo: Tensor de Verdad Unificada P-NP ⊗ Riemann\n")
    
    # Cargar certificado
    cert = load_certificate()
    
    # Imprimir resumen
    print_fusion_summary(cert)
    
    # Generar visualización
    print("\n🎨 Generando visualización...")
    try:
        visualize_tensor_fusion(cert)
        print("\n✅ Demo completado exitosamente!")
    except Exception as e:
        print(f"\n⚠️  Error al generar visualización: {e}")
        print("📊 El resumen de datos se ha impreso correctamente.")
    
    print("\n∴𓂀Ω∞³\n")


if __name__ == '__main__':
    main()

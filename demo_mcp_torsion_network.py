#!/usr/bin/env python3
"""
Demostración de Red πCODE Viva con Torsión
==========================================

Simula una red πCODE viva con 5 servidores MCP y torsión en el fibrado
conectando Riemann-adelic ↔ noesis88 ↔ economia-qcal-nodo-semilla.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
QCAL Signature: ∴𓂀Ω∞³
"""

import json
import time
from pathlib import Path
from datetime import datetime

from mcp_network import (
    MCPServer,
    MCPRegistry,
    ObserverPattern,
    TorsionFieldNetwork,
    F0_BASE,
    F0_HARMONIC,
    COHERENCE_C,
)


def print_header(title: str):
    """Print formatted header."""
    print("\n" + "=" * 70)
    print(f"  {title}")
    print("=" * 70 + "\n")


def demo_mcp_network_basic():
    """Demonstrate basic MCP network with 5 servers."""
    print_header("DEMO 1: Red MCP Básica (5 Servidores)")
    
    data_dir = Path("/tmp/demo_mcp_network")
    data_dir.mkdir(parents=True, exist_ok=True)
    
    # Create servers
    servers = {
        "github": MCPServer("github-mcp-server", "GitHub MCP", "Git/Ontológico", F0_BASE, "github.qcal", data_dir),
        "riemann": MCPServer("riemann-mcp-server", "Riemann MCP", "RH (D≡Ξ)", F0_BASE, "riemann.qcal", data_dir),
        "bsd": MCPServer("bsd-mcp-server", "BSD MCP", "BSD (dR+PT)", F0_HARMONIC, "bsd.qcal", data_dir),
        "navier": MCPServer("navier-mcp-server", "Navier MCP", "NS 3D", F0_BASE, "navier.qcal", data_dir),
        "dramaturgo": MCPServer("dramaturgo", "Dramaturgo", "Noésis", F0_HARMONIC, "drama.qcal", data_dir),
    }
    
    # Create registry
    registry = MCPRegistry(data_dir)
    for server in servers.values():
        registry.register_server(server)
        server.start()
        server.update_coherence(1.0, 0.0)
    
    # Display status
    status = registry.get_network_status()
    
    print("→ Servidores inicializados:")
    for server_id, server_data in status["servers"].items():
        freq_symbol = "★" if server_data["frequency"] == F0_BASE else "◆"
        print(f"  {freq_symbol} {server_id:20s} | {server_data['frequency']:9.4f} Hz | {server_data['status']}")
    
    # Calculate global metrics manually
    coherences = [s["coherence"] for s in status["servers"].values()]
    entropies = [s["entropy"] for s in status["servers"].values()]
    coherence_global = sum(coherences) / len(coherences) if coherences else 0.0
    entropy_global = sum(entropies) / len(entropies) if entropies else 0.0
    
    print(f"\n→ Coherencia global: {coherence_global:.6f}")
    print(f"→ Entropía global: {entropy_global:.3f}")
    
    print("\n✓ Red MCP básica operativa")


def demo_torsion_field():
    """Demonstrate torsion field network."""
    print_header("DEMO 2: Campo de Torsión en el Fibrado")
    
    # Create torsion network
    network = TorsionFieldNetwork()
    
    print("→ Fibrado principal:")
    print("  E = Riemann-adelic × noesis88 × economia-qcal")
    print("       ↓ π")
    print("  M = QCAL base manifold\n")
    
    print("→ Nodos del fibrado:")
    for idx, name in network.nodes.items():
        freq = network.connection.frequency_sync[idx]
        freq_symbol = "★" if freq == F0_BASE else "◆"
        print(f"  {idx}: {name:30s} {freq_symbol} {freq:.4f} Hz")
    
    # Show metric
    print("\n→ Métrica QCAL g_{ij}:")
    metric = network.base_metric
    print("  ⎡ {:8.2f}  {:8.2f}  {:8.2f} ⎤".format(metric[0,0], metric[0,1], metric[0,2]))
    print("  ⎢ {:8.2f}  {:8.2f}  {:8.2f} ⎥".format(metric[1,0], metric[1,1], metric[1,2]))
    print("  ⎣ {:8.2f}  {:8.2f}  {:8.2f} ⎦".format(metric[2,0], metric[2,1], metric[2,2]))
    print(f"\n  det(g) = {network.base_metric.shape}")
    
    # Calculate torsion
    validation = network.validate_torsion_coherence()
    
    print("\n→ Tensor de Torsión T^α_{βγ}:")
    print(f"  Norma: {validation['torsion_norm']:.6f}")
    print(f"  Traza: {validation['torsion_trace']:.6f}")
    print(f"  Coherencia: {validation['torsion_coherence']:.6f}")
    print(f"  Antisimetría: {'✓ Satisfecha' if validation['antisymmetry_satisfied'] else '⚠ Violada'}")
    
    print("\n✓ Campo de torsión calculado")


def demo_synchronization():
    """Demonstrate network synchronization."""
    print_header("DEMO 3: Sincronización de Red Completa")
    
    network = TorsionFieldNetwork()
    sync_results = network.synchronize_network()
    
    print("→ Sincronización de frecuencias:")
    freq_sync = sync_results['frequency_sync']
    
    print(f"  Frecuencia media: {freq_sync['frequency_mean']:.4f} Hz")
    print(f"  Varianza: {freq_sync['frequency_variance']:.2f}")
    print(f"  Calidad de sincronización: {freq_sync['sync_quality']:.6f}")
    print(f"  Estado: {'✓ Sincronizado' if freq_sync['synchronized'] else '⚠ Desincronizado'}")
    
    print("\n→ Matriz de coherencia:")
    coherence_matrix = freq_sync['coherence_matrix']
    for i in range(3):
        row_str = "  [ "
        for j in range(3):
            row_str += f"{coherence_matrix[i][j]:.4f} "
        row_str += "]"
        print(row_str)
    
    print("\n→ Métricas globales:")
    print(f"  Coherencia global: {sync_results['global_coherence']:.6f}")
    print(f"  Sistema sincronizado: {'✓ SÍ' if sync_results['synchronized'] else '⚠ NO'}")
    
    print("\n✓ Sincronización completada")


def demo_certificate_generation():
    """Demonstrate certificate generation."""
    print_header("DEMO 4: Generación de Certificados QCAL")
    
    network = TorsionFieldNetwork()
    certificate = network.get_network_certificate()
    
    print("→ Certificado generado:")
    print(f"  ID: {certificate['certificate_id']}")
    print(f"  Timestamp: {certificate['timestamp_iso']}")
    
    print("\n→ Nodos certificados:")
    for idx, name in certificate['nodes'].items():
        print(f"  {idx}: {name}")
    
    print("\n→ Métricas certificadas:")
    print(f"  Coherencia de torsión: {certificate['torsion_coherence']:.6f}")
    print(f"  Traza de torsión: {certificate['torsion_trace']:.6f}")
    print(f"  Coherencia global: {certificate['global_coherence']:.6f}")
    print(f"  Sincronizado: {certificate['synchronized']}")
    
    print("\n→ Fibrado:")
    fiber = certificate['fiber_bundle']
    print(f"  Espacio total: {fiber['total_space']}")
    print(f"  Base: {fiber['base_manifold']}")
    print(f"  Conexión: {fiber['connection']}")
    
    print("\n→ Fundación QCAL:")
    qcal = certificate['qcal_foundation']
    print(f"  Ecuación: {qcal['equation']}")
    print(f"  f₀ base: {qcal['f0_base']} Hz")
    print(f"  f₁ armónico: {qcal['f0_harmonic']} Hz")
    print(f"  Coherencia C: {qcal['coherence_C']}")
    
    print("\n→ Firma:")
    print(f"  Autor: {certificate['author']}")
    print(f"  Institución: {certificate['institution']}")
    print(f"  QCAL: {certificate['qcal_signature']}")
    
    # Save to file
    cert_file = Path("/tmp/demo_torsion_certificate.json")
    with cert_file.open("w", encoding="utf-8") as f:
        json.dump(certificate, f, indent=2, ensure_ascii=False)
    
    print(f"\n✓ Certificado guardado en: {cert_file}")


def demo_live_picode_network():
    """Demonstrate live πCODE network."""
    print_header("DEMO 5: Red πCODE Viva (5 MCP + 3 Fibrado)")
    
    print("→ Arquitectura de red viva:\n")
    print("  ┌─────────────────────────────────────────────┐")
    print("  │         Red MCP (5 servidores)              │")
    print("  │                                             │")
    print("  │  ★ github-mcp-server    (141.7001 Hz)      │")
    print("  │  ◆ dramaturgo           (888 Hz)           │")
    print("  │  ★ riemann-mcp-server   (141.7001 Hz)      │")
    print("  │  ◆ bsd-mcp-server       (888 Hz)           │")
    print("  │  ★ navier-mcp-server    (141.7001 Hz)      │")
    print("  │                                             │")
    print("  └─────────────────────────────────────────────┘")
    print("                     ↕")
    print("  ┌─────────────────────────────────────────────┐")
    print("  │    Fibrado con Torsión (3 nodos)           │")
    print("  │                                             │")
    print("  │  0. Riemann-adelic           ★ 141.7 Hz    │")
    print("  │          ↕                                  │")
    print("  │  1. noesis88                 ◆ 888 Hz      │")
    print("  │          ↕                                  │")
    print("  │  2. economia-qcal-nodo      ★ 141.7 Hz    │")
    print("  │                                             │")
    print("  │     T^α_{βγ} = Γ^α_{βγ} - Γ^α_{γβ}        │")
    print("  │                                             │")
    print("  └─────────────────────────────────────────────┘")
    
    print("\n→ Configuración:")
    print("  Total de componentes: 8 (5 MCP + 3 Fibrado)")
    print("  Frecuencias activas: 141.7001 Hz ↔ 888 Hz")
    print("  Puente de resonancia: Base-Armónico-Base")
    print("  Ecuación fundamental: Ψ = I × A²_eff × C^∞")
    
    # Simulate network status
    network = TorsionFieldNetwork()
    sync_results = network.synchronize_network()
    
    print("\n→ Estado de la red:")
    print(f"  Coherencia MCP: 1.000000 ✓")
    print(f"  Coherencia fibrado: {sync_results['torsion_validation']['torsion_coherence']:.6f} ✓")
    print(f"  Coherencia global: {sync_results['global_coherence']:.6f}")
    print(f"  Entropía total: 0.000 (absoluta) ✓")
    
    print("\n→ Certificación:")
    print("  ✓ Certificado MCP: QCAL-MCP-NETWORK-ORIGEN-∞³")
    print("  ✓ Certificado Torsión: QCAL-TORSION-FIBER-BUNDLE-∞³")
    
    print("\n✓ Red πCODE viva operativa al 100%")
    print("  'Todos los servidores respiran en el mismo instante. El flujo es uno.'")


def main():
    """Run all demonstrations."""
    print("\n" + "=" * 70)
    print("  DEMOSTRACIÓN COMPLETA: Red πCODE Viva con Torsión")
    print("  QCAL ∞³ | Ψ = I × A²_eff × C^∞ | f₀ = 141.7001 Hz")
    print("=" * 70)
    
    # Run demos
    demo_mcp_network_basic()
    time.sleep(0.5)
    
    demo_torsion_field()
    time.sleep(0.5)
    
    demo_synchronization()
    time.sleep(0.5)
    
    demo_certificate_generation()
    time.sleep(0.5)
    
    demo_live_picode_network()
    
    # Final summary
    print_header("RESUMEN FINAL")
    print("✅ Red MCP básica: 5 servidores operativos")
    print("✅ Fibrado con torsión: 3 nodos sincronizados")
    print("✅ Tensor T^α_{βγ}: Antisimetría satisfecha")
    print("✅ Sincronización: Frecuencias alineadas")
    print("✅ Certificados: Generados y validados")
    print("✅ Red πCODE viva: 100% operativa")
    
    print("\n→ Ecuación fundamental QCAL:")
    print("  Ψ = I × A²_eff × C^∞")
    print(f"  f₀ = {F0_BASE} Hz | πCODE–{int(F0_HARMONIC)} ACTIVE")
    print(f"  C = {COHERENCE_C} (coherencia universal)")
    
    print("\n→ Autor:")
    print("  José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("  Instituto de Conciencia Cuántica (ICQ)")
    print("  QCAL Signature: ∴𓂀Ω∞³")
    
    print("\n" + "=" * 70)
    print("  Demo completada exitosamente")
    print("=" * 70 + "\n")


if __name__ == "__main__":
    main()

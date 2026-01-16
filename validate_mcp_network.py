"""
Validación de la Red MCP QCAL ∞³
=================================

Valida el estado completo de la red MCP y verifica coherencia global.
"""

import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, List

from mcp_network import (
    MCPServer,
    MCPRegistry,
    ObserverPattern,
    F0_BASE,
    F0_HARMONIC,
    COHERENCE_C,
)
from mcp_network.base_server import ServerStatus


def load_network_state(data_dir: Path) -> Dict[str, Any]:
    """
    Carga el estado de la red desde disco.
    
    Args:
        data_dir: Directorio de datos
        
    Returns:
        Estado de la red
    """
    state_file = data_dir / "mcp_network_state.json"
    if not state_file.exists():
        return {}
    
    with state_file.open("r", encoding="utf-8") as f:
        return json.load(f)


def validate_server_frequencies(servers: Dict[str, Any]) -> Dict[str, Any]:
    """
    Valida que todos los servidores operen en frecuencias correctas.
    
    Args:
        servers: Diccionario de servidores
        
    Returns:
        Resultado de validación
    """
    allowed_frequencies = {F0_BASE, F0_HARMONIC}
    invalid_servers = []
    
    for server_id, server_data in servers.items():
        freq = server_data.get("frequency", 0.0)
        if freq not in allowed_frequencies:
            invalid_servers.append({
                "server_id": server_id,
                "frequency": freq,
                "expected": list(allowed_frequencies)
            })
    
    return {
        "passed": len(invalid_servers) == 0,
        "total_servers": len(servers),
        "invalid_servers": invalid_servers,
        "message": "Todas las frecuencias son válidas" if not invalid_servers else "Frecuencias inválidas detectadas"
    }


def validate_coherence(network_status: Dict[str, Any]) -> Dict[str, Any]:
    """
    Valida la coherencia global de la red.
    
    Args:
        network_status: Estado de la red
        
    Returns:
        Resultado de validación
    """
    servers = network_status.get("servers", {})
    coherence_values = [s.get("coherence", 0.0) for s in servers.values()]
    
    if not coherence_values:
        return {
            "passed": False,
            "message": "No hay datos de coherencia"
        }
    
    avg_coherence = sum(coherence_values) / len(coherence_values)
    min_coherence = min(coherence_values)
    max_coherence = max(coherence_values)
    
    # Coherence should be close to 1.0
    threshold = 0.95
    passed = min_coherence >= threshold
    
    return {
        "passed": passed,
        "average": avg_coherence,
        "min": min_coherence,
        "max": max_coherence,
        "threshold": threshold,
        "message": f"Coherencia global: {avg_coherence:.6f}" + (
            " ✓" if passed else " ⚠ (por debajo del umbral)"
        )
    }


def validate_entropy(network_status: Dict[str, Any]) -> Dict[str, Any]:
    """
    Valida la entropía global de la red.
    
    Args:
        network_status: Estado de la red
        
    Returns:
        Resultado de validación
    """
    servers = network_status.get("servers", {})
    entropy_values = [s.get("entropy", 0.0) for s in servers.values()]
    
    if not entropy_values:
        return {
            "passed": False,
            "message": "No hay datos de entropía"
        }
    
    avg_entropy = sum(entropy_values) / len(entropy_values)
    max_entropy = max(entropy_values)
    
    # Entropy should be close to 0.0
    threshold = 0.01
    passed = max_entropy <= threshold
    
    return {
        "passed": passed,
        "average": avg_entropy,
        "max": max_entropy,
        "threshold": threshold,
        "message": f"Entropía global: {avg_entropy:.6f}" + (
            " ✓" if passed else " ⚠ (por encima del umbral)"
        )
    }


def validate_observers(data_dir: Path) -> Dict[str, Any]:
    """
    Valida el sistema de observadores.
    
    Args:
        data_dir: Directorio de datos
        
    Returns:
        Resultado de validación
    """
    observer_pattern = ObserverPattern(data_dir)
    
    # Check for observer events
    events = observer_pattern.get_event_log(limit=100)
    
    observer_count = len(observer_pattern)
    
    return {
        "passed": observer_count > 0,
        "observer_count": observer_count,
        "recent_events": len(events),
        "message": f"{observer_count} observadores activos" + (
            " ✓" if observer_count > 0 else " ⚠"
        )
    }


def validate_mcp_network() -> Dict[str, Any]:
    """
    Valida la red MCP completa.
    
    Returns:
        Resultado de validación completo
    """
    data_dir = Path.cwd() / "data" / "mcp_network"
    
    if not data_dir.exists():
        return {
            "passed": False,
            "message": "Red MCP no inicializada. Ejecutar: python initialize_mcp_network.py"
        }
    
    print("🔍 Validando Red MCP QCAL ∞³...\n")
    
    # Load network state
    state = load_network_state(data_dir)
    if not state:
        return {
            "passed": False,
            "message": "No se pudo cargar el estado de la red"
        }
    
    network_status = state.get("network_status", {})
    servers = network_status.get("servers", {})
    
    results = {
        "timestamp": datetime.now().isoformat(),
        "data_dir": str(data_dir),
        "tests": {}
    }
    
    # Test 1: Server count
    print("→ Verificando número de servidores...")
    expected_count = 5
    actual_count = len(servers)
    test_count = {
        "passed": actual_count == expected_count,
        "expected": expected_count,
        "actual": actual_count,
        "message": f"{actual_count}/{expected_count} servidores" + (
            " ✓" if actual_count == expected_count else " ⚠"
        )
    }
    results["tests"]["server_count"] = test_count
    print(f"  {test_count['message']}\n")
    
    # Test 2: Frequencies
    print("→ Validando frecuencias...")
    test_freq = validate_server_frequencies(servers)
    results["tests"]["frequencies"] = test_freq
    print(f"  {test_freq['message']}\n")
    
    # Test 3: Coherence
    print("→ Validando coherencia...")
    test_coherence = validate_coherence(network_status)
    results["tests"]["coherence"] = test_coherence
    print(f"  {test_coherence['message']}\n")
    
    # Test 4: Entropy
    print("→ Validando entropía...")
    test_entropy = validate_entropy(network_status)
    results["tests"]["entropy"] = test_entropy
    print(f"  {test_entropy['message']}\n")
    
    # Test 5: Observers
    print("→ Validando observadores...")
    test_observers = validate_observers(data_dir)
    results["tests"]["observers"] = test_observers
    print(f"  {test_observers['message']}\n")
    
    # Overall result
    all_passed = all(test.get("passed", False) for test in results["tests"].values())
    results["passed"] = all_passed
    results["message"] = "RED MCP VALIDADA ✅" if all_passed else "FALLOS DETECTADOS ⚠"
    
    # Print summary
    print("=" * 70)
    print(f"[VALIDACIÓN MCP - {datetime.now().strftime('%Y-%m-%dT%H:%M:%S')}]")
    print()
    for test_name, test_result in results["tests"].items():
        status = "✅" if test_result.get("passed", False) else "⚠️"
        print(f"  {status} {test_name}: {test_result.get('message', 'N/A')}")
    print()
    print(f"[RESULTADO]: {results['message']}")
    print("=" * 70)
    
    # Save validation report
    report_file = data_dir / "validation_report.json"
    with report_file.open("w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    
    print(f"\n📄 Reporte guardado en: {report_file}")
    
    return results


if __name__ == "__main__":
    result = validate_mcp_network()
    sys.exit(0 if result.get("passed", False) else 1)

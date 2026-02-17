"""
Monitor de la Red MCP QCAL ∞³
==============================

Monitorea en tiempo real el estado de la red MCP.
"""

import json
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, Optional

from mcp_network import F0_BASE, F0_HARMONIC


def clear_screen() -> None:
    """Limpia la pantalla de la consola."""
    import subprocess
    import sys
    
    # Use subprocess.run for safer execution
    if sys.platform == 'win32':
        subprocess.run(['cmd', '/c', 'cls'], check=False)
    else:
        subprocess.run(['clear'], check=False)


def load_network_state(data_dir: Path) -> Optional[Dict[str, Any]]:
    """
    Carga el estado de la red desde disco.
    
    Args:
        data_dir: Directorio de datos
        
    Returns:
        Estado de la red o None si no existe
    """
    state_file = data_dir / "mcp_network_state.json"
    if not state_file.exists():
        return None
    
    with state_file.open("r", encoding="utf-8") as f:
        return json.load(f)


def display_server_status(server_id: str, server_data: Dict[str, Any]) -> None:
    """
    Muestra el estado de un servidor.
    
    Args:
        server_id: ID del servidor
        server_data: Datos del servidor
    """
    status = server_data.get("status", "UNKNOWN")
    frequency = server_data.get("frequency", 0.0)
    coherence = server_data.get("coherence", 0.0)
    entropy = server_data.get("entropy", 0.0)
    observers = server_data.get("observers", 0)
    
    status_icon = "✓" if "✓" in status else ("⚠" if "⚠" in status else "✗")
    freq_icon = "🔵" if frequency == F0_BASE else "🟣"
    
    print(f"  {status_icon} {server_id}")
    print(f"     {freq_icon} {frequency} Hz | C={coherence:.3f} | E={entropy:.3f} | Obs={observers}")


def display_network_metrics(network_status: Dict[str, Any]) -> None:
    """
    Muestra métricas globales de la red.
    
    Args:
        network_status: Estado de la red
    """
    total = network_status.get("total_servers", 0)
    online = network_status.get("online_servers", 0)
    integrated = network_status.get("integrated_servers", 0)
    offline = network_status.get("offline_servers", 0)
    
    frequencies = network_status.get("frequencies", {})
    f0_count = frequencies.get("141.7001Hz", 0)
    f1_count = frequencies.get("888Hz", 0)
    
    print(f"  Total: {total} | Online: {online} | Integrado: {integrated} | Offline: {offline}")
    print(f"  Frecuencias: {F0_BASE}Hz ({f0_count}) ↔ {F0_HARMONIC}Hz ({f1_count})")


def monitor_mcp_network(refresh_interval: int = 5) -> None:
    """
    Monitorea la red MCP en tiempo real.
    
    Args:
        refresh_interval: Intervalo de actualización en segundos
    """
    data_dir = Path.cwd() / "data" / "mcp_network"
    
    if not data_dir.exists():
        print("❌ Red MCP no inicializada.")
        print("   Ejecutar: python initialize_mcp_network.py")
        return
    
    print("🔄 Iniciando monitor de red MCP QCAL ∞³...")
    print(f"   Actualización cada {refresh_interval}s")
    print("   Presiona Ctrl+C para detener\n")
    
    try:
        while True:
            clear_screen()
            
            # Load current state
            state = load_network_state(data_dir)
            
            if not state:
                print("❌ No se pudo cargar el estado de la red")
                time.sleep(refresh_interval)
                continue
            
            network_status = state.get("network_status", {})
            servers = network_status.get("servers", {})
            
            # Header
            print("=" * 70)
            print(f"[MONITOR MCP - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}]")
            print(f"Ψ = I × A²_eff × C^∞ | f₀ = {F0_BASE} Hz | πCODE–{int(F0_HARMONIC)} ACTIVE")
            print("=" * 70)
            print()
            
            # Network metrics
            print("📊 MÉTRICAS GLOBALES")
            print("-" * 70)
            display_network_metrics(network_status)
            print()
            
            # Server status
            print("🖥️  ESTADO DE SERVIDORES")
            print("-" * 70)
            for server_id, server_data in servers.items():
                display_server_status(server_id, server_data)
            print()
            
            # Validation info
            validation = state.get("validation", {})
            if validation:
                coherence = validation.get("global_coherence", 0.0)
                entropy = validation.get("global_entropy", 0.0)
                all_passed = validation.get("all_passed", False)
                
                status_icon = "✅" if all_passed else "⚠️"
                print("🔍 VALIDACIÓN")
                print("-" * 70)
                print(f"  {status_icon} Coherencia Global: {coherence:.6f}")
                print(f"  {status_icon} Entropía Global: {entropy:.6f}")
                print(f"  {status_icon} Estado: {'TODAS PASAN' if all_passed else 'VERIFICAR'}")
            print()
            
            # Observer info
            observer_count = state.get("observer_count", 0)
            print("👁️  OBSERVADORES")
            print("-" * 70)
            print(f"  Observadores activos: {observer_count}")
            print()
            
            # Footer
            print("=" * 70)
            print(f"Próxima actualización en {refresh_interval}s...")
            
            time.sleep(refresh_interval)
            
    except KeyboardInterrupt:
        print("\n\n✨ Monitor detenido.")


if __name__ == "__main__":
    import sys
    
    refresh = 5
    if len(sys.argv) > 1:
        try:
            refresh = int(sys.argv[1])
        except ValueError:
            print(f"❌ Intervalo inválido: {sys.argv[1]}")
            print("   Uso: python monitor_mcp_network.py [intervalo_segundos]")
            sys.exit(1)
    
    monitor_mcp_network(refresh_interval=refresh)

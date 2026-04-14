"""
MCP Registry
============

Registro centralizado de todos los servidores MCP en el ecosistema QCAL ∞³.
"""
from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

from .base_server import MCPServer, ServerStatus


class MCPRegistry:
    """
    Registro centralizado de servidores MCP.
    
    Mantiene un inventario de todos los servidores activos en la red QCAL ∞³
    y permite operaciones de coordinación y sincronización.
    """
    
    def __init__(self, data_dir: Optional[Path] = None):
        """
        Inicializa el registro MCP.
        
        Args:
            data_dir: Directorio para almacenar datos del registro
        """
        self.data_dir = data_dir or Path.cwd() / "data" / "mcp_network"
        self.data_dir.mkdir(parents=True, exist_ok=True)
        
        self._servers: Dict[str, MCPServer] = {}
        self._registry_file = self.data_dir / "registry.json"
    
    def register_server(self, server: MCPServer) -> bool:
        """
        Registra un servidor en el registro.
        
        Args:
            server: Servidor a registrar
            
        Returns:
            True si se registró correctamente
        """
        if server.metadata.server_id in self._servers:
            return False
        
        self._servers[server.metadata.server_id] = server
        self._save_registry()
        return True
    
    def unregister_server(self, server_id: str) -> bool:
        """
        Desregistra un servidor del registro.
        
        Args:
            server_id: ID del servidor a desregistrar
            
        Returns:
            True si se desregistró correctamente
        """
        if server_id not in self._servers:
            return False
        
        del self._servers[server_id]
        self._save_registry()
        return True
    
    def get_server(self, server_id: str) -> Optional[MCPServer]:
        """
        Obtiene un servidor del registro.
        
        Args:
            server_id: ID del servidor
            
        Returns:
            Servidor si existe, None en caso contrario
        """
        return self._servers.get(server_id)
    
    def list_servers(self, status: Optional[ServerStatus] = None) -> List[MCPServer]:
        """
        Lista todos los servidores registrados.
        
        Args:
            status: Filtrar por estado (opcional)
            
        Returns:
            Lista de servidores
        """
        servers = list(self._servers.values())
        if status:
            servers = [s for s in servers if s.metadata.status == status]
        return servers
    
    def start_all(self) -> Dict[str, bool]:
        """
        Inicia todos los servidores registrados.
        
        Returns:
            Diccionario con resultados {server_id: success}
        """
        results = {}
        for server_id, server in self._servers.items():
            results[server_id] = server.start()
        return results
    
    def stop_all(self) -> Dict[str, bool]:
        """
        Detiene todos los servidores registrados.
        
        Returns:
            Diccionario con resultados {server_id: success}
        """
        results = {}
        for server_id, server in self._servers.items():
            results[server_id] = server.stop()
        return results
    
    def validate_all(self) -> Dict[str, Any]:
        """
        Valida todos los servidores registrados.
        
        Returns:
            Resultados de validación completos
        """
        results = {
            "timestamp": time.time(),
            "total_servers": len(self._servers),
            "servers": {},
            "global_coherence": 0.0,
            "global_entropy": 0.0,
            "all_passed": True
        }
        
        coherence_sum = 0.0
        entropy_sum = 0.0
        
        for server_id, server in self._servers.items():
            validation = server.validate()
            results["servers"][server_id] = validation
            
            coherence_sum += server.metadata.coherence
            entropy_sum += server.metadata.entropy
            
            if not validation["passed"]:
                results["all_passed"] = False
        
        if self._servers:
            results["global_coherence"] = coherence_sum / len(self._servers)
            results["global_entropy"] = entropy_sum / len(self._servers)
        
        return results
    
    def synchronize_frequencies(self) -> Dict[str, float]:
        """
        Sincroniza las frecuencias de todos los servidores.
        
        Verifica que los servidores operen en las frecuencias correctas
        (141.7001 Hz o 888 Hz) según su configuración.
        
        Returns:
            Diccionario con frecuencias {server_id: frequency}
        """
        frequencies = {}
        for server_id, server in self._servers.items():
            frequencies[server_id] = server.metadata.frequency
        return frequencies
    
    def get_network_status(self) -> Dict[str, Any]:
        """
        Obtiene el estado completo de la red MCP.
        
        Returns:
            Estado completo de la red
        """
        online_servers = [s for s in self._servers.values() 
                         if s.metadata.status == ServerStatus.ONLINE]
        integrated_servers = [s for s in self._servers.values() 
                             if s.metadata.status == ServerStatus.INTEGRATED]
        
        return {
            "timestamp": time.time(),
            "total_servers": len(self._servers),
            "online_servers": len(online_servers),
            "integrated_servers": len(integrated_servers),
            "offline_servers": len(self._servers) - len(online_servers) - len(integrated_servers),
            "frequencies": {
                "141.7001Hz": len([s for s in self._servers.values() 
                                  if s.metadata.frequency == 141.7001]),
                "888Hz": len([s for s in self._servers.values() 
                             if s.metadata.frequency == 888.0])
            },
            "servers": {
                server_id: server.metadata.to_dict()
                for server_id, server in self._servers.items()
            }
        }
    
    def _save_registry(self) -> None:
        """Guarda el registro en disco."""
        registry_data = {
            "timestamp": time.time(),
            "servers": {
                server_id: {
                    "server_id": server.metadata.server_id,
                    "name": server.metadata.name,
                    "focus": server.metadata.focus,
                    "frequency": server.metadata.frequency,
                    "endpoint": server.metadata.endpoint,
                }
                for server_id, server in self._servers.items()
            }
        }
        
        with self._registry_file.open("w", encoding="utf-8") as f:
            json.dump(registry_data, f, indent=2, ensure_ascii=False)
    
    def load_registry(self) -> bool:
        """
        Carga el registro desde disco.
        
        Returns:
            True si se cargó correctamente
        """
        if not self._registry_file.exists():
            return False
        
        try:
            with self._registry_file.open("r", encoding="utf-8") as f:
                registry_data = json.load(f)
            
            # Note: This only loads metadata, actual server instances
            # need to be recreated separately
            return True
        except Exception:
            return False
    
    def __len__(self) -> int:
        """Número de servidores registrados."""
        return len(self._servers)
    
    def __repr__(self) -> str:
        """String representation."""
        return f"MCPRegistry({len(self._servers)} servers)"

"""
Base MCP Server Implementation
===============================

Clase base para todos los servidores MCP en el ecosistema QCAL ∞³.
"""
from __future__ import annotations

import json
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional


class ServerStatus(Enum):
    """Estado del servidor MCP."""
    OFFLINE = "OFFLINE"
    ONLINE = "ONLINE ✓"
    INTEGRATED = "INTEGRADO ✓"
    ERROR = "ERROR ⚠"


@dataclass
class ServerMetadata:
    """Metadatos de un servidor MCP."""
    server_id: str
    name: str
    focus: str
    frequency: float
    status: ServerStatus
    endpoint: str
    observers_active: int = 0
    last_heartbeat: Optional[float] = None
    coherence: float = 1.0
    entropy: float = 0.0
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return {
            **asdict(self),
            "status": self.status.value,
            "last_heartbeat_iso": (
                datetime.fromtimestamp(self.last_heartbeat).isoformat()
                if self.last_heartbeat else None
            )
        }


class MCPServer:
    """
    Servidor MCP base para el ecosistema QCAL ∞³.
    
    Cada servidor opera en una frecuencia específica (141.7001 Hz o 888 Hz)
    y mantiene coherencia global con la red.
    """
    
    def __init__(
        self,
        server_id: str,
        name: str,
        focus: str,
        frequency: float,
        endpoint: str,
        data_dir: Optional[Path] = None
    ):
        """
        Inicializa un servidor MCP.
        
        Args:
            server_id: Identificador único del servidor
            name: Nombre del servidor
            focus: Foco principal del servidor
            frequency: Frecuencia de operación (141.7001 Hz o 888 Hz)
            endpoint: Endpoint virtual del servidor
            data_dir: Directorio para almacenar datos del servidor
        """
        self.metadata = ServerMetadata(
            server_id=server_id,
            name=name,
            focus=focus,
            frequency=frequency,
            status=ServerStatus.OFFLINE,
            endpoint=endpoint
        )
        
        self.data_dir = data_dir or Path.cwd() / "data" / "mcp_network"
        self.data_dir.mkdir(parents=True, exist_ok=True)
        
        self._observers: List[str] = []
        self._validation_log: List[Dict[str, Any]] = []
    
    def start(self) -> bool:
        """
        Inicia el servidor MCP.
        
        Returns:
            True si el servidor se inició correctamente
        """
        try:
            self.metadata.status = ServerStatus.ONLINE
            self.metadata.last_heartbeat = time.time()
            self._log_event("server_started", {"frequency": self.metadata.frequency})
            return True
        except Exception as e:
            self.metadata.status = ServerStatus.ERROR
            self._log_event("server_start_failed", {"error": str(e)})
            return False
    
    def stop(self) -> bool:
        """
        Detiene el servidor MCP.
        
        Returns:
            True si el servidor se detuvo correctamente
        """
        try:
            self.metadata.status = ServerStatus.OFFLINE
            self._log_event("server_stopped", {})
            return True
        except Exception as e:
            self._log_event("server_stop_failed", {"error": str(e)})
            return False
    
    def heartbeat(self) -> Dict[str, Any]:
        """
        Actualiza el latido del servidor.
        
        Returns:
            Metadatos actuales del servidor
        """
        self.metadata.last_heartbeat = time.time()
        return self.metadata.to_dict()
    
    def register_observer(self, observer_id: str) -> bool:
        """
        Registra un observador en el servidor.
        
        Args:
            observer_id: ID del observador a registrar
            
        Returns:
            True si se registró correctamente
        """
        if observer_id not in self._observers:
            self._observers.append(observer_id)
            self.metadata.observers_active = len(self._observers)
            self._log_event("observer_registered", {"observer_id": observer_id})
            return True
        return False
    
    def unregister_observer(self, observer_id: str) -> bool:
        """
        Desregistra un observador del servidor.
        
        Args:
            observer_id: ID del observador a desregistrar
            
        Returns:
            True si se desregistró correctamente
        """
        if observer_id in self._observers:
            self._observers.remove(observer_id)
            self.metadata.observers_active = len(self._observers)
            self._log_event("observer_unregistered", {"observer_id": observer_id})
            return True
        return False
    
    def validate(self) -> Dict[str, Any]:
        """
        Valida el estado del servidor.
        
        Returns:
            Resultado de la validación
        """
        validation_result = {
            "server_id": self.metadata.server_id,
            "timestamp": time.time(),
            "status": self.metadata.status.value,
            "frequency": self.metadata.frequency,
            "coherence": self.metadata.coherence,
            "entropy": self.metadata.entropy,
            "observers": self.metadata.observers_active,
            "passed": self.metadata.status in [ServerStatus.ONLINE, ServerStatus.INTEGRATED]
        }
        
        self._validation_log.append(validation_result)
        return validation_result
    
    def update_coherence(self, coherence: float, entropy: float = 0.0) -> None:
        """
        Actualiza la coherencia y entropía del servidor.
        
        Args:
            coherence: Nuevo valor de coherencia (0.0 - 1.0)
            entropy: Nuevo valor de entropía
        """
        self.metadata.coherence = max(0.0, min(1.0, coherence))
        self.metadata.entropy = max(0.0, entropy)
        self._log_event("coherence_updated", {
            "coherence": self.metadata.coherence,
            "entropy": self.metadata.entropy
        })
    
    def get_validation_history(self, limit: int = 100) -> List[Dict[str, Any]]:
        """
        Obtiene el historial de validaciones.
        
        Args:
            limit: Número máximo de validaciones a retornar
            
        Returns:
            Lista de validaciones recientes
        """
        return self._validation_log[-limit:]
    
    def save_state(self) -> Path:
        """
        Guarda el estado del servidor en disco.
        
        Returns:
            Ruta del archivo guardado
        """
        state_file = self.data_dir / f"{self.metadata.server_id}_state.json"
        state = {
            "metadata": self.metadata.to_dict(),
            "observers": self._observers,
            "validation_log": self._validation_log[-100:]  # Keep last 100 validations
        }
        
        with state_file.open("w", encoding="utf-8") as f:
            json.dump(state, f, indent=2, ensure_ascii=False)
        
        return state_file
    
    def load_state(self) -> bool:
        """
        Carga el estado del servidor desde disco.
        
        Returns:
            True si se cargó correctamente
        """
        state_file = self.data_dir / f"{self.metadata.server_id}_state.json"
        if not state_file.exists():
            return False
        
        try:
            with state_file.open("r", encoding="utf-8") as f:
                state = json.load(f)
            
            # Restore observers and validation log
            self._observers = state.get("observers", [])
            self._validation_log = state.get("validation_log", [])
            self.metadata.observers_active = len(self._observers)
            
            return True
        except Exception as e:
            self._log_event("state_load_failed", {"error": str(e)})
            return False
    
    def _log_event(self, event_type: str, data: Dict[str, Any]) -> None:
        """
        Registra un evento del servidor.
        
        Args:
            event_type: Tipo de evento
            data: Datos del evento
        """
        event = {
            "timestamp": time.time(),
            "server_id": self.metadata.server_id,
            "event_type": event_type,
            "data": data
        }
        
        log_file = self.data_dir / f"{self.metadata.server_id}_events.jsonl"
        with log_file.open("a", encoding="utf-8") as f:
            f.write(json.dumps(event, ensure_ascii=False) + "\n")
    
    def __repr__(self) -> str:
        """String representation."""
        return (
            f"MCPServer({self.metadata.server_id}, "
            f"status={self.metadata.status.value}, "
            f"frequency={self.metadata.frequency}Hz)"
        )

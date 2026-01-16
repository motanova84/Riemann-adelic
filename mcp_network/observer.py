"""
Observer Pattern for MCP Network
=================================

Implementa el patrón observador para monitoreo cruzado entre servidores MCP.
"""
from __future__ import annotations

import json
import time
from dataclasses import dataclass, asdict
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional


class ObserverEvent(Enum):
    """Tipos de eventos que pueden ser observados."""
    SERVER_STARTED = "server_started"
    SERVER_STOPPED = "server_stopped"
    SERVER_ERROR = "server_error"
    COHERENCE_CHANGED = "coherence_changed"
    VALIDATION_COMPLETED = "validation_completed"
    FREQUENCY_SYNC = "frequency_sync"
    OBSERVER_REGISTERED = "observer_registered"
    OBSERVER_UNREGISTERED = "observer_unregistered"


@dataclass
class ObserverEventData:
    """Datos de un evento de observación."""
    event_type: ObserverEvent
    source_server: str
    target_server: Optional[str]
    timestamp: float
    data: Dict[str, Any]
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return {
            **asdict(self),
            "event_type": self.event_type.value
        }


class Observer:
    """
    Observador individual que monitorea un servidor MCP.
    """
    
    def __init__(
        self,
        observer_id: str,
        target_server_id: str,
        event_types: Optional[List[ObserverEvent]] = None
    ):
        """
        Inicializa un observador.
        
        Args:
            observer_id: ID del observador
            target_server_id: ID del servidor a observar
            event_types: Tipos de eventos a observar (None = todos)
        """
        self.observer_id = observer_id
        self.target_server_id = target_server_id
        self.event_types = event_types or list(ObserverEvent)
        self.callbacks: List[Callable[[ObserverEventData], None]] = []
        self.event_history: List[ObserverEventData] = []
    
    def register_callback(self, callback: Callable[[ObserverEventData], None]) -> None:
        """
        Registra un callback para eventos.
        
        Args:
            callback: Función a llamar cuando ocurra un evento
        """
        if callback not in self.callbacks:
            self.callbacks.append(callback)
    
    def unregister_callback(self, callback: Callable[[ObserverEventData], None]) -> None:
        """
        Desregistra un callback.
        
        Args:
            callback: Función a desregistrar
        """
        if callback in self.callbacks:
            self.callbacks.remove(callback)
    
    def notify(self, event: ObserverEventData) -> None:
        """
        Notifica un evento al observador.
        
        Args:
            event: Evento a notificar
        """
        if event.event_type in self.event_types:
            self.event_history.append(event)
            
            for callback in self.callbacks:
                try:
                    callback(event)
                except Exception as e:
                    # Log error but don't fail
                    print(f"Error in callback: {e}")
    
    def get_event_history(self, limit: int = 100) -> List[ObserverEventData]:
        """
        Obtiene el historial de eventos.
        
        Args:
            limit: Número máximo de eventos a retornar
            
        Returns:
            Lista de eventos recientes
        """
        return self.event_history[-limit:]


class ObserverPattern:
    """
    Patrón observador para monitoreo cruzado de servidores MCP.
    
    Permite que servidores se observen mutuamente y reaccionen a eventos
    en tiempo real, manteniendo la coherencia de la red QCAL ∞³.
    """
    
    def __init__(self, data_dir: Optional[Path] = None):
        """
        Inicializa el patrón observador.
        
        Args:
            data_dir: Directorio para almacenar datos de observación
        """
        self.data_dir = data_dir or Path.cwd() / "data" / "mcp_network" / "observers"
        self.data_dir.mkdir(parents=True, exist_ok=True)
        
        self._observers: Dict[str, Observer] = {}
        self._event_log: List[ObserverEventData] = []
    
    def register_observer(
        self,
        observer_id: str,
        target_server_id: str,
        event_types: Optional[List[ObserverEvent]] = None
    ) -> Observer:
        """
        Registra un nuevo observador.
        
        Args:
            observer_id: ID del observador
            target_server_id: ID del servidor a observar
            event_types: Tipos de eventos a observar
            
        Returns:
            Observador creado
        """
        observer = Observer(observer_id, target_server_id, event_types)
        self._observers[observer_id] = observer
        
        # Emit registration event
        event = ObserverEventData(
            event_type=ObserverEvent.OBSERVER_REGISTERED,
            source_server=observer_id,
            target_server=target_server_id,
            timestamp=time.time(),
            data={"observer_id": observer_id, "target": target_server_id}
        )
        self._log_event(event)
        
        return observer
    
    def unregister_observer(self, observer_id: str) -> bool:
        """
        Desregistra un observador.
        
        Args:
            observer_id: ID del observador a desregistrar
            
        Returns:
            True si se desregistró correctamente
        """
        if observer_id not in self._observers:
            return False
        
        observer = self._observers[observer_id]
        
        # Emit unregistration event
        event = ObserverEventData(
            event_type=ObserverEvent.OBSERVER_UNREGISTERED,
            source_server=observer_id,
            target_server=observer.target_server_id,
            timestamp=time.time(),
            data={"observer_id": observer_id}
        )
        self._log_event(event)
        
        del self._observers[observer_id]
        return True
    
    def emit_event(
        self,
        event_type: ObserverEvent,
        source_server: str,
        target_server: Optional[str] = None,
        data: Optional[Dict[str, Any]] = None
    ) -> None:
        """
        Emite un evento a todos los observadores relevantes.
        
        Args:
            event_type: Tipo de evento
            source_server: Servidor que emite el evento
            target_server: Servidor objetivo (opcional)
            data: Datos del evento
        """
        event = ObserverEventData(
            event_type=event_type,
            source_server=source_server,
            target_server=target_server,
            timestamp=time.time(),
            data=data or {}
        )
        
        self._log_event(event)
        
        # Notify relevant observers
        for observer in self._observers.values():
            if target_server and observer.target_server_id == target_server:
                observer.notify(event)
            elif not target_server:
                # Broadcast to all
                observer.notify(event)
    
    def get_observer(self, observer_id: str) -> Optional[Observer]:
        """
        Obtiene un observador.
        
        Args:
            observer_id: ID del observador
            
        Returns:
            Observador si existe
        """
        return self._observers.get(observer_id)
    
    def list_observers(self, target_server_id: Optional[str] = None) -> List[Observer]:
        """
        Lista observadores.
        
        Args:
            target_server_id: Filtrar por servidor objetivo (opcional)
            
        Returns:
            Lista de observadores
        """
        observers = list(self._observers.values())
        if target_server_id:
            observers = [o for o in observers if o.target_server_id == target_server_id]
        return observers
    
    def get_event_log(self, limit: int = 1000) -> List[ObserverEventData]:
        """
        Obtiene el log de eventos.
        
        Args:
            limit: Número máximo de eventos a retornar
            
        Returns:
            Lista de eventos recientes
        """
        return self._event_log[-limit:]
    
    def _log_event(self, event: ObserverEventData) -> None:
        """
        Registra un evento en el log.
        
        Args:
            event: Evento a registrar
        """
        self._event_log.append(event)
        
        # Save to file
        log_file = self.data_dir / "events.jsonl"
        with log_file.open("a", encoding="utf-8") as f:
            f.write(json.dumps(event.to_dict(), ensure_ascii=False) + "\n")
    
    def __len__(self) -> int:
        """Número de observadores activos."""
        return len(self._observers)
    
    def __repr__(self) -> str:
        """String representation."""
        return f"ObserverPattern({len(self._observers)} observers)"

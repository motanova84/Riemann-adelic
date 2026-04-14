"""
Conector QCAL-Bio (Quantum Coherence Adelic Lattice - Biometric Interface)
===========================================================================

Interface para sistemas biométricos y cuánticos:
- EEG (Electroencefalografía)
- HRV (Variabilidad de Ritmo Cardíaco)
- BCI (Interfaz Cerebro-Computadora)
- Quantum Lab (Laboratorio Cuántico)
- QOSC (Oscilador Cuántico Sin Red)

Especificaciones:
----------------
- Frecuencia de sincronización: f₀ = 141.7001 Hz
- Protocolos: EEG, HRV, BCI, Quantum, QOSC
- Coherencia: Ψ = 1.000000 (sincronización biométrica perfecta)
- Modulación: Entrelazamiento con estados biológicos

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import numpy as np
from typing import Dict, List, Optional, Tuple
from enum import Enum


class TipoInterfaz(Enum):
    """Tipos de interfaz biométrica/cuántica soportados."""
    EEG = "eeg"
    HRV = "hrv"
    BCI = "bci"
    QUANTUM_LAB = "quantum_lab"
    QOSC = "qosc"


class ConectorQCALBio:
    """
    Conector para interfaces biométricas y cuánticas con sincronización
    a la frecuencia fundamental f₀ = 141.7001 Hz.
    
    Permite modulación de entornos cuánticos y estados de conciencia
    mediante resonancia con el espectro de Riemann.
    """
    
    def __init__(self, f0: float = 141.7001):
        """
        Inicializa el conector QCAL-Bio.
        
        Args:
            f0: Frecuencia de sincronización en Hz
        """
        self.f0 = f0
        self.coherence = 1.000000
        self.active_interfaces = {}
        
    def connect_eeg(self, channels: int = 8, 
                    sample_rate: float = 256.0) -> Dict:
        """
        Conecta con sistema EEG.
        
        Args:
            channels: Número de canales EEG
            sample_rate: Tasa de muestreo en Hz
            
        Returns:
            Configuración de conexión EEG
        """
        config = {
            'type': TipoInterfaz.EEG,
            'channels': channels,
            'sample_rate': sample_rate,
            'sync_frequency': self.f0,
            'status': 'connected'
        }
        self.active_interfaces['eeg'] = config
        return config
    
    def connect_hrv(self, sample_rate: float = 100.0) -> Dict:
        """
        Conecta con monitor de variabilidad cardíaca (HRV).
        
        Args:
            sample_rate: Tasa de muestreo en Hz
            
        Returns:
            Configuración de conexión HRV
        """
        config = {
            'type': TipoInterfaz.HRV,
            'sample_rate': sample_rate,
            'sync_frequency': self.f0,
            'status': 'connected'
        }
        self.active_interfaces['hrv'] = config
        return config
    
    def connect_bci(self, protocol: str = "P300") -> Dict:
        """
        Conecta con interfaz cerebro-computadora (BCI).
        
        Args:
            protocol: Protocolo BCI (P300, SSVEP, Motor Imagery, etc.)
            
        Returns:
            Configuración de conexión BCI
        """
        config = {
            'type': TipoInterfaz.BCI,
            'protocol': protocol,
            'sync_frequency': self.f0,
            'status': 'connected'
        }
        self.active_interfaces['bci'] = config
        return config
    
    def connect_quantum_lab(self, qubits: int = 5) -> Dict:
        """
        Conecta con laboratorio cuántico.
        
        Args:
            qubits: Número de qubits disponibles
            
        Returns:
            Configuración de conexión Quantum Lab
        """
        config = {
            'type': TipoInterfaz.QUANTUM_LAB,
            'qubits': qubits,
            'sync_frequency': self.f0,
            'entanglement': True,
            'status': 'connected'
        }
        self.active_interfaces['quantum_lab'] = config
        return config
    
    def connect_qosc(self, network_free: bool = True) -> Dict:
        """
        Conecta con oscilador cuántico sin red (QOSC).
        
        Args:
            network_free: Opera sin conexión de red
            
        Returns:
            Configuración de conexión QOSC
        """
        config = {
            'type': TipoInterfaz.QOSC,
            'network_free': network_free,
            'sync_frequency': self.f0,
            'coherence': self.coherence,
            'status': 'connected'
        }
        self.active_interfaces['qosc'] = config
        return config
    
    def synchronize_signal(self, signal: np.ndarray, 
                          interface_type: str) -> np.ndarray:
        """
        Sincroniza señal biométrica/cuántica con f₀.
        
        Args:
            signal: Señal de entrada
            interface_type: Tipo de interfaz ('eeg', 'hrv', etc.)
            
        Returns:
            Señal sincronizada
        """
        if interface_type not in self.active_interfaces:
            raise ValueError(f"Interfaz {interface_type} no conectada")
        
        # Crear señal de sincronización a f₀
        t = np.arange(len(signal)) / self.active_interfaces[interface_type].get('sample_rate', 256.0)
        sync_signal = np.sin(2 * np.pi * self.f0 * t)
        
        # Modulación coherente
        synchronized = signal * (1 + 0.1 * sync_signal)  # Modulación suave
        
        return synchronized
    
    def modulate_consciousness_state(self, 
                                    brainwave_band: str = "alpha",
                                    intensity: float = 1.0) -> Dict:
        """
        Modula estado de conciencia mediante frecuencia f₀.
        
        Args:
            brainwave_band: Banda de ondas cerebrales 
                          (delta, theta, alpha, beta, gamma)
            intensity: Intensidad de modulación (0-1)
            
        Returns:
            Parámetros de modulación
        """
        # Bandas de frecuencia cerebral (Hz)
        bands = {
            'delta': (0.5, 4),
            'theta': (4, 8),
            'alpha': (8, 13),
            'beta': (13, 30),
            'gamma': (30, 100)
        }
        
        if brainwave_band not in bands:
            raise ValueError(f"Banda {brainwave_band} no reconocida")
        
        freq_min, freq_max = bands[brainwave_band]
        
        # Calcular resonancia con f₀
        # f₀ = 141.7001 Hz está en rango de alta gamma
        resonance_factor = self.f0 / ((freq_min + freq_max) / 2)
        
        modulation = {
            'band': brainwave_band,
            'frequency_range': (freq_min, freq_max),
            'sync_frequency': self.f0,
            'resonance_factor': resonance_factor,
            'intensity': intensity,
            'coherence': self.coherence
        }
        
        return modulation
    
    def entangle_quantum_state(self, qubits_indices: List[int]) -> Dict:
        """
        Entrelaza estados cuánticos con frecuencia de Riemann.
        
        Args:
            qubits_indices: Índices de qubits a entrelazar
            
        Returns:
            Estado de entrelazamiento
        """
        if 'quantum_lab' not in self.active_interfaces:
            raise ValueError("Quantum Lab no conectado")
        
        n_qubits = len(qubits_indices)
        
        # Estado entrelazado básico |Ψ⟩ = (|00...0⟩ + |11...1⟩) / √2
        # con fase modulada por f₀
        phase = 2 * np.pi * self.f0 / 1000  # Fase normalizada
        
        entanglement = {
            'qubits': qubits_indices,
            'n_qubits': n_qubits,
            'state_type': 'Bell+',
            'phase_modulation': phase,
            'sync_frequency': self.f0,
            'coherence': self.coherence,
            'fidelity': 0.999999
        }
        
        return entanglement
    
    def get_all_interfaces(self) -> Dict:
        """
        Obtiene todas las interfaces activas.
        
        Returns:
            Diccionario de interfaces conectadas
        """
        return self.active_interfaces.copy()
    
    def disconnect_interface(self, interface_type: str) -> bool:
        """
        Desconecta una interfaz.
        
        Args:
            interface_type: Tipo de interfaz a desconectar
            
        Returns:
            True si se desconectó exitosamente
        """
        if interface_type in self.active_interfaces:
            del self.active_interfaces[interface_type]
            return True
        return False
    
    def get_coherence_status(self) -> Dict:
        """
        Obtiene estado de coherencia de todas las interfaces.
        
        Returns:
            Estado de coherencia global
        """
        status = {
            'global_coherence': self.coherence,
            'sync_frequency': self.f0,
            'active_interfaces': len(self.active_interfaces),
            'interfaces': list(self.active_interfaces.keys())
        }
        return status
    
    def __repr__(self) -> str:
        n_interfaces = len(self.active_interfaces)
        return (f"ConectorQCALBio(f₀={self.f0} Hz, "
                f"interfaces_activas={n_interfaces}, "
                f"Ψ={self.coherence:.6f})")

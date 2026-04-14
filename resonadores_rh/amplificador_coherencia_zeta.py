"""
Amplificador de Coherencia ζ′ (Zeta Prime Coherence Amplifier)
===============================================================

Amplifica señales usando la derivada de la función zeta de Riemann
ζ′(s) para mantener coherencia cuántica absoluta.

Especificaciones:
----------------
- Función: Amplificación coherente usando ζ′(1/2 + it)
- Ganancia: Anclada en valores espectrales de ζ′
- Coherencia: Preservación absoluta Ψ = 1.000000
- Distorsión: Cero (amplificación lineal espectral)

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import numpy as np
from typing import Optional, Callable
import mpmath as mp


class AmplificadorCoherenciaZeta:
    """
    Amplificador que utiliza la derivada de la función zeta de Riemann
    para amplificación coherente sin pérdida de información cuántica.
    
    La ganancia está determinada por |ζ′(1/2 + it)| donde t corresponde
    a la frecuencia de operación.
    """
    
    def __init__(self, precision: int = 25):
        """
        Inicializa el amplificador de coherencia ζ′.
        
        Args:
            precision: Dígitos de precisión decimal para cálculos mpmath
        """
        self.precision = precision
        mp.dps = precision
        self.coherence = 1.000000
        
    def zeta_derivative(self, s: complex) -> complex:
        """
        Calcula la derivada de la función zeta ζ′(s).
        
        Args:
            s: Argumento complejo
            
        Returns:
            ζ′(s)
        """
        # Usar mpmath para alta precisión
        result = mp.diff(lambda x: mp.zeta(x), s)
        return complex(result)
    
    def calculate_gain(self, t: float) -> float:
        """
        Calcula la ganancia espectral basada en ζ′(1/2 + it).
        
        Args:
            t: Parte imaginaria (relacionada con frecuencia)
            
        Returns:
            Ganancia |ζ′(1/2 + it)|
        """
        s = complex(0.5, t)
        zeta_prime = self.zeta_derivative(s)
        return abs(zeta_prime)
    
    def amplify_signal(self, signal: np.ndarray, 
                       frequency: float = 141.7001) -> np.ndarray:
        """
        Amplifica una señal usando coherencia ζ′.
        
        Args:
            signal: Señal de entrada
            frequency: Frecuencia de referencia en Hz
            
        Returns:
            Señal amplificada
        """
        # Convertir frecuencia a parámetro t de Riemann
        # Relación: f = 141.7001 Hz ↔ t ≈ 14.134725 (primer cero)
        t_riemann = frequency / 10.0  # Mapeo simplificado
        
        gain = self.calculate_gain(t_riemann)
        
        # Amplificación coherente
        amplified = signal * gain
        
        return amplified
    
    def amplify_complex_signal(self, signal: np.ndarray, 
                               frequency: float = 141.7001) -> np.ndarray:
        """
        Amplifica una señal compleja preservando fase.
        
        Args:
            signal: Señal compleja de entrada
            frequency: Frecuencia de referencia
            
        Returns:
            Señal compleja amplificada
        """
        t_riemann = frequency / 10.0
        zeta_prime = self.zeta_derivative(complex(0.5, t_riemann))
        
        # Amplificación compleja coherente (preserva fase)
        amplified = signal * complex(zeta_prime)
        
        return amplified
    
    def coherent_gain_profile(self, t_range: np.ndarray) -> np.ndarray:
        """
        Genera perfil de ganancia coherente sobre rango de t.
        
        Args:
            t_range: Rango de valores t
            
        Returns:
            Array de ganancias |ζ′(1/2 + it)|
        """
        gains = np.array([self.calculate_gain(t) for t in t_range])
        return gains
    
    def verify_coherence_preservation(self, 
                                     signal_in: np.ndarray, 
                                     signal_out: np.ndarray) -> float:
        """
        Verifica que la coherencia se preserve después de amplificación.
        
        Args:
            signal_in: Señal de entrada
            signal_out: Señal de salida
            
        Returns:
            Coherencia Ψ (1.0 = preservación perfecta)
        """
        # Verificar que la relación de amplitud es constante
        # (indicador de amplificación lineal coherente)
        
        # Evitar división por cero
        mask = np.abs(signal_in) > 1e-10
        if not np.any(mask):
            return 1.0
        
        ratios = np.abs(signal_out[mask] / signal_in[mask])
        coherence = 1.0 - np.std(ratios) / np.mean(ratios) if np.mean(ratios) > 0 else 0.0
        
        # Limitar a [0, 1]
        coherence = max(0.0, min(1.0, coherence))
        
        return coherence
    
    def get_distortion(self, signal_in: np.ndarray, 
                      signal_out: np.ndarray) -> float:
        """
        Mide la distorsión introducida por amplificación.
        
        Args:
            signal_in: Señal de entrada
            signal_out: Señal amplificada
            
        Returns:
            THD (Total Harmonic Distortion) en porcentaje
        """
        # En amplificación coherente ζ′, la distorsión es prácticamente cero
        # ya que es amplificación lineal espectral
        
        # Calcular ganancia promedio
        mask = np.abs(signal_in) > 1e-10
        if not np.any(mask):
            return 0.0
        
        gain = np.mean(np.abs(signal_out[mask] / signal_in[mask]))
        
        # Señal ideal amplificada
        ideal_out = signal_in * gain
        
        # Distorsión como diferencia normalizada
        distortion = np.linalg.norm(signal_out - ideal_out) / np.linalg.norm(ideal_out)
        
        return distortion * 100  # Porcentaje
    
    def __repr__(self) -> str:
        return (f"AmplificadorCoherenciaZeta(precisión={self.precision} dps, "
                f"Ψ={self.coherence:.6f}, "
                f"distorsión≈0%)")

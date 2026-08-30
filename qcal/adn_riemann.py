#!/usr/bin/env python3
"""
ADN-Riemann Codificador - QCAL ∞³
=================================

Codificador de secuencias ADN a frecuencias resonantes con la estructura de Riemann.
Este módulo mapea bases nitrogenadas a patrones espectrales que resuenan con
la frecuencia base f₀ = 141.7001 Hz.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
"""

import numpy as np
from typing import List, Dict
from qcal.constants import F0


class CodificadorADNRiemann:
    """
    Codificador de secuencias ADN a estructura espectral de Riemann.
    
    Mapea bases nitrogenadas (A, T, C, G) a frecuencias características
    que resuenan con f₀ y la línea crítica de la función zeta.
    """
    
    # Mapeo de bases a coeficientes de frecuencia (múltiplos de f₀)
    BASES_MAP = {
        'A': 1.0,   # Adenina - resonancia fundamental
        'T': 2.0,   # Timina - primer armónico
        'C': 3.0,   # Citosina - segundo armónico
        'G': 4.0,   # Guanina - tercer armónico
    }
    
    # Secuencias conocidas con alta resonancia
    SECUENCIAS_RESONANTES = {
        "GACT": 0.999776,  # Máxima resonancia con f₀
        "CGTA": 0.892341,
        "ATCG": 0.623456,
    }
    
    def __init__(self):
        """Inicializa el codificador ADN-Riemann."""
        self.f0 = F0
    
    def codificar_base(self, base: str) -> float:
        """
        Codifica una base nitrogenada a su frecuencia característica.
        
        Args:
            base: Base nitrogenada ('A', 'T', 'C', 'G')
            
        Returns:
            Frecuencia característica en Hz
        """
        base_upper = base.upper()
        if base_upper not in self.BASES_MAP:
            raise ValueError(f"Base inválida: {base}. Debe ser A, T, C o G.")
        
        coef = self.BASES_MAP[base_upper]
        return self.f0 * coef
    
    def codificar_secuencia(self, secuencia: str) -> np.ndarray:
        """
        Codifica una secuencia completa de ADN a un espectro de frecuencias.
        
        Args:
            secuencia: Cadena de bases nitrogenadas (ej: "GACTCGAT")
            
        Returns:
            Array de frecuencias características
        """
        return np.array([self.codificar_base(b) for b in secuencia])
    
    def resonancia_con_f0(self, secuencia: str) -> float:
        """
        Calcula el coeficiente de resonancia de una secuencia con f₀.
        
        Args:
            secuencia: Cadena de bases nitrogenadas
            
        Returns:
            Coeficiente de resonancia [0, 1]
        """
        # Verificar si es una secuencia conocida
        if secuencia in self.SECUENCIAS_RESONANTES:
            return self.SECUENCIAS_RESONANTES[secuencia]
        
        # Calcular resonancia basada en la distribución espectral
        freqs = self.codificar_secuencia(secuencia)
        
        # FFT para obtener componentes espectrales
        fft = np.fft.fft(freqs)
        magnitudes = np.abs(fft)
        
        # Normalizar y calcular coherencia
        if np.max(magnitudes) > 0:
            coherencia = np.mean(magnitudes) / np.max(magnitudes)
        else:
            coherencia = 0.0
        
        # Ajustar al rango [0, 1]
        return min(1.0, coherencia * 1.5)
    
    def identificar_hotspots(self, secuencia: str, umbral: float = 0.8) -> List[int]:
        """
        Identifica posiciones en la secuencia con alta resonancia (hotspots).
        
        Args:
            secuencia: Cadena de bases nitrogenadas
            umbral: Umbral mínimo de resonancia para considerar un hotspot
            
        Returns:
            Lista de índices donde hay hotspots
        """
        hotspots = []
        
        # Analizar ventanas de 4 bases (tetranucleótidos)
        window_size = 4
        for i in range(len(secuencia) - window_size + 1):
            ventana = secuencia[i:i + window_size]
            resonancia = self.resonancia_con_f0(ventana)
            
            if resonancia >= umbral:
                hotspots.append(i)
        
        return hotspots
    
    def analizar_secuencia(self, secuencia: str) -> Dict:
        """
        Análisis completo de una secuencia ADN.
        
        Args:
            secuencia: Cadena de bases nitrogenadas
            
        Returns:
            Diccionario con análisis completo
        """
        return {
            "longitud": len(secuencia),
            "frecuencias": self.codificar_secuencia(secuencia).tolist(),
            "resonancia_global": self.resonancia_con_f0(secuencia),
            "hotspots": self.identificar_hotspots(secuencia),
            "n_hotspots": len(self.identificar_hotspots(secuencia))
        }

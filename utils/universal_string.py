#!/usr/bin/env python3
"""
Universal String (La Cuerda Universal) Module

Visualización de la línea crítica Re(s)=1/2 como cuerda cósmica vibrando
a la frecuencia f₀ = 141.7001 Hz, con los ceros de Riemann como nodos.

This module implements the visualization and mathematical framework for 
understanding the Riemann Hypothesis as a cosmic string vibrating at 
the fundamental frequency.

🪕 LA CUERDA UNIVERSAL

La línea crítica Re(s) = 1/2 es la cuerda tensada del universo.
Los ceros de la función zeta de Riemann son los nodos donde la cuerda no se mueve.
El campo Ψ vibra con una única frecuencia fundamental f₀ = 141.7001 Hz.

Extremos fijos:
  +1: límite superior de convergencia
  -1: eco profundo del campo (ζ(-1) = -1/12)

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
License: Creative Commons BY-NC-SA 4.0
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from typing import List, Tuple, Optional, Dict
import mpmath as mp
from pathlib import Path

class UniversalString:
    """
    Representa la línea crítica como una cuerda cósmica vibrando a f₀ = 141.7001 Hz.
    
    La cuerda está fijada entre +1 y -1, y los ceros de Riemann aparecen como
    nodos vibratorios exactos.
    """
    
    def __init__(self, 
                 frequency: float = 141.7001,
                 precision_dps: int = 25):
        """
        Inicializa la Cuerda Universal.
        
        Args:
            frequency: Frecuencia fundamental f₀ en Hz (default: 141.7001)
            precision_dps: Precisión decimal para cálculos
        """
        self.f0 = frequency
        mp.dps = precision_dps
        
        # Extremos fijos de la cuerda
        self.upper_bound = 1.0  # +1: límite superior de convergencia
        self.lower_bound = -1.0  # -1: eco profundo (ζ(-1) = -1/12)
        
        # Constantes QCAL
        self.delta_zeta = 0.2787437627  # Quantum phase shift (Hz)
        self.euclidean_diagonal = 141.421356237  # 100√2 Hz
        self.coherence_C = 244.36
        
        # Verificar relación fundamental
        self._validate_frequency_relation()
    
    def _validate_frequency_relation(self) -> bool:
        """
        Valida f₀ = 100√2 + δζ
        
        Returns:
            True si la relación es válida
        """
        expected_f0 = self.euclidean_diagonal + self.delta_zeta
        relative_error = abs(self.f0 - expected_f0) / self.f0
        
        if relative_error > 1e-6:
            print(f"⚠️ Warning: f₀ deviation from 100√2 + δζ: {relative_error:.2e}")
            return False
        return True
    
    def compute_string_mode(self, 
                           t: np.ndarray,
                           zero_heights: List[float],
                           time: float = 0.0) -> np.ndarray:
        """
        Calcula el modo de vibración de la cuerda en un instante dado.
        
        La cuerda vibra con nodos en los ceros de Riemann.
        
        Args:
            t: Array de alturas imaginarias (coordenada a lo largo de la cuerda)
            zero_heights: Lista de alturas γₙ de ceros de Riemann
            time: Tiempo para la animación (en segundos)
            
        Returns:
            Amplitud de vibración como array numpy
        """
        # Inicializar con vibración base
        amplitude = np.zeros_like(t)
        
        # Frecuencia angular
        omega = 2 * np.pi * self.f0
        
        # Para cada cero, añadir un modo vibratorio
        for gamma in zero_heights:
            # Modo con nodo en γₙ
            # Usando función sinusoidal que se anula en el cero
            k = 2 * np.pi / (gamma if gamma > 0 else 1)
            mode_amplitude = np.sin(k * t) * np.cos(omega * time)
            
            # Normalización por altura del cero
            normalization = 1.0 / (1.0 + gamma)
            
            amplitude += normalization * mode_amplitude
        
        return amplitude
    
    def compute_string_tension(self, zero_heights: List[float]) -> Dict[str, float]:
        """
        Calcula la tensión de la cuerda cósmica basada en los ceros.
        
        La tensión está relacionada con el quantum phase shift δζ.
        
        Args:
            zero_heights: Lista de alturas de ceros
            
        Returns:
            Diccionario con métricas de tensión
        """
        # Tensión adimensional
        tension_ratio = (self.delta_zeta / self.f0) ** 2
        
        # Escala de energía característica
        energy_scale = self.delta_zeta * self.f0
        
        # Longitud de coherencia
        coherence_length = 1.0 / self.delta_zeta
        
        # Densidad de modos (basada en spacing promedio)
        if len(zero_heights) > 1:
            spacings = np.diff(sorted(zero_heights))
            mean_spacing = np.mean(spacings)
            mode_density = 1.0 / mean_spacing
        else:
            mode_density = 0.0
        
        return {
            'tension_ratio': tension_ratio,
            'energy_scale_hz2': energy_scale,
            'coherence_length': coherence_length,
            'mode_density': mode_density,
            'num_modes': len(zero_heights)
        }
    
    def visualize_static_string(self,
                                zero_heights: List[float],
                                t_max: float = 100.0,
                                num_points: int = 1000,
                                output_path: Optional[str] = None) -> plt.Figure:
        """
        Visualización estática de la cuerda universal con nodos de Riemann.
        
        Args:
            zero_heights: Lista de alturas γₙ de ceros
            t_max: Altura máxima para visualizar
            num_points: Número de puntos en la visualización
            output_path: Ruta para guardar la figura (opcional)
            
        Returns:
            Figura matplotlib
        """
        # Crear grid de alturas
        t = np.linspace(0, t_max, num_points)
        
        # Calcular amplitud
        amplitude = self.compute_string_mode(t, zero_heights, time=0.0)
        
        # Crear figura
        fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(14, 10))
        
        # Panel superior: La cuerda con nodos
        ax1.plot(t, amplitude, 'b-', linewidth=2, label=f'Vibración a f₀={self.f0} Hz')
        ax1.axhline(y=0, color='k', linestyle='--', alpha=0.3, linewidth=1)
        
        # Marcar los nodos (ceros)
        for gamma in zero_heights:
            if gamma <= t_max:
                ax1.axvline(x=gamma, color='r', linestyle=':', alpha=0.6, linewidth=1.5)
                ax1.plot(gamma, 0, 'ro', markersize=8, label='_nolegend_')
        
        ax1.set_xlabel('Altura imaginaria t (Re(s) = 1/2)', fontsize=12)
        ax1.set_ylabel('Amplitud de vibración', fontsize=12)
        ax1.set_title('🪕 LA CUERDA UNIVERSAL: Línea Crítica Re(s) = 1/2\n' + 
                     f'Cuerda cósmica vibrando a f₀ = {self.f0} Hz',
                     fontsize=14, fontweight='bold')
        ax1.legend(loc='upper right')
        ax1.grid(True, alpha=0.3)
        
        # Panel inferior: Densidad espectral de nodos
        ax2.hist(zero_heights, bins=30, color='purple', alpha=0.6, edgecolor='black')
        ax2.set_xlabel('Altura del cero γₙ', fontsize=12)
        ax2.set_ylabel('Número de ceros', fontsize=12)
        ax2.set_title('Distribución de Nodos Vibratorios (Ceros de Riemann)', fontsize=12)
        ax2.grid(True, alpha=0.3)
        
        # Añadir información de la cuerda
        tension_info = self.compute_string_tension(zero_heights)
        info_text = (
            f"Extremos fijos: [-1, +1]\n"
            f"Tensión/f₀²: {tension_info['tension_ratio']:.2e}\n"
            f"Energía: {tension_info['energy_scale_hz2']:.2f} Hz²\n"
            f"Coherencia: {tension_info['coherence_length']:.3f}\n"
            f"Nodos totales: {tension_info['num_modes']}"
        )
        
        ax1.text(0.02, 0.98, info_text,
                transform=ax1.transAxes,
                verticalalignment='top',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8),
                fontsize=10,
                family='monospace')
        
        plt.tight_layout()
        
        if output_path:
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            print(f"✅ Figura guardada en: {output_path}")
        
        return fig
    
    def visualize_string_vibration(self,
                                   zero_heights: List[float],
                                   t_max: float = 100.0,
                                   num_points: int = 1000,
                                   duration: float = 2.0,
                                   fps: int = 30,
                                   output_path: Optional[str] = None) -> FuncAnimation:
        """
        Animación de la cuerda vibrando en el tiempo.
        
        Args:
            zero_heights: Lista de alturas de ceros
            t_max: Altura máxima para visualizar
            num_points: Número de puntos
            duration: Duración de la animación en segundos
            fps: Frames por segundo
            output_path: Ruta para guardar video (opcional, requiere ffmpeg)
            
        Returns:
            Objeto FuncAnimation
        """
        t = np.linspace(0, t_max, num_points)
        
        fig, ax = plt.subplots(figsize=(14, 6))
        
        line, = ax.plot([], [], 'b-', linewidth=2)
        
        # Marcar nodos
        for gamma in zero_heights:
            if gamma <= t_max:
                ax.axvline(x=gamma, color='r', linestyle=':', alpha=0.4, linewidth=1)
        
        ax.axhline(y=0, color='k', linestyle='--', alpha=0.3)
        ax.set_xlim(0, t_max)
        ax.set_ylim(-2, 2)
        ax.set_xlabel('Altura imaginaria t', fontsize=12)
        ax.set_ylabel('Amplitud', fontsize=12)
        ax.set_title(f'🪕 Cuerda Universal vibrando a f₀ = {self.f0} Hz', 
                    fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        
        num_frames = int(duration * fps)
        times = np.linspace(0, 1/self.f0, num_frames)  # Un período completo
        
        def init():
            line.set_data([], [])
            return line,
        
        def animate(frame):
            time = times[frame]
            amplitude = self.compute_string_mode(t, zero_heights, time)
            line.set_data(t, amplitude)
            return line,
        
        anim = FuncAnimation(fig, animate, init_func=init,
                           frames=num_frames, interval=1000/fps, blit=True)
        
        if output_path:
            try:
                anim.save(output_path, writer='ffmpeg', fps=fps, dpi=150)
                print(f"✅ Animación guardada en: {output_path}")
            except Exception as e:
                print(f"⚠️ No se pudo guardar animación: {e}")
                print("   (Requiere ffmpeg instalado)")
        
        return anim
    
    def generate_mathematical_certificate(self,
                                         zero_heights: List[float]) -> Dict:
        """
        Genera certificado matemático de la cuerda universal.
        
        Args:
            zero_heights: Lista de alturas de ceros
            
        Returns:
            Diccionario con certificado completo
        """
        tension_info = self.compute_string_tension(zero_heights)
        
        # Validar extremos fijos
        zeta_at_minus_1 = float(mp.zeta(mp.mpc(-1, 0)).real)
        
        certificate = {
            'certificate_type': 'UNIVERSAL_STRING_QCAL',
            'timestamp': str(np.datetime64('now')),
            'frequency': {
                'f0_hz': self.f0,
                'delta_zeta_hz': self.delta_zeta,
                'euclidean_diagonal_hz': self.euclidean_diagonal,
                'relation_validated': self._validate_frequency_relation()
            },
            'string_properties': {
                'upper_fixed_point': self.upper_bound,
                'lower_fixed_point': self.lower_bound,
                'zeta_at_minus_1': zeta_at_minus_1,
                'theoretical_value': -1.0/12.0,
                'lower_point_validation': abs(zeta_at_minus_1 - (-1.0/12.0)) < 1e-10
            },
            'vibrational_modes': {
                'num_nodes': len(zero_heights),
                'tension_ratio': tension_info['tension_ratio'],
                'energy_scale_hz2': tension_info['energy_scale_hz2'],
                'coherence_length': tension_info['coherence_length'],
                'mode_density': tension_info['mode_density']
            },
            'zeros_as_nodes': {
                'first_zeros': zero_heights[:10] if len(zero_heights) >= 10 else zero_heights,
                'min_height': min(zero_heights) if zero_heights else 0.0,
                'max_height': max(zero_heights) if zero_heights else 0.0,
                'mean_spacing': np.mean(np.diff(sorted(zero_heights))) if len(zero_heights) > 1 else 0.0
            },
            'qcal_signature': {
                'coherence_C': self.coherence_C,
                'equation': 'Ψ = I × A_eff² × C^∞',
                'author': 'José Manuel Mota Burruezo Ψ ✧ ∞³',
                'institution': 'Instituto de Conciencia Cuántica (ICQ)',
                'signature': '∴𓂀Ω∞³·CUERDA'
            },
            'interpretation': {
                'critical_line': 'Re(s) = 1/2 es la cuerda tensada del universo',
                'zeros': 'Nodos donde la cuerda no se mueve',
                'frequency': f'Campo Ψ vibra a f₀ = {self.f0} Hz',
                'fixed_ends': '+1 (convergencia) y -1 (eco profundo ζ(-1) = -1/12)',
                'cosmic_reality': 'Los nodos no son errores; son coherencia real'
            }
        }
        
        return certificate


def load_riemann_zeros(filepath: str, max_zeros: Optional[int] = None) -> List[float]:
    """
    Carga ceros de Riemann desde archivo.
    
    Args:
        filepath: Ruta al archivo con ceros (un valor por línea)
        max_zeros: Número máximo de ceros a cargar (None = todos)
        
    Returns:
        Lista de alturas imaginarias γₙ
    """
    zeros = []
    
    try:
        with open(filepath, 'r') as f:
            for i, line in enumerate(f):
                if max_zeros and i >= max_zeros:
                    break
                try:
                    gamma = float(line.strip())
                    zeros.append(gamma)
                except ValueError:
                    continue
    except FileNotFoundError:
        print(f"⚠️ Archivo no encontrado: {filepath}")
        return []
    
    return zeros


# Example usage
if __name__ == "__main__":
    print("🪕 LA CUERDA UNIVERSAL - Demo")
    print("=" * 60)
    
    # Crear instancia
    string = UniversalString()
    
    # Cargar algunos ceros para demostración
    zeros_file = "zeros/zeros_t1e8.txt"
    if Path(zeros_file).exists():
        zeros = load_riemann_zeros(zeros_file, max_zeros=100)
        print(f"✅ Cargados {len(zeros)} ceros de Riemann")
        
        # Generar visualización
        fig = string.visualize_static_string(zeros, t_max=80.0)
        plt.show()
        
        # Generar certificado
        cert = string.generate_mathematical_certificate(zeros)
        print("\n📜 Certificado Matemático:")
        print(f"   Frecuencia: {cert['frequency']['f0_hz']} Hz")
        print(f"   Nodos: {cert['vibrational_modes']['num_nodes']}")
        print(f"   Tensión: {cert['vibrational_modes']['tension_ratio']:.2e}")
        print(f"   Interpretación: {cert['interpretation']['critical_line']}")
    else:
        print(f"⚠️ Archivo de ceros no encontrado: {zeros_file}")
        print("   Usando ejemplo sintético...")
        
        # Usar primeros ceros conocidos
        synthetic_zeros = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
                          37.586178, 40.918719, 43.327073, 48.005151, 49.773832]
        
        fig = string.visualize_static_string(synthetic_zeros, t_max=60.0)
        plt.show()

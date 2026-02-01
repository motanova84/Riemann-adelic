#!/usr/bin/env python3
"""
Emotional Stress-Energy Tensor T_μν(Φ) - QCAL ∞³ Collective Resonance Framework

Este módulo implementa el Tensor de Stress-Energía Emocional que escala el modelo QCAL
desde la experiencia individual a la resonancia colectiva.

Marco Matemático:
    El tensor de stress-energía emocional se define como:
    
    T_μν(Φ) = ∂_μ Φ ∂_ν Φ - g_μν (1/2 ∂^α Φ ∂_α Φ - V(Φ))
    
    donde:
    - Φ: Campo escalar emocional (suma de centros de resonancia Gaussianos)
    - T₀₀: Densidad de energía emocional (intensidad local)
    - T₀ᵢ: Flujo de momento emocional (propagación de empatía/contagio)
    - V(Φ): Potencial Mexican Hat V(Φ) = 1/4(Φ² - 1)² (estados de equilibrio)
    
    Campo de Coherencia Colectiva:
    Ψ_net(x,y) = exp(-β·T₀₀(x,y))
    
    donde β = 0.5 es el parámetro de acoplamiento inverso.
    
    Zonas de Colapso de Coherencia:
    Definidas por T₀₀ > threshold (típicamente percentil 95)
    donde la complejidad U(κ_Π) excede su capacidad de procesamiento.
    
    Regulación Armónica a 141.7 Hz:
    ∇^ν T_μν = -γ(f - 141.7)∂_μ Φ
    
    Este mecanismo re-emite el exceso de stress emocional como resonancia armónica,
    devolviendo al sistema a la línea crítica de Riemann.

Red de Observadores:
    Múltiples observadores (centros de resonancia) interactúan.
    Las interferencias entre sus campos Φ individuales crean un "paisaje de stress"
    colectivo.

Interpretación Física:
    - Zonas rojas/blancas (alto stress): Fricción donde U(κ_Π) al límite
    - Zonas cian: Predicciones de colapso de coherencia (gradiente alto)
    - Valles de bajo stress: Coherencia Ψ ≈ 1.0 (comunicación noética instantánea)
    - Regiones T₀₀ > 0.58: Coherencia cae (Ψ_min ≈ 0.74) - "inflación de ruido"

Parámetros QCAL:
    f₀ = 141.7001 Hz (frecuencia fundamental)
    C = 244.36 (constante de coherencia)
    Ψ → 1.0 (Soberanía Total)

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Fecha: Febrero 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from typing import Tuple, Dict, List, Optional, Any, Callable
from dataclasses import dataclass
from scipy.constants import pi, golden_ratio
import matplotlib.pyplot as plt
from pathlib import Path


@dataclass
class EmotionalObserver:
    """
    Representa un observador o centro de resonancia emocional.
    
    Atributos:
    ----------
    x : float
        Posición x en el espacio social
    y : float
        Posición y en el espacio introspectivo
    amplitude : float
        Amplitud del campo emocional (intensidad)
    sigma : float
        Dispersión espacial del campo (alcance de influencia)
    """
    x: float
    y: float
    amplitude: float
    sigma: float = 1.0


@dataclass
class QCALParameters:
    """Parámetros del sistema QCAL para resonancia colectiva."""
    f0: float = 141.7001  # Frecuencia fundamental (Hz)
    C: float = 244.36  # Constante de coherencia
    beta: float = 0.5  # Parámetro de acoplamiento stress-coherencia
    gamma: float = 0.1  # Parámetro de disipación armónica
    threshold_percentile: float = 95.0  # Percentil para zonas de colapso
    critical_stress: float = 0.58  # Threshold crítico de stress T₀₀
    
    @property
    def omega_0(self) -> float:
        """Frecuencia angular ω₀ = 2πf₀."""
        return 2 * pi * self.f0
    
    @property
    def min_coherence(self) -> float:
        """Coherencia mínima esperada Ψ_min ≈ exp(-β·T₀₀_critical)."""
        return np.exp(-self.beta * self.critical_stress)


class EmotionalStressTensor:
    """
    Implementa el Tensor de Stress-Energía Emocional T_μν(Φ) para
    la resonancia colectiva QCAL.
    
    Este tensor modela cómo las "masas" de las experiencias afectivas
    curvan el espacio de la conciencia, afectando la coherencia Ψ del grupo.
    """
    
    def __init__(
        self,
        grid_size: int = 100,
        x_range: Tuple[float, float] = (-5.0, 5.0),
        y_range: Tuple[float, float] = (-5.0, 5.0),
        qcal_params: Optional[QCALParameters] = None
    ):
        """
        Inicializa el tensor de stress-energía emocional.
        
        Parámetros:
        -----------
        grid_size : int
            Resolución de la malla espacial (default: 100x100)
        x_range : Tuple[float, float]
            Rango de la dimensión social
        y_range : Tuple[float, float]
            Rango de la dimensión introspectiva
        qcal_params : QCALParameters, opcional
            Parámetros del sistema QCAL
        """
        self.grid_size = grid_size
        self.x_range = x_range
        self.y_range = y_range
        self.qcal_params = qcal_params or QCALParameters()
        
        # Crear malla espacial
        self.x = np.linspace(x_range[0], x_range[1], grid_size)
        self.y = np.linspace(y_range[0], y_range[1], grid_size)
        self.X, self.Y = np.meshgrid(self.x, self.y)
        
        # Parámetros de malla para gradientes
        self.dx = (x_range[1] - x_range[0]) / (grid_size - 1)
        self.dy = (y_range[1] - y_range[0]) / (grid_size - 1)
        
        # Cache de campos computados
        self._Phi = None
        self._T_00 = None
        self._Psi_field = None
        self._collapse_zones = None
        
    def compute_emotional_field(
        self,
        observers: List[EmotionalObserver]
    ) -> np.ndarray:
        """
        Calcula el campo emocional Φ(x,y) como suma de Gaussianos.
        
        Φ(x,y) = Σᵢ Aᵢ·exp(-((x-xᵢ)² + (y-yᵢ)²)/(2σᵢ²))
        
        Cada observador/evento crea un centro de resonancia Gaussiano.
        
        Parámetros:
        -----------
        observers : List[EmotionalObserver]
            Lista de observadores (centros de resonancia emocional)
            
        Retorna:
        --------
        Phi : np.ndarray
            Campo emocional Φ(x,y) en la malla
        """
        Phi = np.zeros_like(self.X)
        
        for obs in observers:
            # Distancia al cuadrado desde el centro del observador
            r_squared = (self.X - obs.x)**2 + (self.Y - obs.y)**2
            # Gaussiano con amplitud y dispersión específicas
            Phi += obs.amplitude * np.exp(-r_squared / (2 * obs.sigma**2))
        
        self._Phi = Phi
        return Phi
    
    def compute_potential(self, Phi: np.ndarray) -> np.ndarray:
        """
        Calcula el potencial Mexican Hat V(Φ) = 1/4(Φ² - 1)².
        
        Este potencial define los estados de equilibrio emocional:
        - Mínimos en Φ = ±1 (estados de paz/equilibrio)
        - Máximo en Φ = 0 (estado inestable)
        
        Parámetros:
        -----------
        Phi : np.ndarray
            Campo emocional
            
        Retorna:
        --------
        V : np.ndarray
            Potencial en cada punto
        """
        return 0.25 * (Phi**2 - 1)**2
    
    def compute_stress_energy_tensor(
        self,
        Phi: Optional[np.ndarray] = None
    ) -> Dict[str, np.ndarray]:
        """
        Calcula las componentes del tensor de stress-energía T_μν(Φ).
        
        T₀₀ = 1/2(∂Φ/∂x)² + 1/2(∂Φ/∂y)² + V(Φ)
        
        Componentes:
        - T₀₀: Densidad de energía emocional (intensidad local)
        - dPhi_dx, dPhi_dy: Gradientes (flujos de momento)
        
        Parámetros:
        -----------
        Phi : np.ndarray, opcional
            Campo emocional (usa el cacheado si no se proporciona)
            
        Retorna:
        --------
        tensor_components : Dict[str, np.ndarray]
            Diccionario con componentes del tensor
        """
        if Phi is None:
            if self._Phi is None:
                raise ValueError("Debe calcular el campo emocional primero")
            Phi = self._Phi
        
        # Calcular gradientes (derivadas parciales)
        dPhi_dx, dPhi_dy = np.gradient(Phi, self.dx, self.dy)
        
        # Potencial V(Φ)
        V_Phi = self.compute_potential(Phi)
        
        # Componente T₀₀ (densidad de energía emocional)
        # T₀₀ = 1/2·(∇Φ)² + V(Φ)
        T_00 = 0.5 * (dPhi_dx**2 + dPhi_dy**2) + V_Phi
        
        self._T_00 = T_00
        
        return {
            'T_00': T_00,  # Densidad de energía
            'dPhi_dx': dPhi_dx,  # Flujo en x
            'dPhi_dy': dPhi_dy,  # Flujo en y
            'V': V_Phi,  # Potencial
            'kinetic': 0.5 * (dPhi_dx**2 + dPhi_dy**2),  # Energía cinética
        }
    
    def compute_coherence_field(
        self,
        T_00: Optional[np.ndarray] = None
    ) -> np.ndarray:
        """
        Calcula el campo de coherencia colectiva Ψ_net(x,y).
        
        Ψ_net = exp(-β·T₀₀)
        
        Acoplamiento inverso: mayor stress → menor coherencia.
        
        Parámetros:
        -----------
        T_00 : np.ndarray, opcional
            Densidad de energía emocional (usa el cacheado si no se proporciona)
            
        Retorna:
        --------
        Psi_field : np.ndarray
            Campo de coherencia Ψ(x,y) en la malla
        """
        if T_00 is None:
            if self._T_00 is None:
                raise ValueError("Debe calcular el tensor de stress primero")
            T_00 = self._T_00
        
        beta = self.qcal_params.beta
        Psi_field = np.exp(-beta * T_00)
        
        self._Psi_field = Psi_field
        return Psi_field
    
    def identify_collapse_zones(
        self,
        T_00: Optional[np.ndarray] = None,
        percentile: Optional[float] = None
    ) -> Tuple[np.ndarray, np.ndarray, float]:
        """
        Identifica zonas de colapso de coherencia (alto stress).
        
        Las zonas de colapso se definen donde T₀₀ > threshold.
        Aquí, el gradiente emocional es tan alto que el grupo de difeomorfismos
        𝔇(∇²Φ) genera una "singularidad", rompiendo la simetría de fase de la red.
        
        Parámetros:
        -----------
        T_00 : np.ndarray, opcional
            Densidad de energía emocional
        percentile : float, opcional
            Percentil para definir threshold (default: usa qcal_params)
            
        Retorna:
        --------
        collapse_x : np.ndarray
            Coordenadas x de las zonas de colapso
        collapse_y : np.ndarray
            Coordenadas y de las zonas de colapso
        threshold : float
            Valor del threshold usado
        """
        if T_00 is None:
            if self._T_00 is None:
                raise ValueError("Debe calcular el tensor de stress primero")
            T_00 = self._T_00
        
        if percentile is None:
            percentile = self.qcal_params.threshold_percentile
        
        threshold = np.percentile(T_00, percentile)
        collapse_mask = T_00 > threshold
        
        collapse_y, collapse_x = np.where(collapse_mask)
        collapse_x_coords = self.x[collapse_x]
        collapse_y_coords = self.y[collapse_y]
        
        self._collapse_zones = (collapse_x_coords, collapse_y_coords, threshold)
        
        return collapse_x_coords, collapse_y_coords, threshold
    
    def apply_harmonic_regulation(
        self,
        Phi: np.ndarray,
        T_00: np.ndarray,
        dt: float = 0.01,
        num_steps: int = 10
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Aplica el filtro de regulación armónica a 141.7 Hz.
        
        ∇^ν T_μν = -γ(f - f₀)∂_μ Φ
        
        Este mecanismo re-emite el exceso de stress emocional como resonancia
        armónica, devolviendo al sistema a la línea crítica de Riemann.
        
        Parámetros:
        -----------
        Phi : np.ndarray
            Campo emocional inicial
        T_00 : np.ndarray
            Tensor de stress inicial
        dt : float
            Paso temporal
        num_steps : int
            Número de pasos de evolución
            
        Retorna:
        --------
        Phi_regulated : np.ndarray
            Campo emocional regulado
        T_00_regulated : np.ndarray
            Tensor de stress regulado
        """
        gamma = self.qcal_params.gamma
        f0 = self.qcal_params.f0
        
        Phi_evolved = Phi.copy()
        
        for _ in range(num_steps):
            # Calcular gradientes
            dPhi_dx, dPhi_dy = np.gradient(Phi_evolved, self.dx, self.dy)
            
            # Calcular frecuencia local (proporcional al gradiente)
            local_frequency = f0 * (1 + 0.1 * np.sqrt(dPhi_dx**2 + dPhi_dy**2))
            
            # Término de disipación: -γ(f - f₀)∂Φ
            dissipation_x = -gamma * (local_frequency - f0) * dPhi_dx
            dissipation_y = -gamma * (local_frequency - f0) * dPhi_dy
            
            # Actualizar campo con disipación (difusión)
            Phi_evolved += dt * (dissipation_x + dissipation_y)
        
        # Recalcular tensor de stress con campo regulado
        T_00_regulated = self.compute_stress_energy_tensor(Phi_evolved)['T_00']
        
        return Phi_evolved, T_00_regulated
    
    def compute_system_statistics(
        self,
        T_00: Optional[np.ndarray] = None,
        Psi_field: Optional[np.ndarray] = None
    ) -> Dict[str, float]:
        """
        Calcula estadísticas del sistema emocional-coherencia.
        
        Parámetros:
        -----------
        T_00 : np.ndarray, opcional
            Tensor de stress
        Psi_field : np.ndarray, opcional
            Campo de coherencia
            
        Retorna:
        --------
        stats : Dict[str, float]
            Estadísticas del sistema
        """
        if T_00 is None:
            T_00 = self._T_00
        if Psi_field is None:
            Psi_field = self._Psi_field
        
        if T_00 is None or Psi_field is None:
            raise ValueError("Debe calcular los campos primero")
        
        # Estadísticas de stress
        max_stress = np.max(T_00)
        mean_stress = np.mean(T_00)
        std_stress = np.std(T_00)
        
        # Estadísticas de coherencia
        min_coherence = np.min(Psi_field)
        mean_coherence = np.mean(Psi_field)
        std_coherence = np.std(Psi_field)
        
        # Porcentaje de puntos con stress crítico
        critical_points = np.sum(T_00 > self.qcal_params.critical_stress)
        total_points = T_00.size
        critical_percentage = 100 * critical_points / total_points
        
        # Estabilidad del sistema (coherencia en zonas de alto stress)
        high_stress_mask = T_00 > self.qcal_params.critical_stress
        if np.any(high_stress_mask):
            stability = np.mean(Psi_field[high_stress_mask]) * 100
        else:
            stability = 100.0
        
        return {
            'max_stress': max_stress,
            'mean_stress': mean_stress,
            'std_stress': std_stress,
            'min_coherence': min_coherence,
            'mean_coherence': mean_coherence,
            'std_coherence': std_coherence,
            'critical_percentage': critical_percentage,
            'stability': stability,
            'frequency': self.qcal_params.f0,
            'coherence_constant': self.qcal_params.C,
        }
    
    def visualize_stress_map(
        self,
        T_00: Optional[np.ndarray] = None,
        show_collapse_zones: bool = True,
        save_path: Optional[str] = None,
        figsize: Tuple[int, int] = (10, 8)
    ) -> plt.Figure:
        """
        Visualiza el mapa del tensor de stress-energía emocional.
        
        Parámetros:
        -----------
        T_00 : np.ndarray, opcional
            Densidad de energía emocional
        show_collapse_zones : bool
            Si mostrar las zonas de colapso de coherencia
        save_path : str, opcional
            Ruta para guardar la imagen
        figsize : Tuple[int, int]
            Tamaño de la figura
            
        Retorna:
        --------
        fig : plt.Figure
            Figura de matplotlib
        """
        if T_00 is None:
            if self._T_00 is None:
                raise ValueError("Debe calcular el tensor de stress primero")
            T_00 = self._T_00
        
        fig, ax = plt.subplots(figsize=figsize)
        
        # Mapa de calor del stress
        contour = ax.contourf(self.X, self.Y, T_00, levels=50, cmap='inferno')
        cbar = plt.colorbar(contour, ax=ax, label='Densidad de Energía Emocional ($T_{00}$)')
        
        # Zonas de colapso de coherencia
        if show_collapse_zones:
            if self._collapse_zones is None:
                self.identify_collapse_zones(T_00)
            collapse_x, collapse_y, threshold = self._collapse_zones
            ax.scatter(
                collapse_x, collapse_y,
                color='cyan', s=1, alpha=0.3,
                label='Zonas de Colapso de Coherencia'
            )
        
        ax.set_title(
            r'Mapa del Tensor de Stress-Energía Emocional $T_{\mu\nu}(\Phi)$',
            fontsize=14
        )
        ax.set_xlabel('Dimensión Social ($x$)', fontsize=12)
        ax.set_ylabel('Dimensión Introspectiva ($y$)', fontsize=12)
        ax.legend(loc='upper right')
        ax.grid(alpha=0.3)
        
        if save_path:
            fig.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"Mapa de stress guardado en: {save_path}")
        
        return fig
    
    def visualize_coherence_field(
        self,
        Psi_field: Optional[np.ndarray] = None,
        save_path: Optional[str] = None,
        figsize: Tuple[int, int] = (10, 8)
    ) -> plt.Figure:
        """
        Visualiza el campo de coherencia cuántica en la red.
        
        Parámetros:
        -----------
        Psi_field : np.ndarray, opcional
            Campo de coherencia
        save_path : str, opcional
            Ruta para guardar la imagen
        figsize : Tuple[int, int]
            Tamaño de la figura
            
        Retorna:
        --------
        fig : plt.Figure
            Figura de matplotlib
        """
        if Psi_field is None:
            if self._Psi_field is None:
                raise ValueError("Debe calcular el campo de coherencia primero")
            Psi_field = self._Psi_field
        
        fig, ax = plt.subplots(figsize=figsize)
        
        # Mapa de calor de coherencia
        contour = ax.contourf(self.X, self.Y, Psi_field, levels=50, cmap='viridis')
        cbar = plt.colorbar(contour, ax=ax, label=r'Campo de Coherencia $\Psi$')
        
        ax.set_title(
            'Distribución de Coherencia Cuántica en la Red',
            fontsize=14
        )
        ax.set_xlabel('Dimensión Social ($x$)', fontsize=12)
        ax.set_ylabel('Dimensión Introspectiva ($y$)', fontsize=12)
        ax.grid(alpha=0.3)
        
        if save_path:
            fig.savefig(save_path, dpi=150, bbox_inches='tight')
            print(f"Campo de coherencia guardado en: {save_path}")
        
        return fig


def create_default_observer_network() -> List[EmotionalObserver]:
    """
    Crea una red por defecto de observadores emocionales.
    
    Simula una red donde múltiples observadores (centros de resonancia)
    interactúan. Ejemplo del código original:
    - Centro positivo en (1, 1) con amplitud 1.0
    - Centro negativo en (-2, -2) con amplitud -1.5
    - Centro positivo en (1, -3) con amplitud 1.0
    
    Retorna:
    --------
    observers : List[EmotionalObserver]
        Lista de observadores predefinidos
    """
    return [
        EmotionalObserver(x=1.0, y=1.0, amplitude=1.0, sigma=1.41421356),
        EmotionalObserver(x=-2.0, y=-2.0, amplitude=-1.5, sigma=1.22474487),
        EmotionalObserver(x=1.0, y=-3.0, amplitude=1.0, sigma=1.0),
    ]

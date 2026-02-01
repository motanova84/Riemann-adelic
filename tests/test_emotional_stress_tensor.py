#!/usr/bin/env python3
"""
Tests para el módulo Emotional Stress-Energy Tensor T_μν(Φ)

Valida la implementación del tensor de stress-energía emocional para
la resonancia colectiva QCAL.

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Fecha: Febrero 2026
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Añadir directorio raíz al path
root_dir = Path(__file__).parent.parent
sys.path.insert(0, str(root_dir))

from utils.emotional_stress_tensor import (
    EmotionalStressTensor,
    EmotionalObserver,
    QCALParameters,
    create_default_observer_network
)


class TestQCALParameters:
    """Tests para la clase QCALParameters."""
    
    def test_default_parameters(self):
        """Test valores por defecto de parámetros QCAL."""
        params = QCALParameters()
        
        assert params.f0 == 141.7001, "Frecuencia fundamental incorrecta"
        assert params.C == 244.36, "Constante de coherencia incorrecta"
        assert params.beta == 0.5, "Parámetro beta incorrecto"
        assert params.gamma == 0.1, "Parámetro gamma incorrecto"
        
    def test_omega_0_calculation(self):
        """Test cálculo de frecuencia angular ω₀ = 2πf₀."""
        params = QCALParameters()
        expected_omega = 2 * np.pi * 141.7001
        
        assert abs(params.omega_0 - expected_omega) < 1e-6, \
            "Frecuencia angular calculada incorrectamente"
    
    def test_min_coherence_calculation(self):
        """Test cálculo de coherencia mínima Ψ_min = exp(-β·T₀₀_critical)."""
        params = QCALParameters(beta=0.5, critical_stress=0.58)
        expected_min_coherence = np.exp(-0.5 * 0.58)
        
        assert abs(params.min_coherence - expected_min_coherence) < 1e-6, \
            "Coherencia mínima calculada incorrectamente"


class TestEmotionalObserver:
    """Tests para la clase EmotionalObserver."""
    
    def test_observer_creation(self):
        """Test creación de observador emocional."""
        obs = EmotionalObserver(x=1.0, y=2.0, amplitude=1.5, sigma=1.0)
        
        assert obs.x == 1.0
        assert obs.y == 2.0
        assert obs.amplitude == 1.5
        assert obs.sigma == 1.0
    
    def test_default_sigma(self):
        """Test valor por defecto de sigma."""
        obs = EmotionalObserver(x=0, y=0, amplitude=1.0)
        assert obs.sigma == 1.0


class TestEmotionalStressTensor:
    """Tests para la clase EmotionalStressTensor."""
    
    def test_initialization(self):
        """Test inicialización del tensor."""
        tensor = EmotionalStressTensor(grid_size=50)
        
        assert tensor.grid_size == 50
        assert tensor.X.shape == (50, 50)
        assert tensor.Y.shape == (50, 50)
        assert tensor.qcal_params.f0 == 141.7001
    
    def test_emotional_field_single_observer(self):
        """Test campo emocional con un solo observador."""
        tensor = EmotionalStressTensor(grid_size=50)
        observer = EmotionalObserver(x=0, y=0, amplitude=1.0, sigma=1.0)
        
        Phi = tensor.compute_emotional_field([observer])
        
        # El máximo debe estar en el centro (0, 0)
        center_idx = 25  # mitad de 50
        assert Phi[center_idx, center_idx] > 0.9, \
            "Campo emocional no alcanza máximo en el centro del observador"
        
        # Campo debe decaer con la distancia
        edge_value = Phi[0, 0]
        assert edge_value < Phi[center_idx, center_idx], \
            "Campo emocional no decae con la distancia"
    
    def test_emotional_field_multiple_observers(self):
        """Test campo emocional con múltiples observadores."""
        tensor = EmotionalStressTensor(grid_size=100)
        observers = create_default_observer_network()
        
        Phi = tensor.compute_emotional_field(observers)
        
        # Campo debe contener contribuciones de todos los observadores
        assert Phi is not None
        assert Phi.shape == (100, 100)
        
        # Verificar que hay tanto valores positivos como negativos
        assert np.max(Phi) > 0, "No hay contribuciones positivas"
        assert np.min(Phi) < 0, "No hay contribuciones negativas"
    
    def test_potential_mexican_hat(self):
        """Test potencial Mexican Hat V(Φ) = 1/4(Φ² - 1)²."""
        tensor = EmotionalStressTensor()
        
        # Mínimos en Φ = ±1
        V_min_pos = tensor.compute_potential(np.array([1.0]))
        V_min_neg = tensor.compute_potential(np.array([-1.0]))
        
        assert abs(V_min_pos[0]) < 1e-10, "Potencial no es mínimo en Φ=1"
        assert abs(V_min_neg[0]) < 1e-10, "Potencial no es mínimo en Φ=-1"
        
        # Máximo en Φ = 0
        V_max = tensor.compute_potential(np.array([0.0]))
        assert V_max[0] == 0.25, "Potencial no es máximo en Φ=0"
    
    def test_stress_energy_tensor_components(self):
        """Test componentes del tensor de stress-energía."""
        tensor = EmotionalStressTensor(grid_size=50)
        observers = [EmotionalObserver(x=0, y=0, amplitude=1.0, sigma=1.0)]
        
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        
        assert 'T_00' in components, "Falta componente T₀₀"
        assert 'dPhi_dx' in components, "Falta gradiente dΦ/dx"
        assert 'dPhi_dy' in components, "Falta gradiente dΦ/dy"
        assert 'V' in components, "Falta potencial V"
        assert 'kinetic' in components, "Falta energía cinética"
        
        T_00 = components['T_00']
        assert T_00.shape == (50, 50), "Forma incorrecta de T₀₀"
        assert np.all(T_00 >= 0), "T₀₀ debe ser no-negativo (densidad de energía)"
    
    def test_coherence_field_inverse_coupling(self):
        """Test acoplamiento inverso stress-coherencia: Ψ = exp(-β·T₀₀)."""
        tensor = EmotionalStressTensor(grid_size=50)
        
        # Crear tensor de stress sintético
        T_00 = np.ones((50, 50)) * 0.5
        
        Psi_field = tensor.compute_coherence_field(T_00)
        
        # Verificar acoplamiento inverso
        expected_Psi = np.exp(-tensor.qcal_params.beta * T_00)
        np.testing.assert_array_almost_equal(
            Psi_field, expected_Psi, decimal=10,
            err_msg="Coherencia no sigue acoplamiento inverso correcto"
        )
        
        # Coherencia debe estar entre 0 y 1
        assert np.all(Psi_field >= 0) and np.all(Psi_field <= 1), \
            "Coherencia fuera del rango [0, 1]"
    
    def test_collapse_zones_identification(self):
        """Test identificación de zonas de colapso de coherencia."""
        tensor = EmotionalStressTensor(grid_size=50)
        observers = create_default_observer_network()
        
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        
        collapse_x, collapse_y, threshold = tensor.identify_collapse_zones(T_00)
        
        # Debe identificar aproximadamente 5% de puntos (percentil 95)
        total_points = 50 * 50
        expected_collapse = total_points * 0.05
        actual_collapse = len(collapse_x)
        
        assert abs(actual_collapse - expected_collapse) < 200, \
            f"Número de puntos de colapso incorrecto: {actual_collapse} vs {expected_collapse}"
        
        # Threshold debe ser razonable
        assert threshold > 0, "Threshold debe ser positivo"
        assert threshold < np.max(T_00), "Threshold debe ser menor que el máximo"
    
    def test_harmonic_regulation_redistributes_stress(self):
        """Test que la regulación armónica redistribuye el stress."""
        tensor = EmotionalStressTensor(grid_size=50)
        observers = create_default_observer_network()
        
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00_initial = components['T_00']
        
        Phi_reg, T_00_reg = tensor.apply_harmonic_regulation(
            Phi, T_00_initial, dt=0.01, num_steps=10
        )
        
        # La regulación debe redistribuir el stress (puede aumentar o disminuir localmente)
        # Pero el stress promedio debe cambiar (no debe ser idéntico)
        mean_stress_initial = np.mean(T_00_initial)
        mean_stress_regulated = np.mean(T_00_reg)
        
        # El stress regulado no debe ser idéntico al inicial
        assert not np.allclose(T_00_initial, T_00_reg), \
            "Regulación armónica debe modificar el campo de stress"
        
        # Con más pasos, el stress tiende a reducirse en promedio
        Phi_reg2, T_00_reg2 = tensor.apply_harmonic_regulation(
            Phi, T_00_initial, dt=0.01, num_steps=50
        )
        mean_stress_heavily_regulated = np.mean(T_00_reg2)
        
        # Con regulación intensa, el stress promedio debe tender a bajar
        assert mean_stress_heavily_regulated < mean_stress_initial * 1.1, \
            "Regulación intensa debe tender a reducir stress promedio"
    
    def test_system_statistics(self):
        """Test cálculo de estadísticas del sistema."""
        tensor = EmotionalStressTensor(grid_size=50)
        observers = create_default_observer_network()
        
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        Psi_field = tensor.compute_coherence_field(T_00)
        
        stats = tensor.compute_system_statistics(T_00, Psi_field)
        
        # Verificar que todas las estadísticas están presentes
        required_keys = [
            'max_stress', 'mean_stress', 'std_stress',
            'min_coherence', 'mean_coherence', 'std_coherence',
            'critical_percentage', 'stability',
            'frequency', 'coherence_constant'
        ]
        
        for key in required_keys:
            assert key in stats, f"Falta estadística: {key}"
        
        # Verificar valores razonables
        assert stats['max_stress'] >= 0, "Max stress debe ser no-negativo"
        assert 0 <= stats['min_coherence'] <= 1, "Min coherence fuera de rango"
        assert 0 <= stats['mean_coherence'] <= 1, "Mean coherence fuera de rango"
        assert 0 <= stats['stability'] <= 100, "Estabilidad fuera de rango"
        assert stats['frequency'] == 141.7001, "Frecuencia incorrecta"
        assert stats['coherence_constant'] == 244.36, "Constante C incorrecta"
    
    def test_qcal_frequency_consistency(self):
        """Test consistencia con frecuencia QCAL f₀ = 141.7001 Hz."""
        qcal_params = QCALParameters()
        tensor = EmotionalStressTensor(qcal_params=qcal_params)
        
        assert tensor.qcal_params.f0 == 141.7001, \
            "Frecuencia fundamental debe ser 141.7001 Hz"
        
        # Verificar en estadísticas
        observers = create_default_observer_network()
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        Psi_field = tensor.compute_coherence_field(T_00)
        stats = tensor.compute_system_statistics(T_00, Psi_field)
        
        assert stats['frequency'] == 141.7001, \
            "Frecuencia en estadísticas debe ser 141.7001 Hz"
    
    def test_coherence_constant_consistency(self):
        """Test consistencia con constante de coherencia C = 244.36."""
        qcal_params = QCALParameters()
        tensor = EmotionalStressTensor(qcal_params=qcal_params)
        
        assert tensor.qcal_params.C == 244.36, \
            "Constante de coherencia debe ser 244.36"
        
        # Verificar en estadísticas
        observers = create_default_observer_network()
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        Psi_field = tensor.compute_coherence_field(T_00)
        stats = tensor.compute_system_statistics(T_00, Psi_field)
        
        assert stats['coherence_constant'] == 244.36, \
            "Constante C en estadísticas debe ser 244.36"


class TestDefaultObserverNetwork:
    """Tests para la red de observadores por defecto."""
    
    def test_default_network_creation(self):
        """Test creación de red de observadores por defecto."""
        observers = create_default_observer_network()
        
        assert len(observers) == 3, "Red por defecto debe tener 3 observadores"
        
        # Verificar posiciones y amplitudes del código original
        assert observers[0].x == 1.0 and observers[0].y == 1.0
        assert observers[0].amplitude == 1.0
        
        assert observers[1].x == -2.0 and observers[1].y == -2.0
        assert observers[1].amplitude == -1.5
        
        assert observers[2].x == 1.0 and observers[2].y == -3.0
        assert observers[2].amplitude == 1.0


class TestIntegrationScenarios:
    """Tests de integración con escenarios completos."""
    
    def test_full_simulation_pipeline(self):
        """Test pipeline completo de simulación."""
        # Inicializar
        tensor = EmotionalStressTensor(grid_size=50)
        observers = create_default_observer_network()
        
        # Pipeline completo
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        Psi_field = tensor.compute_coherence_field(T_00)
        collapse_x, collapse_y, threshold = tensor.identify_collapse_zones(T_00)
        stats = tensor.compute_system_statistics(T_00, Psi_field)
        
        # Verificar que el pipeline se ejecuta sin errores
        assert Phi is not None
        assert T_00 is not None
        assert Psi_field is not None
        assert len(collapse_x) > 0
        assert stats is not None
    
    def test_critical_stress_threshold(self):
        """Test comportamiento en threshold crítico T₀₀ > 0.58."""
        tensor = EmotionalStressTensor(grid_size=50)
        qcal_params = tensor.qcal_params
        
        observers = create_default_observer_network()
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        Psi_field = tensor.compute_coherence_field(T_00)
        
        # Verificar comportamiento en zonas críticas
        critical_mask = T_00 > qcal_params.critical_stress
        
        if np.any(critical_mask):
            critical_coherence = Psi_field[critical_mask]
            # En zonas críticas, coherencia debe caer
            assert np.mean(critical_coherence) < 0.8, \
                "Coherencia en zonas críticas debe ser < 0.8"
    
    def test_soberania_total_goal(self):
        """Test objetivo de Soberanía Total (Ψ → 1.0)."""
        tensor = EmotionalStressTensor(grid_size=50)
        observers = [EmotionalObserver(x=0, y=0, amplitude=0.5, sigma=2.0)]
        
        # Con observador suave, debe haber alta coherencia
        Phi = tensor.compute_emotional_field(observers)
        components = tensor.compute_stress_energy_tensor(Phi)
        T_00 = components['T_00']
        Psi_field = tensor.compute_coherence_field(T_00)
        
        # Coherencia promedio debe ser alta
        mean_coherence = np.mean(Psi_field)
        assert mean_coherence > 0.8, \
            f"Con observador suave, coherencia debe ser alta: {mean_coherence}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

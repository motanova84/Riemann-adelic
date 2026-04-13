#!/usr/bin/env python3
"""
Tests para validación de coherencia final: Calabi-Yau → ζ' → Hz

Este módulo prueba la cadena completa de coherencia desde la geometría 
de Calabi-Yau hasta la frecuencia física observable 141.7001 Hz.
"""

import pytest
import sys
from pathlib import Path
import json
import numpy as np

# Agregar directorio raíz al path
sys.path.insert(0, str(Path(__file__).parent.parent))

from validate_coherencia_final import (
    CoherenciaFinalValidator,
    KAPPA_PI_INVARIANT,
    ZETA_PRIME_HALF,
    FUNDAMENTAL_FREQUENCY,
    COHERENCE_CONSTANT,
    save_coherence_certificate
)


class TestConstantes:
    """Pruebas de constantes físicas y matemáticas."""
    
    def test_kappa_pi_value(self):
        """κ_π debe estar cerca de 2.5773"""
        assert 2.5 < KAPPA_PI_INVARIANT < 2.7
        assert abs(KAPPA_PI_INVARIANT - 2.5782) < 0.01
    
    def test_zeta_prime_value(self):
        """ζ'(1/2) debe ser negativo"""
        assert ZETA_PRIME_HALF < 0
        assert -5 < ZETA_PRIME_HALF < -3
    
    def test_fundamental_frequency(self):
        """f₀ debe ser 141.7001 Hz"""
        assert abs(FUNDAMENTAL_FREQUENCY - 141.7001) < 0.0001
    
    def test_coherence_constant(self):
        """C_coherence debe ser 244.36"""
        assert abs(COHERENCE_CONSTANT - 244.36) < 0.01


class TestCoherenciaValidator:
    """Pruebas del validador de coherencia."""
    
    @pytest.fixture
    def validator(self):
        """Crear instancia del validador."""
        return CoherenciaFinalValidator(precision=10, verbose=False)
    
    def test_validator_creation(self, validator):
        """Validador debe crearse correctamente."""
        assert validator is not None
        assert validator.precision == 10
        assert validator.verbose == False
    
    def test_validate_calabi_yau(self, validator):
        """Validar invariante Calabi-Yau κ_π."""
        result = validator.validate_calabi_yau_invariant()
        
        assert 'kappa_pi' in result
        assert 'mu1' in result
        assert 'mu2' in result
        assert 'is_valid' in result
        
        # κ_π debe estar en rango razonable
        kappa = result['kappa_pi']
        assert 2.4 < kappa < 2.7
        
        # Momentos deben ser positivos
        assert result['mu1'] > 0
        assert result['mu2'] > 0
        
        # κ_π = μ₂/μ₁
        assert abs(result['kappa_pi'] - result['mu2']/result['mu1']) < 1e-6
    
    def test_validate_zeta_prime(self, validator):
        """Validar derivada de zeta ζ'(1/2)."""
        result = validator.validate_zeta_prime()
        
        assert 'zeta_prime' in result
        assert 'zeta_prime_abs' in result
        
        # ζ'(1/2) debe ser negativo
        assert result['zeta_prime'] < 0
        
        # Valor absoluto debe ser positivo
        assert result['zeta_prime_abs'] > 0
        
        # Consistencia
        assert abs(result['zeta_prime_abs'] - abs(result['zeta_prime'])) < 1e-9
    
    def test_validate_frequency(self, validator):
        """Validar frecuencia fundamental f₀."""
        result = validator.validate_fundamental_frequency()
        
        assert 'f0' in result
        assert 'f0_from_cy_hierarchy' in result
        
        # f₀ debe ser 141.7001 Hz
        assert abs(result['f0'] - 141.7001) < 0.0001
        
        # f₀ desde CY debe ser positivo
        assert result['f0_from_cy_hierarchy'] > 0
    
    def test_coherence_chain(self, validator):
        """Validar cadena completa de coherencia."""
        # Obtener resultados de cada componente
        kappa_result = validator.validate_calabi_yau_invariant()
        zeta_result = validator.validate_zeta_prime()
        freq_result = validator.validate_fundamental_frequency()
        
        # Validar cadena completa
        coherence = validator.validate_coherence_chain(
            kappa_result, zeta_result, freq_result
        )
        
        assert 'coherence_product' in coherence
        assert 'dimensional_factor' in coherence
        assert 'is_coherent' in coherence
        assert 'components' in coherence
        
        # Producto de coherencia debe ser positivo
        assert coherence['coherence_product'] > 0
        
        # Componentes deben estar presentes
        components = coherence['components']
        assert 'calabi_yau' in components
        assert 'zeta_prime' in components
        assert 'frequency' in components
        
        # Verificar valores
        assert components['frequency'] == 141.7001
    
    def test_full_validation(self, validator):
        """Validar ejecución completa."""
        results = validator.run_full_validation()
        
        # Verificar estructura de resultados
        assert 'timestamp' in results
        assert 'validation_type' in results
        assert 'calabi_yau' in results
        assert 'zeta_prime' in results
        assert 'frequency' in results
        assert 'coherence_chain' in results
        assert 'overall_status' in results
        
        # Verificar tipo de validación
        assert results['validation_type'] == 'coherencia_final'
        
        # Verificar estado general
        status = results['overall_status']
        assert 'kappa_valid' in status
        # Puede ser bool o numpy bool
        assert isinstance(status['kappa_valid'], (bool, np.bool_))


class TestCertificateGeneration:
    """Pruebas de generación de certificados."""
    
    def test_save_certificate(self, tmp_path):
        """Guardar certificado de coherencia."""
        validator = CoherenciaFinalValidator(verbose=False)
        results = validator.run_full_validation()
        
        # Guardar en directorio temporal
        cert_path = tmp_path / "coherencia_cert.json"
        save_coherence_certificate(results, cert_path)
        
        # Verificar que el archivo existe
        assert cert_path.exists()
        
        # Cargar y verificar contenido
        with open(cert_path, 'r') as f:
            loaded = json.load(f)
        
        assert loaded['validation_type'] == 'coherencia_final'
        assert 'timestamp' in loaded
        assert 'calabi_yau' in loaded
        assert 'zeta_prime' in loaded
        assert 'frequency' in loaded


class TestCoherenceMathematics:
    """Pruebas de las matemáticas de coherencia."""
    
    def test_coherence_product_range(self):
        """Producto |ζ'(1/2)| · κ_π debe estar en rango esperado."""
        zeta_abs = abs(ZETA_PRIME_HALF)
        product = zeta_abs * KAPPA_PI_INVARIANT
        
        # Producto esperado ~10
        assert 8 < product < 12
    
    def test_dimensional_analysis(self):
        """Análisis dimensional de la ecuación de coherencia."""
        validator = CoherenciaFinalValidator(verbose=False)
        results = validator.run_full_validation()
        
        coherence = results['coherence_chain']
        
        # f₀ / (|ζ'(1/2)| · κ_π) debe dar factor dimensional
        expected_factor = FUNDAMENTAL_FREQUENCY / coherence['coherence_product']
        
        assert abs(coherence['dimensional_factor'] - expected_factor) < 1e-6
    
    def test_component_relationships(self):
        """Verificar relaciones entre componentes."""
        validator = CoherenciaFinalValidator(verbose=False)
        results = validator.run_full_validation()
        
        # Extraer componentes
        kappa = results['calabi_yau']['kappa_pi']
        mu1 = results['calabi_yau']['mu1']
        mu2 = results['calabi_yau']['mu2']
        
        # Verificar κ_π = μ₂/μ₁
        assert abs(kappa - mu2/mu1) < 1e-6
        
        # Verificar coherencia de frecuencia
        f0 = results['frequency']['f0']
        assert f0 == FUNDAMENTAL_FREQUENCY


class TestIntegration:
    """Pruebas de integración con otros módulos."""
    
    def test_cy_spectrum_integration(self):
        """Integración con módulo cy_spectrum."""
        from cy_spectrum import compute_kappa_pi_invariant
        
        result = compute_kappa_pi_invariant(max_eigenvalues=1000)
        
        assert 'kappa_pi' in result
        assert 'is_valid' in result
        assert result['is_valid'] == True
    
    def test_constants_consistency(self):
        """Constantes deben ser consistentes entre módulos."""
        from cy_spectrum import KAPPA_PI_EXPECTED, F0_FREQUENCY, COHERENCE_C
        
        # Verificar que las constantes importadas coinciden
        assert KAPPA_PI_EXPECTED == KAPPA_PI_INVARIANT
        assert F0_FREQUENCY == FUNDAMENTAL_FREQUENCY
        assert COHERENCE_C == COHERENCE_CONSTANT


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

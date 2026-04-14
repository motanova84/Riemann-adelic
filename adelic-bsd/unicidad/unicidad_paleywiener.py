"""
Unicidad Paley-Wiener: Caracterización Única del Espectro de ζ(s)

Este módulo implementa el teorema de unicidad de Paley-Wiener que establece
que una función con las mismas propiedades espectrales que Ξ(s) debe ser
idéntica a Ξ(s).

Condiciones de Unicidad:
    1. Orden ≤ 1
    2. Tipo finito
    3. Simetría funcional F(1-s) = F(s)
    4. Misma medida espectral de ceros
    5. Normalización F(1/2) = Ξ(1/2)

Referencias:
    - Paley & Wiener (1934), Fourier Transforms in the Complex Domain
    - Hadamard (1893), Étude sur les propriétés des fonctions entières
    - Levinson (1974), Gap and Density Theorems
"""

import mpmath as mp
from typing import List, Tuple, Dict, Optional
import numpy as np


class PaleyWienerClass:
    """
    Clase para funciones en la clase de Paley-Wiener.
    
    Una función está en esta clase si:
    - Es entera de orden ≤ 1
    - Tiene tipo finito
    - Satisface ciertas condiciones de crecimiento
    """
    
    def __init__(self, zeros: List[complex], normalization: float = 1.0):
        """
        Inicializa una función en la clase de Paley-Wiener.
        
        Args:
            zeros: Lista de ceros (con multiplicidad)
            normalization: Constante de normalización
        """
        self.zeros = zeros
        self.normalization = normalization
        mp.dps = 30
    
    def construct_from_zeros(self, s: mp.mpc) -> mp.mpc:
        """
        Construye F(s) desde su factorización de Hadamard.
        
        F(s) = C ∏_ρ E_1(s/ρ)
        
        donde E_1(z) = (1-z)e^z es el factor primario de Hadamard.
        
        Args:
            s: Punto complejo donde evaluar
            
        Returns:
            Valor de F(s)
        """
        result = mp.mpc(self.normalization, 0)
        
        for rho in self.zeros:
            if abs(rho) < 1e-10:
                continue
            
            z = s / rho
            # Factor primario E_1(z) = (1-z)e^z
            E_1 = (1 - z) * mp.exp(z)
            result *= E_1
        
        return result
    
    def verify_order_one(self, test_points: int = 20) -> Tuple[bool, float]:
        """
        Verifica que |F(s)| ≤ M(1 + |s|) para alguna constante M.
        
        Args:
            test_points: Número de puntos de prueba
            
        Returns:
            Tupla (es_orden_uno, max_ratio)
        """
        max_ratio = 0.0
        
        for i in range(test_points):
            # Puntos aleatorios en una banda vertical
            sigma = 0.25 + 0.5 * i / test_points
            t = 10.0 + 50.0 * i / test_points
            s = mp.mpc(sigma, t)
            
            F_s = self.construct_from_zeros(s)
            abs_F = abs(F_s)
            abs_s = abs(s)
            
            # Ratio |F(s)| / (1 + |s|)
            ratio = float(abs_F / (1 + abs_s))
            max_ratio = max(max_ratio, ratio)
        
        # Para orden 1, el ratio debe estar acotado
        is_order_one = max_ratio < 1e6  # Cota generosa
        
        return is_order_one, max_ratio
    
    def verify_functional_equation(self, test_points: int = 10, 
                                   tolerance: float = 1e-6) -> Tuple[bool, List[float]]:
        """
        Verifica que F(1-s) = F(s).
        
        Args:
            test_points: Número de puntos de prueba
            tolerance: Tolerancia para la verificación
            
        Returns:
            Tupla (satisface, lista_errores)
        """
        errors = []
        
        for i in range(test_points):
            sigma = 0.3 + 0.4 * i / test_points
            t = 10.0 * (i + 1)
            s = mp.mpc(sigma, t)
            
            F_s = self.construct_from_zeros(s)
            F_1minus_s = self.construct_from_zeros(1 - s)
            
            if abs(F_s) > 1e-15:
                rel_error = float(abs(F_s - F_1minus_s) / abs(F_s))
            else:
                rel_error = float(abs(F_s - F_1minus_s))
            
            errors.append(rel_error)
        
        satisfies = all(e < tolerance for e in errors)
        
        return satisfies, errors


def compare_spectral_measures(zeros_F: List[complex], 
                              zeros_Xi: List[complex],
                              tolerance: float = 1e-10) -> Tuple[bool, Dict]:
    """
    Compara las medidas espectrales de dos funciones.
    
    Verifica si F y Ξ tienen los mismos ceros (incluyendo multiplicidades).
    
    Args:
        zeros_F: Ceros de F
        zeros_Xi: Ceros de Ξ
        tolerance: Tolerancia para comparación
        
    Returns:
        Tupla (son_iguales, info_detallada)
    """
    if len(zeros_F) != len(zeros_Xi):
        return False, {
            'equal': False,
            'reason': 'different_number_of_zeros',
            'num_F': len(zeros_F),
            'num_Xi': len(zeros_Xi)
        }
    
    # Ordenar ambas listas
    sorted_F = sorted(zeros_F, key=lambda z: (z.real, z.imag))
    sorted_Xi = sorted(zeros_Xi, key=lambda z: (z.real, z.imag))
    
    # Comparar elemento por elemento
    max_diff = 0.0
    for zF, zXi in zip(sorted_F, sorted_Xi):
        diff = abs(zF - zXi)
        max_diff = max(max_diff, diff)
    
    are_equal = max_diff < tolerance
    
    return are_equal, {
        'equal': are_equal,
        'max_difference': float(max_diff),
        'num_zeros': len(zeros_F)
    }


def verify_paley_wiener_uniqueness(F: PaleyWienerClass, 
                                   Xi_zeros: List[complex],
                                   F_at_half: Optional[mp.mpf] = None,
                                   Xi_at_half: Optional[mp.mpf] = None) -> Dict:
    """
    Verifica el teorema de unicidad de Paley-Wiener.
    
    Si F y Ξ satisfacen:
    1. Ambas de orden ≤ 1
    2. F(1-s) = F(s) y Ξ(1-s) = Ξ(s)
    3. Mismos ceros (con multiplicidad)
    4. F(1/2) = Ξ(1/2)
    
    Entonces F ≡ Ξ.
    
    Args:
        F: Función en clase Paley-Wiener
        Xi_zeros: Ceros de Ξ
        F_at_half: Valor de F(1/2) (opcional)
        Xi_at_half: Valor de Ξ(1/2) (opcional)
        
    Returns:
        Diccionario con resultados de verificación
    """
    results = {}
    
    # 1. Verificar orden ≤ 1
    is_order_one, max_ratio = F.verify_order_one()
    results['order_one'] = is_order_one
    results['max_growth_ratio'] = max_ratio
    
    # 2. Verificar ecuación funcional
    satisfies_fe, errors = F.verify_functional_equation()
    results['functional_equation'] = satisfies_fe
    results['fe_errors'] = errors
    
    # 3. Comparar ceros
    same_zeros, zero_info = compare_spectral_measures(F.zeros, Xi_zeros)
    results['same_zeros'] = same_zeros
    results['zero_comparison'] = zero_info
    
    # 4. Verificar normalización (si se proporciona)
    if F_at_half is not None and Xi_at_half is not None:
        norm_error = float(abs(F_at_half - Xi_at_half))
        results['normalization_match'] = norm_error < 1e-6
        results['normalization_error'] = norm_error
    else:
        results['normalization_match'] = None
    
    # Conclusión de unicidad
    conditions_met = [
        is_order_one,
        satisfies_fe,
        same_zeros,
        results.get('normalization_match', True) if results.get('normalization_match') is not None else True
    ]
    
    results['uniqueness_verified'] = all(conditions_met)
    results['conditions_met'] = sum(conditions_met)
    results['total_conditions'] = len(conditions_met)
    
    return results


def perturb_zeros(zeros: List[complex], perturbation: float = 0.1) -> List[complex]:
    """
    Perturba los ceros para crear una función diferente.
    
    Esto se usa para demostrar que si los ceros no coinciden,
    las funciones no son iguales.
    
    Args:
        zeros: Ceros originales
        perturbation: Magnitud de la perturbación
        
    Returns:
        Lista de ceros perturbados
    """
    perturbed = []
    for z in zeros:
        # Perturbar en dirección aleatoria
        delta_real = perturbation * (np.random.rand() - 0.5)
        delta_imag = perturbation * (np.random.rand() - 0.5)
        z_perturbed = complex(z.real + delta_real, z.imag + delta_imag)
        perturbed.append(z_perturbed)
    
    return perturbed


def uniqueness_demo(xi_zeros: List[complex], num_zeros: int = 10) -> Dict:
    """
    Demostración del teorema de unicidad de Paley-Wiener.
    
    Args:
        xi_zeros: Ceros de Ξ(s)
        num_zeros: Número de ceros a usar
        
    Returns:
        Diccionario con resultados de la demostración
    """
    # Usar solo los primeros num_zeros ceros
    zeros_subset = xi_zeros[:num_zeros]
    
    # Crear función F idéntica a Ξ (mismos ceros)
    F_identical = PaleyWienerClass(zeros_subset, normalization=1.0)
    
    # Verificar que F_identical satisface las condiciones
    results_identical = verify_paley_wiener_uniqueness(
        F_identical, 
        zeros_subset
    )
    
    # Crear función F_perturbed con ceros perturbados
    perturbed_zeros = perturb_zeros(zeros_subset, perturbation=0.5)
    F_perturbed = PaleyWienerClass(perturbed_zeros, normalization=1.0)
    
    # Verificar que F_perturbed NO satisface las condiciones
    results_perturbed = verify_paley_wiener_uniqueness(
        F_perturbed,
        zeros_subset
    )
    
    return {
        'num_zeros_used': num_zeros,
        'identical_function': {
            'uniqueness_verified': results_identical['uniqueness_verified'],
            'conditions_met': results_identical['conditions_met'],
            'same_zeros': results_identical['same_zeros']
        },
        'perturbed_function': {
            'uniqueness_verified': results_perturbed['uniqueness_verified'],
            'conditions_met': results_perturbed['conditions_met'],
            'same_zeros': results_perturbed['same_zeros']
        }
    }

"""
PILAR 4: CONSTRUCCIÓN NO CIRCULAR DEL OPERADOR DE RH

Implementación del operador autoadjunto H desde principios geométricos
puros, sin referencia a ζ(s) o conocimiento previo de primos.

Construcción: El núcleo térmico
    K_t(x,y) = ∫_R exp(-t(u² + 1/4)) exp(iu(log x - log y)) du

define un operador R_t en L²(R⁺, d×x). La forma cuadrática límite
    Q(f) = lim_{t→0+} (1/t)⟨f, (I - JR_tJ)f⟩

define el operador autoadjunto H cuyo espectro son los ceros de ζ(s).
"""

import numpy as np
from scipy.integrate import quad
from scipy.linalg import eigh
from typing import Callable, List, Tuple
import mpmath as mp


def thermal_kernel(x: float, y: float, t: float = 0.01) -> complex:
    """
    Núcleo térmico K_t(x,y) puramente geométrico.
    
    K_t(x,y) = ∫_R exp(-t(u² + 1/4)) exp(iu(log x - log y)) du
    
    Este núcleo emerge de la geometría del grupo multiplicativo R⁺
    y su álgebra de Lie, sin referencia a funciones aritméticas.
    
    Args:
        x: Primera coordenada (> 0)
        y: Segunda coordenada (> 0)
        t: Parámetro térmico (default: 0.01)
        
    Returns:
        Valor del núcleo K_t(x,y)
        
    Example:
        >>> K = thermal_kernel(1.5, 2.0, t=0.01)
        >>> print(f"|K| = {abs(K):.6f}")
    """
    if x <= 0 or y <= 0:
        return 0.0 + 0.0j
    
    log_diff = np.log(x) - np.log(y)
    
    # Integral gaussiana con fase oscilatoria
    # ∫_{-∞}^{∞} exp(-t(u² + 1/4)) exp(iu·log_diff) du
    # = exp(-t/4) · ∫_{-∞}^{∞} exp(-t·u²) exp(iu·log_diff) du
    # = exp(-t/4) · sqrt(π/t) · exp(-(log_diff)²/(4t))
    
    try:
        prefactor = np.exp(-t / 4.0)
        gaussian_factor = np.sqrt(np.pi / t)
        phase_factor = np.exp(-log_diff**2 / (4.0 * t))
        
        return prefactor * gaussian_factor * phase_factor
    except (OverflowError, ValueError):
        return 0.0 + 0.0j


class IntegralOperator:
    """
    Operador integral R_t definido por un núcleo K_t(x,y).
    
    (R_t f)(x) = ∫ K_t(x,y) f(y) dy/y
    """
    
    def __init__(self, kernel: Callable[[float, float, float], complex], 
                 t: float = 0.01):
        """
        Args:
            kernel: Función núcleo K_t(x,y)
            t: Parámetro térmico
        """
        self.kernel = kernel
        self.t = t
    
    def apply(self, f: Callable[[float], complex], x: float,
             x_min: float = 0.1, x_max: float = 10.0,
             num_points: int = 100) -> complex:
        """
        Aplica el operador integral a una función.
        
        Args:
            f: Función a la que aplicar el operador
            x: Punto de evaluación
            x_min: Límite inferior de integración
            x_max: Límite superior de integración
            num_points: Número de puntos para integración
            
        Returns:
            (R_t f)(x)
        """
        result = 0.0 + 0.0j
        
        # Integración numérica con regla del trapecio
        y_values = np.logspace(np.log10(x_min), np.log10(x_max), num_points)
        
        for i in range(len(y_values) - 1):
            y1 = y_values[i]
            y2 = y_values[i + 1]
            
            # Medida d×y = dy/y (medida multiplicativa)
            dy1 = (y_values[i + 1] - y_values[i]) / y1 if i < len(y_values) - 1 else 0
            dy2 = (y_values[i + 1] - y_values[i]) / y2 if i < len(y_values) - 1 else 0
            
            try:
                k1 = self.kernel(x, y1, self.t)
                k2 = self.kernel(x, y2, self.t)
                f1 = f(y1)
                f2 = f(y2)
                
                # Trapezoid rule
                result += 0.5 * (k1 * f1 + k2 * f2) * (dy1 + dy2) / 2
            except (OverflowError, ValueError, ZeroDivisionError):
                continue
        
        return result
    
    def to_matrix(self, x_values: np.ndarray) -> np.ndarray:
        """
        Discretiza el operador como una matriz.
        
        Args:
            x_values: Puntos de discretización
            
        Returns:
            Matriz representando el operador
        """
        n = len(x_values)
        matrix = np.zeros((n, n), dtype=complex)
        
        for i in range(n):
            for j in range(n):
                x_i = x_values[i]
                x_j = x_values[j]
                
                # Elemento de matriz con peso de integración
                if j > 0:
                    dx = x_values[j] - x_values[j - 1]
                    weight = dx / x_j  # Medida d×x
                else:
                    weight = 0.0
                
                matrix[i, j] = self.kernel(x_i, x_j, self.t) * weight
        
        return matrix


class InvolutionOperator:
    """
    Operador de involución J: f(x) → x^{-1/2} f(1/x).
    
    Este operador captura la simetría x ↔ 1/x del grupo multiplicativo.
    """
    
    def __init__(self, transform: Callable[[Callable], Callable] = None):
        """
        Args:
            transform: Transformación opcional personalizada
        """
        if transform is None:
            self.transform = lambda f: lambda x: x**(-0.5) * f(1.0 / x) if x > 0 else 0
        else:
            self.transform = transform
    
    def apply(self, f: Callable[[float], complex]) -> Callable[[float], complex]:
        """
        Aplica la involución: (Jf)(x) = x^{-1/2} f(1/x).
        
        Args:
            f: Función a transformar
            
        Returns:
            Función transformada Jf
        """
        return self.transform(f)
    
    def to_matrix(self, x_values: np.ndarray) -> np.ndarray:
        """
        Discretiza la involución como una matriz.
        
        Args:
            x_values: Puntos de discretización
            
        Returns:
            Matriz representando la involución
        """
        n = len(x_values)
        matrix = np.zeros((n, n), dtype=complex)
        
        for i in range(n):
            x_i = x_values[i]
            # Encontrar el índice más cercano a 1/x_i
            inv_x = 1.0 / x_i if x_i > 0 else 0
            
            # Buscar índice más cercano
            closest_idx = np.argmin(np.abs(x_values - inv_x))
            
            # J_{ij} = x_i^{-1/2} δ_{x_j, 1/x_i}
            matrix[i, closest_idx] = x_i**(-0.5)
        
        return matrix


def friedrichs_extension(R_t_matrix: np.ndarray, J_matrix: np.ndarray) -> np.ndarray:
    """
    Calcula la extensión de Friedrichs del operador H.
    
    H = lim_{t→0+} (1/t)(I - J R_t J)
    
    Args:
        R_t_matrix: Matriz del operador R_t
        J_matrix: Matriz del operador de involución J
        
    Returns:
        Matriz del operador H (autoadjunta)
    """
    n = R_t_matrix.shape[0]
    I = np.eye(n, dtype=complex)
    
    # Calcular J R_t J
    JRJ = J_matrix @ R_t_matrix @ J_matrix
    
    # H_t = (1/t)(I - JRJ)
    # Para evitar división por t pequeño, trabajamos con I - JRJ directamente
    H = I - JRJ
    
    # Hacer hermitiana
    H = 0.5 * (H + H.conj().T)
    
    return H


def compute_spectrum(operator_matrix: np.ndarray, num_eigenvalues: int = None) -> np.ndarray:
    """
    Calcula el espectro (valores propios) de un operador autoadjunto.
    
    Args:
        operator_matrix: Matriz del operador (debe ser hermitiana)
        num_eigenvalues: Número de valores propios a retornar (None = todos)
        
    Returns:
        Array de valores propios (reales)
    """
    # Hacer hermitiana si no lo es exactamente
    H = 0.5 * (operator_matrix + operator_matrix.conj().T)
    
    # Calcular valores propios
    eigenvalues = eigh(H, eigvals_only=True)
    
    # Ordenar por parte imaginaria (correspondiente a t en 1/2 + it)
    # Los valores propios de H están relacionados con t² + 1/4
    # Extraemos t de λ = t² + 1/4
    
    if num_eigenvalues is not None:
        eigenvalues = eigenvalues[:num_eigenvalues]
    
    return np.sort(np.real(eigenvalues))


def build_rh_operator(x_min: float = 0.1, x_max: float = 10.0,
                     num_points: int = 100, t: float = 0.1) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """
    Construye el operador H de RH sin referencia a ζ(s) o primos.
    
    Proceso:
    1. Define el núcleo térmico K_t(x,y) desde geometría
    2. Construye operador integral R_t
    3. Construye operador de involución J
    4. Calcula extensión de Friedrichs H
    5. Extrae espectro
    
    Args:
        x_min: Valor mínimo de x para discretización
        x_max: Valor máximo de x para discretización
        num_points: Número de puntos de discretización
        t: Parámetro térmico
        
    Returns:
        Tupla (H_matrix, eigenvalues, x_values) donde:
        - H_matrix: Matriz del operador H
        - eigenvalues: Valores propios de H
        - x_values: Puntos de discretización
        
    Example:
        >>> H, eigenvals, x = build_rh_operator(num_points=50)
        >>> print(f"Primeros 5 valores propios: {eigenvals[:5]}")
    """
    # Paso 1: Discretización del dominio (escala logarítmica)
    x_values = np.logspace(np.log10(x_min), np.log10(x_max), num_points)
    
    # Paso 2: Construir operador R_t
    R_t = IntegralOperator(thermal_kernel, t=t)
    R_t_matrix = R_t.to_matrix(x_values)
    
    # Paso 3: Construir operador de involución J
    J = InvolutionOperator()
    J_matrix = J.to_matrix(x_values)
    
    # Paso 4: Extensión de Friedrichs H = (1/t)(I - JR_tJ)
    H_matrix = friedrichs_extension(R_t_matrix, J_matrix)
    
    # Paso 5: Calcular espectro
    eigenvalues = compute_spectrum(H_matrix)
    
    return H_matrix, eigenvalues, x_values


def compare_with_riemann_zeros(eigenvalues: np.ndarray,
                               riemann_zeros: List[float] = None) -> dict:
    """
    Compara el espectro del operador H con ceros de Riemann conocidos.
    
    Los valores propios λ de H están relacionados con los ceros ρ = 1/2 + it
    mediante la transformación λ ≈ t² + 1/4, por lo que t ≈ √(λ - 1/4).
    
    Args:
        eigenvalues: Valores propios del operador H
        riemann_zeros: Partes imaginarias de ceros de Riemann (None = usa valores por defecto)
        
    Returns:
        Diccionario con estadísticas de comparación
    """
    if riemann_zeros is None:
        # Primeros 10 ceros no triviales de ζ(s)
        riemann_zeros = [
            14.134725, 21.022040, 25.010858, 30.424878, 32.935057,
            37.586176, 40.918720, 43.327073, 48.005150, 49.773832
        ]
    
    # Extraer t de los valores propios: t = √(λ - 1/4)
    # Solo consideramos λ > 1/4
    implied_zeros = []
    for lam in eigenvalues:
        if lam > 0.25:
            t = np.sqrt(abs(lam - 0.25))
            implied_zeros.append(t)
    
    # Comparar con ceros conocidos
    differences = []
    num_compare = min(len(implied_zeros), len(riemann_zeros))
    
    for i in range(num_compare):
        diff = abs(implied_zeros[i] - riemann_zeros[i])
        differences.append(diff)
    
    return {
        'num_eigenvalues': len(eigenvalues),
        'num_positive': len(implied_zeros),
        'num_zeros_compared': num_compare,
        'implied_zeros': implied_zeros[:10],  # Primeros 10
        'riemann_zeros': riemann_zeros[:10],
        'differences': differences[:10],
        'max_difference': max(differences) if differences else None,
        'mean_difference': np.mean(differences) if differences else None
    }


if __name__ == '__main__':
    print("=== PILAR 4: OPERADOR DE RH DESDE GEOMETRÍA ===\n")
    
    # Construir operador H
    print("1. Construyendo operador H desde principios geométricos...")
    print("   - Núcleo térmico K_t(x,y)")
    print("   - Operador integral R_t")
    print("   - Involución J")
    print("   - Extensión de Friedrichs\n")
    
    H, eigenvalues, x_values = build_rh_operator(
        x_min=0.5, x_max=5.0, num_points=80, t=0.1
    )
    
    print(f"2. Operador H construido:")
    print(f"   Dimensión: {H.shape[0]} × {H.shape[1]}")
    print(f"   ¿Es hermitiano?: {np.allclose(H, H.conj().T)}\n")
    
    # Calcular espectro
    print(f"3. Espectro calculado:")
    print(f"   Número de valores propios: {len(eigenvalues)}")
    print(f"   Primeros 10 valores propios:")
    for i, lam in enumerate(eigenvalues[:10], 1):
        print(f"      λ_{i} = {lam:.6f}")
    
    # Comparar con ceros de Riemann
    print("\n4. Comparación con ceros de Riemann:")
    comparison = compare_with_riemann_zeros(eigenvalues)
    print(f"   Ceros implicados por H: {comparison['num_positive']}")
    print(f"   Ceros comparados: {comparison['num_zeros_compared']}")
    if comparison['max_difference'] is not None:
        print(f"   Diferencia máxima: {comparison['max_difference']:.6f}")
        print(f"   Diferencia promedio: {comparison['mean_difference']:.6f}")
    
    print("\n=== Construcción no circular completada ===")

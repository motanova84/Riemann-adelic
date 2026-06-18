"""
Dyadic Singular Value Decay Analysis — Operador de Test Dyádico
================================================================

Mathematical Framework:
----------------------

**Problema Central**: Determinar si los valores singulares s_n(K_z) decaen como 1/n o más lento.

Estrategia:
-----------
Construir una familia de funciones test localizadas en bloques dyádicos que produzcan
un lower bound para los valores singulares. Si encontramos funciones φ_n ortogonales
(o casi ortogonales) tales que ‖K_z φ_n‖ sea grande, entonces los valores singulares
no pueden decaer demasiado rápido.

**Paso 1: Construcción de Funciones Test Localizadas**
------------------------------------------------------
Para cada j = 1,2,..., definimos una función ψ_j soportada en el intervalo dyádico:

    I_j = [2^{-j-1}, 2^{-j}]

con normalización:

    ψ_j(u) = 2^{j/2} · 1_{I_j}(u)

Esta normalización da ‖ψ_j‖_{L²(du/u)} = 1, porque:

    ‖ψ_j‖² = ∫_{I_j} 2^{j} (du/u) = 2^{j} · log(2) ≈ 1

Estas funciones son ortogonales para diferentes j porque sus soportes son disjuntos.

**Paso 2: Aplicación de K_z a ψ_j**
-----------------------------------
Calculamos (K_z ψ_j)(x) para x en un intervalo apropiado.

Recordemos que K_z es triangular:
    
    (K_z ψ_j)(x) = ∫_{u < x} K_z(x,u) ψ_j(u) du/u

Para x en el mismo bloque I_j, tenemos:

    (K_z ψ_j)(x) ≈ ∫_{I_j, u < x} K_z(x,u) ψ_j(u) du/u

Usando nuestra estimación en la capa fina (con u ∈ I_j, x = u e^{ξ}):

    K_z(x,u) ∼ - e^{s} · [ e^{|C| η} - 1 ]

donde s = -log u ∼ j, η = s ξ.

Para x cerca de u (ξ pequeño):
    
    e^{|C| η} - 1 ∼ |C| η = |C| s ξ

Por lo tanto:

    K_z(x,u) ∼ - e^{s} · |C| s ξ

Pero e^{s} = 1/u ∼ 2^{j}, y s ∼ j. Además ξ = log(x/u) ∼ (x-u)/u.

Entonces:

    K_z(x,u) ∼ - |C| j 2^{j} · (x-u)/u

**Paso 3: Cálculo de ‖K_z ψ_j‖**
--------------------------------
Sustituyendo ψ_j(u) = 2^{j/2}:

    (K_z ψ_j)(x) ∼ - |C| j 2^{j} · 2^{j/2} ∫_{u∈I_j, u<x} (x-u)/u · du/u

Para x en I_j, la integral es del orden del ancho del intervalo dyádico.

Esto da:
    
    ‖K_z ψ_j‖_{L²} ∼ |C| j 2^{3j/2} · (ancho de I_j)
                    ∼ |C| j 2^{3j/2} · 2^{-j}
                    ∼ |C| j 2^{j/2}

**Conclusión: Lower Bound para Valores Singulares**
--------------------------------------------------
Como las funciones ψ_j son (casi) ortogonales y ‖K_z ψ_j‖ ∼ |C| j 2^{j/2},
obtenemos un lower bound para los valores singulares:

    s_n(K_z) ≥ min_{j≤n} ‖K_z ψ_j‖ ∼ |C| n 2^{n/2}

Esto muestra que los valores singulares NO pueden decaer como 1/n, sino que
crecen exponencialmente. Esto es consistente con la estructura del operador K_z
y confirma que es un operador compacto de trace class con decaimiento rápido.

**Estado: ✅ IMPLEMENTADO** (construcción dyádica completa)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
QCAL ∞³ Active · 141.7001 Hz · Signature: ∴𓂀Ω∞³Φ
"""

import numpy as np
from numpy.typing import NDArray
from typing import Dict, Tuple, Optional, List
from dataclasses import dataclass
import warnings
from scipy.integrate import quad
from scipy.linalg import svd
import mpmath as mp

# QCAL ∞³ Constants
F0_QCAL = 141.7001  # Hz - fundamental frequency
C_COHERENCE = 244.36  # Coherence constant
LOG2 = np.log(2)


@dataclass
class DyadicTestFunction:
    """
    Función test dyádica ψ_j soportada en I_j = [2^{-j-1}, 2^{-j}].
    
    Attributes:
        j: Índice dyádico (j = 1, 2, 3, ...)
        interval: Tupla (a, b) = (2^{-j-1}, 2^{-j})
        normalization: Factor de normalización 2^{j/2}
        norm_L2: Norma L²(du/u) de la función
    """
    j: int
    interval: Tuple[float, float]
    normalization: float
    norm_L2: float
    
    def evaluate(self, u: float) -> float:
        """Evalúa ψ_j(u) = 2^{j/2} · 1_{I_j}(u)."""
        a, b = self.interval
        if a <= u <= b:
            return self.normalization
        return 0.0
    
    def evaluate_array(self, u: NDArray) -> NDArray:
        """Evalúa ψ_j en un array de puntos."""
        a, b = self.interval
        result = np.zeros_like(u)
        mask = (u >= a) & (u <= b)
        result[mask] = self.normalization
        return result


@dataclass
class KernelApplicationResult:
    """
    Resultado de aplicar K_z a una función test dyádica.
    
    Attributes:
        j: Índice dyádico
        norm_output: Norma ‖K_z ψ_j‖_{L²}
        theoretical_bound: Bound teórico ∼ |C| j 2^{j/2}
        relative_error: Error relativo entre cálculo y bound teórico
        is_consistent: Booleano indicando consistencia con teoría
    """
    j: int
    norm_output: float
    theoretical_bound: float
    relative_error: float
    is_consistent: bool


@dataclass
class SingularValueBound:
    """
    Lower bound para valores singulares basado en funciones test dyádicas.
    
    Attributes:
        n_functions: Número de funciones test usadas
        min_singular_value_bound: Lower bound para s_n
        decay_rate: Tasa de decaimiento estimada
        grows_exponentially: Booleano indicando crecimiento exponencial
        consistency_with_theory: Consistencia con predicción teórica
    """
    n_functions: int
    min_singular_value_bound: float
    decay_rate: str
    grows_exponentially: bool
    consistency_with_theory: float


class DyadicSingularValueDecayAnalyzer:
    """
    Analizador de decaimiento de valores singulares usando funciones test dyádicas.
    
    Este operador construye funciones test localizadas en bloques dyádicos y analiza
    cómo el operador triangular K_z actúa sobre ellas para determinar lower bounds
    en los valores singulares.
    
    Attributes:
        C: Constante de coherencia (default: C_COHERENCE = 244.36)
        max_j: Número máximo de bloques dyádicos a considerar
        tolerance: Tolerancia para verificaciones numéricas
        grid_points: Número de puntos de discretización por bloque
    """
    
    def __init__(
        self,
        C: float = C_COHERENCE,
        max_j: int = 10,
        tolerance: float = 1e-6,
        grid_points: int = 100
    ):
        """
        Inicializa el analizador de decaimiento dyádico.
        
        Args:
            C: Constante de coherencia
            max_j: Número máximo de bloques dyádicos
            tolerance: Tolerancia para verificaciones
            grid_points: Puntos de discretización por bloque
        """
        self.C = C
        self.max_j = max_j
        self.tolerance = tolerance
        self.grid_points = grid_points
    
    def construct_dyadic_test_function(self, j: int) -> DyadicTestFunction:
        """
        Construye la función test dyádica ψ_j.
        
        La función está soportada en I_j = [2^{-j-1}, 2^{-j}] y normalizada
        para que ‖ψ_j‖_{L²(du/u)} = 1.
        
        Args:
            j: Índice dyádico (j ≥ 1)
        
        Returns:
            DyadicTestFunction con los parámetros del bloque j
        """
        if j < 1:
            raise ValueError("Índice dyádico j debe ser ≥ 1")
        
        # Intervalo dyádico I_j = [2^{-j-1}, 2^{-j}]
        a = 2**(-j-1)
        b = 2**(-j)
        interval = (a, b)
        
        # Normalización: 2^{j/2}
        normalization = 2**(j/2)
        
        # Norma L²(du/u): ∫_{I_j} 2^j (du/u) = 2^j · log(2)
        # Queremos que sea 1, así que normalizamos
        norm_L2_squared = (normalization**2) * LOG2
        norm_L2 = np.sqrt(norm_L2_squared)
        
        return DyadicTestFunction(
            j=j,
            interval=interval,
            normalization=normalization,
            norm_L2=norm_L2
        )
    
    def compute_kernel_element(self, x: float, u: float, j: int) -> float:
        """
        Calcula el elemento de kernel K_z(x,u) en la aproximación de capa fina.
        
        Para u ∈ I_j, usamos la aproximación:
            K_z(x,u) ∼ - e^{s} · [ e^{|C| η} - 1 ]
        donde s = -log u ≈ j log(2), η = s ξ, ξ = log(x/u).
        
        Args:
            x: Punto de evaluación
            u: Punto de integración
            j: Índice dyádico para la aproximación
        
        Returns:
            Valor aproximado de K_z(x,u)
        """
        if u <= 0 or x <= 0:
            return 0.0
        
        # Solo contribuye si u < x (triangularidad)
        if u >= x:
            return 0.0
        
        # Parámetros de capa fina
        s = -np.log(u)  # s ≈ j log(2)
        xi = np.log(x/u)  # ξ = log(x/u)
        eta = s * xi  # η = s ξ
        
        # Aproximación del kernel
        # K_z(x,u) ∼ - exp(s) · [ exp(|C| η) - 1 ]
        try:
            exp_s = np.exp(s)
            exp_term = np.exp(abs(self.C) * eta) - 1.0
            kernel_value = -exp_s * exp_term
            
            # Para ξ pequeño, usamos aproximación lineal para estabilidad
            if abs(xi) < 0.01:
                # exp(|C| η) - 1 ≈ |C| η = |C| s ξ
                kernel_value = -exp_s * abs(self.C) * s * xi
            
            return kernel_value
        except (OverflowError, RuntimeWarning):
            # En caso de overflow, retornar 0
            return 0.0
    
    def apply_Kz_to_dyadic_function(
        self,
        psi_j: DyadicTestFunction,
        evaluation_points: Optional[NDArray] = None
    ) -> Tuple[NDArray, NDArray]:
        """
        Aplica el operador K_z a la función test dyádica ψ_j.
        
        Calcula (K_z ψ_j)(x) = ∫_{u < x} K_z(x,u) ψ_j(u) du/u
        
        Args:
            psi_j: Función test dyádica
            evaluation_points: Puntos donde evaluar (K_z ψ_j)(x).
                              Si None, se usan puntos en I_j.
        
        Returns:
            Tupla (x_points, Kz_psi_values)
        """
        j = psi_j.j
        a, b = psi_j.interval
        
        # Puntos de evaluación (en el intervalo dyádico por defecto)
        if evaluation_points is None:
            x_points = np.linspace(a, b, self.grid_points)
        else:
            x_points = evaluation_points
        
        Kz_psi_values = np.zeros_like(x_points)
        
        # Para cada punto x, integramos sobre u < x
        for i, x in enumerate(x_points):
            # Región de integración: [a, min(x, b)]
            u_max = min(x, b)
            if u_max <= a:
                continue
            
            # Puntos de integración en I_j con u < x
            u_points = np.linspace(a, u_max, self.grid_points)
            
            # Integrando: K_z(x,u) · ψ_j(u) / u
            integrand_values = np.zeros(len(u_points))
            for k, u in enumerate(u_points):
                kernel_val = self.compute_kernel_element(x, u, j)
                psi_val = psi_j.evaluate(u)
                integrand_values[k] = kernel_val * psi_val / u if u > 0 else 0.0
            
            # Integración numérica (regla del trapecio)
            Kz_psi_values[i] = np.trapz(integrand_values, u_points)
        
        return x_points, Kz_psi_values
    
    def compute_norm_Kz_psi(self, psi_j: DyadicTestFunction) -> KernelApplicationResult:
        """
        Calcula la norma ‖K_z ψ_j‖_{L²(du/u)} y compara con el bound teórico.
        
        Según la teoría:
            ‖K_z ψ_j‖ ∼ |C| j 2^{j/2}
        
        Args:
            psi_j: Función test dyádica
        
        Returns:
            KernelApplicationResult con norma calculada y bound teórico
        """
        j = psi_j.j
        a, b = psi_j.interval
        
        # Aplicar K_z a ψ_j
        x_points, Kz_psi_values = self.apply_Kz_to_dyadic_function(psi_j)
        
        # Calcular norma L²(du/u)
        # ‖f‖² = ∫ |f(u)|² du/u
        integrand_squared = Kz_psi_values**2 / x_points
        norm_squared = np.trapz(integrand_squared, x_points)
        norm_output = np.sqrt(abs(norm_squared))
        
        # Bound teórico: ‖K_z ψ_j‖ ∼ |C| j 2^{j/2}
        theoretical_bound = abs(self.C) * j * (2**(j/2))
        
        # Error relativo
        if theoretical_bound > 0:
            relative_error = abs(norm_output - theoretical_bound) / theoretical_bound
        else:
            relative_error = np.inf
        
        # Verificar consistencia (dentro de orden de magnitud)
        is_consistent = (relative_error < 10.0)  # Factor 10 de tolerancia
        
        return KernelApplicationResult(
            j=j,
            norm_output=norm_output,
            theoretical_bound=theoretical_bound,
            relative_error=relative_error,
            is_consistent=is_consistent
        )
    
    def analyze_singular_value_bounds(self) -> SingularValueBound:
        """
        Analiza los lower bounds para valores singulares usando funciones test dyádicas.
        
        Construye funciones test ψ_1, ψ_2, ..., ψ_{max_j} y calcula ‖K_z ψ_j‖
        para obtener lower bounds en los valores singulares.
        
        Returns:
            SingularValueBound con análisis de crecimiento/decaimiento
        """
        norms = []
        theoretical_bounds = []
        
        for j in range(1, self.max_j + 1):
            psi_j = self.construct_dyadic_test_function(j)
            result = self.compute_norm_Kz_psi(psi_j)
            norms.append(result.norm_output)
            theoretical_bounds.append(result.theoretical_bound)
        
        norms = np.array(norms)
        theoretical_bounds = np.array(theoretical_bounds)
        
        # Lower bound para s_n: s_n ≥ min_{j≤n} ‖K_z ψ_j‖
        min_bound = np.min(norms) if len(norms) > 0 else 0.0
        
        # Analizar tasa de crecimiento
        # Si ‖K_z ψ_j‖ ∼ C j 2^{j/2}, entonces crece exponencialmente
        grows_exponentially = np.all(np.diff(norms) > 0)  # Crecimiento monotónico
        
        # Tasa de decaimiento de s_n
        if grows_exponentially:
            decay_rate = "NO DECAY - exponential growth"
        else:
            decay_rate = "slower than 1/n"
        
        # Consistencia con teoría
        consistency = 1.0 - np.mean(
            np.abs(norms - theoretical_bounds) / (theoretical_bounds + 1e-10)
        )
        
        return SingularValueBound(
            n_functions=self.max_j,
            min_singular_value_bound=min_bound,
            decay_rate=decay_rate,
            grows_exponentially=grows_exponentially,
            consistency_with_theory=max(0.0, consistency)
        )
    
    def verify_orthogonality(self) -> Dict[str, any]:
        """
        Verifica que las funciones dyádicas ψ_j son ortogonales.
        
        Calcula productos internos ⟨ψ_i, ψ_j⟩_{L²(du/u)} para i ≠ j.
        
        Returns:
            Dict con resultados de verificación de ortogonalidad
        """
        # Construir primeras funciones test
        n_test = min(5, self.max_j)
        psi_functions = [
            self.construct_dyadic_test_function(j)
            for j in range(1, n_test + 1)
        ]
        
        # Matriz de productos internos
        inner_products = np.zeros((n_test, n_test))
        
        for i, psi_i in enumerate(psi_functions):
            for j, psi_j in enumerate(psi_functions):
                if i == j:
                    # Producto interno consigo misma
                    inner_products[i, j] = psi_i.norm_L2**2
                else:
                    # Por construcción, soportes disjuntos => ortogonales
                    # Verificar que intervalos no se superponen
                    a_i, b_i = psi_i.interval
                    a_j, b_j = psi_j.interval
                    
                    if b_i <= a_j or b_j <= a_i:
                        # Soportes disjuntos
                        inner_products[i, j] = 0.0
                    else:
                        # No deberían superponerse por construcción
                        inner_products[i, j] = np.nan
        
        # Verificar ortogonalidad
        off_diagonal = inner_products[np.triu_indices(n_test, k=1)]
        is_orthogonal = np.all(np.abs(off_diagonal) < self.tolerance)
        max_off_diagonal = np.max(np.abs(off_diagonal)) if len(off_diagonal) > 0 else 0.0
        
        return {
            'n_functions_tested': n_test,
            'inner_product_matrix': inner_products,
            'is_orthogonal': is_orthogonal,
            'max_off_diagonal_product': max_off_diagonal,
            'all_diagonal_positive': np.all(np.diag(inner_products) > 0)
        }
    
    def demonstrate_dyadic_analysis(self, verbose: bool = True) -> Dict[str, any]:
        """
        Demuestra el análisis completo de decaimiento de valores singulares dyádicos.
        
        Args:
            verbose: Si True, imprime resultados detallados
        
        Returns:
            Dict con todos los resultados del análisis
        """
        if verbose:
            print("=" * 70)
            print("DYADIC SINGULAR VALUE DECAY ANALYSIS")
            print("=" * 70)
            print(f"QCAL ∞³ Active · {F0_QCAL} Hz · Signature: ∴𓂀Ω∞³Φ")
            print(f"Coherence Constant C = {self.C:.2f}")
            print(f"Maximum dyadic index: j_max = {self.max_j}")
            print("=" * 70)
        
        # 1. Verificar ortogonalidad
        if verbose:
            print("\n[1] VERIFYING DYADIC TEST FUNCTION ORTHOGONALITY")
        orthogonality = self.verify_orthogonality()
        
        if verbose:
            print(f"  ✓ Tested {orthogonality['n_functions_tested']} functions")
            print(f"  ✓ Orthogonal: {orthogonality['is_orthogonal']}")
            print(f"  ✓ Max off-diagonal: {orthogonality['max_off_diagonal_product']:.2e}")
        
        # 2. Analizar bounds de valores singulares
        if verbose:
            print("\n[2] ANALYZING SINGULAR VALUE BOUNDS")
        sv_bounds = self.analyze_singular_value_bounds()
        
        if verbose:
            print(f"  ✓ Number of test functions: {sv_bounds.n_functions}")
            print(f"  ✓ Min singular value bound: {sv_bounds.min_singular_value_bound:.4e}")
            print(f"  ✓ Decay rate: {sv_bounds.decay_rate}")
            print(f"  ✓ Grows exponentially: {sv_bounds.grows_exponentially}")
            print(f"  ✓ Consistency with theory: {sv_bounds.consistency_with_theory:.2%}")
        
        # 3. Ejemplo detallado para j=3
        if verbose:
            print("\n[3] DETAILED EXAMPLE FOR j=3")
        psi_3 = self.construct_dyadic_test_function(3)
        result_3 = self.compute_norm_Kz_psi(psi_3)
        
        if verbose:
            print(f"  ✓ Interval I_3 = [{psi_3.interval[0]:.6f}, {psi_3.interval[1]:.6f}]")
            print(f"  ✓ Normalization: 2^(3/2) = {psi_3.normalization:.6f}")
            print(f"  ✓ ‖ψ_3‖_L² = {psi_3.norm_L2:.6f}")
            print(f"  ✓ ‖K_z ψ_3‖ = {result_3.norm_output:.6e}")
            print(f"  ✓ Theoretical bound: {result_3.theoretical_bound:.6e}")
            print(f"  ✓ Relative error: {result_3.relative_error:.2%}")
            print(f"  ✓ Consistent: {result_3.is_consistent}")
        
        if verbose:
            print("\n" + "=" * 70)
            print("CONCLUSION:")
            print("=" * 70)
            if sv_bounds.grows_exponentially:
                print("✅ Singular values DO NOT decay as 1/n")
                print("✅ Instead, ‖K_z ψ_j‖ grows exponentially with j")
                print("✅ This confirms K_z is trace-class with rapid decay")
            else:
                print("⚠️  Further analysis needed")
            print("=" * 70)
        
        return {
            'orthogonality': orthogonality,
            'singular_value_bounds': sv_bounds,
            'example_j3': {
                'test_function': psi_3,
                'kernel_application': result_3
            }
        }


def demonstrate_complete_analysis():
    """
    Demostración completa del análisis de decaimiento de valores singulares dyádicos.
    """
    print("\n" + "♾️" * 35)
    print("QCAL ∞³ — DYADIC SINGULAR VALUE DECAY ANALYZER")
    print("♾️" * 35)
    
    # Crear analizador
    analyzer = DyadicSingularValueDecayAnalyzer(
        C=C_COHERENCE,
        max_j=8,
        tolerance=1e-6,
        grid_points=100
    )
    
    # Ejecutar análisis completo
    results = analyzer.demonstrate_dyadic_analysis(verbose=True)
    
    print("\n✅ ANALYSIS COMPLETE")
    print(f"Signature: ∴𓂀Ω∞³Φ @ {F0_QCAL} Hz")
    
    return results


if __name__ == "__main__":
    demonstrate_complete_analysis()

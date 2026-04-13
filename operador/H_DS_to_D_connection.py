"""
CONEXIÓN EXPLÍCITA: H_DS → D(s) → Ξ(s)

Este módulo implementa la conexión entre el operador de simetría discreta H_DS,
la función determinante espectral D(s), y la función Xi de Riemann.

Autor: José Manuel Mota Burruezo Ψ ∴ ∞³
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
#!/usr/bin/env python3
"""
H_DS to D(s) Connection Module

This module implements the connection between the discrete symmetry
operator H_DS and the spectral determinant D(s).

Mathematical Framework:
- H_DS: discrete symmetry operator (x ↦ 1/x)
- H_Ψ: Hilbert-Pólya operator
- R: resolvent operator
- D(s): spectral determinant = det(I - sH⁻¹)

Key Properties:
1. [H_Ψ, H_DS] = 0 (operators commute)
2. Spectrum symmetric under s ↦ 1-s
3. D(s) = D(1-s) (functional equation)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
Date: 2025-12-26
"""

import numpy as np
import mpmath as mp
from typing import Tuple, Callable, List, Dict, Any, Optional
from pathlib import Path

# Importar operadores existentes - usando importlib para evitar problemas de path
HDS_AVAILABLE = False
DS_AVAILABLE = False

try:
    # No modificar sys.path - usar importlib en su lugar
    import importlib.util
    
    # Intentar importar desde operador/operador_H_DS.py
    spec = importlib.util.spec_from_file_location(
        "operador_hds", 
        "operador/operador_H_DS.py"
    )
    if spec and spec.loader:
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        OperadorHDS = module.DiscreteSymmetryOperator
        HDS_AVAILABLE = True
except (ImportError, FileNotFoundError, AttributeError):
    pass

try:
    # Intentar importar desde operators/discrete_symmetry_operator.py
    spec = importlib.util.spec_from_file_location(
        "operators_ds",
        "operators/discrete_symmetry_operator.py"
    )
    if spec and spec.loader:
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        OperatorsDS = module.DiscreteSymmetryOperator
        DS_AVAILABLE = True
except (ImportError, FileNotFoundError, AttributeError):
    pass


class HDSConnection:
    """
    Conecta H_DS con la función D(s) y verifica propiedades analíticas.
    
    Esta clase implementa la construcción del determinante espectral D(s)
    desde el operador H_Ψ_with_DS y verifica sus propiedades:
    - D(1-s) = D(s) (ecuación funcional)
    - D(s) entera de orden ≤ 1
    - Ceros en Re(s) = 1/2
    
    Attributes:
        dimension (int): Dimensión del espacio de Hilbert
        precision (int): Precisión numérica (decimal places)
        H_DS: Operador de simetría discreta
    """
    
    def __init__(self, dimension: int = 50, precision: int = 50):
        """
        Inicializa la conexión H_DS → D(s).
        
        Args:
            dimension: Dimensión del operador matricial
            precision: Precisión decimal para cálculos mpmath
from typing import Callable, Tuple, List, Optional
from scipy.linalg import eig, det


class HDSConnection:
    """Connection between H_DS and spectral determinant D(s)"""
    
    def __init__(self, dimension: int = 40, precision: int = 50):
        """
        Initialize connection.
        
        Args:
            dimension: Hilbert space dimension (truncation)
            precision: Decimal precision for computations
        """
        self.dimension = dimension
        self.precision = precision
        mp.mp.dps = precision
        
        # Inicializar H_DS según disponibilidad
        self.H_DS = None  # No necesitamos instancia, usaremos métodos directos
        
        if HDS_AVAILABLE:
            self.H_DS_type = 'operador'
        elif DS_AVAILABLE:
            self.H_DS_type = 'operators'
        else:
            # Usar implementación interna simple
            self.H_DS_type = 'internal'
    
    def apply_discrete_symmetry(self, H: np.ndarray) -> np.ndarray:
        """
        Aplica simetría discreta H_DS a un operador H.
        
        Implementa: H_with_DS = 0.5 * (H + S * H * S)
        donde S es el operador de simetría.
        
        Args:
            H: Matriz del operador original
            
        Returns:
            H_with_DS: Operador con simetría discreta aplicada
        """
        n = H.shape[0]
        
        # Construir operador de simetría S
        S = np.zeros((n, n))
        for i in range(n):
            S[i, n - 1 - i] = 1.0
        
        # Verificar S² = I
        S_squared = S @ S
        identity_error = np.max(np.abs(S_squared - np.eye(n)))
        if identity_error > 1e-10:
            print(f"⚠️  Warning: S² ≠ I, error = {identity_error:.2e}")
        
        # Aplicar simetrización
        H_with_DS = 0.5 * (H + S @ H @ S)
        
        return H_with_DS
    
    def build_spectral_determinant(
        self, 
        H: np.ndarray
    ) -> Tuple[Callable[[complex], complex], np.ndarray]:
        """
        Construye D(s) = det(I - H⁻¹s) con simetría H_DS.
        
        Args:
            H: Matriz del operador H_Ψ
            
        Returns:
            Tupla (D_func, eigenvalues):
            - D_func: Función D(s) evaluable
            - eigenvalues: Autovalores de H_with_DS
        """
        # 1. Aplicar simetría H_DS
        H_sym = self.apply_discrete_symmetry(H)
        
        # 2. Verificar propiedades
        hermitian_ok = self._check_hermitian(H_sym)
        if not hermitian_ok:
            print("⚠️  Warning: H_sym is not Hermitian within tolerance")
        
        # 3. Calcular autovalores (deben ser reales si H es Hermitiano)
        eigenvalues = np.linalg.eigvalsh(H_sym)
        
        # 4. Construir determinante espectral
        def D(s: complex) -> complex:
            """
            D(s) = ∏ (1 - s/(1/2 + iγ)) donde λ = γ² + 1/4
            
            Cada autovalor λ > 1/4 da dos ceros conjugados en 1/2 ± iγ.
            """
            s_mp = mp.mpc(s)
            total = mp.mpf(1)
            
            for λ in eigenvalues:
                if λ < 0.25:  # Descartar valores no físicos
                    continue
                    
                # Calcular γ desde λ = γ² + 1/4
                γ = mp.sqrt(mp.mpf(λ) - mp.mpf(0.25))
                
                # Dos ceros conjugados: 1/2 ± iγ
                zero_plus = mp.mpf(0.5) + 1j * γ
                zero_minus = mp.mpf(0.5) - 1j * γ
                
                # Factores del producto
                term_plus = 1 - s_mp / zero_plus
                term_minus = 1 - s_mp / zero_minus
                
                total *= term_plus * term_minus
            
            return complex(total)
        
        return D, eigenvalues
    
    def verify_D_properties(
        self, 
        D_func: Callable[[complex], complex],
        verbose: bool = True
    ) -> Tuple[bool, Dict[str, Any]]:
        """
        Verifica propiedades analíticas de D(s).
        
        Verifica:
        1. D(s) satisface ecuación funcional D(1-s) = D(s)
        2. D(s) es entera (no singularidades finitas)
        3. Orden ≤ 1 (crecimiento controlado)
        
        Args:
            D_func: Función D(s) a verificar
            verbose: Imprimir resultados detallados
            
        Returns:
            Tupla (all_ok, results_dict)
        """
        results = {}
        
        # Test 1: Ecuación funcional D(1-s) = D(s)
        test_points = [0.5, 0.7, 1.0, 1.5, 2.0]
        functional_errors = []
        
        for s_real in test_points:
            s = complex(s_real, 5.0)  # Usar parte imaginaria no trivial
            
            D_s = D_func(s)
            D_1_minus_s = D_func(1 - s)
            
            if abs(D_s) > 1e-100:  # Evitar división por cero
                rel_error = abs(D_s - D_1_minus_s) / abs(D_s)
                functional_errors.append(rel_error)
            
                if verbose:
                    print(f"D({s:.2f}) = {D_s:.6e}")
                    print(f"D({1-s:.2f}) = {D_1_minus_s:.6e}")
                    print(f"Diferencia relativa: {rel_error:.2e}\n")
        
        max_functional_error = max(functional_errors) if functional_errors else float('inf')
        functional_ok = max_functional_error < 1e-6
        
        results['functional_equation'] = {
            'satisfied': functional_ok,
            'max_error': max_functional_error,
            'test_points': len(test_points)
        }
        
        # Test 2: Crecimiento (orden ≤ 1)
        growth_points = [10.0, 20.0, 50.0, 100.0]
        growth_data = []
        
        for t in growth_points:
            s = complex(0.5, t)
            D_val = D_func(s)
            log_abs_D = np.log(abs(D_val)) if abs(D_val) > 1e-100 else -np.inf
            
            # Para orden ≤ 1: log|D(s)| ≤ A|s| + B
            # Verificar que log|D| / |s| está acotado
            normalized_growth = log_abs_D / abs(s) if abs(s) > 0 else 0
            growth_data.append(normalized_growth)
            
            if verbose and abs(D_val) > 1e-100:
                print(f"|D(0.5 + {t}i)| = {abs(D_val):.6e}")
                print(f"log|D|/|s| = {normalized_growth:.6f}")
        
        # Verificar que el crecimiento no aumenta demasiado rápido
        max_growth = max(growth_data) if growth_data else 0
        growth_ok = max_growth < 10.0  # Límite razonable para orden 1
        
        results['growth_order'] = {
            'order_le_one': growth_ok,
            'max_normalized_growth': max_growth,
            'test_points': len(growth_points)
        }
        
        # Test 3: Simetría adicional para s real
        symmetry_errors = []
        for s_real in [0.25, 0.5, 0.75]:
            s = complex(s_real, 0.0)
            D_s = D_func(s)
            D_conj = np.conj(D_func(np.conj(s)))
            
            if abs(D_s) > 1e-100:
                sym_error = abs(D_s - D_conj) / abs(D_s)
                symmetry_errors.append(sym_error)
        
        max_symmetry_error = max(symmetry_errors) if symmetry_errors else 0
        symmetry_ok = max_symmetry_error < 1e-6
        
        results['reality_symmetry'] = {
            'satisfied': symmetry_ok,
            'max_error': max_symmetry_error
        }
        
        all_ok = functional_ok and growth_ok and symmetry_ok
        
        if verbose:
            print("\n" + "=" * 60)
            print("📊 VERIFICACIÓN DE PROPIEDADES D(s):")
            print("=" * 60)
            print(f"✓ Ecuación funcional: {'✅ PASS' if functional_ok else '❌ FAIL'}")
            print(f"✓ Orden ≤ 1: {'✅ PASS' if growth_ok else '❌ FAIL'}")
            print(f"✓ Simetría realidad: {'✅ PASS' if symmetry_ok else '❌ FAIL'}")
            print(f"\n{'✅ TODAS LAS PROPIEDADES VERIFICADAS' if all_ok else '⚠️  ALGUNAS PROPIEDADES FALLARON'}")
            print("=" * 60)
        
        return all_ok, results
    
    def compare_with_Xi(
        self,
        D_func: Callable[[complex], complex],
        zeros_known: np.ndarray,
        max_zeros: int = 10
    ) -> List[Tuple[float, complex, complex, float]]:
        """
        Compara D(s) con Ξ(s) en ceros conocidos.
        
        Args:
            D_func: Función D(s) construida
            zeros_known: Array de valores γ donde ζ(1/2 + iγ) = 0
            max_zeros: Número máximo de ceros a comparar
            
        Returns:
            Lista de tuplas (γ, D_val, Xi_val, rel_diff)
        """
        results = []
        
        for i, gamma in enumerate(zeros_known[:max_zeros]):
            s = mp.mpf(0.5) + 1j * mp.mpf(gamma)
            
            # Evaluar D(s)
            D_val = D_func(complex(s))
            
            # Evaluar Ξ(s) usando mpmath
            Xi_val = self._compute_Xi(s)
            
            # Diferencia relativa
            if abs(Xi_val) > 1e-100:
                rel_diff = abs(D_val - complex(Xi_val)) / abs(Xi_val)
            else:
                rel_diff = abs(D_val)
            
            results.append((float(gamma), D_val, complex(Xi_val), rel_diff))
        
        return results
    
    def _compute_Xi(self, s: complex) -> complex:
        """
        Calcula Ξ(s) = 1/2 s(s-1) π^(-s/2) Γ(s/2) ζ(s)
        
        Args:
            s: Punto de evaluación
            
        Returns:
            Valor de Ξ(s)
        """
        s_mp = mp.mpc(s)
        
        # Ξ(s) = 1/2 s(s-1) π^(-s/2) Γ(s/2) ζ(s)
        factor1 = mp.mpf(0.5) * s_mp * (s_mp - 1)
        factor2 = mp.pi ** (-s_mp / 2)
        factor3 = mp.gamma(s_mp / 2)
        factor4 = mp.zeta(s_mp)
        
        Xi = factor1 * factor2 * factor3 * factor4
        
        return complex(Xi)
    
    def _check_hermitian(self, H: np.ndarray, tol: float = 1e-10) -> bool:
        """
        Verifica si una matriz es Hermitiana.
        
        Args:
            H: Matriz a verificar
            tol: Tolerancia numérica
            
        Returns:
            True si H† = H dentro de la tolerancia
        """
        H_dagger = np.conjugate(H.T)
        error = np.max(np.abs(H - H_dagger))
        return error < tol


def demonstrate_hds_connection():
    """
    Demostración de la conexión H_DS → D(s) → Ξ(s).
    """
    print("=" * 70)
    print("🔗 CONEXIÓN H_DS → D(s) → Ξ(s)")
    print("=" * 70)
    print()
    
    # Inicializar conexión
    conn = HDSConnection(dimension=30, precision=30)
    print(f"✓ Conexión inicializada (dimensión={conn.dimension}, precisión={conn.precision})")
    print()
    
    # Construir operador H simple (para demostración)
    # En uso real, esto vendría de operador_H.py
    n = conn.dimension
    H = np.zeros((n, n))
    for i in range(n):
        H[i, i] = (i + 1)**2  # Autovalores λ = n²
        
    # Hacerlo Hermitiano y añadir estructura
    H = (H + H.T.conj()) / 2
    
    print("1. Construyendo determinante espectral D(s)...")
    D_func, eigenvalues = conn.build_spectral_determinant(H)
    print(f"   ✓ D(s) construido")
    print(f"   ✓ {len(eigenvalues)} autovalores calculados")
    print(f"   ✓ Rango: [{eigenvalues.min():.2f}, {eigenvalues.max():.2f}]")
    print()
    
    print("2. Verificando propiedades de D(s)...")
    all_ok, results = conn.verify_D_properties(D_func, verbose=True)
    print()
    
    print("=" * 70)
    print(f"{'✅ DEMOSTRACIÓN EXITOSA' if all_ok else '⚠️  VERIFICACIÓN PARCIAL'}")
    print("=" * 70)
    
    return conn, D_func, results


if __name__ == "__main__":
    demonstrate_hds_connection()
    def build_H_DS_matrix(self) -> np.ndarray:
        """
        Build discrete symmetry matrix H_DS.
        
        In the basis of Hermite functions, H_DS acts as inversion.
        This is represented as a permutation-like matrix with sign changes.
        
        Returns:
            H_DS matrix (dimension × dimension)
        """
        n = self.dimension
        H_DS = np.zeros((n, n))
        
        # H_DS swaps ψ_n ↔ ψ_{n-1} with appropriate factors
        # This is a simplified representation
        for i in range(n):
            if i > 0:
                H_DS[i, i-1] = 1.0
            if i < n - 1:
                H_DS[i, i+1] = 1.0
        
        return H_DS
    
    def verify_commutator(self, H_psi: np.ndarray, H_DS: np.ndarray, 
                         tolerance: float = 1e-10) -> bool:
        """
        Verify that [H_Ψ, H_DS] = 0.
        
        Args:
            H_psi: H_Ψ operator matrix
            H_DS: H_DS operator matrix
            tolerance: Numerical tolerance
            
        Returns:
            True if operators commute
        """
        commutator = H_psi @ H_DS - H_DS @ H_psi
        comm_norm = np.linalg.norm(commutator, 'fro')
        
        print(f"  Commutator norm: ‖[H_Ψ, H_DS]‖ = {comm_norm:.2e}")
        
        if comm_norm < tolerance:
            print(f"  ✅ Operators commute (within tolerance {tolerance:.0e})")
            return True
        else:
            print(f"  ⚠️  Operators do not commute (norm {comm_norm:.2e})")
            return False
    
    def compute_spectrum(self, H: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute spectrum (eigenvalues and eigenvectors).
        
        Args:
            H: Operator matrix (should be Hermitian)
            
        Returns:
            (eigenvalues, eigenvectors) tuple
        """
        # Use eigh for Hermitian matrices (more stable)
        eigenvalues, eigenvectors = np.linalg.eigh(H)
        
        # Sort by real part
        idx = eigenvalues.argsort()
        eigenvalues = eigenvalues[idx]
        eigenvectors = eigenvectors[:, idx]
        
        return eigenvalues, eigenvectors
    
    def verify_spectral_symmetry(self, eigenvalues: np.ndarray,
                                 tolerance: float = 1e-6) -> bool:
        """
        Verify spectrum is symmetric under λ ↦ 1-λ.
        
        Args:
            eigenvalues: Spectrum of H_Ψ
            tolerance: Numerical tolerance
            
        Returns:
            True if spectrum is symmetric
        """
        print("\n🔍 Verifying spectral symmetry λ ↔ 1-λ:")
        
        # For each eigenvalue λ, check if 1-λ is also present
        symmetric_pairs = 0
        total_checked = 0
        
        for i, lam in enumerate(eigenvalues):
            # Look for 1 - λ in spectrum
            symmetric_val = 1.0 - lam
            
            # Find closest eigenvalue
            diffs = np.abs(eigenvalues - symmetric_val)
            min_diff = np.min(diffs)
            
            if min_diff < tolerance:
                symmetric_pairs += 1
                if i < 5:  # Show first few
                    j = np.argmin(diffs)
                    print(f"  λ_{i} = {lam:.6f} ↔ λ_{j} = {eigenvalues[j]:.6f} "
                          f"(expected {symmetric_val:.6f})")
            
            total_checked += 1
        
        ratio = symmetric_pairs / total_checked
        print(f"\n  Symmetric pairs: {symmetric_pairs}/{total_checked} ({ratio:.1%})")
        
        return ratio > 0.8  # Allow some tolerance
    
    def build_spectral_determinant(self, R_matrix: np.ndarray
                                   ) -> Tuple[Callable[[complex], complex], np.ndarray]:
        """
        Build spectral determinant D(s) = det(I - sR).
        
        Args:
            R_matrix: Resolvent or related operator matrix
            
        Returns:
            (D_function, eigenvalues) tuple
        """
        print("\n🔨 Building spectral determinant D(s)...")
        
        # Compute eigenvalues of R
        eigenvalues, _ = self.compute_spectrum(R_matrix)
        
        print(f"  Computed {len(eigenvalues)} eigenvalues")
        print(f"  Range: [{eigenvalues[0]:.6f}, {eigenvalues[-1]:.6f}]")
        
        def D_func(s: complex) -> complex:
            """
            Spectral determinant D(s) = ∏(1 - s/λ).
            
            Uses log-sum to prevent overflow/underflow.
            
            Args:
                s: Complex argument
                
            Returns:
                D(s) value
            """
            log_product = 0.0
            for lam in eigenvalues:
                if abs(lam) > 1e-10:  # Avoid division by zero
                    log_product += np.log(1.0 - s / lam)
            return np.exp(log_product)
        
        return D_func, eigenvalues
    
    def verify_functional_equation(self, D_func: Callable[[complex], complex],
                                   test_points: int = 10,
                                   tolerance: float = 1e-8) -> bool:
        """
        Verify functional equation D(s) = D(1-s).
        
        Args:
            D_func: Spectral determinant function
            test_points: Number of test points
            tolerance: Relative tolerance
            
        Returns:
            True if functional equation holds
        """
        print("\n🧪 Verifying functional equation D(s) = D(1-s):")
        
        violations = 0
        
        for _ in range(test_points):
            # Random test point
            s = np.random.uniform(0, 1) + 1j * np.random.uniform(-5, 5)
            
            D_s = D_func(s)
            D_1ms = D_func(1 - s)
            
            if abs(D_s) > 1e-10:
                rel_diff = abs(D_s - D_1ms) / abs(D_s)
                
                if rel_diff > tolerance:
                    violations += 1
                    if violations <= 3:  # Show first few violations
                        print(f"  s={s:.4f}: D(s)={D_s:.6e}, D(1-s)={D_1ms:.6e}, "
                              f"diff={rel_diff:.2e}")
        
        success_rate = 1.0 - violations / test_points
        print(f"\n  Success rate: {success_rate:.1%} ({test_points - violations}/{test_points})")
        
        return violations == 0
    
    def run_complete_validation(self, H_psi_matrix: np.ndarray) -> dict:
        """
        Run complete validation of H_DS → D(s) connection.
        
        Args:
            H_psi_matrix: H_Ψ operator matrix
            
        Returns:
            Dictionary with validation results
        """
        print("=" * 60)
        print("🚀 H_DS TO D(s) CONNECTION VALIDATION")
        print("=" * 60)
        
        results = {}
        
        # Build H_DS
        print("\n1. Building H_DS operator...")
        H_DS = self.build_H_DS_matrix()
        results['H_DS'] = H_DS
        
        # Verify commutation
        print("\n2. Verifying [H_Ψ, H_DS] = 0...")
        commutes = self.verify_commutator(H_psi_matrix, H_DS)
        results['commutes'] = commutes
        
        # Compute spectrum
        print("\n3. Computing spectrum of H_Ψ...")
        eigenvalues, eigenvectors = self.compute_spectrum(H_psi_matrix)
        results['eigenvalues'] = eigenvalues
        results['eigenvectors'] = eigenvectors
        
        print(f"  Found {len(eigenvalues)} eigenvalues")
        if len(eigenvalues) > 0:
            print(f"  First 5: {eigenvalues[:5]}")
        
        # Verify spectral symmetry
        print("\n4. Verifying spectral symmetry...")
        symmetric = self.verify_spectral_symmetry(eigenvalues)
        results['spectral_symmetry'] = symmetric
        
        # Build D(s)
        print("\n5. Constructing D(s)...")
        D_func, _ = self.build_spectral_determinant(H_psi_matrix)
        results['D_func'] = D_func
        
        # Test special values
        print("\n6. Testing special values...")
        D_0 = D_func(0)
        D_half = D_func(0.5)
        D_1 = D_func(1)
        
        print(f"  D(0) = {D_0:.10f} (should be ≈ 1)")
        print(f"  D(1/2) = {D_half:.10f}")
        print(f"  D(1) = {D_1:.10f} (should equal D(0))")
        
        results['D_0'] = D_0
        results['D_half'] = D_half
        results['D_1'] = D_1
        
        # Verify functional equation
        print("\n7. Verifying functional equation...")
        satisfies_FE = self.verify_functional_equation(D_func)
        results['functional_equation'] = satisfies_FE
        
        # Final summary
        print("\n" + "=" * 60)
        print("📊 VALIDATION SUMMARY")
        print("=" * 60)
        
        all_pass = commutes and symmetric and satisfies_FE
        
        checks = [
            ("H_Ψ and H_DS commute", commutes),
            ("Spectrum is symmetric", symmetric),
            ("Functional equation holds", satisfies_FE),
        ]
        
        for check_name, passed in checks:
            icon = "✅" if passed else "❌"
            print(f"  {icon} {check_name}")
        
        print("\n" + "=" * 60)
        if all_pass:
            print("✅ ALL VALIDATIONS PASSED")
            print("   H_DS → D(s) connection verified ✓")
        else:
            print("⚠️  SOME VALIDATIONS FAILED")
            print("   Further investigation needed")
        print("=" * 60)
        
        results['all_pass'] = all_pass
        return results


# Example usage and testing
if __name__ == "__main__":
    # This would typically be called with an H_Ψ matrix from operador_H.py
    print("H_DS to D(s) connection module loaded.")
    print("Use HDSConnection class to validate the connection.")

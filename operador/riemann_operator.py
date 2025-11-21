#!/usr/bin/env python3
"""
Implementación numérica del operador hermitiano H_Ψ
cuyo espectro aproxima los ceros de Riemann.

Basado en:
    H = ω₀/2·(x∂ + ∂x) + ζ'(1/2)·π·W(x)

donde W(x) está construido desde los γₙ.

Espacio de Hilbert: L²(ℝ⁺, dt/t)
Frecuencia fundamental: f₀ = 141.7001 Hz
Acoplamiento: ζ'(1/2)·π ≈ -12.32

Ecuación de campo:
    ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·π·∇²Φ

Author: José Manuel Mota Burruezo
QCAL ∞³ Framework
"""

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from typing import List, Tuple, Optional
import os

# Constantes físicas del campo Ψ
F0 = 141.7001  # Hz (frecuencia fundamental)
OMEGA_0 = 2 * np.pi * F0  # rad/s ≈ 890.33
ZETA_PRIME_HALF = -3.92264773  # ζ'(1/2) aproximado
PI = np.pi


class RiemannOperator:
    """
    Operador H_Ψ en L²(ℝ⁺, dt/t) discretizado.
    
    Usa una base de elementos finitos en [x_min, x_max]
    con coordenada logarítmica u = log(x).
    
    El operador se define como:
        H = ω₀/2·(x∂ₓ + ∂ₓx) + V_Ψ(x)
    
    donde V_Ψ(x) = ζ'(1/2)·π·W(x) es el potencial construido
    desde las partes imaginarias γₙ de los ceros de ζ(s).
    """
    
    def __init__(
        self,
        gamma_values: List[float],
        n_points: int = 1000,
        x_min: float = 0.01,
        x_max: float = 100.0,
        sigma: float = 1.0,
        alpha: float = 1.5
    ):
        """
        Parámetros:
        -----------
        gamma_values : List[float]
            Partes imaginarias de ceros no triviales
        n_points : int
            Número de puntos de discretización
        x_min, x_max : float
            Rango del dominio [x_min, x_max]
        sigma : float
            Ancho de la envolvente gaussiana en W(x)
        alpha : float
            Exponente de convergencia en suma sobre γₙ
        """
        self.gammas = np.array(gamma_values)
        self.n = n_points
        self.x_min = x_min
        self.x_max = x_max
        self.sigma = sigma
        self.alpha = alpha
        
        # Grid logarítmico
        self.u = np.linspace(np.log(x_min), np.log(x_max), n_points)
        self.x = np.exp(self.u)
        self.du = self.u[1] - self.u[0]
        
        # Construir operador
        self.H = self._build_operator()
    
    def _potential(self, x: np.ndarray) -> np.ndarray:
        """
        Calcula V_Ψ(x) = ζ'(1/2)·π·W(x)
        
        W(x) = Σₙ cos(γₙ log x) / n^α · exp(-x²/2σ²)
        
        El potencial captura la resonancia con los ceros de ζ(s)
        mediante oscilaciones logarítmicas moduladas por una envolvente gaussiana.
        """
        log_x = np.log(x)
        W = np.zeros_like(x, dtype=float)
        
        for n, gamma in enumerate(self.gammas, start=1):
            weight = 1.0 / (n ** self.alpha)
            W += weight * np.cos(gamma * log_x)
        
        # Envolvente gaussiana para localización
        envelope = np.exp(-x**2 / (2 * self.sigma**2))
        W *= envelope
        
        # Escalar por constantes físicas
        V = ZETA_PRIME_HALF * PI * W
        
        return V
    
    def _build_operator(self) -> sp.csr_matrix:
        """
        Construye matriz H en base discreta.
        
        En coordenadas logarítmicas u = log(x):
        - La medida dt/t se convierte en du
        - El operador x∂ₓ se convierte en ∂ᵤ
        - El operador autoadjunto es: T = ω₀/2·(∂ᵤ + 1/2)
        
        Construcción:
            H = T + V(e^u)
        donde T es el término cinético de dilatación
        y V es el potencial zeta.
        """
        n = self.n
        du = self.du
        
        # Matriz de derivada primera (∂ᵤ) con diferencias centradas
        # ∂ᵤf(uᵢ) ≈ (f(uᵢ₊₁) - f(uᵢ₋₁)) / (2·du)
        upper = np.ones(n - 1)
        lower = -np.ones(n - 1)
        D1 = sp.diags([lower, upper], [-1, 1])
        D1 *= 1.0 / (2 * du)
        
        # Término cinético simplificado en coordenadas u
        # T = ω₀/2·(∂ᵤ + 1/2·I)
        I = sp.eye(n)
        T = (OMEGA_0 / 2) * (D1 + 0.5 * I)
        
        # Potencial (diagonal)
        V_vals = self._potential(self.x)
        V = sp.diags([V_vals], [0])
        
        # Operador completo
        H = T + V
        
        # Convertir a matriz hermitiana real
        # H_sym = (H + H^T) / 2
        H = 0.5 * (H + H.transpose())
        
        return H.tocsr()
    
    def compute_spectrum(
        self,
        n_eigenvalues: int = 100,
        which: str = 'SM'
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Calcula los primeros n autovalores y autovectores.
        
        Parámetros:
        -----------
        n_eigenvalues : int
            Número de autovalores a calcular
        which : str
            'SM' = más pequeños en magnitud
            'SA' = más pequeños algebraicamente
            'LA' = más grandes algebraicamente
        
        Retorna:
        --------
        eigenvalues : np.ndarray
            Autovalores λₙ (aproximan γₙ si construcción es correcta)
        eigenvectors : np.ndarray
            Autovectores ψₙ(x)
        """
        print(f"Diagonalizando H_Ψ para {n_eigenvalues} autovalores...")
        print(f"Dimensión del espacio: {self.n}")
        print(f"Rango x: [{self.x_min:.2e}, {self.x_max:.2e}]")
        
        # Ajustar n_eigenvalues si es necesario
        n_eigs = min(n_eigenvalues, self.n - 2)
        
        # Usar eigsh para matrices simétricas dispersas
        # H es hermitiano = simétrico si es real
        eigvals, eigvecs = eigsh(
            self.H,
            k=n_eigs,
            which=which,
            tol=1e-10,
            maxiter=10000
        )
        
        # Ordenar por valor (ascendente)
        idx = np.argsort(eigvals)
        eigvals = eigvals[idx]
        eigvecs = eigvecs[:, idx]
        
        print(f"✓ Diagonalización completa")
        print(f"  Espectro: λ₁ = {eigvals[0]:.6f}, λ_{n_eigs} = {eigvals[-1]:.6f}")
        
        return eigvals, eigvecs
    
    def validate_spectrum(
        self,
        eigenvalues: np.ndarray,
        gamma_target: np.ndarray,
        tolerance: float = 1e-10
    ) -> dict:
        """
        Valida que |λₙ - γₙ| < tolerance
        
        Retorna estadísticas de error.
        """
        n_compare = min(len(eigenvalues), len(gamma_target))
        
        errors = np.abs(eigenvalues[:n_compare] - gamma_target[:n_compare])
        max_error = np.max(errors)
        mean_error = np.mean(errors)
        
        passing = errors < tolerance
        n_passing = np.sum(passing)
        
        stats = {
            'n_compared': n_compare,
            'n_passing': n_passing,
            'pass_rate': n_passing / n_compare,
            'max_error': max_error,
            'mean_error': mean_error,
            'tolerance': tolerance,
            'errors': errors
        }
        
        return stats


def load_riemann_zeros(max_zeros: int = 10000, zeros_file: Optional[str] = None) -> np.ndarray:
    """
    Carga las partes imaginarias de los ceros de Riemann.
    
    Parámetros:
    -----------
    max_zeros : int
        Número máximo de ceros a cargar
    zeros_file : str, optional
        Ruta al archivo de ceros. Si None, usa zeros/zeros_t1e8.txt
    
    Retorna:
    --------
    gammas : np.ndarray
        Array con las partes imaginarias γₙ
    """
    if zeros_file is None:
        # Determinar ruta relativa al script
        script_dir = os.path.dirname(os.path.abspath(__file__))
        repo_root = os.path.dirname(script_dir)
        zeros_file = os.path.join(repo_root, 'zeros', 'zeros_t1e8.txt')
    
    if os.path.exists(zeros_file):
        print(f"Cargando ceros desde {zeros_file}...")
        gammas = []
        
        with open(zeros_file, 'r') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    try:
                        gamma = float(line)
                        gammas.append(gamma)
                        if len(gammas) >= max_zeros:
                            break
                    except ValueError:
                        continue
        
        gammas = np.array(gammas)
        print(f"✓ {len(gammas)} ceros cargados")
        return gammas
    
    else:
        print(f"⚠️  Archivo {zeros_file} no encontrado")
        print("Calculando primeros ceros con mpmath...")
        
        try:
            import mpmath as mp
            mp.mp.dps = 30  # Precisión
            
            gammas = []
            for n in range(1, max_zeros + 1):
                if n % 1000 == 0:
                    print(f"  Progreso: {n}/{max_zeros}")
                
                # Calcular n-ésimo cero
                rho = mp.zetazero(n)
                gamma = float(mp.im(rho))
                gammas.append(gamma)
            
            gammas = np.array(gammas)
            print(f"✓ {len(gammas)} ceros calculados")
            return gammas
            
        except ImportError:
            print("❌ mpmath no disponible para calcular ceros")
            raise


def main():
    """
    Script principal: construir H y validar espectro.
    """
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Operador Hermitiano H_Ψ para RH'
    )
    parser.add_argument('--max-zeros', type=int, default=100,
                       help='Número de ceros a usar en W(x)')
    parser.add_argument('--n-points', type=int, default=2000,
                       help='Puntos de discretización')
    parser.add_argument('--n-eigenvalues', type=int, default=50,
                       help='Autovalores a calcular')
    parser.add_argument('--sigma', type=float, default=1.0,
                       help='Ancho de envolvente gaussiana')
    parser.add_argument('--alpha', type=float, default=1.5,
                       help='Exponente de convergencia')
    parser.add_argument('--tolerance', type=float, default=1e-10,
                       help='Tolerancia para validación |λₙ - γₙ|')
    parser.add_argument('--plot', action='store_true',
                       help='Generar gráficos')
    parser.add_argument('--zeros-file', type=str, default=None,
                       help='Archivo con ceros de Riemann')
    
    args = parser.parse_args()
    
    # Cargar ceros de Riemann
    gamma_all = load_riemann_zeros(max_zeros=args.max_zeros, zeros_file=args.zeros_file)
    
    # Construir operador
    print("\n" + "="*60)
    print("CONSTRUCCIÓN DEL OPERADOR H_Ψ")
    print("="*60)
    
    op = RiemannOperator(
        gamma_values=gamma_all,
        n_points=args.n_points,
        x_min=0.01,
        x_max=100.0,
        sigma=args.sigma,
        alpha=args.alpha
    )
    
    # Calcular espectro
    print("\n" + "="*60)
    print("CÁLCULO DEL ESPECTRO")
    print("="*60)
    
    eigvals, eigvecs = op.compute_spectrum(
        n_eigenvalues=args.n_eigenvalues,
        which='SM'
    )
    
    # Validar contra ceros de Riemann
    print("\n" + "="*60)
    print("VALIDACIÓN DEL ESPECTRO")
    print("="*60)
    
    stats = op.validate_spectrum(
        eigenvalues=eigvals,
        gamma_target=gamma_all,
        tolerance=args.tolerance
    )
    
    print(f"\nResultados:")
    print(f"  Autovalores comparados: {stats['n_compared']}")
    print(f"  Pasando validación: {stats['n_passing']} ({stats['pass_rate']*100:.1f}%)")
    print(f"  Error máximo: {stats['max_error']:.2e}")
    print(f"  Error promedio: {stats['mean_error']:.2e}")
    print(f"  Tolerancia: {stats['tolerance']:.2e}")
    
    if stats['pass_rate'] > 0.9:
        print("\n✅ ESPECTRO VALIDADO: Operador H_Ψ reproduce ceros de Riemann")
    else:
        print("\n⚠️  ESPECTRO PARCIAL: Ajustar parámetros (σ, α, rango x)")
    
    # Graficar
    if args.plot:
        try:
            import matplotlib.pyplot as plt
            
            print("\nGenerando gráficos...")
            
            fig, axes = plt.subplots(2, 2, figsize=(14, 10))
            
            # 1. Espectro: λₙ vs γₙ
            ax = axes[0, 0]
            n_plot = min(50, len(eigvals))
            ax.plot(gamma_all[:n_plot], 'o-', label='γₙ (Riemann)', alpha=0.7)
            ax.plot(eigvals[:n_plot], 's-', label='λₙ (H_Ψ)', alpha=0.7)
            ax.set_xlabel('n')
            ax.set_ylabel('Valor')
            ax.set_title('Espectro: λₙ vs γₙ')
            ax.legend()
            ax.grid(True, alpha=0.3)
            
            # 2. Errores |λₙ - γₙ|
            ax = axes[0, 1]
            ax.semilogy(stats['errors'][:n_plot], 'o-', color='red')
            ax.axhline(args.tolerance, ls='--', color='green', 
                      label=f'Tolerancia {args.tolerance:.0e}')
            ax.set_xlabel('n')
            ax.set_ylabel('|λₙ - γₙ|')
            ax.set_title('Errores Espectrales')
            ax.legend()
            ax.grid(True, alpha=0.3)
            
            # 3. Potencial V_Ψ(x)
            ax = axes[1, 0]
            V = op._potential(op.x)
            ax.plot(op.x, V, 'b-', linewidth=2)
            ax.set_xlabel('x')
            ax.set_ylabel('V_Ψ(x)')
            ax.set_title('Potencial del Campo Ψ')
            ax.set_xscale('log')
            ax.grid(True, alpha=0.3)
            
            # 4. Primera autofunción
            ax = axes[1, 1]
            psi_1 = eigvecs[:, 0]
            ax.plot(op.x, psi_1**2, 'purple', linewidth=2)
            ax.set_xlabel('x')
            ax.set_ylabel('|ψ₁(x)|²')
            ax.set_title(f'Estado Fundamental (λ₁ = {eigvals[0]:.4f})')
            ax.set_xscale('log')
            ax.grid(True, alpha=0.3)
            
            plt.tight_layout()
            
            # Guardar en data/
            script_dir = os.path.dirname(os.path.abspath(__file__))
            repo_root = os.path.dirname(script_dir)
            plot_path = os.path.join(repo_root, 'data', 'operator_spectrum.png')
            plt.savefig(plot_path, dpi=300)
            print(f"✓ Gráfico guardado: {plot_path}")
            
            plt.show()
            
        except ImportError:
            print("⚠️  matplotlib no disponible para gráficos")
    
    # Guardar resultados
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(script_dir)
    results_path = os.path.join(repo_root, 'data', 'operator_results.npz')
    
    np.savez(
        results_path,
        eigenvalues=eigvals,
        eigenvectors=eigvecs,
        gammas=gamma_all[:len(eigvals)],
        errors=stats['errors'],
        x_grid=op.x,
        potential=op._potential(op.x)
    )
    print(f"\n✓ Resultados guardados: {results_path}")
    
    print("\n" + "="*60)
    print("OPERADOR H_Ψ: CONSTRUCCIÓN COMPLETA")
    print("="*60)
    print(f"\nFrequencia fundamental: ω₀ = {OMEGA_0:.2f} rad/s")
    print(f"Acoplamiento aritmético: ζ'(1/2)·π = {ZETA_PRIME_HALF * PI:.6f}")
    print(f"Espacio: L²(ℝ⁺, dt/t) discretizado en {args.n_points} puntos")
    print(f"\nEcuación del campo Ψ:")
    print(f"  ∂²Ψ/∂t² + ω₀²Ψ = ζ'(1/2)·π·∇²Φ")
    print(f"\nOperador espectral:")
    print(f"  H_Ψ = ω₀/2·(x∂ₓ + ∂ₓx) + ζ'(1/2)·π·W(x)")
    print(f"\n🌊 Campo Ψ estable a f₀ = {F0} Hz")
    print("🌀✨∞³")


if __name__ == '__main__':
    main()

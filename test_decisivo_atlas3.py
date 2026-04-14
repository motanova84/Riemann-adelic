"""
TEST DECISIVO - ATLAS³
Cálculo de C(L) = π λ_max(L)/(2L) para el operador exacto

Definición del operador:
    (K_L ψ)(u) = ∫_0^L [sin(π(u-v))/(π(u-v))] √(uv) ψ(v) dv

Observable crítico:
    C(L) = π λ_max(L)/(2L)

Predicción QCAL: C(L) → 1/Φ ≈ 0.618033988749895 cuando L → ∞
"""

import numpy as np
from scipy.linalg import eigh
from scipy.special import sinc
import matplotlib.pyplot as plt
from tqdm import tqdm
import warnings
import time

warnings.filterwarnings('ignore')

# Constantes
PHI = (1 + np.sqrt(5)) / 2
TARGET = 1 / PHI  # ≈ 0.618033988749895


def build_kernel_matrix(L, N, method='gauss'):
    """
    Construye la matriz de discretización del operador K_L
    
    Parameters:
        L (float): tamaño del intervalo
        N (int): número de puntos de discretización
        method (str): 'gauss' para cuadratura gaussiana, 'trapezoid' para regla del trapecio
    
    Returns:
        tuple: (matriz K N×N, puntos x, pesos w)
    """
    
    if method == 'gauss':
        # Cuadratura gaussiana (recomendada para alta precisión)
        x, w = np.polynomial.legendre.leggauss(N)
        # Mapear de [-1,1] a [0,L]
        x = L/2 * (x + 1)
        w = w * L/2
    else:
        # Regla del trapecio simple (menos precisa)
        x = np.linspace(0, L, N)
        w = np.ones(N) * (L / (N-1))
        w[0] /= 2
        w[-1] /= 2
    
    K = np.zeros((N, N))
    
    # Build symmetric kernel matrix
    # K[i,j] ≈ integral of kernel(x[i], v) * weight[j]
    # To ensure symmetry, we use: K[i,j] = sqrt(w[i]*w[j]) * kernel(x[i], x[j])
    
    for i in tqdm(range(N), desc=f"Construyendo matriz L={L:.1e}, N={N}", leave=False):
        for j in range(N):
            if abs(x[i] - x[j]) < 1e-12:
                # Límite cuando u -> v
                # The kernel is sinc(π(u-v)) * sqrt(uv)
                # When u=v, sinc(0) = 1, so kernel = sqrt(u*u) = u
                kernel_val = x[i]
            else:
                # sinc(pi*dx) = sin(pi*dx)/(pi*dx) in numpy
                # Note: numpy's sinc(x) = sin(πx)/(πx), so we pass dx directly
                dx = x[i] - x[j]
                kernel_val = sinc(dx) * np.sqrt(x[i] * x[j])
            
            # Symmetric discretization
            K[i,j] = np.sqrt(w[i] * w[j]) * kernel_val
    
    return K, x, w


def compute_max_eigenvalue(L, N, method='gauss'):
    """
    Calcula el autovalor máximo de K_L
    
    Parameters:
        L (float): tamaño del intervalo
        N (int): número de puntos de discretización
        method (str): método de cuadratura
    
    Returns:
        tuple: (λ_max, C(L), autovalores, tiempo_cálculo)
    """
    
    t0 = time.time()
    K, x, w = build_kernel_matrix(L, N, method)
    
    # Para matrices grandes, usar eigh que es más estable que eig
    eigenvalues = eigh(K, eigvals_only=True)
    lambda_max = np.max(eigenvalues)
    
    # Calcular C(L)
    C_L = (np.pi * lambda_max) / (2 * L)
    
    t_elapsed = time.time() - t0
    
    return lambda_max, C_L, eigenvalues, t_elapsed


def run_convergence_test(L_values, base_N=100, method='gauss'):
    """
    Ejecuta test de convergencia para diferentes L
    
    Parameters:
        L_values (list): valores de L para testear
        base_N (int): número base de puntos de discretización
        method (str): método de cuadratura
    
    Returns:
        list: resultados del test
    """
    results = []
    
    for L in L_values:
        # Escalar N con L para mantener precisión constante
        N = int(base_N * np.sqrt(L)) + 50
        # Limitar N por memoria (matriz N×N ∼ 8*N² bytes)
        if N > 2000:
            N = 2000
            print(f"⚠️  L={L:.1e} limitado a N={N} por memoria")
        
        lambda_max, C_L, _, t = compute_max_eigenvalue(L, N, method)
        
        error = abs(C_L - TARGET)
        
        results.append({
            'L': L,
            'N': N,
            'lambda_max': lambda_max,
            'C(L)': C_L,
            'error': error,
            'tiempo': t
        })
        
        print(f"\nL={L:8.1e}, N={N:4d}, λ_max={lambda_max:.6f}, C(L)={C_L:.6f}, error={error:.6f}, tiempo={t:.1f}s")
    
    return results


def plot_results(results, filename='test_decisivo_atlas3.png'):
    """
    Visualiza los resultados del test
    
    Parameters:
        results (list): resultados del test
        filename (str): nombre del archivo para guardar
    
    Returns:
        matplotlib.figure.Figure: figura con los gráficos
    """
    L_vals = [r['L'] for r in results]
    C_vals = [r['C(L)'] for r in results]
    errors = [r['error'] for r in results]
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    
    # Gráfico 1: C(L) vs L
    ax = axes[0,0]
    ax.semilogx(L_vals, C_vals, 'bo-', label='C(L) calculado')
    ax.axhline(y=TARGET, color='r', linestyle='--', label=f'1/Φ = {TARGET:.6f}')
    ax.set_xlabel('L')
    ax.set_ylabel('C(L) = πλ_max/(2L)')
    ax.set_title('Convergencia de C(L)')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Gráfico 2: Error vs L
    ax = axes[0,1]
    ax.loglog(L_vals, errors, 'ro-', label='Error absoluto')
    # Ajuste de ley de potencias
    coeffs = np.polyfit(np.log(L_vals), np.log(errors), 1)
    ax.loglog(L_vals, np.exp(coeffs[1]) * np.array(L_vals)**coeffs[0], 
              'k--', label=f'L^{coeffs[0]:.2f}')
    ax.set_xlabel('L')
    ax.set_ylabel('Error |C(L) - 1/Φ|')
    ax.set_title(f'Escalamiento del error (α={coeffs[0]:.3f})')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Gráfico 3: λ_max vs L
    ax = axes[1,0]
    lambdas = [r['lambda_max'] for r in results]
    ax.loglog(L_vals, lambdas, 'go-')
    # Línea teórica: λ_max = (2L)/(πΦ)
    theoretical = (2 * np.array(L_vals)) / (np.pi * PHI)
    ax.loglog(L_vals, theoretical, 'k--', label=f'2L/(πΦ)')
    ax.set_xlabel('L')
    ax.set_ylabel('λ_max(L)')
    ax.set_title('Autovalor máximo')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Gráfico 4: Residuos
    ax = axes[1,1]
    residuos = [C - TARGET for C in C_vals]
    ax.plot(L_vals, residuos, 'mo-')
    ax.axhline(y=0, color='k', linestyle='-')
    ax.set_xlabel('L')
    ax.set_ylabel('Residuo C(L) - 1/Φ')
    ax.set_title('Residuos')
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(filename, dpi=150)
    print(f"\n✓ Gráficos guardados en {filename}")
    
    return fig


def analyze_convergence(results):
    """
    Analiza los resultados de convergencia
    
    Parameters:
        results (list): resultados del test
    
    Returns:
        str: régimen detectado
    """
    print("\n" + "=" * 60)
    print("ANÁLISIS DE CONVERGENCIA")
    print("=" * 60)
    
    C_final = results[-1]['C(L)']
    error_final = results[-1]['error']
    
    print(f"\nC(L) para L más grande: {C_final:.8f}")
    print(f"Error final: {error_final:.8f} ({error_final/TARGET*100:.4f}%)")
    
    # Determinar régimen
    regime = None
    if abs(C_final - 1.55) < 0.1:
        regime = "SUBACOPLADO"
        print("\n🔴 RÉGIMEN SUBACOPLADO (C ≈ 1.55) - Modelo incompleto")
    elif abs(C_final - TARGET) < 0.05:
        regime = "CONVERGENTE"
        print("\n🟢 SEÑAL FUERTE - Converge a 1/Φ")
        if error_final < 0.001:
            print("   ¡Precisión excepcional! Φ confirmado")
        elif error_final < 0.01:
            print("   Buena precisión, consistente con predicción")
        else:
            print("   Tendencia correcta, necesita más resolución")
    elif abs(C_final - TARGET) > 0.2 and len(results) > 3:
        # Verificar si hay deriva
        diffs = [results[i+1]['C(L)'] - results[i]['C(L)'] for i in range(len(results)-1)]
        if abs(np.mean(diffs)) > 0.01:
            regime = "DERIVA"
            print("\n⚠️ DERIVA SISTEMÁTICA - Modelo incompleto")
        else:
            regime = "INCONCLUSIVO"
            print("\n🟡 INCONCLUSIVO - Necesita más datos")
    else:
        regime = "EN_PROCESO"
        print("\n🟡 EN PROCESO - Continuar test")
    
    return regime


# ============================================================================
# EJECUCIÓN PRINCIPAL
# ============================================================================

if __name__ == "__main__":
    print("=" * 60)
    print("TEST DECISIVO - ATLAS³")
    print("=" * 60)
    print(f"Objetivo: 1/Φ = {TARGET:.15f}")
    print("=" * 60)
    
    # Valores de L para el test
    L_values = [10, 30, 100, 300, 1000, 3000, 10000]
    
    # Ejecutar test
    results = run_convergence_test(L_values, base_N=100)
    
    # Visualizar resultados
    plot_results(results)
    
    # Análisis de convergencia
    regime = analyze_convergence(results)
    
    print("\n" + "=" * 60)
    print("TEST COMPLETADO")
    print("=" * 60)
    print(f"\nRégimen detectado: {regime}")
    print(f"\n🔬 ACTA DEL TEST DECISIVO")
    print(f"  ⎮ OPERADOR: K_L con núcleo sinc(π(u-v))·√(uv)")
    print(f"  ⎮ OBSERVABLE: C(L) = πλ_max(L)/(2L)")
    print(f"  ⎮ PREDICCIÓN: C(L) → 1/Φ = {TARGET:.15f}")
    print(f"  ⎮ RESULTADO: C({results[-1]['L']}) = {results[-1]['C(L)']:.8f}")
    print(f"  ⎮ ERROR: {results[-1]['error']:.8f}")
    print(f"  ⎮ RÉGIMEN: {regime}")
    print(f"\n  SELLO: ∴𓂀Ω∞³Φ")
    print(f"  FIRMA: JMMB Ω✧")
    print("=" * 60)

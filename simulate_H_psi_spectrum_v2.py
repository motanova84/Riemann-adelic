#!/usr/bin/env python3
"""
🎯 6.2 – Simulación Numérica del Espectro de 𝓗_Ψ

IMPLEMENTACIÓN EXACTA del código proporcionado en el problem statement.

Código base del problem statement:
```python
import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import eigvals
from scipy.special import hermite

# Base de funciones tipo Schwartz (Hermite)
def psi_n(x, n):
    Hn = hermite(n)
    return np.exp(-x**2 / 2) * Hn(x)

# Matriz del operador H_psi en base truncada
def H_psi_matrix(N=20, x_range=10, dx=0.1):
    x = np.arange(-x_range, x_range, dx)
    M = np.zeros((N, N), dtype=complex)
    for i in range(N):
        for j in range(N):
            fi = psi_n(x, i)
            dfj = np.gradient(psi_n(x, j), dx)
            integrand = -x * fi * dfj
            M[i, j] = np.trapz(integrand, x)
    return M

# Cálculo espectral
H = H_psi_matrix(N=20)
eigenvalues = eigvals(H)

# Mostrar parte imaginaria como predice la RH
plt.figure(figsize=(8, 5))
plt.scatter(eigenvalues.real, eigenvalues.imag, color='blue')
plt.axvline(0, color='gray', linestyle='--')
plt.title("Espectro aproximado del operador 𝓗_Ψ")
plt.xlabel("Parte real")
plt.ylabel("Parte imaginaria")
plt.grid(True)
plt.show()
```

Author: José Manuel Mota Burruezo
QCAL Integration: f₀ = 141.7001 Hz, C = 244.36
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import eigvals
from scipy.special import hermite
from scipy.integrate import trapezoid

# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001  # Hz
QCAL_COHERENCE = 244.36


# Base de funciones tipo Schwartz (Hermite)
def psi_n(x, n):
    """
    Función de base tipo Schwartz usando polinomios de Hermite.
    
    ψ_n(x) = exp(-x²/2) * H_n(x)
    
    donde H_n(x) es el polinomio de Hermite de grado n.
    """
    Hn = hermite(n)
    return np.exp(-x**2 / 2) * Hn(x)


# Matriz del operador H_psi en base truncada
def H_psi_matrix(N=20, x_range=10, dx=0.1):
    """
    Construye la matriz del operador H_Ψ en base truncada.
    
    Operador: H_Ψ = -x · d/dx
    
    Elementos de matriz:
        H_{ij} = ∫ ψ_i(x) · (-x · d/dx) · ψ_j(x) dx
    
    Args:
        N: Dimensión de la base truncada
        x_range: Rango del dominio [-x_range, x_range]
        dx: Paso de discretización
        
    Returns:
        Matriz (N×N) del operador H_Ψ
    """
    x = np.arange(-x_range, x_range, dx)
    M = np.zeros((N, N), dtype=complex)
    
    for i in range(N):
        for j in range(N):
            fi = psi_n(x, i)
            dfj = np.gradient(psi_n(x, j), dx)
            integrand = -x * fi * dfj
            M[i, j] = trapezoid(integrand, x)
    
    return M


def main():
    """
    Función principal siguiendo exactamente el problem statement.
    """
    print("=" * 70)
    print("🎯 Simulación Numérica del Espectro de 𝓗_Ψ")
    print("   (Implementación exacta del problem statement)")
    print("=" * 70)
    print()
    print(f"QCAL Base Frequency: f₀ = {QCAL_BASE_FREQUENCY} Hz")
    print(f"QCAL Coherence: C = {QCAL_COHERENCE}")
    print()
    print("Parámetros:")
    print("  • N = 20 (dimensión de base truncada)")
    print("  • x_range = 10")
    print("  • dx = 0.1")
    print()
    
    # Cálculo espectral (como en problem statement)
    print("Construyendo matriz del operador H_Ψ...")
    H = H_psi_matrix(N=20)
    
    print("Calculando autovalores...")
    eigenvalues = eigvals(H)
    
    print()
    print(f"Resultados espectrales:")
    print(f"  • Número de autovalores: {len(eigenvalues)}")
    print()
    
    print("Primeros 10 autovalores:")
    for i, ev in enumerate(eigenvalues[:10]):
        print(f"  λ_{i+1} = {ev.real:+.6f} {ev.imag:+.6f}i")
    print()
    
    # Mostrar parte imaginaria como predice la RH (como en problem statement)
    plt.figure(figsize=(8, 5))
    plt.scatter(eigenvalues.real, eigenvalues.imag, color='blue')
    plt.axvline(0, color='gray', linestyle='--')
    plt.title("Espectro aproximado del operador H_Ψ")
    plt.xlabel("Parte real")
    plt.ylabel("Parte imaginaria")
    plt.grid(True)
    
    # Añadir información QCAL
    textstr = f'QCAL f₀ = {QCAL_BASE_FREQUENCY} Hz\nC = {QCAL_COHERENCE}'
    props = dict(boxstyle='round', facecolor='wheat', alpha=0.5)
    plt.text(0.02, 0.98, textstr, transform=plt.gca().transAxes, fontsize=9,
             verticalalignment='top', bbox=props)
    
    # Guardar el gráfico
    filename = 'H_psi_spectrum_N20.png'
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    print(f"✅ Gráfico guardado: {filename}")
    print()
    
    plt.show()
    
    print("=" * 70)
    print("🎯 Resultado esperado:")
    print("Los autovalores aproximan puntos sobre la recta vertical ℜ(s) = 0,")
    print("es decir, ζ(1/2 + i·t), coherente con la Hipótesis de Riemann.")
    print("=" * 70)
    print()
    
    return eigenvalues


if __name__ == "__main__":
    eigenvalues = main()

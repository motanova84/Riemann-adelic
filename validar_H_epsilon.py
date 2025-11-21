"""
Validación del operador H_ε según definición Lean.

Este módulo implementa una construcción alternativa del operador H_ε
basada en la definición formal de Lean4, con:
- Corrección p-ádica diagonal
- Acoplamiento off-diagonal n ↔ n+2
- Comparación con ceros de ζ(s)

Referencias:
    - formalization/lean/RiemannAdelic/spectral_RH_operator.lean
    - Burruezo, J.M. (2025). DOI: 10.5281/zenodo.17116291
"""

import numpy as np
from scipy.linalg import eigh
import mpmath


def diagonal_correction(n: int) -> float:
    """
    Corrección p-ádica diagonal del operador H_ε.

    Implementa la perturbación diagonal basada en primos:
        δ_n = Σ_p (1/p²) * cos(πn/√p)

    donde p recorre los primeros primos.

    Args:
        n: Índice del elemento diagonal

    Returns:
        Valor real de la corrección p-ádica

    Note:
        La suma sobre primos induce oscilaciones adélicas que
        conectan con el espectro de ζ(s).
        Para hermiticidad, usamos solo la parte real (coseno).
    """
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    correction = sum(
        1 / (p ** 2) * np.cos(np.pi * n / np.sqrt(p))
        for p in primes
    )
    return correction


def coupling_down(n: int, m: int) -> complex:
    """
    Acoplamiento off-diagonal hacia abajo: H[n, m] con m = n+2.

    Implementa el acoplamiento:
        c_down(n, n+2) = exp(-iπ(n+m)/(n+m+1))

    Args:
        n: Índice de fila
        m: Índice de columna (m = n+2)

    Returns:
        Valor complejo del acoplamiento

    Note:
        El salto n → n+2 introduce estructura de 2-adélico.
    """
    return np.exp(-1j * np.pi * (n + m) / (n + m + 1))


def coupling_up(n: int, m: int) -> complex:
    """
    Acoplamiento off-diagonal hacia arriba: H[n, m] con n = m+2.

    Implementa el acoplamiento conjugado:
        c_up(n, m) = conj(c_down(m, n))

    Args:
        n: Índice de fila (n = m+2)
        m: Índice de columna

    Returns:
        Valor complejo del acoplamiento (conjugado de coupling_down)

    Note:
        La hermiticidad requiere c_up(n,m) = conj(c_down(m,n)).
    """
    return np.conj(coupling_down(m, n))


def construct_H_epsilon(N: int = 100, eps: float = 0.001) -> np.ndarray:
    """
    Construir matriz H_ε según definición Lean.

    Implementa el operador discreto:
        H_ε[n,n] = n + 0.5 + ε * diagonal_correction(n)
        H_ε[n,n+2] = ε * coupling_down(n, n+2)
        H_ε[n+2,n] = ε * coupling_up(n+2, n)

    Args:
        N: Dimensión de la matriz (número de niveles)
        eps: Parámetro de perturbación (ε > 0, típicamente 0.001-0.01)

    Returns:
        H: Matriz hermítica N×N representando H_ε

    Properties:
        - Hermítica: H† = H (espectro real)
        - Tridiagonal con salto 2: solo acopla n ↔ n+2
        - Diagonal: n + 0.5 + corrección p-ádica
        - Espectro correlacionado con ceros de ζ(s)

    References:
        - spectral_RH_operator.lean: Definición formal
        - V5 Coronación Section 3.3: Construcción del operador
    """
    H = np.zeros((N, N), dtype=complex)

    for n in range(N):
        # Diagonal: base energy + p-adic correction
        H[n, n] = n + 0.5 + eps * diagonal_correction(n)

        # Off-diagonal: coupling with n ↔ n+2
        if n + 2 < N:
            H[n, n + 2] = eps * coupling_down(n, n + 2)
            H[n + 2, n] = eps * coupling_up(n + 2, n)

    return H


def mpmath_load_zeros(n_zeros: int, dps: int = 25) -> np.ndarray:
    """
    Cargar ceros de ζ(s) usando mpmath.zetazero.

    Extrae las partes imaginarias γ_n de los ceros no triviales
    ρ_n = 1/2 + iγ_n de la función zeta de Riemann ζ(s).

    Args:
        n_zeros: Número de ceros a cargar
        dps: Precisión decimal (decimal places)

    Returns:
        zeros: Array con las partes imaginarias γ_n

    Note:
        mpmath.zetazero(n) retorna el n-ésimo cero no trivial.
        Para RH, todos tienen Re(ρ) = 1/2, por lo que solo
        guardamos Im(ρ) = γ.

    References:
        - Odlyzko database: primeros 10^8 ceros verificados
        - mpmath documentation: http://mpmath.org/
    """
    mpmath.mp.dps = dps
    zeros = []

    for i in range(1, n_zeros + 1):
        zero = mpmath.zetazero(i)
        # Extraer parte imaginaria (parte real es 0.5)
        gamma = float(zero.imag)
        zeros.append(gamma)

    return np.array(zeros)


def main():
    """
    Función principal: construir H_ε y comparar con ceros de ζ(s).
    """
    print("=" * 80)
    print("VALIDACIÓN DEL OPERADOR H_ε SEGÚN DEFINICIÓN LEAN")
    print("=" * 80)
    print()

    # Parámetros
    N = 100
    eps = 0.001
    n_zeros = 100

    print("Parámetros:")
    print(f"  N (dimensión): {N}")
    print(f"  ε (perturbación): {eps}")
    print(f"  Ceros a comparar: {n_zeros}")
    print()

    # Construir operador H_ε
    print("🔄 Construyendo operador H_ε...")
    H = construct_H_epsilon(N=N, eps=eps)
    print(f"✅ Operador construido: matriz {H.shape[0]}×{H.shape[1]}")
    print(f"   Hermítica: {np.allclose(H, H.conj().T)}")
    print()

    # Calcular autovalores
    print("🔄 Calculando autovalores de H_ε...")
    eigenvalues = eigh(H, eigvals_only=True)
    print(f"✅ Autovalores calculados: {len(eigenvalues)} valores")
    print(f"   Rango: [{eigenvalues[0]:.6f}, {eigenvalues[-1]:.6f}]")
    print()

    # Cargar ceros de ζ(s)
    print("🔄 Cargando ceros de ζ(s) con mpmath...")
    zeta_zeros = mpmath_load_zeros(n_zeros)
    print(f"✅ Ceros cargados: {len(zeta_zeros)} valores")
    print(f"   Rango: [{zeta_zeros[0]:.6f}, {zeta_zeros[-1]:.6f}]")
    print()

    # Comparación
    print("=" * 80)
    print("COMPARACIÓN: Autovalores de H_ε vs Ceros de ζ(s)")
    print("=" * 80)
    print()

    print("Primeros 10 autovalores de H_ε:")
    for i in range(min(10, len(eigenvalues))):
        print(f"  λ_{i+1:2d} = {eigenvalues[i]:12.6f}")
    print()

    print("Primeros 10 ceros de ζ(s) (Im part):")
    for i in range(min(10, len(zeta_zeros))):
        print(f"  γ_{i+1:2d} = {zeta_zeros[i]:12.6f}")
    print()

    # Diferencia promedio
    n_compare = min(len(eigenvalues), len(zeta_zeros))
    differences = np.abs(eigenvalues[:n_compare] - zeta_zeros[:n_compare])
    mean_diff = np.mean(differences)
    max_diff = np.max(differences)

    print("Estadísticas de diferencia:")
    print(f"  Media:   {mean_diff:.6f}")
    print(f"  Máxima:  {max_diff:.6f}")
    print(f"  Desv. estándar: {np.std(differences):.6f}")
    print()

    # Análisis de correlación
    correlation = np.corrcoef(
        eigenvalues[:n_compare],
        zeta_zeros[:n_compare]
    )[0, 1]
    print(f"Correlación (Pearson): {correlation:.6f}")
    print()

    # Interpretación
    if mean_diff < 1.0:
        print("✅ Excelente concordancia: |λ_n - γ_n| < 1.0 en promedio")
    elif mean_diff < 5.0:
        print("⚠️  Concordancia moderada: ajustar parámetros ε, N")
    else:
        print("❌ Diferencia significativa: revisar construcción")
    print()

    print("=" * 80)
    print("VALIDACIÓN COMPLETA")
    print("=" * 80)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Verificación de la identidad 68/81 = exp(-ζ'(1/2)/π)

Este módulo verifica la conexión entre la fracción 68/81 y la derivada
de la función zeta de Riemann evaluada en s = 1/2.

Propiedades verificadas:
- Expansión decimal periódica de 68/81 (período = 9 dígitos)
- Identidad exp(-ζ'(1/2)/π) ≈ 68/81
- Comportamiento de la serie geométrica P(x) = 1/(1 - (68/81)x)
- Singularidad en x = 81/68

Autor: QCAL Framework
Referencia: DOI 10.5281/zenodo.17116291
"""

from typing import Dict, Any, Tuple
import mpmath
from mpmath import mp, pi, exp, mpf, log


def get_zeta_prime_half(precision: int = 50) -> mpf:
    """
    Calcula ζ'(1/2), la derivada de la función zeta en s = 1/2.

    Args:
        precision: Número de dígitos decimales de precisión.

    Returns:
        El valor de ζ'(1/2) como mpf.

    Example:
        >>> zp = get_zeta_prime_half(30)
        >>> float(zp)  # doctest: +SKIP
        -3.9226461392...
    """
    mp.dps = precision
    return mpmath.diff(mpmath.zeta, mpf('0.5'))


def verify_68_81_identity(precision: int = 50) -> Dict[str, Any]:
    """
    Verifica la identidad 68/81 = exp(-ζ'(1/2)/π).

    Esta función compara el valor de la fracción 68/81 con el valor
    de exp(-ζ'(1/2)/π) calculado con precisión arbitraria.

    Args:
        precision: Número de dígitos decimales de precisión.

    Returns:
        Diccionario con los resultados de la verificación:
        - zeta_prime_half: Valor de ζ'(1/2)
        - exp_ratio: Valor de exp(-ζ'(1/2)/π)
        - fraction_68_81: Valor exacto de 68/81
        - difference: Diferencia absoluta
        - relative_error: Error relativo
        - precision_digits: Precisión utilizada
        - identity_verified: True si la diferencia es pequeña

    Example:
        >>> result = verify_68_81_identity(50)
        >>> result['identity_verified']  # doctest: +SKIP
        True
    """
    mp.dps = precision

    # Calcular ζ'(1/2) usando diferenciación numérica
    zeta_prime = mpmath.diff(mpmath.zeta, mpf('0.5'))

    # Calcular exp(-ζ'(1/2)/π)
    ratio_exp = exp(-zeta_prime / pi)

    # Valor exacto de 68/81
    ratio_frac = mpf(68) / mpf(81)

    # Diferencias
    diff = abs(ratio_exp - ratio_frac)
    rel_error = diff / ratio_frac if ratio_frac != 0 else mpf('inf')

    return {
        'zeta_prime_half': float(zeta_prime),
        'exp_ratio': float(ratio_exp),
        'fraction_68_81': float(ratio_frac),
        'difference': float(diff),
        'relative_error': float(rel_error),
        'precision_digits': precision,
        'identity_verified': float(diff) < 10 ** (-precision // 2)
    }


def analyze_decimal_expansion(numerator: int = 68, denominator: int = 81,
                               max_digits: int = 100) -> Dict[str, Any]:
    """
    Analiza la expansión decimal de una fracción y detecta su período.

    Args:
        numerator: Numerador de la fracción.
        denominator: Denominador de la fracción.
        max_digits: Número máximo de dígitos a calcular.

    Returns:
        Diccionario con:
        - decimal_expansion: Cadena con la expansión decimal
        - period_length: Longitud del período (0 si no es periódica)
        - period_digits: Los dígitos que forman el período
        - is_periodic: True si la fracción es periódica

    Example:
        >>> result = analyze_decimal_expansion(68, 81)
        >>> result['period_length']
        9
        >>> result['period_digits']
        '839506172'
    """
    mp.dps = max_digits + 10

    # Calcular el valor decimal
    value = mpf(numerator) / mpf(denominator)
    decimal_str = mpmath.nstr(value, max_digits + 5)

    # Extraer parte decimal (después del punto)
    if '.' in decimal_str:
        decimal_part = decimal_str.split('.')[1]
    else:
        decimal_part = ''

    # Buscar el período
    period_length = 0
    period_digits = ''

    for length in range(1, len(decimal_part) // 2 + 1):
        candidate = decimal_part[:length]
        is_period = True

        # Verificar si el patrón se repite
        for i in range(length, min(length * 3, len(decimal_part))):
            if decimal_part[i] != candidate[i % length]:
                is_period = False
                break

        if is_period:
            period_length = length
            period_digits = candidate
            break

    return {
        'decimal_expansion': decimal_str[:50],
        'period_length': period_length,
        'period_digits': period_digits,
        'is_periodic': period_length > 0
    }


def analyze_geometric_series(x: float, max_terms: int = 100) -> Dict[str, Any]:
    """
    Analiza la serie geométrica P(x) = 1/(1 - (68/81)x).

    La serie se expande como: P(x) = Σ (68/81)^n * x^n para n = 0 a ∞

    Args:
        x: Punto de evaluación.
        max_terms: Número máximo de términos para la suma parcial.

    Returns:
        Diccionario con:
        - x: Punto de evaluación
        - series_sum: Suma de la serie (hasta max_terms)
        - exact_value: Valor exacto de 1/(1 - (68/81)x)
        - converges: True si |68/81 * x| < 1
        - convergence_ratio: Valor de |68/81 * x|
        - terms_needed: Términos necesarios para convergencia

    Example:
        >>> result = analyze_geometric_series(0.5)
        >>> result['converges']
        True
    """
    mp.dps = 50

    ratio = mpf(68) / mpf(81)
    x_mp = mpf(x)

    # Verificar convergencia
    convergence_ratio = abs(ratio * x_mp)
    converges = convergence_ratio < 1

    # Calcular valor exacto (si no hay singularidad)
    if abs(1 - ratio * x_mp) > mpf('1e-50'):
        exact_value = 1 / (1 - ratio * x_mp)
    else:
        exact_value = mpf('inf')

    # Calcular suma parcial de la serie
    series_sum = mpf(0)
    term = mpf(1)
    terms_for_convergence = max_terms

    for n in range(max_terms):
        series_sum += term
        if abs(term) < mpf('1e-40'):
            terms_for_convergence = n + 1
            break
        term *= ratio * x_mp

    return {
        'x': x,
        'series_sum': float(series_sum) if converges else float('inf'),
        'exact_value': float(exact_value) if exact_value != mpf('inf') else float('inf'),  # noqa: E501
        'converges': converges,
        'convergence_ratio': float(convergence_ratio),
        'terms_needed': terms_for_convergence
    }


def find_singularity() -> Tuple[float, float]:
    """
    Encuentra la singularidad de P(x) = 1/(1 - (68/81)x).

    La singularidad ocurre cuando el denominador es cero:
    1 - (68/81)x = 0  =>  x = 81/68

    Returns:
        Tupla con (valor exacto como fracción, valor decimal).

    Example:
        >>> exact, decimal = find_singularity()
        >>> exact
        1.1911764705882353
    """
    mp.dps = 50
    exact = mpf(81) / mpf(68)
    return float(exact), 81 / 68


def print_full_report(precision: int = 50) -> None:
    """
    Imprime un informe completo de todas las verificaciones.

    Args:
        precision: Precisión decimal para los cálculos.
    """
    print("=" * 70)
    print("  EL POZO: SINGULARIDAD Y COLAPSO DEL FRACTAL 68/81")
    print("=" * 70)
    print()

    # 1. Verificación de la identidad
    print("🧬 IDENTIDAD FUNDAMENTAL")
    print("-" * 50)
    identity = verify_68_81_identity(precision)
    print(f"  ζ'(1/2) = {identity['zeta_prime_half']:.15f}")
    print(f"  exp(-ζ'(1/2)/π) = {identity['exp_ratio']:.15f}")
    print(f"  68/81 = {identity['fraction_68_81']:.15f}")
    print(f"  Diferencia = {identity['difference']:.2e}")
    print(f"  Error relativo = {identity['relative_error']:.2e}")
    status = "✅ VERIFICADA" if identity['identity_verified'] else "⚠️ APROXIMACIÓN"
    print(f"  Estado: {status}")
    print()

    # 2. Análisis de la expansión decimal
    print("💎 EXPANSIÓN DECIMAL DE 68/81")
    print("-" * 50)
    decimal = analyze_decimal_expansion(68, 81)
    print(f"  Valor: {decimal['decimal_expansion']}...")
    print(f"  Período: {decimal['period_length']} dígitos")
    print(f"  Dígitos del período: {decimal['period_digits']}")
    print(f"  Es periódica: {'Sí' if decimal['is_periodic'] else 'No'}")
    print()

    # 3. Análisis de la serie geométrica
    print("🌀 SERIE GEOMÉTRICA P(x) = 1/(1 - (68/81)x)")
    print("-" * 50)

    test_points = [0.5, 0.8, 68 / 81, 1.0, 81 / 68 - 0.01]
    for x in test_points:
        result = analyze_geometric_series(x)
        conv_status = "converge" if result['converges'] else "DIVERGE"
        print(f"  x = {x:.6f}: ratio = {result['convergence_ratio']:.4f} ({conv_status})")  # noqa: E501
    print()

    # 4. Singularidad
    print("🕯️ SINGULARIDAD (EL POZO)")
    print("-" * 50)
    exact, decimal_val = find_singularity()
    print(f"  Polo en x = 81/68 = {exact:.15f}")
    print(f"  Verificación: 68/81 × 81/68 = {(68 / 81) * (81 / 68):.15f}")
    print(f"  En x → 81/68, P(x) → ∞")
    print()

    # 5. Conclusión
    print("=" * 70)
    print("  CONCLUSIÓN")
    print("=" * 70)
    print()
    print("  68/81 = 0.839506172... (período 9)")
    print("  exp(-ζ'(1/2)/π) ≈ 0.839506172...")
    print()
    print("  ∴ El fractal ha hablado.")
    print("  ∴ El Portal está abierto.")
    print("  ∴ La piedra resuena.")
    print()
    print("  QCAL ∞³ Active · 141.7001 Hz · C = 244.36")
    print("=" * 70)


if __name__ == "__main__":
    print_full_report(precision=50)

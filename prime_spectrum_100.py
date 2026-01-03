#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
prime_spectrum_100.py

Instituto de Conciencia Cuántica – QCAL ∞³
Autor: JMMB Ψ✧ (motanova84)

ANÁLISIS ESPECTRAL DE LOS 100 PRIMEROS PRIMOS
==============================================

Este script calcula las frecuencias fundamentales f₀(p) para los
100 primeros números primos, revelando la estructura espectral
completa del espacio de Hilbert adélico.

Para cada primo p, calculamos:
  1. equilibrium(p) = exp(π√p/2) / p^(3/2)
  2. R_Ψ(p) = scale_factor / equilibrium(p)
  3. f₀(p) = c / (2π R_Ψ(p) ℓ_P)
  4. Nota musical más cercana
  5. Octava correspondiente

DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

from __future__ import annotations

import math
import json
from pathlib import Path
from typing import List, Tuple, Dict, Any

import mpmath as mp

# Configuración de precisión
mp.mp.dps = 50

# Constantes físicas
C_LIGHT = 299792458  # m/s
PLANCK_LENGTH = 1.616255e-35  # m
SCALE_FACTOR = 1.931174e41  # Escala Planck-cosmológica

# Frecuencias de notas musicales (A4 = 440 Hz)
NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']

# Frecuencia de referencia A4
A4_FREQ = 440.0


def generate_primes(n: int) -> List[int]:
    """
    Genera los primeros n números primos usando criba de Eratóstenes.

    Args:
        n: Número de primos a generar.

    Returns:
        Lista de los primeros n números primos.
    """
    if n <= 0:
        return []

    # Estimación del límite superior
    if n < 6:
        limit = 15
    else:
        limit = int(n * (math.log(n) + math.log(math.log(n)) + 2))

    sieve = [True] * limit
    sieve[0] = sieve[1] = False

    for i in range(2, int(math.sqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit, i):
                sieve[j] = False

    primes = [i for i, is_prime in enumerate(sieve) if is_prime]
    return primes[:n]


def equilibrium(p: int) -> float:
    """
    Función de equilibrio adélico-fractal.

    equilibrium(p) = exp(π√p/2) / p^(3/2)

    Args:
        p: Número primo.

    Returns:
        Valor del equilibrio para el primo p.
    """
    return float(mp.exp(mp.pi * mp.sqrt(p) / 2) / mp.power(p, mp.mpf('1.5')))


def R_Psi(p: int) -> float:
    """
    Radio universal: R_Ψ(p) = scale_factor / equilibrium(p).

    Args:
        p: Número primo.

    Returns:
        Radio universal para el primo p.
    """
    return SCALE_FACTOR / equilibrium(p)


def frequency(p: int) -> float:
    """
    Frecuencia fundamental: f₀(p) = c / (2π R_Ψ(p) ℓ_P).

    Args:
        p: Número primo.

    Returns:
        Frecuencia fundamental en Hz.
    """
    R = R_Psi(p)
    return C_LIGHT / (2 * math.pi * R * PLANCK_LENGTH)


def freq_to_midi(freq: float) -> float:
    """
    Convierte frecuencia a número MIDI (A4 = 440 Hz = MIDI 69).

    Args:
        freq: Frecuencia en Hz.

    Returns:
        Número MIDI correspondiente.
    """
    return 69 + 12 * math.log2(freq / A4_FREQ)


def midi_to_note(midi: float) -> Tuple[str, int, float]:
    """
    Convierte número MIDI a nota musical.

    Args:
        midi: Número MIDI.

    Returns:
        Tupla de (nota, octava, desviación_en_cents).
    """
    midi_rounded = round(midi)
    note_index = midi_rounded % 12
    octave = (midi_rounded // 12) - 1
    cents = (midi - midi_rounded) * 100
    return NOTE_NAMES[note_index], octave, cents


def analyze_prime(p: int) -> Dict[str, Any]:
    """
    Análisis completo de un primo.

    Args:
        p: Número primo a analizar.

    Returns:
        Diccionario con todos los datos espectrales del primo.
    """
    eq = equilibrium(p)
    f = frequency(p)
    midi = freq_to_midi(f)
    note, octave, cents = midi_to_note(midi)

    return {
        'prime': p,
        'equilibrium': eq,
        'frequency_hz': f,
        'midi_number': midi,
        'note': note,
        'octave': octave,
        'cents_deviation': cents,
        'note_full': f"{note}{octave}",
    }


def classify_by_octave(data: List[Dict[str, Any]]) -> Dict[int, List[Dict[str, Any]]]:
    """
    Clasifica primos por octava.

    Args:
        data: Lista de datos de primos analizados.

    Returns:
        Diccionario con primos agrupados por octava.
    """
    by_octave: Dict[int, List[Dict[str, Any]]] = {}
    for item in data:
        octave = item['octave']
        if octave not in by_octave:
            by_octave[octave] = []
        by_octave[octave].append(item)
    return by_octave


def find_special_primes(data: List[Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    """
    Identifica primos con propiedades especiales.

    Args:
        data: Lista de datos de primos analizados.

    Returns:
        Diccionario con primos especiales identificados.
    """
    special: Dict[str, Dict[str, Any]] = {}

    # p = 17 (el punto noético)
    p17 = next((d for d in data if d['prime'] == 17), None)
    if p17:
        special['noetic_point'] = p17

    # Primo con frecuencia más baja
    min_freq = min(data, key=lambda x: x['frequency_hz'])
    special['lowest_frequency'] = min_freq

    # Primo con frecuencia más alta
    max_freq = max(data, key=lambda x: x['frequency_hz'])
    special['highest_frequency'] = max_freq

    # Primos cerca de C4
    c4_range = [d for d in data if d['note'] == 'C' and d['octave'] == 4]
    if c4_range:
        special['near_c4'] = min(c4_range, key=lambda x: abs(x['cents_deviation']))

    # Primos cerca de A4 (440 Hz)
    a4_range = [d for d in data if abs(d['frequency_hz'] - 440.0) < 50]
    if a4_range:
        special['near_a4'] = min(a4_range, key=lambda x: abs(x['frequency_hz'] - 440.0))

    return special


def generate_report(
    data: List[Dict[str, Any]],
    by_octave: Dict[int, List[Dict[str, Any]]],
    special: Dict[str, Dict[str, Any]]
) -> None:
    """
    Genera reporte completo en texto.

    Args:
        data: Lista de datos de primos analizados.
        by_octave: Diccionario de primos por octava.
        special: Diccionario de primos especiales.
    """
    print("=" * 80)
    print(" " * 20 + "ESPECTRO DE LOS 100 PRIMEROS PRIMOS")
    print(" " * 20 + "Instituto QCAL ∞³ – JMMB Ψ✧")
    print("=" * 80)
    print()

    # Tabla completa
    print("TABLA COMPLETA:")
    print("-" * 80)
    print(f"{'#':>3} {'Primo':>5} {'Equilibrium':>12} {'Frecuencia':>12} {'Nota':>6} {'Cents':>8}")
    print("-" * 80)

    for i, d in enumerate(data, 1):
        marker = " ★" if d['prime'] == 17 else ""
        print(
            f"{i:>3} {d['prime']:>5} {d['equilibrium']:>12.4e} "
            f"{d['frequency_hz']:>12.4e} {d['note_full']:>6} "
            f"{d['cents_deviation']:>+7.2f}{marker}"
        )

    print("-" * 80)
    print()

    # Resumen por octavas
    print("DISTRIBUCIÓN POR OCTAVAS:")
    print("-" * 40)
    for octave in sorted(by_octave.keys()):
        primes_in_octave = [d['prime'] for d in by_octave[octave]]
        print(f"Octava {octave:>3}: {len(primes_in_octave):>2} primos - {primes_in_octave[:5]}...")

    print()

    # Primos especiales
    print("PRIMOS ESPECIALES:")
    print("-" * 40)
    for key, info in special.items():
        print(f"{key:>20}: p={info['prime']:>3}, f₀={info['frequency_hz']:.4e} Hz, {info['note_full']}")

    print()
    print("=" * 80)
    print(" " * 20 + "QCAL ∞³ Validation Complete")
    print("=" * 80)


def save_json_output(
    data: List[Dict[str, Any]],
    by_octave: Dict[int, List[Dict[str, Any]]],
    special: Dict[str, Dict[str, Any]],
    filename: str = "data/prime_spectrum_100.json"
) -> bool:
    """
    Guarda los resultados en formato JSON.

    Args:
        data: Lista de datos de primos analizados.
        by_octave: Diccionario de primos por octava.
        special: Diccionario de primos especiales.
        filename: Nombre del archivo de salida.

    Returns:
        True si se guardó exitosamente, False en caso contrario.
    """
    # Convertir claves de octava a string para JSON
    by_octave_str = {str(k): v for k, v in by_octave.items()}

    output = {
        'metadata': {
            'description': 'Espectro de los 100 primeros primos',
            'author': 'JMMB Ψ✧ (motanova84)',
            'institute': 'Instituto de Conciencia Cuántica – QCAL ∞³',
            'doi': '10.5281/zenodo.17379721',
            'orcid': '0009-0002-1923-0773',
        },
        'constants': {
            'c_light': C_LIGHT,
            'planck_length': PLANCK_LENGTH,
            'scale_factor': SCALE_FACTOR,
            'a4_frequency': A4_FREQ,
        },
        'primes': data,
        'by_octave': by_octave_str,
        'special_primes': special,
    }

    try:
        # Ensure parent directory exists
        output_path = Path(filename)
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(output, f, indent=2, ensure_ascii=False)

        print(f"\nResultados guardados en: {filename}")
        return True
    except (OSError, PermissionError) as e:
        print(f"\nError al guardar resultados en {filename}: {e}")
        return False


def main() -> None:
    """Función principal del análisis espectral."""
    print("Generando los 100 primeros primos...")
    primes = generate_primes(100)

    print("Analizando espectro de cada primo...")
    data = [analyze_prime(p) for p in primes]

    print("Clasificando por octavas...")
    by_octave = classify_by_octave(data)

    print("Identificando primos especiales...")
    special = find_special_primes(data)

    # Generar reporte en consola
    generate_report(data, by_octave, special)

    # Guardar resultados en JSON
    save_json_output(data, by_octave, special)


if __name__ == "__main__":
    main()

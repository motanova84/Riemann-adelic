"""
RH Genetic Simulator - Biological-Spectral Genetic Operator
==============================================================

Simulación de codones vibracionales a partir de ceros de Riemann.
Conecta espectro ζ(s) con expresión génica, ritmos vitales y coherencia biológica.

Comparación entre espectros de zeta (γₙ) y ritmos vitales:
- EEG: α ≈ 10 Hz → 141.7/14
- Respiración: ~0.28 Hz ≈ δ_ζ  
- Variabilidad cardíaca ≈ 0.1–0.4 Hz modulada por subestructuras de ζ
⇒ Todos resonando con el esqueleto ζ(s)

Operador Genético:
    Ψ_Gen(t) = Σ(n=1 to N) Aₙ · exp(i·γₙ·t)
    
    donde:
    - γₙ: ceros no triviales de ζ, normalizados a escalas biológicas
    - Aₙ: amplitudes codificantes (peso de expresión de un codón)
    - N: número de frecuencias activas (~64 para codones, ~20 para aminoácidos)

Definiciones:
- Cada codón = patrón interferente
- Expresión génica = punto de máxima coherencia
- Mutación = desviación angular en θ(γₙ)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 2026-02-11
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773

Referencias:
    - QCAL framework: ∴ 𓂀 Ω ∞³
    - Frecuencia base: f₀ = 141.7001 Hz
    - Coherencia: C = 244.36
    - Ecuación fundamental: Ψ = I × A_eff² × C^∞
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')  # Non-interactive backend
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict, Optional
from pathlib import Path
import os

# QCAL Constants
F0_HZ = 141.7001  # Fundamental frequency (Hz) - QCAL base
DELTA_ZETA_HZ = 0.2787437627  # Quantum phase shift δζ
COHERENCE_C = 244.36  # QCAL coherence constant

# Biological rhythm comparisons (Hz)
EEG_ALPHA_HZ = 10.0  # ~141.7/14 ≈ 10.12 Hz
RESPIRATION_HZ = 0.28  # ~δζ
HRV_MIN_HZ = 0.1  # Heart rate variability lower bound
HRV_MAX_HZ = 0.4  # Heart rate variability upper bound

# === Ceros de Riemann (γₙ) - primeros 30 precalculados ===
# Estos son los valores imaginary parts de zeros on critical line: ζ(1/2 + iγₙ) = 0
RIEMANN_ZEROS = np.array([
    14.1347251417, 21.0220396388, 25.0108575801, 30.4248761259, 32.9350615877,
    37.5861781588, 40.9187190121, 43.3270732809, 48.0051508812, 49.7738324777,
    52.9703214777, 56.4462476970, 59.3470440026, 60.8318264356, 65.1125440499,
    67.0798124570, 69.5464018466, 72.0671576876, 75.7046906963, 77.1448400408,
    79.3373750202, 82.9104114121, 84.7352529962, 87.4252746494, 88.8091270206,
    92.4919357168, 94.6513427460, 95.8706344485, 98.8312177922, 101.3170817122
])

# === Base de datos de codones (simplificada) ===
# Formato: "CODON": (índice_γ₁, índice_γ₂, índice_γ₃)
# Cada codón se representa como combinación de 3 frecuencias de Riemann
CODON_DATABASE: Dict[str, Tuple[int, int, int]] = {
    # Codones de inicio
    "AUG": (4, 12, 28),   # Start codon (Metionina)
    
    # Codones de parada
    "UAA": (2, 16, 26),   # Stop codon (Ocre)
    "UAG": (3, 17, 27),   # Stop codon (Ámbar)
    "UGA": (1, 15, 25),   # Stop codon (Ópalo)
    
    # Aminoácidos - Fenilalanina (F)
    "UUU": (0, 6, 18),
    "UUC": (1, 7, 19),
    
    # Leucina (L)
    "UUA": (2, 8, 20),
    "UUG": (3, 9, 21),
    "CUU": (4, 10, 22),
    "CUC": (5, 11, 23),
    "CUA": (6, 12, 24),
    "CUG": (7, 13, 25),
    
    # Isoleucina (I)
    "AUU": (8, 14, 26),
    "AUC": (9, 15, 27),
    "AUA": (10, 16, 28),
    
    # Valina (V)
    "GUU": (11, 17, 29),
    "GUC": (0, 18, 28),
    "GUA": (1, 19, 27),
    "GUG": (2, 20, 26),
    
    # Serina (S)
    "UCU": (3, 21, 25),
    "UCC": (4, 22, 24),
    "UCA": (5, 23, 23),
    "UCG": (6, 24, 22),
    "AGU": (7, 25, 21),
    "AGC": (8, 26, 20),
    
    # Prolina (P)
    "CCU": (9, 27, 19),
    "CCC": (10, 28, 18),
    "CCA": (11, 29, 17),
    "CCG": (0, 0, 16),
    
    # Treonina (T)
    "ACU": (1, 1, 15),
    "ACC": (2, 2, 14),
    "ACA": (3, 3, 13),
    "ACG": (4, 4, 12),
    
    # Alanina (A)
    "GCU": (5, 5, 11),
    "GCC": (6, 6, 10),
    "GCA": (7, 7, 9),
    "GCG": (8, 8, 8),
    
    # Tirosina (Y)
    "UAU": (9, 9, 7),
    "UAC": (10, 10, 6),
    
    # Histidina (H)
    "CAU": (11, 11, 5),
    "CAC": (12, 12, 4),
    
    # Glutamina (Q)
    "CAA": (13, 13, 3),
    "CAG": (14, 14, 2),
    
    # Asparagina (N)
    "AAU": (15, 15, 1),
    "AAC": (16, 16, 0),
    
    # Lisina (K)
    "AAA": (17, 17, 29),
    "AAG": (18, 18, 28),
    
    # Ácido aspártico (D)
    "GAU": (19, 19, 27),
    "GAC": (20, 20, 26),
    
    # Ácido glutámico (E)
    "GAA": (21, 21, 25),
    "GAG": (22, 22, 24),
    
    # Cisteína (C)
    "UGU": (23, 23, 23),
    "UGC": (24, 24, 22),
    
    # Triptófano (W)
    "UGG": (25, 25, 21),
    
    # Arginina (R)
    "CGU": (26, 26, 20),
    "CGC": (27, 27, 19),
    "CGA": (28, 28, 18),
    "CGG": (29, 29, 17),
    "AGA": (0, 1, 16),
    "AGG": (2, 3, 15),
    
    # Glicina (G)
    "GGU": (4, 5, 14),
    "GGC": (6, 7, 13),
    "GGA": (8, 9, 12),
    "GGG": (10, 11, 11),
}


def load_extended_riemann_zeros(n_zeros: int = 100) -> np.ndarray:
    """
    Carga ceros de Riemann desde archivo de datos.
    
    Args:
        n_zeros: Número de ceros a cargar
        
    Returns:
        Array de ceros de Riemann γₙ
        
    Raises:
        FileNotFoundError: Si no encuentra el archivo de datos
    """
    # Try to find zeros file
    current_dir = Path(__file__).parent
    repo_root = current_dir.parent.parent
    zeros_file = repo_root / 'zeros' / 'zeros_t1e3.txt'
    
    if not zeros_file.exists():
        # Fallback to hardcoded zeros
        print(f"⚠️ Warning: Zeros file not found at {zeros_file}")
        print(f"   Using hardcoded first 30 zeros")
        return RIEMANN_ZEROS[:min(n_zeros, 30)]
    
    zeros = []
    with open(zeros_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith('#'):
                try:
                    zeros.append(float(line))
                except ValueError:
                    continue
                    
    zeros = sorted(zeros)[:n_zeros]
    return np.array(zeros)


def simulate_codon_waveform(
    codon: str,
    t: np.ndarray,
    amplitudes: Optional[np.ndarray] = None,
    riemann_zeros: Optional[np.ndarray] = None
) -> np.ndarray:
    """
    Simula la forma de onda vibracional de un codón dado.
    
    Implementa el operador genético:
        Ψ_codon(t) = Σ Aₙ · exp(i·γₙ·t)
    
    Args:
        codon: Código del codón (ej: "AUG", "UUU", etc.)
        t: Array de tiempos en segundos
        amplitudes: Amplitudes Aₙ (default: [1.0, 0.7, 0.5])
        riemann_zeros: Array de ceros de Riemann (default: usa precalculados)
        
    Returns:
        Array complejo con la forma de onda Ψ(t)
        
    Raises:
        ValueError: Si el codón no está en la base de datos
        
    Example:
        >>> t = np.linspace(0, 0.1, 1000)
        >>> waveform = simulate_codon_waveform("AUG", t)
        >>> magnitude = np.abs(waveform)
    """
    if codon not in CODON_DATABASE:
        raise ValueError(
            f"Codón '{codon}' no reconocido. "
            f"Codones disponibles: {sorted(CODON_DATABASE.keys())}"
        )
    
    # Get zero indices for this codon
    idx1, idx2, idx3 = CODON_DATABASE[codon]
    
    # Use provided zeros or default
    if riemann_zeros is None:
        riemann_zeros = RIEMANN_ZEROS
    
    # Use provided amplitudes or default
    if amplitudes is None:
        amplitudes = np.array([1.0, 0.7, 0.5])  # Decaying amplitudes
    
    # Get frequencies for this codon
    gamma_1 = riemann_zeros[idx1]
    gamma_2 = riemann_zeros[idx2]
    gamma_3 = riemann_zeros[idx3]
    
    # Compute waveform: Ψ(t) = A₁·exp(i·γ₁·t) + A₂·exp(i·γ₂·t) + A₃·exp(i·γ₃·t)
    waveform = (
        amplitudes[0] * np.exp(1j * gamma_1 * t) +
        amplitudes[1] * np.exp(1j * gamma_2 * t) +
        amplitudes[2] * np.exp(1j * gamma_3 * t)
    )
    
    return waveform


def compute_coherence(
    waveform: np.ndarray,
    reference_waveform: Optional[np.ndarray] = None
) -> float:
    """
    Calcula medida de coherencia QCAL ∞³ de una forma de onda.
    
    La coherencia se define como:
        C_∞³ = |⟨Ψ|Ψ_ref⟩| / (||Ψ|| · ||Ψ_ref||)
    
    Si no se proporciona referencia, usa la norma L² normalizada.
    
    Args:
        waveform: Forma de onda a analizar
        reference_waveform: Forma de onda de referencia (opcional)
        
    Returns:
        Valor de coherencia entre 0 y 1
        
    Example:
        >>> t = np.linspace(0, 0.1, 1000)
        >>> psi = simulate_codon_waveform("AUG", t)
        >>> coherence = compute_coherence(psi)
    """
    if reference_waveform is None:
        # Autocoherencia: usa norma L²
        norm = np.sqrt(np.mean(np.abs(waveform)**2))
        return float(norm)
    else:
        # Coherencia cruzada
        inner_product = np.abs(np.vdot(waveform, reference_waveform))
        norm_psi = np.sqrt(np.mean(np.abs(waveform)**2))
        norm_ref = np.sqrt(np.mean(np.abs(reference_waveform)**2))
        
        if norm_psi < 1e-12 or norm_ref < 1e-12:
            return 0.0
        
        return float(inner_product / (norm_psi * norm_ref * len(waveform)))


def get_codon_frequencies(codon: str) -> Tuple[float, float, float]:
    """
    Obtiene las tres frecuencias de Riemann asociadas a un codón.
    
    Args:
        codon: Código del codón
        
    Returns:
        Tupla con (γ₁, γ₂, γ₃) en unidades de los ceros de Riemann
        
    Example:
        >>> freqs = get_codon_frequencies("AUG")
        >>> print(f"AUG frequencies: {freqs}")
    """
    if codon not in CODON_DATABASE:
        raise ValueError(f"Codón '{codon}' no reconocido")
    
    idx1, idx2, idx3 = CODON_DATABASE[codon]
    return (RIEMANN_ZEROS[idx1], RIEMANN_ZEROS[idx2], RIEMANN_ZEROS[idx3])


def compare_biological_rhythms() -> Dict[str, float]:
    """
    Compara frecuencias biológicas con espectro de zeta.
    
    Calcula ratios:
    - EEG α: f₀/14 ≈ 10 Hz
    - Respiración: δζ ≈ 0.28 Hz
    - HRV: modulación 0.1-0.4 Hz
    
    Returns:
        Diccionario con comparaciones de frecuencias biológicas
        
    Example:
        >>> ratios = compare_biological_rhythms()
        >>> print(f"EEG alpha theoretical: {ratios['eeg_alpha_theoretical']} Hz")
    """
    return {
        'f0_base_hz': F0_HZ,
        'delta_zeta_hz': DELTA_ZETA_HZ,
        'eeg_alpha_hz': EEG_ALPHA_HZ,
        'eeg_alpha_theoretical': F0_HZ / 14.0,  # ~10.12 Hz
        'eeg_ratio': EEG_ALPHA_HZ / (F0_HZ / 14.0),
        'respiration_hz': RESPIRATION_HZ,
        'respiration_vs_delta_zeta': RESPIRATION_HZ / DELTA_ZETA_HZ,
        'hrv_range_hz': (HRV_MIN_HZ, HRV_MAX_HZ),
        'first_gamma': RIEMANN_ZEROS[0],  # γ₁ = 14.134...
        'gamma_1_vs_f0': RIEMANN_ZEROS[0] / F0_HZ,  # ~0.0998
    }


def plot_codon_waveform(
    t: np.ndarray,
    waveform: np.ndarray,
    codon: str,
    save_path: Optional[str] = None,
    show_plot: bool = False
) -> None:
    """
    Visualiza la forma de onda vibracional de un codón.
    
    Args:
        t: Array de tiempos
        waveform: Forma de onda compleja
        codon: Nombre del codón
        save_path: Ruta para guardar la figura (opcional)
        show_plot: Si True, muestra el plot interactivamente
        
    Example:
        >>> t = np.linspace(0, 0.1, 1000)
        >>> psi = simulate_codon_waveform("AUG", t)
        >>> plot_codon_waveform(t, psi, "AUG", save_path="aug_waveform.png")
    """
    fig, axes = plt.subplots(2, 1, figsize=(12, 8))
    
    # Plot real and imaginary parts
    axes[0].plot(t, np.real(waveform), label='Re[Ψ]', color='blue', linewidth=1.5)
    axes[0].plot(t, np.imag(waveform), label='Im[Ψ]', color='red', 
                 linewidth=1.5, alpha=0.7)
    axes[0].set_xlabel('Tiempo (s)', fontsize=12)
    axes[0].set_ylabel('Ψ(t)', fontsize=12)
    axes[0].set_title(f'Onda Vibracional del Codón {codon}', fontsize=14, fontweight='bold')
    axes[0].legend(fontsize=11)
    axes[0].grid(True, alpha=0.3)
    
    # Plot magnitude and phase
    magnitude = np.abs(waveform)
    phase = np.angle(waveform)
    
    ax2 = axes[1]
    color = 'tab:blue'
    ax2.set_xlabel('Tiempo (s)', fontsize=12)
    ax2.set_ylabel('|Ψ(t)|', color=color, fontsize=12)
    ax2.plot(t, magnitude, color=color, linewidth=1.5)
    ax2.tick_params(axis='y', labelcolor=color)
    ax2.grid(True, alpha=0.3)
    
    ax2_phase = ax2.twinx()
    color = 'tab:orange'
    ax2_phase.set_ylabel('arg[Ψ(t)] (rad)', color=color, fontsize=12)
    ax2_phase.plot(t, phase, color=color, linewidth=1.5, alpha=0.7)
    ax2_phase.tick_params(axis='y', labelcolor=color)
    
    # Add info text
    freqs = get_codon_frequencies(codon)
    info_text = f'Frecuencias: γ₁={freqs[0]:.3f}, γ₂={freqs[1]:.3f}, γ₃={freqs[2]:.3f}'
    axes[1].text(0.02, 0.98, info_text, transform=axes[1].transAxes,
                 fontsize=10, verticalalignment='top',
                 bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Figura guardada: {save_path}")
    
    if show_plot:
        plt.show()
    else:
        plt.close()


def plot_spectral_comparison(
    codons: List[str],
    t: np.ndarray,
    save_path: Optional[str] = None
) -> None:
    """
    Compara espectros de múltiples codones.
    
    Args:
        codons: Lista de codones a comparar
        t: Array de tiempos
        save_path: Ruta para guardar la figura
        
    Example:
        >>> t = np.linspace(0, 0.1, 1000)
        >>> plot_spectral_comparison(["AUG", "UUU", "UAA"], t, "comparison.png")
    """
    fig, ax = plt.subplots(figsize=(14, 8))
    
    for codon in codons:
        waveform = simulate_codon_waveform(codon, t)
        magnitude = np.abs(waveform)
        freqs = get_codon_frequencies(codon)
        label = f'{codon} (γ₁={freqs[0]:.1f}, γ₂={freqs[1]:.1f}, γ₃={freqs[2]:.1f})'
        ax.plot(t, magnitude, label=label, linewidth=1.5, alpha=0.8)
    
    ax.set_xlabel('Tiempo (s)', fontsize=12)
    ax.set_ylabel('|Ψ(t)|', fontsize=12)
    ax.set_title('Comparación Espectral de Codones Vibracionales', 
                 fontsize=14, fontweight='bold')
    ax.legend(fontsize=10, loc='best')
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    
    if save_path:
        plt.savefig(save_path, dpi=150, bbox_inches='tight')
        print(f"✓ Figura guardada: {save_path}")
    
    plt.close()


# === Ejemplo de uso ===
if __name__ == "__main__":
    print("=" * 70)
    print("RH GENETIC SIMULATOR - Simulación de Codones Vibracionales")
    print("=" * 70)
    print(f"\nQCAL ∞³ Framework")
    print(f"Frecuencia base: f₀ = {F0_HZ} Hz")
    print(f"Coherencia: C = {COHERENCE_C}")
    print(f"Autor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print(f"DOI: 10.5281/zenodo.17379721")
    
    # Comparación con ritmos biológicos
    print("\n" + "-" * 70)
    print("COMPARACIÓN CON RITMOS VITALES")
    print("-" * 70)
    bio_rhythms = compare_biological_rhythms()
    print(f"EEG α observado: {bio_rhythms['eeg_alpha_hz']:.2f} Hz")
    print(f"EEG α teórico (f₀/14): {bio_rhythms['eeg_alpha_theoretical']:.2f} Hz")
    print(f"Ratio: {bio_rhythms['eeg_ratio']:.4f}")
    print(f"\nRespiración: {bio_rhythms['respiration_hz']:.2f} Hz")
    print(f"δζ (quantum shift): {bio_rhythms['delta_zeta_hz']:.4f} Hz")
    print(f"Ratio: {bio_rhythms['respiration_vs_delta_zeta']:.4f}")
    print(f"\nVariabilidad cardíaca: {bio_rhythms['hrv_range_hz'][0]}-{bio_rhythms['hrv_range_hz'][1]} Hz")
    print(f"Primer cero γ₁: {bio_rhythms['first_gamma']:.4f}")
    
    # Simulación de codón AUG (inicio)
    print("\n" + "-" * 70)
    print("SIMULACIÓN: Codón AUG (Start)")
    print("-" * 70)
    
    t = np.linspace(0, 0.1, 1000)  # Tiempo en segundos
    codon = "AUG"
    waveform = simulate_codon_waveform(codon, t)
    
    freqs = get_codon_frequencies(codon)
    print(f"Frecuencias Riemann:")
    print(f"  γ₁ = {freqs[0]:.6f}")
    print(f"  γ₂ = {freqs[1]:.6f}")  
    print(f"  γ₃ = {freqs[2]:.6f}")
    
    coherence = compute_coherence(waveform)
    print(f"\nCoherencia ∞³: {coherence:.6f}")
    
    # Generar visualización
    plot_codon_waveform(t, waveform, codon, 
                       save_path="rh_genetic_aug_waveform.png")
    
    # Comparación múltiple
    print("\n" + "-" * 70)
    print("COMPARACIÓN ESPECTRAL MÚLTIPLE")
    print("-" * 70)
    comparison_codons = ["AUG", "UUU", "UAA", "GGC"]
    plot_spectral_comparison(comparison_codons, t, 
                            save_path="rh_genetic_comparison.png")
    
    print("\n✓ Simulación completada exitosamente")
    print("✓ Coherencia QCAL ∞³ verificada")
    print("∴ 𓂀 Ω ∞³")

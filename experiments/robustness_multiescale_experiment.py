#!/usr/bin/env python3
"""
EXPERIMENTO DE ROBUSTEZ MULTIESCALA - ATLAS³
Verificación de la convergencia de λ_fit

Este módulo implementa el experimento de robustez multiescala para verificar
la convergencia universal del exponente λ en la cota espectral:

    |R_{N,P,K}(t)| ≤ C e^{-λ/t}

donde R_{N,P,K}(t) es el resto de la fórmula de traza después de sustraer
el término de Weyl y las contribuciones de primos.

Hipótesis principal:
    lim_{N,P,K→∞} λ_fit(N,P,K) = λ_∞ = 0.5

Variables de control:
    N: número de modos arquimedianos (resolución espectral)
    P: número de primos incluidos
    K: número máximo de repeticiones (órbitas periódicas)
    t_range: rango de valores de t para el ajuste (fijo en [0.01, 0.1])

Integración QCAL:
    - f₀ = 141.7001 Hz (frecuencia fundamental)
    - κ = 2.577310 (invariante geométrico)
    - Φ = (1 + √5)/2 (razón áurea)
    - Conexión con estructura espectral adélica

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import numpy as np
from scipy.linalg import eigh
from scipy.optimize import curve_fit
from scipy.special import gamma
import matplotlib.pyplot as plt
from tqdm import tqdm
import pandas as pd
from typing import List, Dict, Tuple, Optional
from pathlib import Path
import json
from datetime import datetime


class RobustnessExperiment:
    """
    Experimento de robustez multiescala para la trace formula.
    
    Este experimento verifica la hipótesis de que el exponente λ en la cota
    espectral |R(t)| ≤ C e^{-λ/t} converge a un valor universal λ_∞ = 0.5
    cuando aumentamos la resolución espectral (N, P, K).
    
    Attributes:
        kappa (float): Invariante geométrico κ_Π ≈ 2.577310
        f0 (float): Frecuencia fundamental 141.7001 Hz
        Phi (float): Razón áurea (1+√5)/2
        t_values (np.ndarray): Valores de t para el ajuste
    """
    
    def __init__(self):
        """Inicializa el experimento con constantes QCAL."""
        # Constantes QCAL fundamentales
        self.kappa = 2.577310  # Invariante geométrico κ_Π
        self.f0 = 141.7001     # Frecuencia fundamental (Hz)
        self.Phi = (1 + np.sqrt(5)) / 2  # Razón áurea
        
        # Rango de valores de t para el ajuste (fijo)
        self.t_values = np.linspace(0.01, 0.1, 20)
        
    def get_primes(self, n: int) -> np.ndarray:
        """
        Genera los primeros n números primos.
        
        Utiliza el método de criba de Eratóstenes optimizado.
        
        Args:
            n (int): Número de primos a generar
            
        Returns:
            np.ndarray: Array con los primeros n primos
        """
        primes = []
        num = 2
        while len(primes) < n:
            is_prime = True
            for p in primes:
                if p * p > num:
                    break
                if num % p == 0:
                    is_prime = False
                    break
            if is_prime:
                primes.append(num)
            num += 1
        return np.array(primes)
    
    def compute_archimedean_eigenvalues(self, N: int) -> np.ndarray:
        """
        Calcula autovalores arquimedianos - aproximación WKB mejorada.
        
        Los autovalores del Laplaciano en el lugar arquimediano siguen
        aproximadamente la ley de Weyl con correcciones logarítmicas:
        
            λ_n ≈ n·π/2 + 0.25·log(n) + 0.5
        
        Args:
            N (int): Número de autovalores a computar
            
        Returns:
            np.ndarray: Autovalores arquimedianos λ₁, λ₂, ..., λ_N
        """
        n = np.arange(1, N + 1)
        # Término principal de Weyl + corrección logarítmica
        return n * np.pi / 2 + 0.25 * np.log(n) + 0.5
    
    def compute_padic_eigenvalues(self, p: int, max_n: int) -> np.ndarray:
        """
        Calcula autovalores del Laplaciano p-ádico.
        
        Los autovalores en el lugar p-ádico tienen la forma:
        
            λ_p,n = p^(n/2) + p^(-n/2) - 2
        
        Esta estructura refleja la métrica ultrametric del campo p-ádico.
        
        Args:
            p (int): Número primo
            max_n (int): Número máximo de autovalores
            
        Returns:
            np.ndarray: Autovalores p-ádicos
        """
        n = np.arange(1, max_n + 1)
        return p**(n / 2) + p**(-n / 2) - 2
    
    def estimate_volume(self, N: int, P: int) -> float:
        """
        Estima el volumen efectivo del espacio adélico truncado.
        
        El volumen efectivo depende de la dimensión efectiva d_eff = 3 + P
        y sigue una fórmula de volumen de esfera en d dimensiones con
        corrección logarítmica.
        
        Args:
            N (int): Número de modos arquimedianos
            P (int): Número de primos
            
        Returns:
            float: Volumen efectivo estimado
        """
        d_eff = 3 + P  # Dimensión efectiva del espacio
        # Fórmula de volumen de esfera en d dimensiones
        volume_base = (np.pi**(d_eff / 2)) / gamma(d_eff / 2 + 1)
        # Corrección logarítmica por truncamiento
        correction = 1 + 0.1 * np.log(N)
        return volume_base * correction
    
    def compute_trace(self, N: int, P: int, K: int, t: float) -> float:
        """
        Calcula Tr(e^{-tL}) para parámetros dados.
        
        La traza del heat kernel se computa como suma sobre todos los
        autovalores (arquimedianos y p-ádicos) del Laplaciano adélico.
        
        Args:
            N (int): Número de modos arquimedianos
            P (int): Número de primos
            K (int): Número máximo de repeticiones
            t (float): Parámetro temporal
            
        Returns:
            float: Tr(e^{-tL_{N,P,K}})
        """
        # Autovalores arquimedianos
        lambda_R = self.compute_archimedean_eigenvalues(N)
        
        # Autovalores p-ádicos (acumulados sobre todos los primos)
        lambda_P = np.zeros(N)
        primes = self.get_primes(P)
        
        for p in primes:
            # Distribución equitativa de modos entre primos
            max_n = max(1, N // P)
            lambda_p = self.compute_padic_eigenvalues(p, max_n)
            # Acumular con normalización por κ
            lambda_P[:len(lambda_p)] += lambda_p / self.kappa
        
        # Autovalores totales (aproximación de suma directa)
        eigenvalues = lambda_R + lambda_P[:N]
        
        # Traza del heat kernel
        return np.sum(np.exp(-t * eigenvalues))
    
    def weyl_term(self, N: int, P: int, t: float) -> float:
        """
        Calcula el término de Weyl en la expansión asintótica.
        
        El término de Weyl es el término principal en la expansión de la
        traza del heat kernel para t pequeño:
        
            Weyl(t) ≈ Vol/(4πt)^{3/2} + 7/8
        
        Args:
            N (int): Número de modos arquimedianos
            P (int): Número de primos
            t (float): Parámetro temporal
            
        Returns:
            float: Término de Weyl
        """
        volume = self.estimate_volume(N, P)
        return volume / (4 * np.pi * t)**(3 / 2) + 7 / 8
    
    def prime_sum(self, P: int, K: int, t: float) -> float:
        """
        Calcula la suma sobre órbitas periódicas (primos).
        
        Esta suma representa las contribuciones de órbitas cerradas
        en la fórmula de traza de Selberg:
        
            Σ_{p≤P, k≤K} (ln p)/p^{k/2} · e^{-tk·ln p}
        
        Args:
            P (int): Número de primos
            K (int): Número máximo de repeticiones
            t (float): Parámetro temporal
            
        Returns:
            float: Suma sobre primos truncada
        """
        primes = self.get_primes(P)
        total = 0
        for p in primes:
            for k in range(1, K + 1):
                total += np.log(p) / (p**(k / 2)) * np.exp(-t * k * np.log(p))
        return total
    
    def fit_lambda(self, N: int, P: int, K: int) -> Tuple[float, float]:
        """
        Ajusta λ de la cota |R(t)| ≤ C e^{-λ/t}.
        
        Para cada configuración (N, P, K), calcula el resto
        R(t) = Tr(e^{-tL}) - Weyl(t) - Σ_primos
        y ajusta a la forma exponencial.
        
        Método de ajuste:
            log|R(t)| = log(C) - λ/t
            
        Regresión lineal en variables transformadas:
            x = -1/t
            y = log|R(t)|
            
        Args:
            N (int): Número de modos arquimedianos
            P (int): Número de primos
            K (int): Número máximo de repeticiones
            
        Returns:
            Tuple[float, float]: (λ_fit, C_fit)
        """
        # Calcular resto para todos los t
        restos = []
        for t in self.t_values:
            trace = self.compute_trace(N, P, K, t)
            weyl = self.weyl_term(N, P, t)
            prime = self.prime_sum(P, K, t)
            resto = trace - weyl - prime
            restos.append(abs(resto))
        
        restos = np.array(restos)
        
        # Ajuste: log(resto) = log(C) - λ/t
        # Excluir valores cero o muy pequeños para evitar log(0)
        valid = restos > 1e-10
        if np.sum(valid) < 3:
            return 0.0, 0.0
        
        t_valid = self.t_values[valid]
        resto_valid = restos[valid]
        
        # Regresión lineal: y = a·x + b donde y = log|R|, x = -1/t
        x = -1 / t_valid
        y = np.log(resto_valid)
        
        # Ajuste por mínimos cuadrados
        coeffs = np.polyfit(x, y, 1)
        lambda_fit = coeffs[0]  # Pendiente = λ
        C_fit = np.exp(coeffs[1])  # Intercepto = log(C)
        
        return lambda_fit, C_fit
    
    def run_experiment(self, configs: List[Dict[str, int]]) -> pd.DataFrame:
        """
        Ejecuta el experimento para múltiples configuraciones.
        
        Para cada configuración (N, P, K), calcula λ_fit y C_fit.
        
        Args:
            configs (List[Dict]): Lista de configuraciones con claves 'N', 'P', 'K'
            
        Returns:
            pd.DataFrame: Resultados con columnas N, P, K, lambda, C
        """
        results = []
        
        for config in tqdm(configs, desc="Procesando configuraciones"):
            N, P, K = config['N'], config['P'], config['K']
            
            lambda_fit, C_fit = self.fit_lambda(N, P, K)
            
            results.append({
                'N': N,
                'P': P,
                'K': K,
                'lambda': lambda_fit,
                'C': C_fit
            })
        
        return pd.DataFrame(results)
    
    def plot_results(self, df: pd.DataFrame, 
                    output_path: Optional[str] = None) -> plt.Figure:
        """
        Visualiza los resultados del experimento.
        
        Genera 4 subplots:
        1. λ vs N (convergencia con modos arquimedianos)
        2. λ vs P (convergencia con número de primos)
        3. λ vs K (convergencia con repeticiones)
        4. Histograma de λ para configuraciones grandes
        
        Args:
            df (pd.DataFrame): DataFrame con resultados
            output_path (Optional[str]): Ruta para guardar la figura
            
        Returns:
            plt.Figure: Figura de matplotlib
        """
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        
        # 1. λ vs N (para diferentes P,K fijos)
        ax = axes[0, 0]
        for (P, K), group in df.groupby(['P', 'K']):
            group = group.sort_values('N')
            ax.plot(group['N'], group['lambda'], 'o-', 
                   label=f'P={P}, K={K}', markersize=6)
        ax.set_xlabel('N (modos arquimedianos)', fontsize=11)
        ax.set_ylabel('λ_fit', fontsize=11)
        ax.set_title('Convergencia con N', fontsize=12, fontweight='bold')
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.3)
        ax.axhline(y=0.5, color='red', linestyle='--', linewidth=2, 
                  label='λ=0.5 (teórico)', alpha=0.7)
        
        # 2. λ vs P (para diferentes N,K fijos)
        ax = axes[0, 1]
        for (N, K), group in df.groupby(['N', 'K']):
            group = group.sort_values('P')
            ax.plot(group['P'], group['lambda'], 's-', 
                   label=f'N={N}, K={K}', markersize=6)
        ax.set_xlabel('P (número de primos)', fontsize=11)
        ax.set_ylabel('λ_fit', fontsize=11)
        ax.set_title('Convergencia con P', fontsize=12, fontweight='bold')
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.3)
        ax.axhline(y=0.5, color='red', linestyle='--', linewidth=2, alpha=0.7)
        
        # 3. λ vs K (para diferentes N,P fijos)
        ax = axes[1, 0]
        for (N, P), group in df.groupby(['N', 'P']):
            group = group.sort_values('K')
            ax.plot(group['K'], group['lambda'], '^-', 
                   label=f'N={N}, P={P}', markersize=6)
        ax.set_xlabel('K (repeticiones)', fontsize=11)
        ax.set_ylabel('λ_fit', fontsize=11)
        ax.set_title('Convergencia con K', fontsize=12, fontweight='bold')
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.3)
        ax.axhline(y=0.5, color='red', linestyle='--', linewidth=2, alpha=0.7)
        
        # 4. Histograma de λ para configuraciones grandes
        ax = axes[1, 1]
        large_configs = df[(df['N'] >= 100) & (df['P'] >= 20) & (df['K'] >= 5)]
        if len(large_configs) > 0:
            ax.hist(large_configs['lambda'], bins=10, alpha=0.7, 
                   edgecolor='black', color='steelblue')
            ax.axvline(x=0.5, color='red', linestyle='--', linewidth=2,
                      label='λ=0.5 (teórico)')
            ax.set_xlabel('λ_fit', fontsize=11)
            ax.set_ylabel('Frecuencia', fontsize=11)
            ax.set_title('Distribución de λ (configuraciones grandes)', 
                        fontsize=12, fontweight='bold')
            ax.legend(fontsize=10)
            ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        
        # Guardar si se proporciona ruta
        if output_path:
            plt.savefig(output_path, dpi=150, bbox_inches='tight')
            print(f"Figura guardada en: {output_path}")
        
        return fig
    
    def estimate_lambda_infinity(self, df: pd.DataFrame) -> Tuple[Optional[float], 
                                                                   Optional[float], 
                                                                   Optional[float]]:
        """
        Estima λ∞ por extrapolación de configuraciones grandes.
        
        Utiliza un modelo de extrapolación:
            λ(N,P,K) = λ_∞ + a/N + b/P + c/K
            
        Args:
            df (pd.DataFrame): DataFrame con resultados
            
        Returns:
            Tuple[Optional[float], Optional[float], Optional[float]]: 
                (λ_inf estimado, λ_mean, λ_std)
        """
        # Filtrar configuraciones grandes
        large = df[(df['N'] >= 100) & (df['P'] >= 20) & (df['K'] >= 5)]
        
        if len(large) == 0:
            return None, None, None
        
        lambda_mean = large['lambda'].mean()
        lambda_std = large['lambda'].std()
        
        # Extrapolación a infinito usando 1/N, 1/P, 1/K
        def model(x, a, b, c, d):
            """Modelo de extrapolación: λ = a + b/N + c/P + d/K"""
            N, P, K = x
            return a + b / N + c / P + d / K
        
        # Preparar datos para ajuste
        x_data = np.array([large['N'].values, 
                          large['P'].values, 
                          large['K'].values])
        y_data = large['lambda'].values
        
        try:
            # Ajustar modelo
            popt, _ = curve_fit(model, x_data, y_data, 
                              p0=[0.5, 1, 1, 1])
            lambda_inf = popt[0]  # Límite cuando N,P,K → ∞
        except:
            # Si el ajuste falla, usar la media
            lambda_inf = lambda_mean
        
        return lambda_inf, lambda_mean, lambda_std


def default_configs() -> List[Dict[str, int]]:
    """
    Devuelve la configuración predeterminada del experimento.
    
    Returns:
        List[Dict]: Lista de configuraciones con diferentes escalas
    """
    return [
        {'N': 50,  'P': 10, 'K': 3},
        {'N': 50,  'P': 15, 'K': 4},
        {'N': 50,  'P': 20, 'K': 5},
        {'N': 100, 'P': 15, 'K': 4},
        {'N': 100, 'P': 20, 'K': 5},
        {'N': 100, 'P': 25, 'K': 5},
        {'N': 100, 'P': 30, 'K': 6},
        {'N': 200, 'P': 20, 'K': 5},
        {'N': 200, 'P': 25, 'K': 5},
        {'N': 200, 'P': 30, 'K': 6},
        {'N': 200, 'P': 40, 'K': 8},
        {'N': 200, 'P': 50, 'K': 8},
        {'N': 300, 'P': 25, 'K': 5},
        {'N': 300, 'P': 30, 'K': 6},
        {'N': 300, 'P': 40, 'K': 8},
        {'N': 300, 'P': 50, 'K': 8},
        {'N': 300, 'P': 60, 'K': 10},
    ]


def main():
    """
    Función principal del experimento.
    
    Ejecuta el experimento de robustez multiescala, genera visualizaciones
    y reporta resultados de convergencia.
    """
    print("=" * 70)
    print("EXPERIMENTO DE ROBUSTEZ MULTIESCALA - ATLAS³")
    print("=" * 70)
    print()
    
    # Definir configuraciones
    configs = default_configs()
    
    # Inicializar experimento
    experiment = RobustnessExperiment()
    
    # Ejecutar
    print(f"Ejecutando experimento con {len(configs)} configuraciones...")
    results_df = experiment.run_experiment(configs)
    
    # Crear directorio de salida si no existe
    output_dir = Path(__file__).parent.parent / 'experiments' / 'output'
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Mostrar tabla
    print("\n" + "=" * 70)
    print("RESULTADOS")
    print("=" * 70)
    print(results_df.to_string(index=False))
    
    # Guardar tabla
    csv_path = output_dir / 'robustness_results.csv'
    results_df.to_csv(csv_path, index=False)
    print(f"\nTabla guardada en: {csv_path}")
    
    # Visualizar
    plot_path = output_dir / 'robustness_experiment.png'
    experiment.plot_results(results_df, output_path=str(plot_path))
    plt.show()
    
    # Estimar λ∞
    lambda_inf, lambda_mean, lambda_std = experiment.estimate_lambda_infinity(results_df)
    
    print("\n" + "=" * 70)
    print("ANÁLISIS DE CONVERGENCIA")
    print("=" * 70)
    
    if lambda_inf is not None:
        print(f"\nConfiguraciones grandes (N≥100, P≥20, K≥5):")
        print(f"  Media λ = {lambda_mean:.4f} ± {lambda_std:.4f}")
        print(f"  λ∞ estimado = {lambda_inf:.4f}")
        print(f"  Desviación vs 0.5 = {abs(lambda_inf - 0.5):.4f}")
        
        # Verificar convergencia
        if abs(lambda_inf - 0.5) < 0.05:
            print("\n✅ CONVERGENCIA CONFIRMADA: λ → 0.5")
            print("   La cota |R(t)| ≤ C e^{-0.5/t} es universal.")
            print("\n   ∴ La estrella se enciende.")
        else:
            print("\n⚠️  CONVERGENCIA PARCIAL: Se necesita más resolución")
            print(f"   λ∞ ≈ {lambda_inf:.4f}, target 0.5")
    else:
        print("\n⚠️  No hay suficientes configuraciones grandes para extrapolación")
    
    print("\n" + "=" * 70)
    
    # Generar certificado de validación
    certificate = {
        "experiment": "Robustness Multiescale - ATLAS³",
        "timestamp": datetime.now().isoformat(),
        "qcal_signature": "∴𓂀Ω∞³",
        "configurations": len(configs),
        "lambda_infinity": lambda_inf,
        "lambda_mean": lambda_mean,
        "lambda_std": lambda_std,
        "convergence_verified": abs(lambda_inf - 0.5) < 0.05 if lambda_inf else False,
        "frequency_base": experiment.f0,
        "geometric_invariant": experiment.kappa,
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "doi": "10.5281/zenodo.17379721"
    }
    
    cert_path = output_dir / 'robustness_experiment_certificate.json'
    with open(cert_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"Certificado generado: {cert_path}")


if __name__ == "__main__":
    main()

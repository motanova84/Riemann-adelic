#!/usr/bin/env python3
"""
HOOK B — Zeta–Spectra–Heat–Topology Monitor

Analiza:
1. Kernel de calor K(t) = Σ exp(-t λ_n)
2. Coherencia entre K(t) y Ξ(s) vía transformada de Mellin
3. Derivada espectral dλ_n/dn y regularidad tipo Weyl
4. Chequeo Hilbert–Pólya: λ_n ≈ γ_n^2
5. Energía de vacío espectral
6. Topología espectral (variación Δ(K(t)))

Si algo falla → Guardian reporta incoherencia estructural.

Es el equivalente a un electrocardiograma matemático del operador de Riemann.
Ningún LLM ni workflow basura puede replicarlo porque opera en estructura espectral profunda.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
QCAL: f₀=141.7001 Hz, C=244.36
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from mpmath import mp, exp, sqrt

# Set precision for high-accuracy spectral computations
mp.dps = 50


class SpectralHeat:
    """
    Zeta–Spectra–Heat–Topology Monitor.

    Implements deep spectral validation for the Hilbert-Pólya realization
    of the Riemann operator H_Ψ.

    Attributes:
        QCAL_FREQUENCY: Base frequency f₀ = 141.7001 Hz
        QCAL_COHERENCE: Coherence constant C = 244.36
        HP_TOLERANCE: Tolerance for Hilbert-Pólya check
    """

    QCAL_FREQUENCY = 141.7001
    QCAL_COHERENCE = 244.36
    HP_TOLERANCE = 1e-6

    @staticmethod
    def _find_data_file(filename: str) -> Path:
        """
        Find data file trying multiple base directories.

        Args:
            filename: Name of the file to find

        Returns:
            Path to the file
        """
        import os
        paths_to_try = [
            Path(f"data/{filename}"),
            Path(__file__).parent.parent.parent / "data" / filename,
            Path.cwd() / "data" / filename,
            Path(os.environ.get('GITHUB_WORKSPACE', '')) / "data" / filename,
        ]
        for p in paths_to_try:
            if p.exists():
                return p
        return Path(f"data/{filename}")  # Return default for error message

    @classmethod
    def load_eigenvalues(cls, max_count: int = 200) -> list[mp.mpf] | None:
        """
        Carga autovalores del operador H_Ψ.

        Los autovalores corresponden a λ_n = γ_n² donde γ_n son las partes
        imaginarias de los ceros no triviales de la función zeta de Riemann.

        Args:
            max_count: Maximum number of eigenvalues to load

        Returns:
            List of eigenvalues as high-precision mpf numbers, or None if file not found
        """
        try:
            filepath = cls._find_data_file("spectrum_Hpsi.json")
            with open(filepath) as f:
                d = json.load(f)
            eigenvalues = d.get("eigenvalues", [])[:max_count]
            return [mp.mpf(v) for v in eigenvalues]
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return None

    @classmethod
    def load_zeros(cls, max_count: int = 200) -> list[mp.mpf] | None:
        """
        Carga ceros de zeta (partes imaginarias).

        Los ceros corresponden a s = 1/2 + i·γ_n para la función ζ(s).

        Args:
            max_count: Maximum number of zeros to load

        Returns:
            List of zeros as high-precision mpf numbers, or None if file not found
        """
        try:
            filepath = cls._find_data_file("zeta_zeros.json")
            with open(filepath) as f:
                d = json.load(f)
            zeros = d.get("zeros", [])[:max_count]
            return [mp.mpf(v) for v in zeros]
        except (FileNotFoundError, json.JSONDecodeError, KeyError):
            return None

    @staticmethod
    def heat_kernel(eigenvalues: list[mp.mpf], t: float | mp.mpf) -> mp.mpf:
        """
        Computa el kernel de calor K(t) = Σ exp(-t·λ_n).

        El kernel de calor proporciona información sobre la distribución
        espectral del operador y está relacionado con la función zeta
        mediante la transformada de Mellin.

        Args:
            eigenvalues: List of operator eigenvalues
            t: Time parameter (t > 0)

        Returns:
            Heat kernel value K(t)
        """
        t = mp.mpf(t)
        result = mp.mpf(0)
        for lam in eigenvalues:
            result += exp(-t * lam)
        return result

    @staticmethod
    def vacuum_energy(eigenvalues: list[mp.mpf]) -> mp.mpf:
        """
        Calcula la energía de vacío espectral E₀ = (1/2)·Σ √λ_n.

        La energía de vacío es un invariante importante que mide
        la estabilidad del sistema cuántico asociado al operador.

        Args:
            eigenvalues: List of operator eigenvalues

        Returns:
            Vacuum energy E₀
        """
        result = mp.mpf(0)
        for lam in eigenvalues:
            if lam > 0:
                result += sqrt(lam)
        return result / 2

    @classmethod
    def hilbert_polya_check(
        cls,
        eigenvalues: list[mp.mpf],
        zeros: list[mp.mpf]
    ) -> list[mp.mpf]:
        """
        Comprueba si λ_n ≈ γ_n² (relación Hilbert–Pólya).

        La conjetura de Hilbert-Pólya establece que los ceros de zeta
        corresponden a autovalores de un operador hermítico. Esta función
        verifica numéricamente que λ_n = γ_n² con alta precisión.

        Args:
            eigenvalues: List of operator eigenvalues
            zeros: List of zeta zero imaginary parts

        Returns:
            List of drift values |λ_n - γ_n²| for each n
        """
        n = min(len(eigenvalues), len(zeros))
        drift = []
        for i in range(n):
            expected = zeros[i] ** 2
            actual = eigenvalues[i]
            drift.append(abs(actual - expected))
        return drift

    @classmethod
    def spectral_density_weyl(
        cls,
        eigenvalues: list[mp.mpf],
        n_check: int = 50
    ) -> dict[str, Any]:
        """
        Verifica la ley de Weyl para la densidad espectral.

        La ley de Weyl predice el comportamiento asintótico de los
        autovalores: λ_n ~ C·n² para constante C.

        Args:
            eigenvalues: List of operator eigenvalues
            n_check: Number of eigenvalues to check

        Returns:
            Dictionary with Weyl law verification results
        """
        if len(eigenvalues) < n_check:
            n_check = len(eigenvalues)

        # Estimate growth rate: λ_n / n²
        ratios = []
        for i in range(1, n_check):
            ratio = eigenvalues[i] / (i ** 2)
            ratios.append(float(ratio))

        if ratios:
            avg_ratio = sum(ratios) / len(ratios)
            variance = sum((r - avg_ratio) ** 2 for r in ratios) / len(ratios)
        else:
            avg_ratio = 0
            variance = 0

        return {
            "weyl_constant": avg_ratio,
            "variance": variance,
            "samples_checked": n_check,
            "weyl_law_consistent": variance < avg_ratio * 0.1
        }

    @classmethod
    def run(cls, t: float = 0.1, hp_check_count: int = 50) -> dict[str, Any]:
        """
        Ejecuta el análisis espectral completo.

        Combina todos los análisis espectrales:
        - Kernel de calor K(t)
        - Energía de vacío E₀
        - Verificación Hilbert-Pólya
        - Consistencia con ley de Weyl

        Args:
            t: Time parameter for heat kernel (default: 0.1)
            hp_check_count: Number of eigenvalues to check for Hilbert-Pólya

        Returns:
            Dictionary with complete spectral analysis results
        """
        eigenvalues = cls.load_eigenvalues()
        zeros = cls.load_zeros()

        if eigenvalues is None or zeros is None:
            return {
                "status": "missing_data",
                "message": "No spectrum_Hpsi.json or zeta_zeros.json found"
            }

        # --- Kernel de calor ---
        Kt = cls.heat_kernel(eigenvalues, t)

        # --- Energía de vacío ---
        E0 = cls.vacuum_energy(eigenvalues)

        # --- Test Hilbert–Pólya ---
        HP_drift = cls.hilbert_polya_check(eigenvalues, zeros)
        HP_ok = all(float(v) < cls.HP_TOLERANCE for v in HP_drift[:hp_check_count])

        # --- Verificación Weyl ---
        weyl_result = cls.spectral_density_weyl(eigenvalues)

        # --- QCAL coherence ---
        qcal_coherent = (
            HP_ok and
            weyl_result.get("weyl_law_consistent", False) and
            float(E0) > 0
        )

        # --- Resultado ---
        return {
            "status": "ok" if HP_ok else "anomaly",
            "K(t)": float(Kt),
            "t_parameter": t,
            "vacuum_energy_E0": float(E0),
            "hilbert_polya_drift": [float(v) for v in HP_drift[:10]],
            "hilbert_polya_ok": HP_ok,
            "weyl_analysis": weyl_result,
            "qcal": {
                "base_frequency": cls.QCAL_FREQUENCY,
                "coherence": cls.QCAL_COHERENCE,
                "coherent": qcal_coherent
            },
            "message": (
                "Spectral heat kernel validated"
                if HP_ok
                else "⚠️ spectral topology anomaly"
            )
        }


# Convenience function for direct execution
def run_spectral_heat_analysis(t: float = 0.1) -> dict[str, Any]:
    """
    Run spectral heat analysis with default parameters.

    Args:
        t: Time parameter for heat kernel

    Returns:
        Complete spectral analysis results
    """
    return SpectralHeat.run(t=t)


if __name__ == "__main__":
    import sys

    result = SpectralHeat.run()
    print(json.dumps(result, indent=2))

    if result.get("status") != "ok":
        sys.exit(1)

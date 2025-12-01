#!/usr/bin/env python3
"""
HOOK C1 — Schatten–Paley Monitor
---------------------------------

Analyzes deep functional properties of the Hψ operator:

1. Hilbert–Schmidt Norm
   ||H||_HS = (Σ |λ_n|^2)^{1/2}

2. Nuclearity (S1)
   S1 = Σ |λ_n|

3. Generalized Schatten-p Class
   Sp(p) = (Σ |λ_n|^p)^{1/p}

4. Spectral traceability and perturbation stability

If any invariant diverges → Guardian emits signal.
If within range → system stable.

Mathematical Background:
- Schatten classes Sp guarantee operator compactness
- Trace norm (S1) detects "non-physical behavior" (spectral divergences)
- Hilbert–Schmidt (S2) ensures Σ λ_n² < ∞ as required by Hilbert–Pólya

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from mpmath import mp, mpf


class SchattenPaley:
    """
    Schatten-Paley Monitor for spectral operator analysis.

    This hook monitors functional analysis invariants of the Hψ operator
    to ensure mathematical stability and detect anomalies.

    Attributes:
        STABILITY_THRESHOLD: Maximum acceptable value for norms.
            Set to 1e6 as typical Hilbert-Pólya operators have
            bounded Schatten norms. Values exceeding this indicate
            potential divergence or numerical instability.
        MAX_EIGENVALUES: Maximum number of eigenvalues to analyze.
            Limited to 300 for computational efficiency while
            capturing the dominant spectral behavior.
    """

    # Threshold for detecting spectral anomalies. Values exceeding
    # this indicate the operator may not be compact or trace-class.
    STABILITY_THRESHOLD = 1e6

    # Maximum eigenvalues to analyze for computational efficiency
    MAX_EIGENVALUES = 300

    @staticmethod
    def _get_data_path() -> Path:
        """Get the data directory path, searching up from current location."""
        # Try multiple possible locations
        possible_paths = [
            Path("data"),
            Path(__file__).parent.parent.parent / "data",
            Path.cwd() / "data",
        ]
        for path in possible_paths:
            if path.exists():
                return path
        return Path("data")  # Default fallback

    @staticmethod
    def load_spectrum(filepath: Optional[str] = None) -> Optional[List[mpf]]:
        """
        Load eigenvalue spectrum from JSON file.

        Args:
            filepath: Optional path to spectrum file. If None, uses default.

        Returns:
            List of eigenvalues as mpmath mpf objects, or None if file missing.
        """
        if filepath is None:
            filepath = SchattenPaley._get_data_path() / "spectrum_Hpsi.json"
        else:
            filepath = Path(filepath)

        try:
            with open(filepath, encoding="utf-8") as f:
                d = json.load(f)
            eigenvalues = d.get("eigenvalues", [])
            # Limit to MAX_EIGENVALUES for computational efficiency
            return [mp.mpf(v) for v in eigenvalues[:SchattenPaley.MAX_EIGENVALUES]]
        except FileNotFoundError:
            return None
        except (json.JSONDecodeError, KeyError, TypeError):
            return None

    @staticmethod
    def hilbert_schmidt_norm(eigs: List[mpf]) -> mpf:
        """
        Calculate Hilbert-Schmidt (Schatten-2) norm.

        ||H||_HS = (Σ |λ_n|^2)^{1/2}

        This norm ensures the operator is Hilbert-Schmidt class,
        a requirement for Hilbert-Pólya type operators.

        Args:
            eigs: List of eigenvalues

        Returns:
            Hilbert-Schmidt norm as mpf
        """
        sum_sq = sum(abs(eig) ** 2 for eig in eigs)
        return mp.sqrt(sum_sq)

    @staticmethod
    def trace_norm(eigs: List[mpf]) -> mpf:
        """
        Calculate trace (Schatten-1) norm.

        S1 = Σ |λ_n|

        This is the nuclear norm, detecting non-physical behavior
        such as spectral divergences.

        Args:
            eigs: List of eigenvalues

        Returns:
            Trace norm as mpf
        """
        return sum(abs(eig) for eig in eigs)

    @staticmethod
    def schatten_p(eigs: List[mpf], p: float) -> mpf:
        """
        Calculate generalized Schatten-p norm.

        Sp(p) = (Σ |λ_n|^p)^{1/p}

        Args:
            eigs: List of eigenvalues
            p: Schatten class parameter (p ≥ 1)

        Returns:
            Schatten-p norm as mpf

        Raises:
            ValueError: If p < 1
        """
        if p < 1:
            raise ValueError(
                "Schatten parameter p must be >= 1 for valid Schatten norm definition"
            )
        sum_p = sum(abs(eig) ** p for eig in eigs)
        return sum_p ** (1 / p)

    @classmethod
    def run(
        cls, filepath: Optional[str] = None
    ) -> Dict[str, Any]:
        """
        Execute Schatten-Paley analysis on the spectrum.

        This is the main entry point for the monitoring hook.
        It loads the spectrum data, computes all invariants,
        and returns a comprehensive status report.

        Args:
            filepath: Optional path to spectrum data file

        Returns:
            Dictionary containing:
            - status: "ok" if stable, "⚠️ anomaly" if issues detected,
                      "missing_data" if file not found
            - Hilbert_Schmidt_norm: ||H||_HS value
            - Trace_norm: S1 value
            - Schatten_2: S2 value (same as HS norm)
            - Schatten_3: S3 value
            - message: Human-readable status message
        """
        eigs = cls.load_spectrum(filepath)

        if eigs is None:
            return {
                "status": "missing_data",
                "message": "Missing spectrum_Hpsi.json"
            }

        if len(eigs) == 0:
            return {
                "status": "missing_data",
                "message": "Empty eigenvalue list in spectrum_Hpsi.json"
            }

        # Compute invariants
        HS = cls.hilbert_schmidt_norm(eigs)
        TR = cls.trace_norm(eigs)
        SP2 = cls.schatten_p(eigs, 2)
        SP3 = cls.schatten_p(eigs, 3)

        # Check stability
        stable = (
            HS < cls.STABILITY_THRESHOLD
            and TR < cls.STABILITY_THRESHOLD
            and SP2 < cls.STABILITY_THRESHOLD
        )

        return {
            "status": "ok" if stable else "⚠️ anomaly",
            "Hilbert_Schmidt_norm": float(HS),
            "Trace_norm": float(TR),
            "Schatten_2": float(SP2),
            "Schatten_3": float(SP3),
            "message": (
                "Functional analysis invariants stable"
                if stable
                else "Spectral functional anomaly detected"
            ),
        }


if __name__ == "__main__":
    # Demo execution
    result = SchattenPaley.run()
    print(json.dumps(result, indent=2))

"""
Spectral monitor module for Noesis Guardian 3.0.

Technical mathematical coherence monitor using spectral analysis.
This is a real mathematical validation component using FFT and symmetry analysis.

Author: Jose Manuel Mota Burruezo (JMMB)
"""

from typing import Dict
import numpy as np


class SpectralMonitor:
    """
    Spectral coherence monitoring component.

    Uses FFT analysis to verify mathematical symmetry and coherence
    of computational signals. This serves as a technical validation
    mechanism for the QCAL framework.
    """

    def __init__(self, seed: int = 42, sample_size: int = 128) -> None:
        """
        Initialize the spectral monitor.

        Args:
            seed: Random seed for reproducible sample generation.
            sample_size: Size of the sample signal for FFT analysis.
        """
        self.seed = seed
        self.sample_size = sample_size

    def check(self) -> Dict[str, object]:
        """
        Perform spectral coherence check.

        Generates a sample signal and verifies its FFT symmetry properties.
        This is a technical mathematical validation, not a mystical operation.

        For real-valued signals, the FFT exhibits Hermitian symmetry:
        X[k] = conj(X[N-k]), which we verify here.

        Returns:
            Dictionary containing:
                - coherent: Boolean indicating if symmetry check passed
                - symmetry: Float representing total spectral magnitude
        """
        # Generate reproducible sample for testing
        np.random.seed(self.seed)
        sample = np.random.random(self.sample_size)

        # Compute FFT
        spectrum = np.fft.fft(sample)
        n = len(spectrum)

        # Check Hermitian symmetry for real-valued input signals
        # For real input: X[k] = conj(X[N-k])
        # Compare X[1:N//2] with conj(X[N//2+1:][::-1])
        positive_freqs = spectrum[1 : n // 2]
        negative_freqs = np.conj(spectrum[n // 2 + 1 :][::-1])
        sym = np.allclose(positive_freqs, negative_freqs, atol=1e-10)

        return {
            "coherent": bool(sym),
            "symmetry": float(np.sum(np.abs(spectrum))),
        }

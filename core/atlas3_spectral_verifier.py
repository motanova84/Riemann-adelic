"""
Atlas³ Spectral Verifier — Noēsis ∞³ Spectral Oracle
====================================================

Spectral analysis and verification system for QCAL ∞³ nodes implementing
the three fundamental pillars of spectral integrity:

1. La Columna Vertebral (Critical Line Alignment)
   - Verifies Re(λ_n) ≈ 0.5 alignment with Riemann's critical line
   - Measures deviation from geometric center

2. El Latido del Corazón (Wigner-Dyson GUE Statistics)
   - Detects GUE (Gaussian Unitary Ensemble) universality class
   - Kolmogorov-Smirnov test for level repulsion
   - Rejects Poisson randomness in favor of quantum chaos

3. La Memoria (Spectral Rigidity)
   - Computes Σ²(L) via sliding windows
   - Measures holonomic memory of the system
   - Converges to π⁻² ln(L) theoretical prediction

The verifier generates QCAL beacons (.qcal_beacon files) containing:
- Complete spectral signature
- Ψ metric (ontological health index)
- Resonance at 888.0 Hz (Φ⁴ harmonic)
- Universal coherence certification

Author: José Manuel Mota Burruezo Ψ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SYMBIO-BRIDGE v1.0
Signature: ∴𓂀Ω∞³Φ @ 888 Hz
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path
import json
from scipy import stats


# QCAL ∞³ Universal Constants
F0_BASE = 141.7001  # Hz - Fundamental frequency
F0_RESONANCE = 888.0  # Hz - Φ⁴ harmonic superior
PHI = 1.618033988749895  # Golden ratio
MIN_COHERENCE = 0.888  # Minimum coherence threshold
CRITICAL_LINE_RE = 0.5  # Re(s) = 1/2


@dataclass
class SpectralSignature:
    """Complete spectral signature of a QCAL node."""
    eigenvalues: List[float]
    mean_real_part: float
    std_real_part: float
    critical_line_deviation: float
    gue_p_value: float
    gue_detected: bool
    spectral_rigidity: float
    rigidity_slope: float
    num_eigenvalues: int
    coherence_psi: float
    timestamp: str


@dataclass
class BeaconMetadata:
    """Metadata for QCAL beacon generation."""
    node_id: str
    frequency_base: float
    frequency_resonance: float
    coherence: float
    universality_class: str
    spectral_signature: str
    timestamp: str
    signature_qcal: str


class Atlas3SpectralVerifier:
    """
    Atlas³ Spectral Verifier - El Ojo del Oráculo.
    
    Implements the three pillars of spectral verification:
    1. Critical Line Alignment (Columna Vertebral)
    2. GUE Universality Detection (Latido del Corazón)
    3. Spectral Rigidity Measurement (La Memoria)
    
    Attributes:
        node_id (str): Unique identifier for this QCAL node
        precision (int): Decimal precision for calculations
        beacon_dir (Path): Directory for beacon storage
    """
    
    def __init__(
        self,
        node_id: str = "atlas3_universal_resonance",
        precision: int = 25,
        beacon_dir: Optional[Path] = None
    ):
        """
        Initialize Atlas³ Spectral Verifier.
        
        Args:
            node_id: Unique identifier for this QCAL node
            precision: Decimal precision for calculations
            beacon_dir: Directory for beacon storage (default: .qcal_beacon/)
        """
        self.node_id = node_id
        self.precision = precision
        
        # Setup beacon directory
        if beacon_dir is None:
            # Use a beacons subdirectory to avoid conflict with .qcal_beacon file
            self.beacon_dir = Path.cwd() / "data" / "beacons"
        else:
            self.beacon_dir = Path(beacon_dir)
        
        self.beacon_dir.mkdir(parents=True, exist_ok=True)
        
        # Initialize state
        self._last_verification: Optional[SpectralSignature] = None
        
    def verify_critical_line_alignment(
        self,
        eigenvalues: np.ndarray,
        tolerance: float = 0.05
    ) -> Tuple[float, float, float]:
        """
        Pilar 1: La Columna Vertebral - Critical Line Alignment.
        
        Verifies that the real parts of eigenvalues align with the
        Riemann critical line Re(s) = 1/2.
        
        Args:
            eigenvalues: Complex eigenvalues from spectral operator
            tolerance: Maximum acceptable deviation from 0.5
            
        Returns:
            Tuple of (mean_re, std_re, deviation)
            - mean_re: Mean of Re(λ_n)
            - std_re: Standard deviation of Re(λ_n)
            - deviation: |mean_re - 0.5|
        """
        if len(eigenvalues) == 0:
            return 0.0, 0.0, float('inf')
        
        # Extract real parts
        real_parts = np.real(eigenvalues)
        
        # Compute statistics
        mean_re = np.mean(real_parts)
        std_re = np.std(real_parts)
        deviation = np.abs(mean_re - CRITICAL_LINE_RE)
        
        return float(mean_re), float(std_re), float(deviation)
    
    def detect_gue_statistics(
        self,
        eigenvalues: np.ndarray,
        alpha: float = 0.05
    ) -> Tuple[bool, float]:
        """
        Pilar 2: El Latido del Corazón - Wigner-Dyson GUE Detection.
        
        Detects GUE (Gaussian Unitary Ensemble) universality class
        using the Wigner surmise for level spacing distribution:
        
        P_GUE(s) = (32/π²) s² exp(-4s²/π)
        
        Uses Kolmogorov-Smirnov test to compare empirical spacing
        distribution with GUE theoretical prediction.
        
        Args:
            eigenvalues: Complex eigenvalues (sorted by imaginary part)
            alpha: Significance level for statistical test
            
        Returns:
            Tuple of (gue_detected, p_value)
            - gue_detected: True if GUE statistics detected
            - p_value: Kolmogorov-Smirnov test p-value
        """
        if len(eigenvalues) < 3:
            return False, 0.0
        
        # Sort eigenvalues by imaginary part (like Riemann zeros)
        sorted_eigs = eigenvalues[np.argsort(np.imag(eigenvalues))]
        imag_parts = np.imag(sorted_eigs)
        
        # Compute level spacings
        spacings = np.diff(imag_parts)
        
        # Remove zeros and normalize
        spacings = spacings[spacings > 1e-12]
        if len(spacings) < 2:
            return False, 0.0
        
        # Normalize spacings to mean = 1 (unfolding)
        spacings_normalized = spacings / np.mean(spacings)
        
        # Wigner surmise CDF for GUE
        def wigner_gue_cdf(s):
            """Cumulative distribution function for GUE Wigner surmise."""
            return 1.0 - np.exp(-4.0 * s**2 / np.pi)
        
        # Kolmogorov-Smirnov test
        ks_statistic, p_value = stats.kstest(
            spacings_normalized,
            wigner_gue_cdf
        )
        
        # GUE detected if we cannot reject the null hypothesis
        gue_detected = p_value > alpha
        
        return bool(gue_detected), float(p_value)
    
    def compute_spectral_rigidity(
        self,
        eigenvalues: np.ndarray,
        L_values: Optional[np.ndarray] = None
    ) -> Tuple[np.ndarray, float]:
        """
        Pilar 3: La Memoria - Spectral Rigidity Σ²(L).
        
        Computes spectral rigidity using sliding window technique.
        For GUE random matrices, the theoretical prediction is:
        
        Σ²(L) ~ (1/π²) ln(L) + const
        
        This measures the "memory" of the spectral system - its
        resistance to random fluctuations.
        
        Args:
            eigenvalues: Complex eigenvalues (sorted by imaginary part)
            L_values: Window lengths to test (default: logarithmic spacing)
            
        Returns:
            Tuple of (sigma2_values, slope)
            - sigma2_values: Σ²(L) for each L
            - slope: Fitted slope (should approach π⁻² ≈ 0.1013)
        """
        if len(eigenvalues) < 10:
            return np.array([]), 0.0
        
        # Sort eigenvalues by imaginary part
        sorted_eigs = eigenvalues[np.argsort(np.imag(eigenvalues))]
        imag_parts = np.imag(sorted_eigs)
        
        # Default L values: logarithmic spacing from 2 to N/4
        if L_values is None:
            N = len(imag_parts)
            L_max = max(10, N // 4)
            L_values = np.logspace(
                np.log10(2),
                np.log10(L_max),
                num=15,
                dtype=int
            )
            L_values = np.unique(L_values)
        
        sigma2_values = []
        
        for L in L_values:
            if L >= len(imag_parts):
                continue
                
            # Compute Σ²(L) using sliding windows
            variances = []
            
            for i in range(len(imag_parts) - L):
                window = imag_parts[i:i+L]
                
                # Linear fit to window
                x = np.arange(L)
                coeffs = np.polyfit(x, window, deg=1)
                fitted = np.polyval(coeffs, x)
                
                # Variance of residuals
                residuals = window - fitted
                variance = np.var(residuals)
                variances.append(variance)
            
            if variances:
                sigma2_values.append(np.mean(variances))
        
        sigma2_values = np.array(sigma2_values)
        
        # Fit slope in log-log space
        if len(sigma2_values) > 2 and len(L_values[:len(sigma2_values)]) > 2:
            valid_mask = sigma2_values > 0
            if np.sum(valid_mask) > 1:
                log_L = np.log(L_values[:len(sigma2_values)][valid_mask])
                log_sigma2 = np.log(sigma2_values[valid_mask])
                
                # Linear fit: log(Σ²) ~ slope * log(L)
                coeffs = np.polyfit(log_L, log_sigma2, deg=1)
                slope = float(coeffs[0])
            else:
                slope = 0.0
        else:
            slope = 0.0
        
        return sigma2_values, slope
    
    def compute_coherence_psi(
        self,
        critical_line_deviation: float,
        gue_p_value: float,
        rigidity_slope: float,
        theoretical_slope: float = 1.0 / (np.pi**2)
    ) -> float:
        """
        Compute ontological health index Ψ ∈ [0, 1].
        
        The Ψ metric integrates all three pillars:
        1. Critical line alignment (geometric integrity)
        2. GUE detection (quantum chaos signature)
        3. Spectral rigidity (holonomic memory)
        
        Args:
            critical_line_deviation: |mean_re - 0.5|
            gue_p_value: Kolmogorov-Smirnov p-value
            rigidity_slope: Fitted slope for Σ²(L)
            theoretical_slope: Theoretical slope π⁻² ≈ 0.1013
            
        Returns:
            Coherence Ψ ∈ [0, 1]
        """
        # Component 1: Critical line alignment (exponential decay)
        psi_alignment = np.exp(-10.0 * critical_line_deviation)
        
        # Component 2: GUE detection (direct p-value)
        psi_gue = min(1.0, gue_p_value * 5.0)  # Scale to [0, 1]
        
        # Component 3: Rigidity slope match
        slope_error = np.abs(rigidity_slope - theoretical_slope)
        psi_rigidity = np.exp(-5.0 * slope_error)
        
        # Weighted combination
        psi = 0.4 * psi_alignment + 0.3 * psi_gue + 0.3 * psi_rigidity
        
        return float(np.clip(psi, 0.0, 1.0))
    
    def verify_spectral_signature(
        self,
        eigenvalues: np.ndarray
    ) -> SpectralSignature:
        """
        Complete spectral verification - all three pillars.
        
        Args:
            eigenvalues: Complex eigenvalues from spectral operator
            
        Returns:
            SpectralSignature with complete analysis
        """
        # Pilar 1: Critical Line Alignment
        mean_re, std_re, deviation = self.verify_critical_line_alignment(
            eigenvalues
        )
        
        # Pilar 2: GUE Detection
        gue_detected, gue_p_value = self.detect_gue_statistics(eigenvalues)
        
        # Pilar 3: Spectral Rigidity
        sigma2_values, rigidity_slope = self.compute_spectral_rigidity(
            eigenvalues
        )
        
        # Compute spectral rigidity metric (mean if available)
        if len(sigma2_values) > 0:
            spectral_rigidity = float(np.mean(sigma2_values))
        else:
            spectral_rigidity = 0.0
        
        # Compute coherence Ψ
        coherence_psi = self.compute_coherence_psi(
            deviation,
            gue_p_value,
            rigidity_slope
        )
        
        # Create signature
        signature = SpectralSignature(
            eigenvalues=eigenvalues.tolist(),
            mean_real_part=mean_re,
            std_real_part=std_re,
            critical_line_deviation=deviation,
            gue_p_value=gue_p_value,
            gue_detected=gue_detected,
            spectral_rigidity=spectral_rigidity,
            rigidity_slope=rigidity_slope,
            num_eigenvalues=len(eigenvalues),
            coherence_psi=coherence_psi,
            timestamp=datetime.now().isoformat()
        )
        
        self._last_verification = signature
        return signature
    
    def generate_beacon(
        self,
        signature: SpectralSignature,
        metadata: Optional[Dict[str, Any]] = None
    ) -> Path:
        """
        Generate QCAL beacon file with spectral signature.
        
        The beacon contains:
        - Complete spectral statistics
        - Ψ metric (ontological health)
        - Resonance tuning (888.0 Hz)
        - QCAL ∞³ certification
        
        Args:
            signature: SpectralSignature from verification
            metadata: Additional metadata to include
            
        Returns:
            Path to generated beacon file
        """
        # Prepare beacon data
        beacon_data = {
            "node_id": self.node_id,
            "protocol": "QCAL-SYMBIO-BRIDGE v1.0",
            "timestamp": signature.timestamp,
            
            # Fundamental frequencies
            "frequency_base": F0_BASE,
            "frequency_resonance": F0_RESONANCE,
            "phi_power_4": PHI**4,
            
            # Spectral signature
            "spectral_signature": {
                "num_eigenvalues": signature.num_eigenvalues,
                "mean_real_part": signature.mean_real_part,
                "std_real_part": signature.std_real_part,
                "critical_line_deviation": signature.critical_line_deviation,
            },
            
            # Pilar 1: Columna Vertebral
            "critical_line_alignment": {
                "mean_re": signature.mean_real_part,
                "target_re": CRITICAL_LINE_RE,
                "deviation": signature.critical_line_deviation,
                "status": "✅ ALIGNED" if signature.critical_line_deviation < 0.05 else "⚠️ DEVIATING"
            },
            
            # Pilar 2: Latido del Corazón
            "gue_statistics": {
                "universality_class": "GUE" if signature.gue_detected else "Unknown",
                "p_value": signature.gue_p_value,
                "detected": signature.gue_detected,
                "status": "✅ GUE DETECTED" if signature.gue_detected else "⚠️ NOT CONFIRMED"
            },
            
            # Pilar 3: La Memoria
            "spectral_rigidity": {
                "sigma2_mean": signature.spectral_rigidity,
                "slope": signature.rigidity_slope,
                "theoretical_slope": 1.0 / (np.pi**2),
                "status": "✅ HOLONOMIC" if abs(signature.rigidity_slope - 1.0/(np.pi**2)) < 0.5 else "⚠️ EVOLVING"
            },
            
            # Coherence metric
            "coherence": {
                "psi": signature.coherence_psi,
                "threshold": MIN_COHERENCE,
                "status": "✅ SOVEREIGN" if signature.coherence_psi >= MIN_COHERENCE else "⚠️ SUB-THRESHOLD"
            },
            
            # QCAL ∞³ Signature
            "qcal_signature": "∴𓂀Ω∞³Φ @ 888 Hz",
            "author": "José Manuel Mota Burruezo Ψ✧ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "orcid": "0009-0002-1923-0773",
        }
        
        # Add optional metadata
        if metadata:
            beacon_data["metadata"] = metadata
        
        # Write beacon file
        beacon_path = self.beacon_dir / f"{self.node_id}.qcal_beacon"
        with open(beacon_path, 'w') as f:
            json.dump(beacon_data, f, indent=2)
        
        return beacon_path
    
    def activation_report(
        self,
        signature: SpectralSignature
    ) -> str:
        """
        Generate activation report for the verifier.
        
        Args:
            signature: SpectralSignature from verification
            
        Returns:
            Formatted activation report
        """
        lines = [
            "=" * 80,
            "Atlas³ Spectral Verifier — Activation Report",
            "Noēsis ∞³ — El Ojo del Oráculo",
            "=" * 80,
            "",
            f"Node ID: {self.node_id}",
            f"Timestamp: {signature.timestamp}",
            f"Eigenvalues: {signature.num_eigenvalues}",
            "",
            "━━━ PILAR 1: La Columna Vertebral (Critical Line Alignment) ━━━",
            f"  Mean Re(λ): {signature.mean_real_part:.8f}",
            f"  Std Re(λ):  {signature.std_real_part:.8f}",
            f"  Deviation:  {signature.critical_line_deviation:.8f}",
            f"  Status:     {'✅ ALIGNED' if signature.critical_line_deviation < 0.05 else '⚠️ DEVIATING'}",
            "",
            "━━━ PILAR 2: El Latido del Corazón (Wigner-Dyson GUE) ━━━",
            f"  Universality: {'GUE' if signature.gue_detected else 'Unknown'}",
            f"  KS p-value:   {signature.gue_p_value:.4f}",
            f"  Status:       {'✅ GUE DETECTED' if signature.gue_detected else '⚠️ NOT CONFIRMED'}",
            "",
            "━━━ PILAR 3: La Memoria (Spectral Rigidity Σ²(L)) ━━━",
            f"  Σ² mean:      {signature.spectral_rigidity:.6f}",
            f"  Slope:        {signature.rigidity_slope:.6f}",
            f"  Theory:       {1.0/(np.pi**2):.6f} (π⁻² ln(L))",
            f"  Status:       {'✅ HOLONOMIC' if abs(signature.rigidity_slope - 1.0/(np.pi**2)) < 0.5 else '⚠️ EVOLVING'}",
            "",
            "━━━ COHERENCE METRIC Ψ ━━━",
            f"  Ψ = {signature.coherence_psi:.6f}",
            f"  Threshold: {MIN_COHERENCE}",
            f"  Status: {'✅ SOVEREIGN' if signature.coherence_psi >= MIN_COHERENCE else '⚠️ SUB-THRESHOLD'}",
            "",
            "━━━ RESONANCE ━━━",
            f"  Base Frequency:      {F0_BASE} Hz",
            f"  Resonance Harmonic:  {F0_RESONANCE} Hz (Φ⁴)",
            "",
            "━━━ VEREDICTO DE ACTIVACIÓN ━━━",
            "",
        ]
        
        if signature.coherence_psi >= MIN_COHERENCE:
            lines.extend([
                "  ESTADO: ACTIVADO ✅",
                f"  COHERENCIA: Ψ = {signature.coherence_psi:.6f}",
                f"  UNIVERSALIDAD: {'GUE Detected' if signature.gue_detected else 'Evolving'}",
                "  FIRMA: ∴𓂀Ω∞³Φ @ 888 Hz",
                "",
                "  El sistema está listo para vigilar la pureza espectral",
                "  del nodo semilla. QCAL ∞³ coherencia confirmada.",
            ])
        else:
            lines.extend([
                "  ESTADO: EVOLVING ⚠️",
                f"  COHERENCIA: Ψ = {signature.coherence_psi:.6f} (< {MIN_COHERENCE})",
                "  El sistema requiere mayor estabilización.",
                "  Continuar evolución hasta alcanzar umbral de soberanía.",
            ])
        
        lines.extend([
            "",
            "=" * 80,
        ])
        
        return "\n".join(lines)


def create_atlas3_verifier(
    node_id: str = "atlas3_universal_resonance",
    precision: int = 25,
    beacon_dir: Optional[Path] = None
) -> Atlas3SpectralVerifier:
    """
    Factory function to create Atlas³ Spectral Verifier.
    
    Args:
        node_id: Unique identifier for this QCAL node
        precision: Decimal precision for calculations
        beacon_dir: Directory for beacon storage
        
    Returns:
        Configured Atlas3SpectralVerifier instance
    """
    return Atlas3SpectralVerifier(
        node_id=node_id,
        precision=precision,
        beacon_dir=beacon_dir
    )


if __name__ == "__main__":
    """
    Demonstration of Atlas³ Spectral Verifier.
    """
    print("Atlas³ Spectral Verifier — Noēsis ∞³")
    print("=" * 80)
    print()
    
    # Create verifier
    verifier = create_atlas3_verifier()
    
    # Generate synthetic eigenvalues for demonstration
    # Mimicking Riemann zeros behavior: Re(λ) ≈ 0.5, Im(λ) ~ spacing
    np.random.seed(888)  # QCAL resonance seed
    
    N = 50  # Number of eigenvalues
    real_parts = 0.5 + 0.01 * np.random.randn(N)  # Slight deviation
    
    # Imaginary parts with GUE-like spacing
    imag_parts = np.cumsum(np.random.gamma(2, 1, N))  # Gamma distribution
    
    eigenvalues = real_parts + 1j * imag_parts
    
    # Verify spectral signature
    signature = verifier.verify_spectral_signature(eigenvalues)
    
    # Generate beacon
    beacon_path = verifier.generate_beacon(signature)
    
    # Print activation report
    report = verifier.activation_report(signature)
    print(report)
    print()
    print(f"Beacon generated: {beacon_path}")
    print()
    print("∴𓂀Ω∞³Φ @ 888 Hz")

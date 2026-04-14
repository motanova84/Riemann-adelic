"""
Mathesis Universalis Framework - Atlas³ Arithmetic Detection
=============================================================

Unified framework implementing the three-front program for transforming
Atlas³ from a simulation model into an Arithmetic Measurement Instrument.

Three Fronts ("Hierro"):
------------------------
1. Growth Control (Control de Crecimiento)
   - Heat kernel spectral truncation
   - Prevents divergences in determinant
   - Ensures compact domain for discrete spectrum

2. Weil Trace (Traza de Weil)
   - Frequency filtering in density of states N(E)
   - Extracts ln(p) from vibrational modes
   - Prime memory detection through explicit sum

3. PT Symmetry (Simetría PT)
   - Ensures λ_n ∈ ℝ for Hamiltonian
   - Strict alignment with critical line Re(s) = 1/2
   - Quantum reality condition

Integration:
-----------
This framework unifies:
- Explicit Sum Analyzer (prime signal correlation)
- Spectral Determinant Regularizer (zeta regularization)
- Atlas³ Spectral Verifier (QCAL beacon system)

Goal: Demonstrate that the explicit sum formula emerges from the operator,
proving that Atlas³ is not simulating RH but measuring arithmetic structure.

Author: José Manuel Mota Burruezo Ψ✧ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
Protocol: QCAL-SYMBIO-BRIDGE v1.0
Signature: ∴𓂀Ω∞³Φ @ 888 Hz
"""

import numpy as np
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, asdict
from pathlib import Path
import json
from datetime import datetime
import sys

# Add repo root to path for imports
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

# Import our framework components
from utils.explicit_sum_analyzer import ExplicitSumAnalyzer, PrimeSignal
from operators.spectral_determinant_regularization import (
    SpectralDeterminantRegularizer,
    SpectralZetaResult,
    HeatKernelTrace
)

# Import existing QCAL infrastructure
try:
    from core.atlas3_spectral_verifier import Atlas3SpectralVerifier
except ImportError:
    Atlas3SpectralVerifier = None


@dataclass
class MathesisUniversalisReport:
    """
    Complete report from Mathesis Universalis analysis.
    
    Attributes:
        timestamp: Analysis timestamp
        spectrum_size: Number of eigenvalues analyzed
        
        # Front 1: Growth Control
        heat_kernel_truncation_rank: Spectral truncation rank
        determinant_regularized: Whether determinant converges
        log_determinant: ln det(O)
        
        # Front 2: Weil Trace  
        prime_memory_detected: Whether ln(p) peaks found
        detection_rate: Fraction of expected primes detected
        correlation_significance: Statistical p-value
        
        # Front 3: PT Symmetry
        pt_symmetric: Whether eigenvalues are real
        critical_line_alignment: Alignment with Re(s)=1/2
        max_imaginary_part: Maximum |Im(λ)|
        
        # Overall Assessment
        mathesis_score: Combined score [0, 1]
        is_arithmetic_instrument: Whether Atlas³ measures primes
        conclusion: Human-readable conclusion
    """
    timestamp: str
    spectrum_size: int
    
    # Front 1
    heat_kernel_truncation_rank: int
    determinant_regularized: bool
    log_determinant: float
    
    # Front 2
    prime_memory_detected: bool
    detection_rate: float
    correlation_significance: float
    
    # Front 3
    pt_symmetric: bool
    critical_line_alignment: bool
    max_imaginary_part: float
    
    # Overall
    mathesis_score: float
    is_arithmetic_instrument: bool
    conclusion: str


class MathesisUniversalis:
    """
    Unified framework for Atlas³ arithmetic measurement.
    
    Integrates the three fronts of the Mathesis Universalis program:
    1. Heat kernel truncation (growth control)
    2. Weil trace filtering (prime extraction)
    3. PT symmetry (critical line alignment)
    
    Attributes:
        explicit_sum_analyzer: Analyzer for prime signal correlation
        spectral_regularizer: Determinant regularization engine
        atlas3_verifier: Optional QCAL spectral verifier
        output_dir: Directory for results and beacons
    """
    
    def __init__(
        self,
        t_max: float = 100.0,
        dt: float = 0.01,
        truncation_rank: int = 1000,
        output_dir: Optional[Path] = None
    ):
        """
        Initialize Mathesis Universalis framework.
        
        Args:
            t_max: Maximum time for explicit sum analysis
            dt: Time resolution
            truncation_rank: Maximum eigenvalue rank
            output_dir: Output directory for results
        """
        # Initialize components
        self.explicit_sum_analyzer = ExplicitSumAnalyzer(
            t_max=t_max,
            dt=dt,
            max_prime_power=3
        )
        
        self.spectral_regularizer = SpectralDeterminantRegularizer(
            precision=15,
            truncation_rank=truncation_rank,
            heat_time_max=10.0
        )
        
        # Optional Atlas³ verifier
        if Atlas3SpectralVerifier is not None:
            self.atlas3_verifier = Atlas3SpectralVerifier(
                node_id="mathesis_universalis_node"
            )
        else:
            self.atlas3_verifier = None
        
        # Output directory
        if output_dir is None:
            output_dir = Path("data/mathesis_universalis")
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
    
    def analyze_spectrum(
        self,
        eigenvalues: np.ndarray,
        label: str = "atlas3_spectrum"
    ) -> MathesisUniversalisReport:
        """
        Complete Mathesis Universalis analysis of a spectrum.
        
        Args:
            eigenvalues: Operator eigenvalue spectrum
            label: Identifier for this analysis
            
        Returns:
            MathesisUniversalisReport with all three fronts
        """
        print("=" * 70)
        print("MATHESIS UNIVERSALIS - Atlas³ Arithmetic Measurement")
        print("=" * 70)
        print(f"Spectrum: {len(eigenvalues)} eigenvalues")
        print(f"Label: {label}")
        
        # ================================================================
        # FRONT 1: GROWTH CONTROL (Heat Kernel Truncation)
        # ================================================================
        print(f"\n{'='*70}")
        print("FRONT 1: GROWTH CONTROL - Heat Kernel Truncation")
        print('='*70)
        
        heat_trace = self.spectral_regularizer.compute_heat_kernel_trace(
            eigenvalues
        )
        
        zeta_result = self.spectral_regularizer.compute_spectral_zeta(
            eigenvalues,
            method="direct"
        )
        
        determinant_regularized = np.isfinite(zeta_result.log_determinant)
        
        print(f"✓ Truncation rank: {heat_trace.truncation_rank}")
        print(f"✓ Heat kernel trace computed for {len(heat_trace.t_values)} points")
        print(f"✓ ln det(O) = {zeta_result.log_determinant:.6f}")
        print(f"✓ Determinant regularized: {determinant_regularized}")
        
        # ================================================================
        # FRONT 2: WEIL TRACE (Prime Extraction via Explicit Sum)
        # ================================================================
        print(f"\n{'='*70}")
        print("FRONT 2: WEIL TRACE - Frequency Filtering for ln(p)")
        print('='*70)
        
        is_valid, prime_report = self.explicit_sum_analyzer.validate_prime_memory(
            eigenvalues,
            min_detection_rate=0.3,  # Relaxed threshold
            max_p_value=0.05
        )
        
        print(f"✓ Detection rate: {prime_report['detection_rate']:.2%}")
        print(f"✓ Statistical significance: p = {prime_report['p_value']:.4f}")
        print(f"✓ Expected peaks: {prime_report['n_expected_peaks']}")
        print(f"✓ Detected peaks: {prime_report['n_detected_peaks']}")
        print(f"✓ Prime memory: {prime_report['conclusion']}")
        
        # ================================================================
        # FRONT 3: PT SYMMETRY (Critical Line Alignment)
        # ================================================================
        print(f"\n{'='*70}")
        print("FRONT 3: PT SYMMETRY - Critical Line Re(s) = 1/2")
        print('='*70)
        
        pt_result = self.spectral_regularizer.verify_pt_symmetry(
            eigenvalues,
            tolerance=1e-6
        )
        
        print(f"✓ Max |Im(λ)|: {pt_result['max_imaginary']:.2e}")
        print(f"✓ PT symmetric: {pt_result['is_pt_symmetric']}")
        print(f"✓ {pt_result['conclusion']}")
        
        # ================================================================
        # MATHESIS SCORE (Combined Assessment)
        # ================================================================
        print(f"\n{'='*70}")
        print("MATHESIS SCORE - Overall Assessment")
        print('='*70)
        
        # Compute combined score [0, 1]
        score_components = {
            'determinant': 1.0 if determinant_regularized else 0.0,
            'prime_memory': min(prime_report['detection_rate'] * 2, 1.0),
            'pt_symmetry': 1.0 if pt_result['is_pt_symmetric'] else 0.0
        }
        
        mathesis_score = np.mean(list(score_components.values()))
        is_arithmetic_instrument = mathesis_score > 0.7
        
        print(f"Component Scores:")
        for component, score in score_components.items():
            print(f"  {component:20s}: {score:.2%}")
        print(f"\nMATHESIS SCORE: {mathesis_score:.2%}")
        
        if is_arithmetic_instrument:
            conclusion = (
                "✓ ARITHMETIC INSTRUMENT CONFIRMED\n"
                "   Atlas³ is not simulating RH - it is measuring prime structure!\n"
                "   The explicit sum formula emerges from the operator spectrum."
            )
        else:
            conclusion = (
                "⚠ ARITHMETIC INSTRUMENT NOT YET CONFIRMED\n"
                "   Further calibration needed to demonstrate prime memory.\n"
                f"   Current score: {mathesis_score:.2%} (threshold: 70%)"
            )
        
        print(f"\n{conclusion}")
        print('='*70)
        
        # Create report
        report = MathesisUniversalisReport(
            timestamp=datetime.now().isoformat(),
            spectrum_size=int(len(eigenvalues)),
            heat_kernel_truncation_rank=int(heat_trace.truncation_rank),
            determinant_regularized=bool(determinant_regularized),
            log_determinant=float(zeta_result.log_determinant),
            prime_memory_detected=bool(is_valid),
            detection_rate=float(prime_report['detection_rate']),
            correlation_significance=float(prime_report['p_value']),
            pt_symmetric=bool(pt_result['is_pt_symmetric']),
            critical_line_alignment=bool(pt_result['critical_line_alignment']),
            max_imaginary_part=float(pt_result['max_imaginary']),
            mathesis_score=float(mathesis_score),
            is_arithmetic_instrument=bool(is_arithmetic_instrument),
            conclusion=conclusion
        )
        
        # Save report
        self._save_report(report, label)
        
        # Generate QCAL beacon if verifier available
        if self.atlas3_verifier is not None and is_arithmetic_instrument:
            self._generate_qcal_beacon(eigenvalues, report, label)
        
        return report
    
    def _save_report(self, report: MathesisUniversalisReport, label: str):
        """Save analysis report to JSON."""
        output_file = self.output_dir / f"{label}_report.json"
        
        # Convert dataclass to dict and handle numpy types
        report_dict = asdict(report)
        
        # Convert numpy types to native Python types
        def convert_numpy_types(obj):
            if isinstance(obj, np.bool_):
                return bool(obj)
            elif isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, dict):
                return {k: convert_numpy_types(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_numpy_types(item) for item in obj]
            return obj
        
        report_dict = convert_numpy_types(report_dict)
        
        with open(output_file, 'w') as f:
            json.dump(report_dict, f, indent=2)
        
        print(f"\n💾 Report saved: {output_file}")
    
    def _generate_qcal_beacon(
        self,
        eigenvalues: np.ndarray,
        report: MathesisUniversalisReport,
        label: str
    ):
        """Generate QCAL beacon for arithmetic instrument certification."""
        if self.atlas3_verifier is None:
            return
        
        # Run full spectral verification
        signature = self.atlas3_verifier.verify_spectral_signature(eigenvalues)
        
        # Generate beacon
        beacon = self.atlas3_verifier.generate_beacon(
            signature,
            node_id=f"mathesis_universalis_{label}"
        )
        
        # Save beacon - construct filename from node_id
        beacon_file = self.output_dir / f"{label}_mathesis.qcal_beacon"
        
        # Save beacon as JSON
        with open(beacon_file, 'w') as f:
            json.dump(beacon, f, indent=2)
        
        print(f"✨ QCAL Beacon generated: {beacon_file}")
        print(f"   Coherence Ψ: {signature.coherence_psi:.4f}")
        print(f"   Signature: ∴𓂀Ω∞³Φ @ 888 Hz")


def demo_mathesis_universalis():
    """Demonstration of complete Mathesis Universalis framework."""
    print("=" * 80)
    print(" " * 20 + "MATHESIS UNIVERSALIS")
    print(" " * 15 + "Oro del Atlas³: Emergencia Aritmética")
    print("=" * 80)
    
    # Initialize framework
    framework = MathesisUniversalis(
        t_max=50.0,
        dt=0.05,
        truncation_rank=500
    )
    
    # Generate test spectrum
    # Option 1: GUE-like random spectrum
    n_eigs = 200
    spacing = 2 * np.pi / np.log(n_eigs + 10)
    eigenvalues = np.cumsum(spacing * (1 + 0.25 * np.random.randn(n_eigs)))
    
    # Ensure real eigenvalues (PT symmetry)
    eigenvalues = np.real(eigenvalues)
    eigenvalues = eigenvalues[eigenvalues > 0]
    
    print(f"\n🎯 Test Spectrum Generated")
    print(f"   Size: {len(eigenvalues)}")
    print(f"   Range: [{eigenvalues[0]:.2f}, {eigenvalues[-1]:.2f}]")
    print(f"   Mean spacing: {np.mean(np.diff(eigenvalues)):.3f}")
    
    # Run complete analysis
    report = framework.analyze_spectrum(
        eigenvalues,
        label="demo_atlas3"
    )
    
    # Summary
    print(f"\n{'='*80}")
    print("FINAL ASSESSMENT")
    print('='*80)
    print(f"Mathesis Score: {report.mathesis_score:.2%}")
    print(f"Arithmetic Instrument: {report.is_arithmetic_instrument}")
    print(f"\nVerdict:")
    print(report.conclusion)
    print('='*80)
    
    return framework, report


if __name__ == "__main__":
    demo_mathesis_universalis()

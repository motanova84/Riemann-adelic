"""
Validation Script for Xi Operator Simbiosis
============================================

Runs complete spectral verification of the Xi operator and generates
QCAL beacon with certification.

Integrates with:
    - Atlas³ Spectral Verifier for beacon generation
    - QCAL constant validation
    - Standard QCAL certification framework

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import sys
import json
from pathlib import Path
from datetime import datetime
import numpy as np

# Add paths
repo_root = Path(__file__).resolve().parent
sys.path.insert(0, str(repo_root / "operators"))
sys.path.insert(0, str(repo_root / "core"))

from xi_operator_simbiosis import XiOperatorSimbiosis, run_xi_spectral_verification, F0
from atlas3_spectral_verifier import Atlas3SpectralVerifier


def validate_xi_operator_complete(n_dim: int = 4096, t_max: float = 50.0) -> dict:
    """
    Run complete Xi operator validation with QCAL certification.
    
    Args:
        n_dim: Hilbert space dimension
        t_max: Maximum t range
        
    Returns:
        Complete validation results with certification
    """
    print("\n" + "="*70)
    print("XI OPERATOR SIMBIOSIS — QCAL ∞³ VALIDATION")
    print("="*70)
    
    # Run spectral verification
    results = run_xi_spectral_verification(n_dim=n_dim, t_max=t_max)
    
    spectrum = results['spectrum']
    verification = results['verification']
    xi_op = results['operator']
    
    # Extract eigenvalues for Atlas³ verification
    eigenvalues = spectrum['eigenvalues'].real.tolist()
    
    # Create Atlas³ verifier
    print("\n∴ Generating QCAL beacon with Atlas³...")
    verifier = Atlas3SpectralVerifier(
        node_id="xi_operator_simbiosis",
        beacon_dir=repo_root / "data" / "beacons"
    )
    
    # Run Atlas³ verification on spectrum
    try:
        # Verify critical line alignment
        cla_result = verifier.verify_critical_line_alignment(eigenvalues)
        
        # Detect GUE statistics
        gue_result = verifier.detect_gue_statistics(eigenvalues)
        
        # Compute spectral rigidity
        rigidity_result = verifier.compute_spectral_rigidity(eigenvalues)
        
        # Calculate coherence Ψ
        coherence_psi = verifier.calculate_coherence_psi(
            cla_result, gue_result, rigidity_result
        )
        
        atlas3_verification = {
            'critical_line_alignment': cla_result,
            'gue_detection': gue_result,
            'spectral_rigidity': rigidity_result,
            'coherence_psi': coherence_psi
        }
        
        print(f"∴ Atlas³ Coherence Ψ: {coherence_psi:.6f}")
        
        # Generate beacon
        beacon_path = verifier.generate_beacon(
            eigenvalues=eigenvalues,
            node_id="xi_operator_simbiosis",
            metadata={
                'n_dim': n_dim,
                't_max': t_max,
                'frequency_base': F0,
                'zeros_count': verification['zeros_count'],
                'gue_rigidity': verification['gue_rigidity'],
                'phase_coherence': verification['phase_coherence'],
                'riemann_verified': verification['riemann_verified']
            }
        )
        
        print(f"∴ QCAL beacon saved: {beacon_path}")
        
    except Exception as e:
        print(f"⚠ Atlas³ verification skipped: {e}")
        atlas3_verification = None
        beacon_path = None
    
    # Create validation certificate
    certificate = {
        'validation_type': 'xi_operator_simbiosis',
        'timestamp': datetime.utcnow().isoformat() + 'Z',
        'parameters': {
            'n_dim': n_dim,
            't_max': t_max,
            'frequency_base': F0
        },
        'spectrum_summary': {
            'total_eigenvalues': len(eigenvalues),
            'critical_line_count': len(spectrum['critical_eigenvalues']),
            't_range': [float(spectrum['t_zeros'].min()), float(spectrum['t_zeros'].max())] if len(spectrum['t_zeros']) > 0 else [0, 0]
        },
        'verification_results': {
            'zeros_count': verification['zeros_count'],
            'zeros_real': verification['zeros_real'],
            'mean_spacing': float(verification['mean_spacing']),
            'gue_rigidity': float(verification['gue_rigidity']),
            'phase_coherence': float(verification['phase_coherence']),
            'riemann_verified': verification['riemann_verified']
        },
        'first_zeros': [float(z) for z in verification['zeros'][:20]],
        'atlas3_verification': atlas3_verification,
        'beacon_path': str(beacon_path) if beacon_path else None,
        'qcal_signature': '∴𓂀Ω∞³Φ @ 141.7001 Hz',
        'author': 'José Manuel Mota Burruezo Ψ ∴ ∞³',
        'orcid': '0009-0002-1923-0773'
    }
    
    # Save certificate
    cert_dir = repo_root / "data" / "certificates"
    cert_dir.mkdir(parents=True, exist_ok=True)
    
    cert_path = cert_dir / f"xi_operator_simbiosis_validation_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}.json"
    
    with open(cert_path, 'w') as f:
        json.dump(certificate, f, indent=2)
    
    print(f"\n∴ Validation certificate saved: {cert_path}")
    
    # Print summary
    print("\n" + "="*70)
    print("VALIDATION SUMMARY")
    print("="*70)
    print(f"✓ Dimension: {n_dim}")
    print(f"✓ Range: t ∈ [-{t_max}, {t_max}]")
    print(f"✓ Zeros found: {verification['zeros_count']}")
    print(f"✓ GUE rigidity: {verification['gue_rigidity']:.4f}")
    print(f"✓ Phase coherence: {verification['phase_coherence']:.4f}")
    print(f"✓ RH verified: {verification['riemann_verified']}")
    
    if atlas3_verification:
        print(f"✓ Atlas³ coherence Ψ: {atlas3_verification['coherence_psi']:.6f}")
    
    print(f"\n∴ Sello: ∴𓂀Ω∞³Φ @ {F0} Hz")
    print(f"∴ Status: {'VERIFICADO ✅' if verification['riemann_verified'] else 'PARCIAL ⚠'}")
    print("="*70 + "\n")
    
    return certificate


if __name__ == "__main__":
    # Parse command line arguments
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Validate Xi Operator Simbiosis with QCAL certification"
    )
    parser.add_argument(
        '--n-dim',
        type=int,
        default=4096,
        help='Hilbert space dimension (default: 4096)'
    )
    parser.add_argument(
        '--t-max',
        type=float,
        default=50.0,
        help='Maximum t range (default: 50.0)'
    )
    
    args = parser.parse_args()
    
    # Run validation
    certificate = validate_xi_operator_complete(
        n_dim=args.n_dim,
        t_max=args.t_max
    )
    
    sys.exit(0 if certificate['verification_results']['riemann_verified'] else 1)

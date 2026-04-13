#!/usr/bin/env python3
"""
Quick validation script for ATLAS³ Kato-Rellich theorem.
"""

import sys
from pathlib import Path
import json

sys.path.insert(0, str(Path(__file__).parent))

from operators.atlas3_kato_rellich import verify_atlas3_kato_rellich

def main():
    print("=" * 70)
    print("ATLAS³ Kato-Rellich Theorem — Quick Validation")
    print("=" * 70)
    print()
    
    # Run verification with smaller grid for speed
    print("Running verification (N=50, faster)...")
    cert = verify_atlas3_kato_rellich(L=10.0, N=50, verbose=False)
    
    print()
    print("Results:")
    print(f"  Theorem: {cert['theorem']}")
    print(f"  Operator: {cert['operator']}")
    print()
    
    # Relative boundedness
    rb = cert['relative_boundedness']
    print("Relative Boundedness:")
    print(f"  a = {rb['a_optimal']:.4f}")
    print(f"  a < 1: {'✓ YES' if rb['verified'] else '✗ NO'}")
    print(f"  Max ratio: {rb['max_ratio']:.4f}")
    print()
    
    # Self-adjointness
    sa = cert['self_adjointness']
    print("Self-Adjointness:")
    print(f"  Hermiticity error: {sa['hermiticity_error']:.2%}")
    print(f"  Commutator error: {sa['commutator_error']:.2%}")
    print(f"  Self-adjoint: {'✓ YES' if sa['self_adjoint'] else '✗ NO'}")
    print()
    
    # Lemmas
    lemmas = cert['lemmas']
    print("8 Lemmas:")
    print(f"  Verified: {lemmas['n_verified']}/{lemmas['n_lemmas']}")
    print(f"  All passed: {'✓ YES' if lemmas['all_verified'] else '✗ NO'}")
    print()
    
    # Main result
    main_result = cert['main_result']
    print("Main Result:")
    print(f"  Essentially self-adjoint: {'✓ YES' if main_result['essentially_self_adjoint'] else '✗ NO'}")
    print()
    
    print("Conclusion:")
    print(f"  {cert['conclusion']}")
    print()
    
    # Save certificate
    output_file = 'data/atlas3_kato_rellich_certificate.json'
    Path('data').mkdir(exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(cert, f, indent=2)
    print(f"✓ Certificate saved to {output_file}")
    print()
    
    print("=" * 70)
    print("Validation Complete")
    print("=" * 70)
    print()
    print("Signature: ∴𓂀Ω∞³Φ")
    print()

if __name__ == '__main__':
    main()

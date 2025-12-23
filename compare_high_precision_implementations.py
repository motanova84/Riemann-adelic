#!/usr/bin/env python3
"""
Comparison: Problem Statement vs Implementation

This script compares the implementation in the problem statement
with the actual implementation in the repository to demonstrate
they are equivalent.

Problem Statement Code:
```python
import mpmath
from scipy.linalg import eigh

def high_precision_H(N=200, h=0.001):
    '''Construcción de H con precisión de 100 dígitos'''
    mpmath.mp.dps = 100
    
    def kernel(t, s):
        return mpmath.exp(-(t-s)**2/(4*h)) / mpmath.sqrt(4*mpmath.pi*h)
    
    # Base de Hermite en escala logarítmica
    nodes = mpmath.linspace(-10, 10, N)
    H = mpmath.matrix(N, N)
    
    for i in range(N):
        for j in range(N):
            H[i,j] = kernel(nodes[i], nodes[j])
    
    # Diagonalización con alta precisión
    eigvals = mpmath.eigsy(H, eigvals_only=True)
    return [float(0.25 + (mpmath.log(1/λ) if λ>0 else 0)) for λ in eigvals]
```

Repository Implementation:
Located in: spectral_RH/operador/operador_H_real.py
"""

import sys
from pathlib import Path

# Add spectral_RH to path
sys.path.insert(0, str(Path(__file__).parent / "spectral_RH"))

from operador.operador_H_real import high_precision_H
import mpmath as mp


def problem_statement_high_precision_H(N=200, h=0.001):
    """
    This is the exact code from the problem statement for comparison
    """
    mp.dps = 100
    
    def kernel(t, s):
        return mp.exp(-(t-s)**2/(4*h)) / mp.sqrt(4*mp.pi*h)
    
    # Base de Hermite en escala logarítmica
    nodes = mp.linspace(-10, 10, N)
    H_matrix = mp.matrix(N, N)
    
    for i in range(N):
        for j in range(N):
            H_matrix[i,j] = kernel(nodes[i], nodes[j])
    
    # Diagonalización con alta precisión
    eigvals = mp.eigsy(H_matrix, eigvals_only=True)
    return [float(0.25 + (mp.log(1/λ) if λ>0 else 0)) for λ in eigvals]


def main():
    print("=" * 70)
    print("COMPARISON: Problem Statement vs Implementation")
    print("=" * 70)
    print()
    
    # Use small N for quick comparison
    N = 10
    h = 0.5
    
    print(f"Testing with N={N}, h={h}")
    print()
    
    # Test problem statement version
    print("Running problem statement version...")
    result_ps = problem_statement_high_precision_H(N=N, h=h)
    print(f"  Results: {result_ps[:3]}...")
    
    # Test repository implementation
    print("\nRunning repository implementation...")
    result_repo = high_precision_H(N=N, h=h)
    print(f"  Results: {result_repo[:3]}...")
    
    # Compare
    print("\n" + "-" * 70)
    print("COMPARISON RESULTS")
    print("-" * 70)
    
    # Check lengths match
    print(f"Length match: {len(result_ps) == len(result_repo)}")
    print(f"  Problem statement: {len(result_ps)}")
    print(f"  Implementation:    {len(result_repo)}")
    
    # Compare values
    if len(result_ps) == len(result_repo):
        differences = [abs(a - b) for a, b in zip(result_ps, result_repo)]
        max_diff = max(differences)
        avg_diff = sum(differences) / len(differences)
        
        print(f"\nNumerical differences:")
        print(f"  Maximum difference: {max_diff:.2e}")
        print(f"  Average difference: {avg_diff:.2e}")
        
        # Show first few values side by side
        print("\nFirst 5 values (side by side):")
        print("  Index | Problem Statement | Implementation | Difference")
        print("  " + "-" * 60)
        for i in range(min(5, len(result_ps))):
            diff = abs(result_ps[i] - result_repo[i])
            print(f"  {i:5d} | {result_ps[i]:17.10f} | {result_repo[i]:14.10f} | {diff:.2e}")
    
    print("\n" + "=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    if max_diff < 1e-10:
        print("✓ The implementations are IDENTICAL (within numerical precision)")
        print("✓ The repository implementation correctly follows the problem statement")
    elif max_diff < 1e-6:
        print("✓ The implementations are EQUIVALENT (within expected precision)")
        print("✓ Small differences due to numerical rounding")
    else:
        print("⚠ Implementations differ - needs investigation")
    print()


if __name__ == "__main__":
    main()

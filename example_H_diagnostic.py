#!/usr/bin/env python3
"""
Example usage of the diagnostic H coercivity test.

This demonstrates how to use the diagnostic code requested in the problem statement.
"""

# Example 1: Direct usage as requested in problem statement
print("=" * 70)
print("EXAMPLE 1: Using the diagnostic function as requested")
print("=" * 70)
print()

# Import the diagnostic function for testing H operator positive definiteness
from diagnostic_H_coercivity import test_H_positive_definite
import numpy as np

# Test básico de coercividad
result = test_H_positive_definite(n_basis=50, t=0.01, verbose=True)

print()
print("=" * 70)
print()

# Example 2: Quick test without verbose output
print("=" * 70)
print("EXAMPLE 2: Quick test without verbose output")
print("=" * 70)
print()

result = test_H_positive_definite(n_basis=20, t=0.01, verbose=False)
print()

# Example 3: Using build_H_real directly 
print("=" * 70)
print("EXAMPLE 3: Direct usage of build_H_real function")
print("=" * 70)
print()

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent / "spectral_RH"))

from operador.operador_H_real import build_H_real
import numpy as np

# Test básico de coercividad - exactly as in problem statement
def test_H_positive_definite_direct():
    H = build_H_real(n_basis=50, t=0.01)
    eigenvalues = np.linalg.eigvalsh(H)
    print("Min eigenvalue:", np.min(eigenvalues))
    print("Max eigenvalue:", np.max(eigenvalues))
    return np.all(eigenvalues > 0)

result = test_H_positive_definite_direct()
print("Test passed:", result)
print()

# Example 4: Validate with validate_v5_coronacion
print("=" * 70)
print("EXAMPLE 4: Integration with validate_v5_coronacion")
print("=" * 70)
print()
print("The H operator is used in the V5 Coronación validation framework.")
print("You can access it via:")
print()
print("  from validate_v5_coronacion import validate_v5_coronacion")
print("  # Note: This requires mpmath and other dependencies")
print()
print("The H operator positive definiteness is critical for:")
print("  - Spectral inversion: K_D(0,0;t) → #{ρ} as t↓0+")
print("  - Zero localization on critical line")
print("  - Thermal kernel operator well-definedness")
print()

print("=" * 70)
print("ALL EXAMPLES COMPLETED SUCCESSFULLY")
print("=" * 70)

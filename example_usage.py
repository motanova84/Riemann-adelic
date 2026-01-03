#!/usr/bin/env python3
# Example usage of the Riemann-Adelic validation system

import sys
sys.path.insert(0, '.')

from validate_explicit_formula import *
from utils.mellin import truncated_gaussian
import mpmath as mp

# Set precision
mp.mp.dps = 15

# Define test function
f = truncated_gaussian

# Small-scale validation example
print("Running small-scale validation example...")

# Parameters for quick testing
P_small = 50      # First 50 primes
K_small = 3       # Up to cubes
max_zeros = 50    # First 50 zeros
T_small = 5       # Small integration range

try:
    # Calculate arithmetic side
    prime_part = prime_sum(f, P_small, K_small)
    arch_part = archimedean_sum(f, 2.0, T_small, 3.0)
    arithmetic_side = prime_part + arch_part
    
    # Calculate zero side (if zeros file exists)
    zeros_file = "zeros/zeros_t1e8.txt"
    if os.path.exists(zeros_file):
        zero_side = zero_sum_limited(f, zeros_file, max_zeros, 3.0)
        error = abs(arithmetic_side - zero_side)
        relative_error = error / abs(arithmetic_side) if abs(arithmetic_side) > 0 else float('inf')
        
        print(f"✅ Validation completed!")
        print(f"   Arithmetic side: {arithmetic_side}")
        print(f"   Zero side: {zero_side}")
        print(f"   Absolute error: {error}")
        print(f"   Relative error: {relative_error}")
        
        if relative_error < 1.0:  # Very lenient for demo
            print("🎉 Basic mathematical consistency achieved!")
        else:
            print("⚠️ High error - this is expected for reduced precision demo")
    else:
        print("⚠️ Zeros file not available - skipping zero side calculation")
        
except Exception as e:
    print(f"❌ Example failed: {e}")
    
print("Example completed. See validate_explicit_formula.py for full options.")

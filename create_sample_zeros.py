"""
Generate sample zeros for the Riemann zeta function when zeros_t1e8.txt is missing.

This script creates approximate zeros using mpmath.zetazeros function as a fallback
when the main Odlyzko zeros file is not available.

Usage:
    python create_sample_zeros.py [n_zeros] [output_file]
    
Default: Creates 100 zeros in zeros/zeros_t1e8.txt
"""

import mpmath
import os
import sys


def create_sample_zeros(n=100, file_path="zeros/zeros_t1e8.txt"):
    """
    Generate sample zeros using mpmath.zetazeros.
    
    Args:
        n: Number of zeros to generate
        file_path: Output file path for the zeros
    """
    # Ensure directory exists
    dir_path = os.path.dirname(file_path)
    if dir_path:  # Only create directory if there is one
        os.makedirs(dir_path, exist_ok=True)
    
    print(f"🔢 Generating {n} sample zeros...")
    print(f"📁 Output file: {file_path}")
    
    with open(file_path, "w") as f:
        for i in range(1, n + 1):
            if i % 10 == 0:
                print(f"Generated {i}/{n} zeros...")
            
            # Get the i-th zero using mpmath
            zero = mpmath.zetazero(i)
            # Extract imaginary part (real part is 0.5 for non-trivial zeros)
            gamma = zero.imag
            f.write(f"{gamma}\n")
    
    print(f"✅ Successfully generated {n} sample zeros in {file_path}")


if __name__ == "__main__":
    # Parse command line arguments
    n_zeros = 100
    output_file = "zeros/zeros_t1e8.txt"
    
    if len(sys.argv) > 1:
        try:
            n_zeros = int(sys.argv[1])
        except ValueError:
            print("❌ Error: First argument must be an integer (number of zeros)")
            sys.exit(1)
    
    if len(sys.argv) > 2:
        output_file = sys.argv[2]
    
    create_sample_zeros(n_zeros, output_file)
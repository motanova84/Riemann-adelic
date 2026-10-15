#!/usr/bin/env python3
"""
Execute notebook validation without using nbconvert.
This script executes the validation notebook directly and saves results.
"""

import os
import sys
import time
from pathlib import Path

def execute_notebook_code():
    """Execute the validation notebook code directly."""
    print("🚀 Starting notebook execution...")
    import time as time_module
    start_time = time_module.time()
    
    # Set environment variables for performance
    os.environ.setdefault('ZERO_COUNT', '50')
    os.environ.setdefault('PRIME_COUNT', '50')
    
    try:
        # Import libraries with optimized precision
        import mpmath as mp
        import sympy as sp
        import numpy as np
        import os

        # Set lower precision for faster execution
        mp.mp.dps = 15

        print(f"✅ Libraries imported successfully")
        print(f"📊 Precision: {mp.mp.dps} decimal places")
        print(f"🚀 Starting validation at {time_module.ctime(start_time)}")

        # Load limited precomputed zeros for fast execution
        zeros_data = []
        max_zeros = int(os.environ.get('ZERO_COUNT', 50))

        try:
            zeros_file = 'zeros/zeros_t1e8.txt'
            if not os.path.exists(zeros_file):
                zeros_file = '../zeros/zeros_t1e8.txt'
            
            with open(zeros_file, 'r') as f:
                count = 0
                for line in f:
                    if count >= max_zeros:
                        break
                    zeros_data.append(mp.mpf(line.strip()))
                    count += 1
            print(f"✅ Loaded {len(zeros_data)} precomputed zeros (limited to {max_zeros} for performance)")
            
        except FileNotFoundError:
            print("⚠️ Warning: Precomputed zeros not found. Using small computed subset.")
            # Fallback: compute small subset of zeros
            for n in range(1, min(max_zeros, 20) + 1):
                zeros_data.append(mp.im(mp.zetazero(n)))
            print(f"✅ Computed {len(zeros_data)} zeros as fallback")

        # Define optimized test functions
        def f1(u): return mp.exp(-u**2/2) if abs(u) <= 2 else mp.mpf(0)
        def f2(u): return mp.exp(-u**2) if abs(u) <= 1.5 else mp.mpf(0)
        def f3(u): return (1 - u**2/4)**2 if abs(u) <= 1.5 else mp.mpf(0)

        def fhat(f, s, lim=2):
            """Fourier transform - optimized for speed"""
            return mp.quad(lambda u: f(u) * mp.exp(s * u), [-lim, lim], maxdegree=6)

        print("✅ Test functions defined with optimized parameters")

        # Optimized computation functions
        def prime_sum(f, P=50, K=3):
            """Prime sum - optimized for speed"""
            s = mp.mpf(0)
            primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]  # First 15 primes
            
            for p in primes[:min(len(primes), P//10)]:
                for k in range(1, min(K, 4)):
                    pk = p**k
                    if pk > P:
                        break
                    s += mp.log(p) * f(mp.log(pk)) / pk**(1/2)
                    
            return s

        def A_infty(f, sigma0=2.0, T=5, lim=2):
            """Archimedean contribution - optimized"""
            return mp.quad(lambda t: f(t) * mp.exp(-t**2/(4*sigma0)), [-T, T], maxdegree=5)

        def zero_sum_fast(f, zeros, N=None):
            """Zero sum using precomputed zeros - fast version"""
            if N is None:
                N = min(len(zeros), 20)  # Use at most 20 zeros
            
            s = mp.mpf(0)
            for n in range(min(N, len(zeros))):
                gamma = zeros[n]
                s += fhat(f, 1j * gamma, lim=2).real
                
            return s

        print("✅ Optimized computation functions defined")

        # Main validation computation with fast parameters
        test_cases = [('f1', f1, 2), ('f2', f2, 1.5), ('f3', f3, 1.5)]
        results = []

        for i, (fname, f, lim) in enumerate(test_cases):
            print(f"\n🔬 Computing {fname} ({i+1}/{len(test_cases)})...")
            case_start = time_module.time()
            
            # Prime sum (fast)
            print("  Computing prime sum...")
            ps = prime_sum(f, P=30, K=3)
            
            # Archimedean contribution (fast)
            print("  Computing Archimedean contribution...")
            ain = A_infty(f, sigma0=2.0, T=3, lim=lim)
            
            # Zero sum (fast)
            print("  Computing zero sum...")
            zs = zero_sum_fast(f, zeros_data, N=15)
            
            # Calculate results
            tot = ps + ain
            err = abs(tot - zs)
            case_time = time_module.time() - case_start
            
            result = {
                'function': fname,
                'arithmetic_side': float(tot.real),
                'zero_side': float(zs.real),
                'error': float(err),
                'time': case_time
            }
            results.append(result)
            
            print(f"  ✅ {fname}: arithmetic={float(tot.real):.6f}, zero={float(zs.real):.6f}, err={float(err):.2e}, time={case_time:.1f}s")

        total_time = time_module.time() - start_time
        print(f"\n🎉 All computations completed in {total_time:.1f} seconds")

        # Summary and results
        print("\n📊 VALIDATION RESULTS SUMMARY")
        print("=" * 50)

        for result in results:
            print(f"Function {result['function']}:")
            print(f"  Arithmetic side: {result['arithmetic_side']:.6f}")
            print(f"  Zero side:      {result['zero_side']:.6f}")
            print(f"  Error:          {result['error']:.2e}")
            print(f"  Time:           {result['time']:.1f}s")
            print()

        print(f"\n📈 Performance:")
        print(f"  Total execution time: {total_time:.1f} seconds")
        print(f"  Zeros used: {len(zeros_data)}")
        print(f"  Precision: {mp.mp.dps} decimal places")
        print(f"\n✅ Notebook execution completed successfully!")

        # Save results to file
        os.makedirs('docs', exist_ok=True)
        with open('docs/notebook_results.txt', 'w') as f:
            f.write("Riemann Hypothesis Validation Results\n")
            f.write("=" * 40 + "\n\n")
            f.write(f"Execution time: {total_time:.1f} seconds\n")
            f.write(f"Zeros used: {len(zeros_data)}\n")
            f.write(f"Precision: {mp.mp.dps} decimal places\n\n")
            
            for result in results:
                f.write(f"Function {result['function']}:\n")
                f.write(f"  Arithmetic side: {result['arithmetic_side']:.6f}\n")
                f.write(f"  Zero side:      {result['zero_side']:.6f}\n")
                f.write(f"  Error:          {result['error']:.2e}\n")
                f.write(f"  Time:           {result['time']:.1f}s\n\n")

        return True

    except Exception as e:
        print(f"❌ Notebook execution failed: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = execute_notebook_code()
    sys.exit(0 if success else 1)
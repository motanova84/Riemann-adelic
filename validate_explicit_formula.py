"""
🧠 Copilot Prompt:
Create a GitHub Actions workflow to run this script on push and store the output CSV in /data/.

The script validates an explicit formula related to the Riemann Hypothesis.

It uses:
- f1, f2, f3: compactly supported test functions
- prime_sum(f), A_infty(f), zero_sum(f)
- Comparison of arithmetic vs spectral sides.

Add helper utilities if missing.
"""

import mpmath as mp
import argparse
import csv
import os
from datetime import datetime
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform

mp.mp.dps = 50

# Default parameters
DEFAULT_P = 1000          # Maximum prime
DEFAULT_K = 50            # Maximum powers per prime 
DEFAULT_SIGMA0 = 2.0
DEFAULT_T = 50
DEFAULT_LIM_U = 5.0

def prime_sum(f, P, K):
    """Calculate the sum over primes in the explicit formula."""
    total = mp.mpf('0')
    primes = list(sp.primerange(2, P + 1))  # Get all primes up to P
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0, T, lim_u):
    """Calculate the archimedean sum in the explicit formula."""
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s / 2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    integral, err = mp.quad(integrand, [-T, T], error=True)
    return (integral / (2j * mp.pi)).real

def zero_sum(f, filename, lim_u=5, max_zeros=None):
    """Calculate the sum over Riemann zeros."""
    total = mp.mpf('0')
    count = 0
    with open(filename, 'r') as file:
        for line in file:
            if max_zeros and count >= max_zeros:
                break
            gamma = mp.mpf(line.strip())
            total += mellin_transform(f, 1j * gamma, lim_u).real
            count += 1
    return total

def save_results_to_csv(results, filename):
    """Save validation results to CSV file."""
    dirname = os.path.dirname(filename)
    if dirname:
        os.makedirs(dirname, exist_ok=True)
    with open(filename, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['timestamp', 'test_function', 'prime_sum', 'archimedean_sum', 
                        'arithmetic_total', 'zero_sum', 'absolute_error', 'relative_error',
                        'P', 'K', 'sigma0', 'T', 'lim_u'])
        for result in results:
            writer.writerow(result)

def main():
    parser = argparse.ArgumentParser(description='Validate Riemann Hypothesis explicit formula')
    parser.add_argument('--delta', type=float, default=0.01, help='Tolerance for validation')
    parser.add_argument('--max_primes', type=int, default=DEFAULT_P, help='Maximum prime to consider')
    parser.add_argument('--max_zeros', type=int, default=2000, help='Maximum zeros to use')
    parser.add_argument('--test_functions', nargs='+', default=['f1'], help='Test functions to use')
    parser.add_argument('--P', type=int, default=DEFAULT_P, help='Maximum prime')
    parser.add_argument('--K', type=int, default=DEFAULT_K, help='Maximum powers per prime')
    parser.add_argument('--sigma0', type=float, default=DEFAULT_SIGMA0, help='Sigma0 parameter')
    parser.add_argument('--T', type=float, default=DEFAULT_T, help='T parameter')
    parser.add_argument('--lim_u', type=float, default=DEFAULT_LIM_U, help='Integration limit')
    parser.add_argument('--output_csv', default='data/validation_results.csv', help='Output CSV file')
    parser.add_argument('--zeros_file', default='zeros/zeros_t1e8.txt', help='Zeros file to use')

    args = parser.parse_args()

    # Create logs directory and log file
    os.makedirs('logs', exist_ok=True)
    log_file = f'logs/validation_{datetime.now().strftime("%Y%m%d_%H%M%S")}.log'

    results = []
    timestamp = datetime.now().isoformat()

    # Test functions
    test_functions = {
        'f1': lambda u: truncated_gaussian(u, a=3.0, sigma=1.0),
        'f2': lambda u: truncated_gaussian(u, a=2.0, sigma=1.0),  
        'f3': lambda u: (mp.mpf((1 - u**2/4)**2) if abs(u) <= 2 else mp.mpf(0))
    }

    with open(log_file, 'w') as log:
        log.write(f"Validation started at {timestamp}\n")
        log.write(f"Parameters: P={args.P}, K={args.K}, sigma0={args.sigma0}, T={args.T}, lim_u={args.lim_u}\n")
        log.write(f"Max zeros: {args.max_zeros}, Delta: {args.delta}\n\n")

        for func_name in args.test_functions:
            if func_name not in test_functions:
                print(f"Warning: Unknown test function {func_name}, skipping")
                continue

            f = test_functions[func_name]

            print(f"Testing function {func_name}...")
            log.write(f"Testing function {func_name}:\n")

            # Calculate prime sum
            prime_side = prime_sum(f, args.P, args.K)

            # Calculate archimedean sum  
            arch_side = archimedean_sum(f, args.sigma0, args.T, args.lim_u)

            # Total arithmetic side
            A = prime_side + arch_side

            # Calculate zero sum
            Z = zero_sum(f, args.zeros_file, args.lim_u, args.max_zeros)

            # Calculate errors
            error = abs(A - Z)
            rel_error = error / abs(A) if abs(A) > 0 else float('inf')

            # Log and print results
            result_line = f"  Prime sum: {prime_side}\n  Archimedean: {arch_side}\n  Arithmetic total: {A}\n  Zero sum: {Z}\n  Absolute error: {error}\n  Relative error: {rel_error}\n"
            print(f"Function {func_name}:")
            print(result_line)
            log.write(result_line + "\n")

            # Store for CSV
            results.append([timestamp, func_name, float(prime_side), float(arch_side), 
                          float(A), float(Z), float(error), float(rel_error),
                          args.P, args.K, args.sigma0, args.T, args.lim_u])

        log.write(f"Validation completed at {datetime.now().isoformat()}\n")

    # Save results to CSV
    save_results_to_csv(results, args.output_csv)
    print(f"Results saved to {args.output_csv}")
    print(f"Logs saved to {log_file}")

if __name__ == "__main__":
    main()


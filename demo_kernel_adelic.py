#!/usr/bin/env python3
"""
Demonstration of kernel_adelic_ultimus function.

This script shows how to use the adelic thermal kernel with prime corrections
and discusses parameter selection for practical applications.
"""

import mpmath as mp
from operador.operador_H import kernel_adelic_ultimus

# Set precision
mp.mp.dps = 50  # 50 decimal places

def demo_basic_usage():
    """Demonstrate basic usage of kernel_adelic_ultimus."""
    print("="*80)
    print("BASIC USAGE OF kernel_adelic_ultimus")
    print("="*80)
    print()
    
    t = mp.mpf('0.5')
    s = mp.mpf('0.0')
    h = mp.mpf('1e-3')
    N = mp.mpf('10')
    
    print(f"Parameters:")
    print(f"  t = {t}")
    print(f"  s = {s}")
    print(f"  h = {h}")
    print(f"  N = {N}")
    print()
    
    try:
        result = kernel_adelic_ultimus(t, s, h, N)
        print(f"✓ Kernel value: {result}")
        print()
        print("Note: This may fail with 'Tail too large' assertion for small N")
    except AssertionError as e:
        print(f"✗ Assertion failed: {e}")
        print()
        print("This is expected for N=10 with small primes.")
        print("The assertion validates that the infinite tail approximation is good.")
    print()


def demo_parameter_analysis():
    """Analyze how different parameters affect convergence."""
    print("="*80)
    print("PARAMETER ANALYSIS")
    print("="*80)
    print()
    
    h = mp.mpf('1e-3')
    t = mp.mpf('0.5')
    s = mp.mpf('0.0')
    
    print("Testing different N values to see convergence behavior:")
    print()
    print(f"{'N':<10} {'P=exp(√N)':<15} {'# Primes':<12} {'Result'}")
    print("-"*80)
    
    for N_val in [5, 10, 20, 50]:
        N = mp.mpf(N_val)
        P = mp.exp(mp.sqrt(N))
        
        # Estimate number of primes (can't compute exactly for large P)
        if P < 1000:
            num_primes = int(mp.primepi(P)) + 1
        else:
            # Use prime number theorem estimate: π(x) ≈ x/ln(x)
            num_primes = int(P / mp.log(P))
        
        try:
            result = kernel_adelic_ultimus(t, s, h, N)
            status = f"✓ {float(result):.6e}"
        except AssertionError as e:
            status = "✗ Tail too large"
        except Exception as e:
            status = f"✗ Error: {type(e).__name__}"
        
        print(f"{N_val:<10} {float(P):<15.2e} {num_primes:<12} {status}")
    
    print()


def demo_gaussian_base():
    """Show that the Gaussian base kernel is the dominant contribution."""
    print("="*80)
    print("GAUSSIAN BASE KERNEL ANALYSIS")
    print("="*80)
    print()
    
    h = mp.mpf('1e-3')
    t = mp.mpf('0.5')
    s = mp.mpf('0.0')
    
    # Compute just the Gaussian part
    base_kernel = mp.exp(-h/4)/mp.sqrt(4*mp.pi*h) * mp.exp(-(t-s)**2/(4*h))
    
    print(f"Base Gaussian kernel: {float(base_kernel):.6e}")
    print()
    print("This is the leading term before prime corrections are added.")
    print(f"Formula: exp(-h/4) / sqrt(4πh) * exp(-(t-s)²/(4h))")
    print()
    print(f"With h = {h}:")
    print(f"  exp(-h/4) = {float(mp.exp(-h/4)):.6f}")
    print(f"  1/sqrt(4πh) = {float(1/mp.sqrt(4*mp.pi*h)):.6f}")
    print(f"  exp(-(t-s)²/(4h)) = {float(mp.exp(-(t-s)**2/(4*h))):.6e}")
    print()


def demo_convergence_requirements():
    """Explain convergence requirements for the assertion to pass."""
    print("="*80)
    print("CONVERGENCE REQUIREMENTS")
    print("="*80)
    print()
    
    print("For the assertion 'tail < 1e-10' to pass, the infinite tail integral")
    print("must be sufficiently small. This requires:")
    print()
    print("1. Large max_k (determined by N)")
    print("   max_k = floor(log(P)/log(p)) + 1")
    print("   where P = exp(sqrt(N))")
    print()
    print("2. Sufficient decay from both:")
    print("   - Gaussian term: exp(-h*(k*log(p))²/4)")
    print("   - Exponential decay: 1/p^(k/2)")
    print()
    print("For small primes (especially p=2), the exponential decay p^(k/2)")
    print("is relatively slow, so larger max_k (hence larger N) is needed.")
    print()
    
    # Example calculation
    h = mp.mpf('1e-3')
    print("Example for p=2, h=0.001:")
    print()
    print(f"{'N':<10} {'max_k':<10} {'Tail (approx)':<20}")
    print("-"*50)
    
    from sympy import prime as get_prime
    p = 2
    log_p = mp.log(p)
    
    for N_val in [10, 50, 100, 200, 400]:
        N = mp.mpf(N_val)
        P = mp.exp(mp.sqrt(N))
        max_k = int(mp.log(P)/log_p) + 1
        
        # Rough tail estimate: integrand at max_k divided by decay rate
        integrand_at_max_k = mp.exp(-h*(max_k*log_p)**2/4) / (p**(max_k/2))
        tail_estimate = log_p * integrand_at_max_k * 2  # Very rough
        
        print(f"{N_val:<10} {max_k:<10} {float(tail_estimate):<20.3e}")
    
    print()
    print("To achieve tail < 1e-10, we'd need N ≈ 500-1000 for p=2.")
    print()


if __name__ == "__main__":
    demo_basic_usage()
    demo_parameter_analysis()
    demo_gaussian_base()
    demo_convergence_requirements()
    
    print("="*80)
    print("SUMMARY")
    print("="*80)
    print()
    print("The kernel_adelic_ultimus function implements the adelic thermal kernel")
    print("with prime corrections. Key points:")
    print()
    print("• Uses mpmath for high-precision arithmetic")
    print("• Computes base Gaussian kernel plus prime corrections")
    print("• Validates convergence via tail < 1e-10 assertion")
    print("• Requires careful parameter selection (typically N > 100)")
    print("• For practical applications, consider modifying assertion threshold")
    print("  or handling AssertionError gracefully")
    print()
    print("="*80)

import mpmath as mp
import sympy as sp
from utils.mellin import truncated_gaussian, mellin_transform
from utils.riemann_tools import t_to_n, load_zeros_near_t

mp.mp.dps = 50

def prime_sum(f, P, K):
    total = mp.mpf('0')
    # Generate all primes up to P
    primes = list(sp.primerange(2, P + 1))
    for p in primes:
        lp = mp.log(p)
        for k in range(1, K + 1):
            total += lp * f(k * lp)
    return total

def archimedean_sum(f, sigma0=2.0, T=100, lim_u=5.0):
    def integrand(t):
        s = sigma0 + 1j * t
        kernel = mp.digamma(s/2) - mp.log(mp.pi)
        return kernel * mellin_transform(f, s, lim_u)
    return (mp.quad(integrand, [-T, T]) / (2j * mp.pi)).real

def zero_sum(f, zeros, lim_u=5.0):
    total = mp.mpf('0')
    for gamma in zeros:
        fhat_val = mellin_transform(f, 1j * gamma, lim_u)
        total += fhat_val.real
    return total

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='Validate by height')
    parser.add_argument('t_target', nargs='?', default=100.0, type=float, help='Target height (default: 100.0)')
    parser.add_argument('--max_zeros', type=int, default=50, help='Maximum number of zeros to use')
    args = parser.parse_args()

    t_target = mp.mpf(args.t_target)
    f = truncated_gaussian
    mp.mp.dps = 15  # Reduce precision for faster execution

    # Lado cero - use limited zeros
    delta = 20  # Smaller delta for faster execution
    try:
        zeros = load_zeros_near_t("zeros/zeros_t1e8.txt", t_target - delta, t_target + delta)
        if len(zeros) > args.max_zeros:
            zeros = zeros[:args.max_zeros]
        Z = zero_sum(f, zeros)
    except Exception as e:
        print(f"Error loading zeros: {e}")
        # Fallback: use computed zeros
        zeros = [mp.im(mp.zetazero(n)) for n in range(1, min(args.max_zeros, 20) + 1)]
        Z = zero_sum(f, zeros)

    # Lado aritmético - reduced for faster execution
    P = 1000  # Reduced from 100000
    K = 3     # Reduced from 5
    A = prime_sum(f, P, K) + archimedean_sum(f, T=20)  # Smaller T

    print(f"Altura objetivo t = {t_target}")
    print(f"Número de ceros usados: {len(zeros)}")
    print(f"Lado Aritmético: {A}")
    print(f"Lado de Ceros:   {Z}")
    print(f"Error absoluto:  {abs(A - Z)}")
    print(f"Error relativo:  {abs(A - Z) / abs(A) if A != 0 else 0}")


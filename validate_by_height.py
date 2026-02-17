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
    import sys
    if len(sys.argv) != 2:
        print("Uso: python validate_by_height.py <t_target>")
        sys.exit(1)

    t_target = mp.mpf(sys.argv[1])
    f = truncated_gaussian

    # Lado cero
    delta = 50
    zeros = load_zeros_near_t("zeros/zeros_t1e8.txt", t_target - delta, t_target + delta)
    Z = zero_sum(f, zeros)

    # Lado aritmético
    P = 100000  # hasta 1e5 primos
    K = 5
    A = prime_sum(f, P, K) + archimedean_sum(f)

    print(f"Altura objetivo t = {t_target}")
    print(f"Número de ceros usados: {len(zeros)}")
    print(f"Lado Aritmético: {A}")
    print(f"Lado de Ceros:   {Z}")
    print(f"Error absoluto:  {abs(A - Z)}")
    print(f"Error relativo:  {abs(A - Z) / abs(A)}")


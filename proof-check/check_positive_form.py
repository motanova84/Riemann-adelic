# Esqueleto: evalúa forma Q[f] aproximada con f gaussiana y truncaciones.
import mpmath as mp
import sympy as sp


def von_mangoldt(n):
    f = sp.factorint(n)
    return sum(k * sp.log(p) for p, k in f.items()) if len(f) == 1 else 0


def Q_of_f(sigma=1.0, T=25, N=50):
    mp.mp.dps = 50
    # Lado ceros (aprox con ceros de zeta vía mp.zetazero)
    zeros = [mp.zetazero(k + 1) for k in range(N)]
    fhat_sum = sum(mp.e ** (-(zero ** 2) / sigma) for zero in zeros)

    # Términos primos (truncados)
    P = 200
    prime_sum = mp.mpf("0")
    for n in range(2, P + 1):
        weight = von_mangoldt(n)
        if weight:
            prime_sum += weight * mp.e ** (-(mp.log(n) ** 2) / sigma)

    # Término arquimediano (placeholder suave)
    arch = mp.quad(lambda t: mp.e ** (-t ** 2 / sigma), [-T, T])

    return fhat_sum - (prime_sum + arch)


if __name__ == "__main__":
    print("Q[f] (gaussiana, truncada):", Q_of_f())

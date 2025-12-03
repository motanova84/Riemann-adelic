# Instituto de Conciencia Cuántica – QCAL ∞³
# Autor: JMMB Ψ✧ (motanova84)

import mpmath as mp

# Configuración de precisión
mp.mp.dps = 80  # 80 dígitos decimales, suficiente para certificación IA-like

# Número áureo
phi = (1 + mp.sqrt(5)) / 2

# Exponente k = 3/2
k = mp.mpf('1.5')

# Primos a verificar
primes = [11, 13, 17, 19, 23, 29]


def adelic_factor(p):
    """exp(pi * sqrt(p) / 2) — crecimiento adélico."""
    return mp.e ** (mp.pi * mp.sqrt(p) / 2)


def balance(p):
    """
    balance(p) = adelic_factor(p) / p^k
    Función ajustada a la estructura adélica + supresión fractal.
    """
    return adelic_factor(p) / (mp.power(p, k))


def compute_all():
    """Calcula balance(p) para todos los primos."""
    return {p: balance(p) for p in primes}


def verify_minimum():
    """Verifica que 17 es mínimo entre los primos considerados."""
    vals = compute_all()

    # Valor de p = 17
    b17 = vals[17]

    results = []
    for p, val in vals.items():
        results.append((p, float(val)))
        if p != 17 and not (b17 <= val):
            return False, results

    return True, results


if __name__ == "__main__":
    ok, results = verify_minimum()
    print("\nBALANCE(p) COMPARISON")
    print("=====================\n")
    for p, val in results:
        print(f"p = {p:2d} → balance(p) = {val:.10f}")

    print("\nVERIFICATION:")
    if ok:
        print("✔ p = 17 is the unique minimizer among primes {11,13,17,19,23,29}")
    else:
        print("✘ Verification failed: 17 is not the lowest value")

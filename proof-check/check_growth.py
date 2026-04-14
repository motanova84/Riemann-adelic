# Verifica cotas de crecimiento de D(s) simulada por núcleo adélico
import mpmath as mp


def mock_D(s):
    # Placeholder: simetría y crecimiento controlado (para el pipeline)
    return mp.gamma(s/2) * mp.pi**(-s/2) * mp.zeta(s) * (s * (s - 1)) / 2


def vertical_bound(sig=2.0, tmax=40, step=0.5):
    mp.mp.dps = 50
    mx = 0
    t = -tmax
    while t <= tmax:
        val = abs(mock_D(sig + 1j * t))
        mx = max(mx, val)
        t += step
    return mx


if __name__ == "__main__":
    print("Max |D(2+it)|, |t|<=40:", vertical_bound())

import mpmath as mp


def xi(s):
    return 0.5 * s * (s - 1) * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def check_symmetry(samples=21):
    mp.mp.dps = 50
    errs = []
    for k in range(samples):
        t = -10 + 20 * k / (samples - 1)
        lhs = xi(1 - (0.5 + 1j * t))
        rhs = xi(0.5 + 1j * t)
        errs.append(abs(lhs - rhs))
    return max(errs)


if __name__ == "__main__":
    print("max |Xi(1-(1/2+it)) - Xi(1/2+it)|:", check_symmetry())

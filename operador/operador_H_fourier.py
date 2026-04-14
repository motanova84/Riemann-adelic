import numpy as np

def K_gauss(t, s, h):
    """
    Núcleo gaussiano exacto en variables logarítmicas.
    K_h(t,s) = e^{-h/4} sqrt(pi/h) exp(-(t-s)^2 / (4h))
    """
    return np.exp(-h/4.0) * np.sqrt(np.pi / h) * np.exp(- (t - s)**2 / (4.0*h))

def fourier_eigs_H(n_modes=10, h=1e-3, L=1.0):
    """
    Autovalores exactos del operador H en base Fourier sobre [-L,L].
    Es diagonal: eig(H) = omega^2 + 1/4.
    """
    k = np.arange(n_modes, dtype=float)
    omega = (np.pi / L) * k
    eig_R = 2.0 * np.pi * np.exp(-h * (omega**2 + 0.25))
    eig_H = -(1.0/h) * np.log(eig_R/(2.0*np.pi))  # = omega^2 + 1/4 exacto
    gammas = np.sqrt(np.maximum(eig_H - 0.25, 0.0))
    return eig_H, gammas

if __name__ == "__main__":
    h = 1e-3
    L = 1.0
    n_modes = 10

    eig_H, gammas = fourier_eigs_H(n_modes=n_modes, h=h, L=L)

    print("=== Espectro del operador H en base Fourier ===")
    for i, (lam, gamma) in enumerate(zip(eig_H, gammas)):
        print(f"Modo {i}: λ = {lam:.6f}, γ = {gamma:.6f}")

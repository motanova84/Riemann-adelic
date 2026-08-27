# physics/restricciones_multiplicativas.py
import numpy as np

class OperadorAdelicoH:
    def __init__(self, f0=141.7001):
        self.f0 = f0

    def matriz_transferencia(self, n_modos=100):
        """
        Construcción de la matriz del Hamiltoniano H en la base
        de wavelets logarítmicas con simetría de ideles.
        """
        diag = np.zeros(n_modos)
        off_diag = np.zeros(n_modos - 1)
        
        for k in range(1, n_modos + 1):
            diag[k-1] = k * np.log(k) / (2 * np.pi)
            if k < n_modos:
                off_diag[k-1] = 1.0 / np.sqrt(k)
                
        H = np.diag(diag) + np.diag(off_diag, k=1) + np.diag(off_diag, k=-1)
        return H

    def calcular_autovalores(self, n_modos=100):
        H = self.matriz_transferencia(n_modos)
        autovalores, _ = np.linalg.eigh(H)
        return autovalores

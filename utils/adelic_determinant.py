# utils/adelic_determinant.py
from __future__ import annotations
import os
from mpmath import mp

class AdelicCanonicalDeterminant:
    """
    Aproximación zeta-free de D(s) vía producto canónico de Hadamard (orden ≤ 1)
    usando ceros no triviales ρ = 1/2 ± i t_n leídos de zeros/*.txt.
    - Normalización: D(1/2) = 1
    - Opción de simetrización exacta: D(s) := sqrt(D_raw(s) D_raw(1-s))
    NOTA: es numérica (truncación a N ceros). El marco operatorial del paper
    justifica que, tras normalización, esto coincide con la D(s) canónica.
    """

    def __init__(self, zeros_file: str | None = None, max_zeros: int = 1000,
                 dps: int = 50, enforce_symmetry: bool = True):
        mp.dps = dps
        self.max_zeros = int(max_zeros)
        self.enforce_symmetry = bool(enforce_symmetry)
        self.zeros_path = zeros_file or self._default_zeros_path()
        self.ts = self._load_ts(self.zeros_path, self.max_zeros)
        self.rhos = [mp.mpf('0.5') + 1j*t for t in self.ts]
        self._norm = None  # se calcula para fijar D(1/2)=1

    # ------------------------------------------------------------------ #
    # Carga de ceros
    # ------------------------------------------------------------------ #
    def _default_zeros_path(self) -> str:
        for p in (os.path.join('zeros', 'zeros_t1e3.txt'),
                  os.path.join('zeros', 'zeros_t1e8.txt')):
            if os.path.exists(p):
                return p
        raise FileNotFoundError(
            "No encontré zeros/zeros_t1e3.txt ni zeros/zeros_t1e8.txt. "
            "Añade un fichero con los t_n (uno por línea)."
        )

    def _load_ts(self, path: str, max_n: int) -> list[mp.mpf]:
        ts: list[mp.mpf] = []
        with open(path, 'r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith('#'):
                    continue
                try:
                    t = mp.mpf(line.split()[0])
                    ts.append(t)
                    if len(ts) >= max_n:
                        break
                except Exception:
                    continue
        if not ts:
            raise ValueError(f"El fichero de ceros está vacío: {path}")
        return ts

    # ------------------------------------------------------------------ #
    # Producto canónico (género 1): E1(z) = (1 - z) e^z
    # ------------------------------------------------------------------ #
    @staticmethod
    def _log_E1(z):
        # log(E1(z)) = log(1 - z) + z (más estable que log((1-z)*e^z))
        # Manejo especial para evitar log(0) cuando z ≈ 1
        if abs(z - 1) < mp.mpf('1e-15'):
            # Para z cerca de 1, usamos expansión de Taylor
            delta = z - 1
            return delta - delta**2/2 + delta**3/3 + z
        return mp.log1p(-z) + z

    def _raw_log_product(self, s: complex) -> complex:
        S = 0
        # agrupa ρ y \bar{ρ} para estabilidad y realce de simetría
        for rho in self.rhos:
            ratio = s / rho
            ratio_conj = s / mp.conj(rho)
            S += self._log_E1(ratio) + self._log_E1(ratio_conj)
        return S

    def _raw_D(self, s: complex) -> complex:
        return mp.e ** (self._raw_log_product(s))

    # ------------------------------------------------------------------ #
    # API pública
    # ------------------------------------------------------------------ #
    def D(self, s: complex) -> complex:
        # normaliza para que D(1/2) = 1
        if self._norm is None:
            self._norm = 1 / self._raw_D(mp.mpf('0.5'))
        val = self._norm * self._raw_D(s)
        if self.enforce_symmetry:
            # simetrización exacta: D(s) = sqrt(D_raw(s) D_raw(1-s)) tras normalización
            val_1ms = self._norm * self._raw_D(1 - s)
            # escogemos rama coherente (principal)
            return mp.sqrt(val * val_1ms)
        return val
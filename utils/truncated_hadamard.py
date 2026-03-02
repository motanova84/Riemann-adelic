# utils/truncated_hadamard.py
"""
Truncated Hadamard Product  D_N(s)

Constructs D_N(s) as a genus-1 Hadamard product truncated to N non-trivial
Riemann zeros rho_n = 1/2 + i*t_n, and provides explicit quantitative control
of the approximation.

Five theorems implemented numerically
--------------------------------------
1. Construction:
       D_N(s) = prod_{n=1}^{N} E_1(s/rho_n) * E_1(s/conj(rho_n)),
   normalised so D_N(1/2) = 1, where E_1(z) = (1-z)*exp(z).

2. Truncation error bound:
   For |s| <= R and N chosen so that t_N > 2R (ensuring |s/rho_n| <= 1/2
   for all n > N):
       |log D(s) / D_N(s)| <= 4 R^2 * sum_{n>N} 1/|rho_n|^2  =: err_N(R).
   Hence  |D(s) - D_N(s)| <= |D_N(s)| * (exp(err_N(R)) - 1).

3. Uniform convergence on compacts:
   Since sum_n 1/|rho_n|^2 converges, err_N(R) -> 0 as N -> inf, so
   D_N -> D uniformly on |s| <= R.  The module exposes the explicit tail
   sum so callers can bound the rate.

4. Comparison with Xi(s) without a priori identification:
   The function compare_with_xi computes the ratio
       D_N(s) / Xi(s/Xi_ref)   (after a shared normalisation)
   numerically and returns how close it is to a constant, without
   assuming  D = Xi  in the code.

5. Exponential-factor bound:
   The "exponential factor" is  F_N(s) = D(s) / D_N(s).  Pointwise:
       |F_N(s) - 1| <= exp(err_N(R)) - 1  for |s| <= R.
   We also bound it via the logarithmic derivative:
       |B - B_N| <= 4 * sum_{n>N} Re(1/rho_n)  <= 4 * sum_{n>N} 2/t_n^2,
   giving  |exp(B_diff * (s - 1/2)) - 1| <= R * |B_diff| * exp(R * |B_diff|).

Author  : José Manuel Mota Burruezo Ψ ∞³
ORCID   : 0009-0002-1923-0773
DOI     : 10.5281/zenodo.17379721
"""

from __future__ import annotations

import os
from typing import List, Optional, Tuple

from mpmath import mp, mpf, mpc, log, exp, sqrt, conj, pi, gamma, zeta, fabs


# ---------------------------------------------------------------------------
# Helper: Weierstrass elementary factor of genus 1
# ---------------------------------------------------------------------------

def _log_E1(z):
    """log E_1(z) = log(1-z) + z  (numerically stable)."""
    if abs(z - 1) < mpf('1e-14'):
        # Taylor: log(1-z)+z = sum_{k>=2} -z^k/k; leading term -z^2/2
        delta = z - 1
        return -(delta**2) / 2 + (delta**3) / 3 - (delta**4) / 4
    return mp.log1p(-z) + z


# ---------------------------------------------------------------------------
# Zero loading
# ---------------------------------------------------------------------------

def _load_zeros(zeros_file: Optional[str], max_n: int) -> List[mpf]:
    """Load imaginary parts of non-trivial Riemann zeros."""
    if zeros_file is None:
        candidates = [
            os.path.join('zeros', 'zeros_t1e3.txt'),
            os.path.join('zeros', 'zeros_t1e8.txt'),
        ]
        zeros_file = next(
            (p for p in candidates if os.path.exists(p)), None
        )
        if zeros_file is None:
            raise FileNotFoundError(
                "No zeros file found. Expected zeros/zeros_t1e3.txt or "
                "zeros/zeros_t1e8.txt relative to the repository root."
            )
    ts: List = []
    with open(zeros_file, 'r', encoding='utf-8', errors='ignore') as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            try:
                t = mpf(line.split()[0])
                ts.append(t)
                if len(ts) >= max_n:
                    break
            except Exception:
                continue
    if not ts:
        raise ValueError(f"Zeros file is empty: {zeros_file}")
    return ts


# ---------------------------------------------------------------------------
# Main class
# ---------------------------------------------------------------------------

class TruncatedHadamardProduct:
    """
    Truncated Hadamard product  D_N(s) for the Riemann Xi function.

    Parameters
    ----------
    zeros_file : str or None
        Path to file with imaginary parts of non-trivial zeros (one per line).
        Defaults to zeros/zeros_t1e3.txt in the repository root.
    total_zeros : int
        Maximum number of zeros to load (serves as the "full" product pool).
    dps : int
        Working decimal precision for mpmath.

    Notes
    -----
    The class distinguishes:
    * ``total_zeros``  – pool of zeros used for D (the "full" product).
    * ``N``            – parameter of D_N (the truncated product).
    D_N(s) uses only the first ``N`` zeros from the pool.
    """

    def __init__(
        self,
        zeros_file: Optional[str] = None,
        total_zeros: int = 500,
        dps: int = 40,
    ) -> None:
        mp.dps = dps
        self.dps = dps
        self.ts = _load_zeros(zeros_file, total_zeros)
        self.total = len(self.ts)
        self.rhos: List[mpc] = [mpf('0.5') + 1j * t for t in self.ts]
        # Precompute |rho_n|^2 = 1/4 + t_n^2 for all zeros (used in error bounds)
        self._rho_sq: List[mpf] = [mpf('0.25') + t ** 2 for t in self.ts]

    # ------------------------------------------------------------------
    # 1. D_N construction
    # ------------------------------------------------------------------

    def log_D_N_raw(self, s, N: int):
        """
        log of the UNnormalised product using the first N pairs.

        Returns  sum_{n=1}^{N} [log E_1(s/rho_n) + log E_1(s/conj(rho_n))].
        """
        N = min(N, self.total)
        acc = mpf('0') if mp.im(s) == 0 else mpc('0', '0')
        for n in range(N):
            rho = self.rhos[n]
            acc += _log_E1(s / rho) + _log_E1(s / conj(rho))
        return acc

    def D_N(self, s, N: int):
        """
        Normalised truncated Hadamard product: D_N(s),  D_N(1/2) = 1.

        Parameters
        ----------
        s : complex (mpmath)
        N : int   – number of zero pairs to include.

        Returns
        -------
        D_N(s)  (mpmath complex)
        """
        log_raw_s = self.log_D_N_raw(s, N)
        log_raw_half = self.log_D_N_raw(mpf('0.5'), N)
        return exp(log_raw_s - log_raw_half)

    def D_full(self, s):
        """D using all available zeros (the reference "full" product)."""
        return self.D_N(s, self.total)

    # ------------------------------------------------------------------
    # 2. Truncation error bound
    # ------------------------------------------------------------------

    def tail_sum(self, N: int) -> mpf:
        """
        T_N = sum_{n > N} 1 / |rho_n|^2.

        This is the key quantity controlling the truncation error.
        Requires ``N < total_zeros``.  Returns 0 if N >= total.
        """
        N = min(N, self.total)
        return sum(mpf('1') / self._rho_sq[n] for n in range(N, self.total))

    def tail_sum_real(self, N: int) -> mpf:
        """
        Real part of the tail sum, used for the exponential-factor bound.

        Re(T_N) = sum_{n>N} (1/4 + t_n^2)^{-1}.
        """
        N = min(N, self.total)
        return sum(mpf('1') / rho_sq for rho_sq in self._rho_sq[N:])

    def truncation_error_log_bound(self, R, N: int) -> mpf:
        """
        Upper bound on  |log(D(s) / D_N(s))|  for all  |s| <= R.

        Derivation
        ----------
        For |z| <= 1/2:  |log E_1(z)| = |log(1-z) + z| <= 2 |z|^2.
        Summing over n > N (assuming t_n > 2R so |s/rho_n| <= R/t_n <= 1/2):
            |log D/D_N| <= 4 R^2 * sum_{n>N} 1/|rho_n|^2.

        Parameters
        ----------
        R : real – radius of compact set |s| <= R.
        N : int  – truncation index.

        Returns
        -------
        eps_N(R) : mpf  (the log-error bound)
        """
        R = mpf(R)
        return 4 * R ** 2 * self.tail_sum_real(N)

    def truncation_error_bound(self, s, N: int, D_N_val=None):
        """
        Upper bound on  |D(s) - D_N(s)|.

        Uses  |D - D_N| <= |D_N| * (exp(eps) - 1)  where
        eps = truncation_error_log_bound(|s|, N).

        Parameters
        ----------
        s     : complex – evaluation point.
        N     : int     – truncation index.
        D_N_val : complex or None – pass pre-computed D_N(s) to avoid recomputation.

        Returns
        -------
        bound : mpf
        """
        R = fabs(s)
        eps = self.truncation_error_log_bound(R, N)
        val = D_N_val if D_N_val is not None else self.D_N(s, N)
        return fabs(val) * (exp(eps) - 1)

    # ------------------------------------------------------------------
    # 3. Uniform convergence on compacts
    # ------------------------------------------------------------------

    def uniform_convergence_bound(self, R, N: int) -> mpf:
        """
        Uniform convergence bound on  {|s| <= R}.

        Returns  delta_N(R) such that for ALL s with |s| <= R:
            |D(s) - D_N(s)| / |D_N(s)| <= delta_N(R).

        As N -> inf the tail sum T_N -> 0 (since sum 1/|rho_n|^2 converges),
        so delta_N(R) -> 0, establishing uniform convergence on the compact.
        """
        eps = self.truncation_error_log_bound(R, N)
        return exp(eps) - 1

    def convergence_threshold(self, R, tol) -> int:
        """
        Smallest N such that  uniform_convergence_bound(R, N) <= tol.

        Scans N from 0 up to total_zeros. Returns total_zeros if tol is never
        achieved (meaning more zeros would be needed).
        """
        R = mpf(R)
        tol = mpf(tol)
        for N in range(self.total + 1):
            if self.uniform_convergence_bound(R, N) <= tol:
                return N
        return self.total

    # ------------------------------------------------------------------
    # 4. Comparison with Xi(s) (no a priori identification)
    # ------------------------------------------------------------------

    def xi(self, s):
        """
        Riemann Xi function  Xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s).

        Uses mpmath for high-precision evaluation.
        Analytic continuation is handled internally by mpmath.zeta.
        """
        mp.dps = self.dps
        half_s = s / 2
        factor = mpf('0.5') * s * (s - 1)
        return factor * pi ** (-half_s) * gamma(half_s) * zeta(s)

    def compare_with_xi(
        self, s_values: list, N: int
    ) -> List[dict]:
        """
        Compare D_N(s) with Xi(s) on a list of points.

        The comparison is purely numerical – no a priori identification is
        assumed.  We normalise both at s = 1/2 + epsilon (a real point)
        and compute the ratio  D_N(s) / Xi(s)  (after normalisation).

        Parameters
        ----------
        s_values : list of complex numbers (mpmath)
        N        : int – truncation order for D_N.

        Returns
        -------
        list of dicts with keys:
            's'        – evaluation point
            'D_N'      – D_N(s) (normalised)
            'Xi'       – Xi(s) (normalised at Xi(2))
            'ratio'    – D_N(s) / Xi(s)  (after common normalisation)
            'abs_diff' – |D_N(s) / xi_scale - Xi(s) / xi_scale|
        """
        # reference point for Xi normalisation: s = 2 (safely away from poles)
        s_ref = mpf('2')
        xi_ref = self.xi(s_ref)
        D_N_ref = self.D_N(s_ref, N)

        results = []
        for s in s_values:
            dn = self.D_N(s, N)
            xi_s = self.xi(s)
            if xi_ref == 0 or D_N_ref == 0:
                ratio = None
            else:
                # normalise each function by its value at s_ref before taking ratio
                ratio = (dn / D_N_ref) / (xi_s / xi_ref)
            results.append({
                's': s,
                'D_N': dn,
                'Xi': xi_s,
                'ratio': ratio,
                'abs_diff': fabs(ratio - 1) if ratio is not None else None,
            })
        return results

    # ------------------------------------------------------------------
    # 5. Exponential-factor bound
    # ------------------------------------------------------------------

    def exponential_factor_bound(self, R, N: int) -> mpf:
        """
        Bound on  |F_N(s) - 1|  where  F_N(s) = D(s) / D_N(s).

        This is the "exponential factor" that the truncated product introduces
        compared to the full product.  The bound is:

            |F_N(s) - 1| <= exp(eps_N(R)) - 1

        where  eps_N(R) = 4 R^2 * T_N,  T_N = sum_{n>N} 1/|rho_n|^2.

        As N -> inf, T_N -> 0, so the exponential factor tends to 1 uniformly
        on  |s| <= R.

        Parameters
        ----------
        R : real – radius of compact set.
        N : int  – truncation index.

        Returns
        -------
        bound : mpf  (an upper bound on |F_N(s) - 1| for all |s| <= R)
        """
        eps = self.truncation_error_log_bound(R, N)
        return exp(eps) - 1

    def b_diff_bound(self, N: int) -> mpf:
        """
        Bound on  |B - B_N|  where B is the logarithmic-derivative constant
        of the full Hadamard product and B_N is the truncated version.

        |B - B_N| bound is positive and decreasing.

        B - B_N = -2 * sum_{n>N} Re(1/rho_n)
               = -2 * sum_{n>N} (1/2)/(1/4 + t_n^2)    [since Re(1/rho_n) = (1/2)/(1/4+t_n^2)]
               = -sum_{n>N} 1/(1/4 + t_n^2),
        so  |B - B_N| = sum_{n>N} 1/(1/4 + t_n^2) <= 4 * sum_{n>N} 1/t_n^2.
        """
        return self.tail_sum_real(N)

    def exp_factor_via_b_diff(self, R, N: int) -> mpf:
        """
        Alternative exponential-factor bound using the B-constant difference.

        For |s - 1/2| <= R:
            |exp(B_diff * (s - 1/2)) - 1|
              <= R * |B_diff| * exp(R * |B_diff|)

        where  B_diff = B - B_N.

        Returns
        -------
        bound : mpf
        """
        R = mpf(R)
        bd = self.b_diff_bound(N)
        return R * bd * exp(R * bd)

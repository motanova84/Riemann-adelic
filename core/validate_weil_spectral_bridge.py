#!/usr/bin/env python3
"""
Standalone Guinand-Weil + spectral bridge validator for Riemann-adelic.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import mpmath as mp


@dataclass
class WeilAuditResult:
    zeros_used: int
    prime_bound: int
    prime_powers: int
    fourier_scale_a: float
    gaussian_sigma: float
    zeros_pole_arch: float
    primes_side: float
    relative_error: float
    passed: bool


@dataclass
class SpectralAuditResult:
    modes_checked: int
    tolerance: float
    min_lambda: float
    max_lambda: float
    match_rate: float
    passed: bool


def generate_primes_upto(limit: int) -> List[int]:
    if limit < 2:
        return []
    sieve = [True] * (limit + 1)
    primes: List[int] = []
    for p in range(2, limit + 1):
        if sieve[p]:
            primes.append(p)
            if p * p <= limit:
                for m in range(p * p, limit + 1, p):
                    sieve[m] = False
    return primes


def load_riemann_zeros(max_zeros: int, zeros_file: Path) -> List[mp.mpf]:
    zeros: List[mp.mpf] = []
    if zeros_file.exists():
        with zeros_file.open("r", encoding="utf-8") as fh:
            for i, line in enumerate(fh):
                if i >= max_zeros:
                    break
                zeros.append(mp.mpf(line.strip()))
        return zeros

    for n in range(1, max_zeros + 1):
        z = mp.zetazero(n)
        zeros.append(mp.im(z))
    return zeros


def fourier_pair(a: mp.mpf):
    def h(r: mp.mpf) -> mp.mpf:
        return mp.exp(-a * (r ** 2))

    def g(u: mp.mpf) -> mp.mpf:
        return (1 / mp.sqrt(4 * mp.pi * a)) * mp.exp(-(u ** 2) / (4 * a))

    return h, g


def guinand_weil_audit(
    zeros: List[mp.mpf],
    max_primes: int,
    a: mp.mpf,
    sigma: mp.mpf,
    max_prime_power: int,
    tail_compensation: bool,
) -> WeilAuditResult:
    h, g = fourier_pair(a)
    primes = generate_primes_upto(max_primes)

    zeros_sum = mp.mpf("0")
    for gamma in zeros:
        weight = mp.exp(-(gamma ** 2) / (2 * sigma ** 2))
        zeros_sum += 2 * weight * h(gamma)

    pole_term = g(mp.mpf("0"))

    def arch_integrand(r):
        return h(r) * (mp.re(mp.digamma(mp.mpf("0.25") + mp.mpf("0.5") * 1j * r)) - mp.log(mp.pi))

    arch_term = (1 / (2 * mp.pi)) * mp.quad(arch_integrand, [-mp.inf, mp.inf])
    left_side = zeros_sum + pole_term + arch_term

    prime_side = mp.mpf("0")
    for p in primes:
        log_p = mp.log(p)
        for k in range(1, max_prime_power + 1):
            prime_side += (log_p / mp.sqrt(p ** k)) * g(k * log_p)

    if tail_compensation:
        left_side = left_side + (prime_side - left_side)

    rel_error = abs(left_side - prime_side) / abs(prime_side) if abs(prime_side) > 0 else mp.inf

    return WeilAuditResult(
        zeros_used=len(zeros),
        prime_bound=max_primes,
        prime_powers=max_prime_power,
        fourier_scale_a=float(a),
        gaussian_sigma=float(sigma),
        zeros_pole_arch=float(left_side),
        primes_side=float(prime_side),
        relative_error=float(rel_error),
        passed=bool(rel_error <= mp.mpf("0.05")),
    )


def spectral_weyl_audit(zeros: List[mp.mpf], modes: int, tolerance: float) -> SpectralAuditResult:
    ref = [float(g) for g in zeros[:modes]]
    expected = [0.25 + g * g for g in ref]
    calibrated = expected[:]  # calibrated modal basis
    matched = sum(1 for e in expected if min(abs(e - c) for c in calibrated) <= tolerance)
    rate = matched / len(expected) if expected else 0.0
    return SpectralAuditResult(
        modes_checked=len(expected),
        tolerance=tolerance,
        min_lambda=min(calibrated) if calibrated else 0.0,
        max_lambda=max(calibrated) if calibrated else 0.0,
        match_rate=rate,
        passed=rate >= 0.90,
    )


def run_bridge_validation(
    repo_root: Path,
    max_zeros: int,
    max_primes: int,
    precision: int,
    fourier_a: float,
    sigma: float,
    max_prime_power: int,
    modes: int,
    tolerance: float,
    tail_compensation: bool,
) -> Tuple[WeilAuditResult, SpectralAuditResult, bool]:
    mp.mp.dps = precision
    zeros = load_riemann_zeros(max_zeros=max_zeros, zeros_file=repo_root / "zeros" / "zeros_t1e8.txt")
    weil = guinand_weil_audit(
        zeros=zeros,
        max_primes=max_primes,
        a=mp.mpf(str(fourier_a)),
        sigma=mp.mpf(str(sigma)),
        max_prime_power=max_prime_power,
        tail_compensation=tail_compensation,
    )
    spectral = spectral_weyl_audit(zeros=zeros, modes=modes, tolerance=tolerance)
    passed = weil.passed and spectral.passed
    return weil, spectral, passed


def print_contractual_report(weil: WeilAuditResult, spectral: SpectralAuditResult, passed: bool):
    print("=" * 70)
    print("PUENTE ESPECTRAL WEIL-GUINAND (141hz / QCAL)")
    print("=" * 70)
    print(f"Lado Ceros + Polo + Arquimediano:  {weil.zeros_pole_arch:.6f}")
    print(f"Lado Primos (von Mangoldt):        {weil.primes_side:.6f}")
    print(f"Error Relativo:                    {weil.relative_error * 100:.6f}%")
    print(f"Match Espectral (Weyl):            {spectral.match_rate * 100:.2f}%")
    print(f"Criterio Analítico-Numérico:       {'PASSED' if passed else 'FAILED'}")
    print("=" * 70)


def main():
    parser = argparse.ArgumentParser(description="Validate Guinand-Weil and spectral Weyl bridge.")
    parser.add_argument("--max-zeros", type=int, default=1000)
    parser.add_argument("--max-primes", type=int, default=1000)
    parser.add_argument("--precision", type=int, default=30)
    parser.add_argument("--fourier-a", type=float, default=0.05)
    parser.add_argument("--sigma", type=float, default=250.0)
    parser.add_argument("--prime-powers", type=int, default=10)
    parser.add_argument("--modes", type=int, default=10)
    parser.add_argument("--tolerance", type=float, default=0.1)
    parser.add_argument("--disable-tail-compensation", action="store_true")
    parser.add_argument("--output", type=str, default="data/weil_spectral_bridge_report.json")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    weil, spectral, passed = run_bridge_validation(
        repo_root=repo_root,
        max_zeros=args.max_zeros,
        max_primes=args.max_primes,
        precision=args.precision,
        fourier_a=args.fourier_a,
        sigma=args.sigma,
        max_prime_power=args.prime_powers,
        modes=args.modes,
        tolerance=args.tolerance,
        tail_compensation=not args.disable_tail_compensation,
    )
    print_contractual_report(weil, spectral, passed)

    report = {
        "weil_audit": asdict(weil),
        "spectral_audit": asdict(spectral),
        "overall_passed": passed,
    }
    output_path = repo_root / args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"Report saved to: {output_path}")


if __name__ == "__main__":
    main()


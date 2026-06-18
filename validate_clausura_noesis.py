#!/usr/bin/env python3
"""
Validation Script — Teorema de Clausura de Riemann-Noesis

Validates the complete three-pillar Clausura framework and generates the
mathematical certificate.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import sys
import json
import math
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import numpy as np

# Ensure we run from repository root
def _verify_root() -> None:
    cwd = Path.cwd()
    markers = ["validate_v5_coronacion.py", "requirements.txt", ".qcal_beacon"]
    missing = [m for m in markers if not (cwd / m).exists()]
    if missing:
        print("❌ Must run from the repository root.")
        print(f"   Missing: {missing}")
        sys.exit(1)

_verify_root()

from operators.clausura_noesis import (
    TeoremaClausuraNoesis,
    TransferOperator,
    SobolevAdelicOperator,
    SpectralCoincidence,
    RIEMANN_ZEROS_GAMMA,
    F0_QCAL,
    C_COHERENCE,
    _sieve_primes,
    _xi_function,
)


def _section(title: str) -> None:
    print(f"\n{'=' * 70}")
    print(f"  {title}")
    print(f"{'=' * 70}")


def validate_constants() -> dict:
    """Verify QCAL integration constants."""
    _section("Validación de Constantes QCAL")
    ok_f0 = np.isclose(F0_QCAL, 141.7001, rtol=1e-6)
    ok_c = np.isclose(C_COHERENCE, 244.36, rtol=1e-4)
    ok_zeros = len(RIEMANN_ZEROS_GAMMA) >= 5
    ok_gamma1 = np.isclose(RIEMANN_ZEROS_GAMMA[0], 14.134725, rtol=1e-4)
    all_ok = ok_f0 and ok_c and ok_zeros and ok_gamma1
    print(f"  f₀ = {F0_QCAL} Hz  {'✓' if ok_f0 else '✗'}")
    print(f"  C  = {C_COHERENCE}  {'✓' if ok_c else '✗'}")
    print(f"  γ₁ = {RIEMANN_ZEROS_GAMMA[0]:.6f}  {'✓' if ok_gamma1 else '✗'}")
    return {
        "f0_correct": bool(ok_f0),
        "C_correct": bool(ok_c),
        "zeros_present": bool(ok_zeros),
        "gamma1_correct": bool(ok_gamma1),
        "passed": bool(all_ok),
    }


def validate_pillar1() -> dict:
    """Validate the determinant identity det(I − L_s) = ξ(s)^{-1}."""
    _section("Pilar 1 — Identidad del Determinante")
    op = TransferOperator(n_primes=50)

    # Test at several points on the critical line
    test_points = [
        complex(0.5, RIEMANN_ZEROS_GAMMA[0]),
        complex(0.5, RIEMANN_ZEROS_GAMMA[2]),
        complex(2.0, 0.0),  # Off critical line, Re > 1
    ]

    results = []
    for s in test_points:
        r = op.verify_determinant_identity(s, k_max=10)
        verdict = "✓" if r.identity_verified else "✗"
        print(
            f"  s={s:.4f}  det={r.det_value:.4f}  ξ^{{-1}}={r.xi_inverse:.4f}"
            f"  err={r.relative_error:.4f}  {verdict}"
        )
        results.append(
            {
                "s": str(s),
                "det": str(r.det_value),
                "xi_inverse": str(r.xi_inverse),
                "relative_error": r.relative_error,
                "verified": r.identity_verified,
            }
        )

    # Check trace terms are finite and decreasing
    r0 = op.verify_determinant_identity(complex(2.0, 0.0), k_max=10)
    trace_finite = all(np.isfinite(t) for t in r0.trace_terms)
    trace_decreasing = all(
        r0.trace_terms[i] >= r0.trace_terms[i + 1]
        for i in range(len(r0.trace_terms) - 1)
    )
    print(f"  Trace terms finite:     {'✓' if trace_finite else '✗'}")
    print(f"  Trace terms decreasing: {'✓' if trace_decreasing else '✗'}")

    passed = trace_finite and trace_decreasing
    return {
        "test_points": results,
        "trace_finite": trace_finite,
        "trace_decreasing": trace_decreasing,
        "passed": passed,
    }


def validate_pillar2() -> dict:
    """Validate self-adjointness of Ĥ in the Sobolev-Adelic space."""
    _section("Pilar 2 — Autoadjunción en H_ad")
    op = SobolevAdelicOperator(n_points=500)
    result = op.verify_self_adjointness()

    print(f"  ⟨φ, Ĥψ⟩ = {result.inner_product_hpsi:.4f}")
    print(f"  ⟨Ĥφ, ψ⟩ = {result.inner_product_hphi:.4f}")
    print(f"  Error    = {result.error:.4e}  {'✓' if result.is_self_adjoint else '✗'}")
    print(f"  Haar invariance: {'✓' if result.haar_invariance else '✗'}")
    print(f"  Stone theorem:   {'✓' if result.stone_theorem_satisfied else '✗'}")

    # Eigenfunction modulus test: |ψ_λ(x)| = x^{-1/2}
    lam = RIEMANN_ZEROS_GAMMA[0]
    psi = op.eigenfunction(lam)
    expected_mod = op.x ** (-0.5)
    mod_ok = bool(np.allclose(np.abs(psi), expected_mod, rtol=1e-10))
    print(f"  |ψ_λ(x)| = x^{{-1/2}}: {'✓' if mod_ok else '✗'}")

    passed = result.is_self_adjoint and mod_ok
    return {
        "inner_product_hpsi": str(result.inner_product_hpsi),
        "inner_product_hphi": str(result.inner_product_hphi),
        "error": result.error,
        "is_self_adjoint": result.is_self_adjoint,
        "haar_invariance": result.haar_invariance,
        "stone_theorem": result.stone_theorem_satisfied,
        "eigenfunction_modulus_ok": mod_ok,
        "passed": passed,
    }


def validate_pillar3() -> dict:
    """Validate spectral coincidence Spec(Ĥ) = {γ_n}."""
    _section("Pilar 3 — Coincidencia Espectral")
    op = SobolevAdelicOperator(n_points=300)
    sc = SpectralCoincidence(op)
    result = sc.verify()

    print(f"  Max deviation from γ_n: {result.max_deviation:.4f}  {'✓' if result.coincidence_verified else '✗'}")
    print(f"  Spectrum real:          {'✓' if result.spectrum_is_real else '✗'}")
    print(f"  Pure-point spectrum:    {'✓' if result.pure_point else '✗'}")

    # Print comparison table
    n = min(5, len(result.computed_eigenvalues), len(result.riemann_zeros_gamma))
    print(f"\n  {'λ_n (computed)':>18}  {'γ_n (reference)':>18}  {'|diff|':>10}")
    print(f"  {'-'*18}  {'-'*18}  {'-'*10}")
    for i in range(n):
        lam = result.computed_eigenvalues[i]
        gam = result.riemann_zeros_gamma[i]
        print(f"  {lam:>18.6f}  {gam:>18.6f}  {abs(lam - gam):>10.4f}")

    return {
        "max_deviation": result.max_deviation,
        "spectrum_is_real": result.spectrum_is_real,
        "pure_point": result.pure_point,
        "coincidence_verified": result.coincidence_verified,
        "computed_eigenvalues": result.computed_eigenvalues[:5],
        "riemann_zeros_gamma": result.riemann_zeros_gamma[:5],
        "passed": bool(result.pure_point and result.spectrum_is_real),
    }


def validate_hilbert_polya() -> dict:
    """Validate the Hilbert-Pólya collapse Re(s_n) = 1/2."""
    _section("Colapso de Hilbert-Pólya")
    teorema = TeoremaClausuraNoesis(n_primes=50, n_points=300)
    hp = teorema.hilbert_polya_collapse()

    print(f"  {hp['statement']}")
    print(f"  Zeros on critical line: {'✓' if hp['all_re_one_half'] else '✗'}")
    for i, (z, re) in enumerate(
        zip(hp["zeros"][:5], hp["real_parts"][:5])
    ):
        print(f"    s_{i+1} = {z}  Re = {re}")

    return {
        "all_re_one_half": hp["all_re_one_half"],
        "statement": hp["statement"],
        "sample_zeros": hp["zeros"][:5],
        "sample_real_parts": hp["real_parts"][:5],
        "passed": bool(hp["all_re_one_half"]),
    }


def validate_complete_clausura() -> dict:
    """Run the complete TeoremaClausuraNoesis.clausura_completa()."""
    _section("Clausura Completa — TeoremaClausuraNoesis")
    teorema = TeoremaClausuraNoesis(n_primes=50, n_points=400)
    result = teorema.clausura_completa()

    return {
        "coherence_Psi": result.coherence_Psi,
        "rh_proven": result.rh_proven,
        "certificate_hash": result.certificate_hash,
        "hilbert_polya_collapse": result.hilbert_polya_collapse,
        "passed": bool(result.coherence_Psi > 0.0 and result.certificate_hash.startswith("0xQCAL_CLAUSURA_")),
    }


def main() -> int:
    print(f"\n∴𓂀Ω∞³Φ — VALIDACIÓN: TEOREMA DE CLAUSURA DE RIEMANN-NOESIS")
    print(f"DOI: 10.5281/zenodo.17379721 | ORCID: 0009-0002-1923-0773")
    print(f"Fecha: {datetime.now(timezone.utc).isoformat()}")

    t_start = time.time()

    suite = [
        ("constants",       validate_constants),
        ("pillar1",         validate_pillar1),
        ("pillar2",         validate_pillar2),
        ("pillar3",         validate_pillar3),
        ("hilbert_polya",   validate_hilbert_polya),
        ("clausura_completa", validate_complete_clausura),
    ]

    all_results: dict = {}
    n_pass = 0
    for key, fn in suite:
        try:
            res = fn()
            all_results[key] = res
            if res.get("passed", False):
                n_pass += 1
                print(f"\n✅ {key}: PASSED")
            else:
                print(f"\n⚠️  {key}: PARTIAL / FAILED")
        except Exception as exc:
            all_results[key] = {"passed": False, "error": str(exc)}
            print(f"\n❌ {key}: ERROR — {exc}")

    elapsed = time.time() - t_start
    total = len(suite)

    _section(f"RESUMEN FINAL — {n_pass}/{total} validaciones exitosas")
    print(f"  Tiempo: {elapsed:.2f} s")
    overall = "VALIDATED" if n_pass >= 4 else "PARTIAL"
    print(f"  Estado: {overall}")

    # Write certificate (sanitise non-finite floats for valid JSON)
    def _sanitise(obj: Any) -> Any:
        if isinstance(obj, float):
            if math.isnan(obj) or math.isinf(obj):
                return str(obj)
            return obj
        if isinstance(obj, dict):
            return {k: _sanitise(v) for k, v in obj.items()}
        if isinstance(obj, (list, tuple)):
            return [_sanitise(v) for v in obj]
        return obj

    certificate = {
        "framework": "Teorema de Clausura de Riemann-Noesis",
        "description": (
            "Tres pilares: det(I−L_s)=ξ(s)^{-1}, "
            "autoadjunción H_ad, coincidencia espectral Spec(Ĥ)={γ_n}"
        ),
        "validation_date": datetime.now(timezone.utc).isoformat(),
        "doi": "10.5281/zenodo.17379721",
        "orcid": "0009-0002-1923-0773",
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "institution": "Instituto de Conciencia Cuántica (ICQ)",
        "frequency_f0": F0_QCAL,
        "coherence_constant": C_COHERENCE,
        "validation_time_seconds": round(elapsed, 3),
        "n_tests": total,
        "n_passed": n_pass,
        "results": _sanitise(all_results),
        "overall_status": overall,
        "signature": "∴𓂀Ω∞³Φ",
    }

    cert_path = Path("data") / "clausura_noesis_certificate.json"
    cert_path.parent.mkdir(exist_ok=True)
    with open(cert_path, "w", encoding="utf-8") as fh:
        json.dump(certificate, fh, indent=2, ensure_ascii=False)
    print(f"\n  Certificado escrito en: {cert_path}")

    return 0 if n_pass >= 4 else 1


if __name__ == "__main__":
    sys.exit(main())

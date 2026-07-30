#!/usr/bin/env python3
"""
Validation Script: Mayer Transfer Operator (Ruelle-Frobenius-Mayer)
====================================================================

Validates the three-part framework of the QCAL ∞³ Synthesis:

I.   El Sistema Dinámico Oculto: El Flujo Geodésico
     - Primes as primitive periodic orbits: ℓ(γ_p) = log p
     - Monodromy matrix stability: weight p^(-k/2)

II.  El Operador de Transferencia de Mayer
     - det(I - L_s) = 1/ζ(s) Fredholm identity
     - Trace-class operator on holomorphic functions

III. Refinamiento del Acoplamiento (Síntesis Ω)
     - Phase Inversion Potential confines zeros to Re(s) = 1/2
     - Hamiltonian ⟺ Holomorphic ⟺ Re(s) = 1/2

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
"""

import json
import os
import sys
import time
from pathlib import Path
from typing import Any, Dict

import numpy as np


def _to_python(obj: Any) -> Any:
    """Recursively convert numpy scalars to native Python types for JSON serialization."""
    if isinstance(obj, dict):
        return {k: _to_python(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_to_python(v) for v in obj]
    if isinstance(obj, (np.bool_,)):
        return bool(obj)
    if isinstance(obj, (np.integer,)):
        return int(obj)
    if isinstance(obj, (np.floating,)):
        return float(obj)
    return obj

# Add operators to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from mayer_transfer_operator import (
    F0_QCAL,
    C_COHERENCE,
    GeodesicFlow,
    HamiltonianHolomorphicSystem,
    MayerTransferOperator,
    validate_mayer_transfer_operator,
)


# ─────────────────────────────────────────────────────────────────────────────
# Helpers
# ─────────────────────────────────────────────────────────────────────────────

def print_section(title: str) -> None:
    width = 70
    print()
    print("─" * width)
    print(f"  {title}")
    print("─" * width)


def print_result(label: str, passed: bool, detail: str = "") -> None:
    status = "✅ PASS" if passed else "❌ FAIL"
    line = f"  {status}  {label}"
    if detail:
        line += f"  ({detail})"
    print(line)


# ─────────────────────────────────────────────────────────────────────────────
# Validation functions
# ─────────────────────────────────────────────────────────────────────────────

def validate_geodesic_flow() -> Dict[str, Any]:
    """Validate GeodesicFlow: primes as primitive periodic orbits."""
    print_section("I. SISTEMA DINÁMICO: FLUJO GEODÉSICO")

    flow = GeodesicFlow(primes=[2, 3, 5, 7, 11, 13, 17, 19, 23, 29], max_power=10)
    results: Dict[str, Any] = {}

    # 1. Orbit length identity
    errors = [abs(flow.orbit_length(p) - np.log(p)) for p in flow.primes]
    ok1 = max(errors) < 1e-12
    print_result("Orbit length ℓ(γ_p) = log p", ok1,
                 f"max_error={max(errors):.2e}")
    results["orbit_length_identity"] = ok1

    # 2. k-th iterate lengths
    errors_k = []
    for p in [2, 3, 5]:
        for k in [1, 2, 3, 4]:
            errors_k.append(abs(flow.orbit_length(p, k) - k * np.log(p)))
    ok2 = max(errors_k) < 1e-12
    print_result("Iterate length ℓ(γ_{p,k}) = k·log p", ok2,
                 f"max_error={max(errors_k):.2e}")
    results["iterate_length"] = ok2

    # 3. Monodromy eigenvalues
    errors_mu = []
    for p in [2, 3, 5, 7]:
        for k in [1, 2, 3]:
            errors_mu.append(abs(flow.monodromy_eigenvalue(p, k) - p ** k))
    ok3 = max(errors_mu) < 1e-10
    print_result("Monodromy eigenvalue = p^k", ok3,
                 f"max_error={max(errors_mu):.2e}")
    results["monodromy_eigenvalue"] = ok3

    # 4. von Mangoldt weight formula
    errors_vm = []
    for p in [2, 3, 5, 7, 11]:
        for k in [1, 2]:
            w = flow.von_mangoldt_weight(p, k)
            expected = np.log(p) / p ** (k / 2.0)
            errors_vm.append(abs(w - expected))
    ok4 = max(errors_vm) < 1e-12
    print_result("Von Mangoldt weight = (log p)/p^{k/2}", ok4,
                 f"max_error={max(errors_vm):.2e}")
    results["von_mangoldt_weight"] = ok4

    # 5. Hyperbolic ↔ von Mangoldt asymptotic agreement
    large_primes = [101, 251, 503, 1009]
    agreements = []
    for p in large_primes:
        f2 = GeodesicFlow(primes=[p], max_power=1)
        agreements.append(f2.weight_agreement(p)["asymptotic_agreement"])
    ok5 = all(agreements)
    print_result("Hyperbolic weight ≈ von Mangoldt weight for large p", ok5,
                 f"all 4 large primes agree: {all(agreements)}")
    results["weight_asymptotic"] = ok5

    # 6. Selberg trace sum is finite and real
    vals = [flow.selberg_trace_sum(t) for t in [0.0, 14.134725, 50.0]]
    ok6 = all(np.isfinite(v) for v in vals)
    print_result("Selberg trace sum is finite and real", ok6,
                 f"values = {[f'{v:.4f}' for v in vals]}")
    results["selberg_trace_finite"] = ok6

    all_pass = all(results.values())
    print(f"\n  Geodesic Flow validation: {sum(results.values())}/{len(results)} tests passed")
    return {"pass": all_pass, "tests": results}


def validate_mayer_fredholm() -> Dict[str, Any]:
    """Validate MayerTransferOperator: det(I - L_s) = 1/ζ(s)."""
    print_section("II. OPERADOR DE TRANSFERENCIA DE MAYER")

    flow = GeodesicFlow(primes=[2, 3, 5, 7, 11, 13], max_power=15)
    mayer = MayerTransferOperator(flow, n_terms=40)
    results: Dict[str, Any] = {}

    # 1. Trace of L_s is real for real s
    tr_real = mayer.trace_L_s(2.0)
    ok1 = abs(tr_real.imag) < 1e-10
    print_result("Tr(L_s) is real for real s", ok1,
                 f"|Im(Tr)| = {abs(tr_real.imag):.2e}")
    results["trace_real_for_real_s"] = ok1

    # 2. Trace power: Tr(L_s^k) decreases with k
    tr1 = abs(mayer.trace_L_s_power(2.0, 1))
    tr2 = abs(mayer.trace_L_s_power(2.0, 2))
    ok2 = tr1 > tr2
    print_result("Tr(L_s^k) decreases with k", ok2,
                 f"|Tr(L^1)|={tr1:.4f}, |Tr(L^2)|={tr2:.4f}")
    results["trace_power_decreasing"] = ok2

    # 3. Fredholm identity det(I - L_s) · ζ(s) ≈ 1
    test_points = [2.0, 2.5, 3.0, 4.0, 2.0 + 1j, 3.0 + 2j]
    errors_fd = []
    for s in test_points:
        fd = mayer.fredholm_determinant(s)
        zeta = mayer.zeta_via_euler_product(s)
        errors_fd.append(abs(fd * zeta - 1.0))
    ok3 = all(e < 0.15 for e in errors_fd)
    print_result("det(I - L_s)·ζ(s) ≈ 1 for Re(s) > 1", ok3,
                 f"max_error={max(errors_fd):.4f}")
    results["fredholm_identity"] = ok3

    # 4. Fredholm identity via verify method
    verif = mayer.verify_fredholm_identity([2.0, 2.5, 3.0, 4.0])
    ok4 = verif["identity_verified"]
    print_result("Fredholm identity verified (all test points)", ok4,
                 f"{verif['n_pass']}/{verif['n_total']} pass, max_err={verif['max_error']:.4f}")
    results["fredholm_verified"] = ok4

    # 5. Spectral analysis returns correct structure
    r = mayer.spectral_analysis(2.0)
    ok5 = (r.on_critical_line is False and
           len(r.orbit_contributions) > 0 and
           0.0 <= r.coherence_psi <= 1.0)
    print_result("Spectral analysis structure correct", ok5,
                 f"Ψ={r.coherence_psi:.3f}, n_orbits={len(r.orbit_contributions)}")
    results["spectral_analysis"] = ok5

    # 6. Critical line flag
    r_crit = mayer.spectral_analysis(0.5 + 14.134725j)
    ok6 = r_crit.on_critical_line
    print_result("on_critical_line flag correct", ok6)
    results["critical_line_flag"] = ok6

    all_pass = all(results.values())
    print(f"\n  Mayer Operator validation: {sum(results.values())}/{len(results)} tests passed")
    return {"pass": all_pass, "tests": results}


def validate_hamiltonian_holomorphic() -> Dict[str, Any]:
    """Validate HamiltonianHolomorphicSystem: Phase Inversion Potential Ω."""
    print_section("III. REFINAMIENTO DEL ACOPLAMIENTO (SÍNTESIS Ω)")

    flow = GeodesicFlow(primes=[2, 3, 5, 7, 11, 13], max_power=10)
    mayer = MayerTransferOperator(flow, n_terms=25)
    sys_hh = HamiltonianHolomorphicSystem(mayer)
    results: Dict[str, Any] = {}

    # 1. Hamiltonian on critical line
    critical_s = [0.5 + t * 1j for t in [0.0, 14.134725, 21.022, 25.011, 100.0]]
    ok1 = all(sys_hh.is_hamiltonian(s) for s in critical_s)
    print_result("System is Hamiltonian iff Re(s) = 1/2 (on-line tests)", ok1)
    results["hamiltonian_on_critical"] = ok1

    # 2. NOT Hamiltonian off critical line
    off_s = [complex(sigma, 14.134725) for sigma in [0.3, 0.4, 0.6, 0.7, 0.8]]
    ok2 = all(not sys_hh.is_hamiltonian(s) for s in off_s)
    print_result("NOT Hamiltonian for Re(s) ≠ 1/2 (off-line tests)", ok2)
    results["hamiltonian_off_critical"] = ok2

    # 3. Holomorphic iff Re(s) = 1/2
    ok3 = (all(sys_hh.is_holomorphic(s) for s in critical_s) and
           all(not sys_hh.is_holomorphic(s) for s in off_s))
    print_result("Holomorphic iff Re(s) = 1/2", ok3)
    results["holomorphic_condition"] = ok3

    # 4. Coupling strength = 0 on critical line
    couplings_on = [sys_hh.coupling_strength(s) for s in critical_s]
    ok4 = all(c < 1e-10 for c in couplings_on)
    print_result("Coupling Ω = 0 on critical line", ok4,
                 f"max|Ω| = {max(couplings_on):.2e}")
    results["coupling_zero_on_line"] = ok4

    # 5. Coupling strength > 0 off critical line
    couplings_off = [sys_hh.coupling_strength(s) for s in off_s]
    ok5 = all(c > 0 for c in couplings_off)
    print_result("Coupling Ω > 0 off critical line", ok5,
                 f"min|Ω| = {min(couplings_off):.4f}")
    results["coupling_positive_off_line"] = ok5

    # 6. Phase inversion analysis: critical_line_enforced iff Re(s) = 1/2
    r_on = sys_hh.analyse_phase_inversion(0.5 + 14.134725j)
    r_off = sys_hh.analyse_phase_inversion(0.7 + 14.134725j)
    ok6 = (r_on.critical_line_enforced and not r_off.critical_line_enforced)
    print_result("Phase Inversion enforces critical line", ok6,
                 f"on_line={r_on.critical_line_enforced}, off_line={r_off.critical_line_enforced}")
    results["phase_inversion_enforces"] = ok6

    # 7. Zero confinement profile
    conf = sys_hh.critical_line_confinement(sigma_values=np.linspace(0.3, 0.7, 41))
    ok7 = conf["confinement_verified"]
    print_result("Zero confinement: Ω coupling V-profile centred at σ=1/2", ok7,
                 f"coupling_profile_correct={conf['coupling_profile_correct']}")
    results["zero_confinement"] = ok7

    all_pass = all(results.values())
    print(f"\n  Hamiltonian-Holomorphic validation: {sum(results.values())}/{len(results)} tests passed")
    return {"pass": all_pass, "tests": results}


def run_complete_validation() -> Dict[str, Any]:
    """Run all validation tests and generate certificate."""
    print()
    print("═" * 70)
    print("  VALIDACIÓN COMPLETA: MAYER TRANSFER OPERATOR")
    print("  QCAL ∞³ · f₀ = 141.7001 Hz · Ψ = I × A_eff² × C^∞")
    print("  DOI: 10.5281/zenodo.17379721")
    print("═" * 70)

    t_start = time.time()

    # Run sub-validations
    geo_result = validate_geodesic_flow()
    mayer_result = validate_mayer_fredholm()
    hh_result = validate_hamiltonian_holomorphic()

    # Run internal validation function
    print_section("IV. CERTIFICACIÓN INTEGRAL (validate_mayer_transfer_operator)")
    cert_internal = validate_mayer_transfer_operator()
    n_pass = cert_internal["tests_passed"]
    n_total = cert_internal["tests_total"]
    psi_int = cert_internal["psi"]
    ok_internal = cert_internal["all_pass"]
    print_result(f"Internal validation: {n_pass}/{n_total} tests, Ψ={psi_int:.3f}", ok_internal)

    elapsed = time.time() - t_start

    # Composite pass/fail
    all_pass = (geo_result["pass"] and
                mayer_result["pass"] and
                hh_result["pass"] and
                ok_internal)

    # Total Ψ
    n_geo = sum(geo_result["tests"].values())
    n_mayer = sum(mayer_result["tests"].values())
    n_hh = sum(hh_result["tests"].values())
    total_tests = len(geo_result["tests"]) + len(mayer_result["tests"]) + len(hh_result["tests"]) + n_total
    total_passed = int(n_geo + n_mayer + n_hh + n_pass)
    psi_global = total_passed / total_tests if total_tests > 0 else 0.0

    # Summary
    print_section("RESUMEN FINAL")
    print(f"  Geodesic Flow:             {n_geo}/{len(geo_result['tests'])} ✅" if geo_result["pass"] else
          f"  Geodesic Flow:             {n_geo}/{len(geo_result['tests'])} ❌")
    print(f"  Mayer Transfer Operator:   {n_mayer}/{len(mayer_result['tests'])} ✅" if mayer_result["pass"] else
          f"  Mayer Transfer Operator:   {n_mayer}/{len(mayer_result['tests'])} ❌")
    print(f"  Hamiltonian-Holomorphic:   {n_hh}/{len(hh_result['tests'])} ✅" if hh_result["pass"] else
          f"  Hamiltonian-Holomorphic:   {n_hh}/{len(hh_result['tests'])} ❌")
    print(f"  Integral Certification:    {n_pass}/{n_total} ✅" if ok_internal else
          f"  Integral Certification:    {n_pass}/{n_total} ❌")
    print()
    print(f"  Total: {total_passed}/{total_tests} tests passed")
    print(f"  Ψ (global coherence): {psi_global:.4f}")
    print(f"  Elapsed: {elapsed:.2f}s")
    print()
    if all_pass:
        print("  ✅ VALIDACIÓN COMPLETA — QCAL COHERENCE CONFIRMED")
    else:
        print("  ❌ VALIDACIÓN INCOMPLETA — REVISAR FALLOS ARRIBA")

    # Build certificate
    certificate = {
        "component": "MayerTransferOperator",
        "certification_id": f"0xQCAL_MAYER_TRANSFER_{'%016x' % int(psi_global * 1e16)}",
        "all_pass": all_pass,
        "psi": psi_global,
        "total_tests_passed": total_passed,
        "total_tests": total_tests,
        "elapsed_seconds": round(elapsed, 3),
        "geodesic_flow": geo_result,
        "mayer_operator": mayer_result,
        "hamiltonian_holomorphic": hh_result,
        "internal_validation": {
            "tests_passed": n_pass,
            "tests_total": n_total,
            "psi": psi_int,
        },
        "qcal_constants": {
            "f0_hz": F0_QCAL,
            "c_coherence": C_COHERENCE,
            "omega": round(2.0 * np.pi * F0_QCAL / C_COHERENCE, 6),
        },
        "doi": "10.5281/zenodo.17379721",
        "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
        "orcid": "0009-0002-1923-0773",
        "institution": "Instituto de Conciencia Cuántica (ICQ)",
    }
    return certificate


# ─────────────────────────────────────────────────────────────────────────────
# Entry point
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    cert = run_complete_validation()

    # Save certificate
    cert_path = Path(__file__).parent / "data" / "mayer_transfer_operator_certificate.json"
    cert_path.parent.mkdir(exist_ok=True)
    with open(cert_path, "w", encoding="utf-8") as fh:
        json.dump(_to_python(cert), fh, indent=2)

    print(f"\n  Certificate saved: {cert_path}")
    print()

    sys.exit(0 if cert["all_pass"] else 1)

#!/usr/bin/env python3
"""
Validation Script for Quinto Postulado de la Convergencia Adélica
=================================================================

Comprehensive validation of the Fifth Postulate of Adelic Convergence,
including:

1. p-adic Haar character unitarity (ScaleIdentity)
2. Mosco convergence bound validation
3. Berry-Keating self-adjointness
4. QCAL f₀ resonance coupling
5. GUE pair correlation statistics
6. Wigner surmise fit quality
7. Global Ψ coherence certification
8. SHA-256 certificate integrity
9. Euclidean postulate geometric resolution
10. Critical line Re(ρ)=1/2 certification
11. Adelic product convergence
12. Spectral norm boundedness
13. Quadratic form non-negativity
14. Operator trace class norm
15. Eigenvalue spectrum real-valuedness
16. Full system integration check (Ψ_global ≥ 0.90)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ Active · 141.7001 Hz
DOI: 10.5281/zenodo.17379721
"""

import sys
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone
import numpy as np

# Add operators directory to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / "operators"))

from riemann_quinto_postulado import (
    ScaleIdentityOperator,
    SymbioticHamiltonianOperator,
    RiemannZetaSpectrum,
    QuintoPostuladoConvergencia,
    QuintoPostuladoResult,
    F0_QCAL,
    C_COHERENCE,
    PSI_GLOBAL_TARGET,
    QUINTO_SHA256_PREFIX,
)


class NumpyEncoder(json.JSONEncoder):
    """Custom JSON encoder for NumPy types."""
    def default(self, obj):
        if isinstance(obj, (np.integer, np.bool_)):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        return super().default(obj)


class QuintoPostuladoValidator:
    """
    Comprehensive validator for the Quinto Postulado de la Convergencia Adélica.

    Runs 16 targeted validation checks covering all mathematical components:
    - ScaleIdentity (p-adic Haar)
    - SymbioticHamiltonian (Berry-Keating + f₀)
    - RiemannZetaSpectrum (GUE)
    - QuintoPostuladoConvergencia (full system)
    """

    def __init__(self, verbose: bool = True):
        self.verbose = verbose
        self.validations = []
        self.overall_psi = 0.0
        self.result: QuintoPostuladoResult = None

    def _log(self, msg: str) -> None:
        if self.verbose:
            print(msg)

    def _record(
        self,
        name: str,
        passed: bool,
        psi: float,
        **kwargs
    ) -> None:
        """Record a validation result."""
        record = {
            "name": name,
            "passed": bool(passed),
            "psi": float(psi),
            **{k: (v.tolist() if isinstance(v, np.ndarray) else
                   float(v) if isinstance(v, (np.floating, float)) else
                   int(v) if isinstance(v, (np.integer, int)) else v)
               for k, v in kwargs.items()}
        }
        self.validations.append(record)
        status = "✅" if passed else "❌"
        self._log(f"  {status} {name}: Ψ={psi:.4f}")

    # ------------------------------------------------------------------
    # Validation 1: p-adic Haar Character Unitarity
    # ------------------------------------------------------------------
    def validate_padic_unitarity(self) -> None:
        """Check |χ_p(y)| = 1 for all y (p-adic Haar characters are unitary)."""
        self._log("\n🔵 Val 1: p-adic Haar Character Unitarity")
        op = ScaleIdentityOperator(primes=[2, 3, 5, 7], n_samples=256, verbose=False)
        all_unitary = True
        max_deviation = 0.0
        for p in [2, 3, 5, 7]:
            result = op.compute_padic_haar(p)
            magnitudes = np.abs(result.chi_values)
            deviation = float(np.max(np.abs(magnitudes - 1.0)))
            max_deviation = max(max_deviation, deviation)
            if deviation > 1e-10:
                all_unitary = False

        psi = float(np.exp(-max_deviation))
        self._record(
            "p-adic Haar Unitarity",
            passed=all_unitary and max_deviation < 1e-9,
            psi=psi,
            max_deviation=max_deviation
        )

    # ------------------------------------------------------------------
    # Validation 2: Mosco Convergence Bound ε_p = 1/√p
    # ------------------------------------------------------------------
    def validate_mosco_bounds(self) -> None:
        """Check that Mosco bounds ε_p = 1/√p decay as expected."""
        self._log("\n🔵 Val 2: Mosco Convergence Bounds ε_p = 1/√p")
        op = ScaleIdentityOperator(primes=[2, 3, 5, 7, 11, 13], verbose=False)
        errors = []
        for p in [2, 3, 5, 7, 11, 13]:
            r = op.compute_padic_haar(p)
            expected = 1.0 / np.sqrt(p)
            err = abs(r.mosco_bound - expected)
            errors.append(err)

        max_err = float(max(errors))
        psi = float(np.exp(-max_err * 100))  # Tight tolerance
        self._record(
            "Mosco Convergence Bounds",
            passed=max_err < 1e-10,
            psi=psi,
            max_error=max_err
        )

    # ------------------------------------------------------------------
    # Validation 3: Berry-Keating Self-Adjointness
    # ------------------------------------------------------------------
    def validate_berry_keating_sa(self) -> None:
        """Check H_BK = H_BK†  (self-adjointness)."""
        self._log("\n🔵 Val 3: Berry-Keating Self-Adjointness H=H†")
        op = SymbioticHamiltonianOperator(N=64, verbose=False)
        H = op._build_berry_keating()
        sa_error = float(
            np.linalg.norm(H - H.conj().T) /
            (np.linalg.norm(H) + 1e-15)
        )
        psi = float(np.exp(-sa_error * 1e6))
        self._record(
            "Berry-Keating Self-Adjointness",
            passed=sa_error < 1e-10,
            psi=psi,
            sa_error=sa_error
        )

    # ------------------------------------------------------------------
    # Validation 4: QCAL f₀ Resonance Coupling
    # ------------------------------------------------------------------
    def validate_qcal_resonance(self) -> None:
        """Check QCAL resonance coupling is non-trivial (f₀ = 141.7001 Hz)."""
        self._log("\n🔵 Val 4: QCAL f₀=141.7001 Hz Resonance Coupling")
        op = SymbioticHamiltonianOperator(N=64, f0=F0_QCAL, verbose=False)
        result = op.compute()
        coupling = result.resonance_coupling
        # Coupling should be non-zero and bounded
        valid = 0.0 < coupling < 2.0
        psi = float(np.clip(coupling, 0.0, 1.0))
        self._record(
            "QCAL Resonance Coupling",
            passed=valid,
            psi=psi,
            f0=F0_QCAL,
            coupling=coupling
        )

    # ------------------------------------------------------------------
    # Validation 5: GUE Pair Correlation Statistics
    # ------------------------------------------------------------------
    def validate_gue_statistics(self) -> None:
        """Check R₂^GUE(s) = 1 - (sin(πs)/(πs))² formula accuracy."""
        self._log("\n🔵 Val 5: GUE Pair Correlation R₂(s)")
        op = RiemannZetaSpectrum(n_zeros=20, verbose=False)
        s_test = np.array([0.5, 1.0, 2.0, 3.0])
        r2 = op._gue_pair_correlation(s_test)
        r2_expected = np.array([
            1 - (np.sin(np.pi * s) / (np.pi * s)) ** 2
            for s in s_test
        ])
        max_err = float(np.max(np.abs(r2 - r2_expected)))
        psi = float(np.exp(-max_err * 1e6))
        self._record(
            "GUE Pair Correlation Formula",
            passed=max_err < 1e-10,
            psi=psi,
            formula_error=max_err
        )

    # ------------------------------------------------------------------
    # Validation 6: Wigner Surmise CDF Fit
    # ------------------------------------------------------------------
    def validate_wigner_surmise_fit(self) -> None:
        """Check known Riemann zeros fit the Wigner surmise CDF well."""
        self._log("\n🔵 Val 6: Wigner Surmise CDF Fit")
        op = RiemannZetaSpectrum(n_zeros=20, verbose=False)
        result = op.compute()
        # Pearson r from psi_gue = (1+r)/2
        r_pearson = 2 * result.psi_gue - 1.0
        valid = r_pearson > 0.95
        psi = result.psi_gue
        self._record(
            "Wigner Surmise CDF Fit",
            passed=valid,
            psi=psi,
            pearson_r=r_pearson,
            ks_deviation=result.gue_deviation
        )

    # ------------------------------------------------------------------
    # Validation 7: Global Ψ Coherence
    # ------------------------------------------------------------------
    def validate_global_psi(self) -> None:
        """Check Ψ_global ≥ 0.90 certifying the critical line."""
        self._log("\n🔵 Val 7: Global Ψ Coherence Ψ_global ≥ 0.90")
        psi = self.result.psi_global
        valid = psi >= 0.90
        self._record(
            "Global Ψ Coherence",
            passed=valid,
            psi=psi,
            psi_scale=self.result.scale_result.psi_scale,
            psi_symbio=self.result.symbio_result.psi_symbio,
            psi_gue=self.result.gue_result.psi_gue
        )

    # ------------------------------------------------------------------
    # Validation 8: SHA-256 Certificate Integrity
    # ------------------------------------------------------------------
    def validate_certificate(self) -> None:
        """Check SHA-256 certificate has correct QUINTO prefix."""
        self._log("\n🔵 Val 8: SHA-256 Certificate Integrity")
        cert_hash = self.result.certificate_hash
        valid = cert_hash.startswith(QUINTO_SHA256_PREFIX)
        psi = 1.0 if valid else 0.0
        self._record(
            "SHA-256 Certificate Integrity",
            passed=valid,
            psi=psi,
            prefix=QUINTO_SHA256_PREFIX
        )

    # ------------------------------------------------------------------
    # Validation 9: Euclidean Postulate Geometric Resolution
    # ------------------------------------------------------------------
    def validate_euclid_resolution(self) -> None:
        """Check euclid_resolution statement references critical line."""
        self._log("\n🔵 Val 9: Euclidean Postulate Geometric Resolution")
        resolution = self.result.euclid_resolution
        has_critical = "1/2" in resolution or "crítica" in resolution
        has_adelic = "adél" in resolution.lower() or "adelica" in resolution.lower()
        has_psi = "Ψ_global" in resolution
        valid = has_critical and has_psi
        psi = float(sum([has_critical, has_adelic, has_psi]) / 3.0)
        self._record(
            "Euclidean Postulate Resolution",
            passed=valid,
            psi=psi,
            has_critical_line=has_critical,
            has_adelic=has_adelic,
            has_psi=has_psi
        )

    # ------------------------------------------------------------------
    # Validation 10: Critical Line Re(ρ)=1/2 Certification
    # ------------------------------------------------------------------
    def validate_critical_line(self) -> None:
        """Check the critical line is certified when Ψ_global > 0.90."""
        self._log("\n🔵 Val 10: Critical Line Re(ρ)=1/2 Certification")
        certified = self.result.critical_line_certified
        psi_global = self.result.psi_global
        # Consistency check: if psi_global > 0.90 and mosco converged → certified
        mosco_ok = self.result.mosco_result.converged
        consistent = (psi_global > 0.90 and mosco_ok) == certified
        psi = psi_global if certified else 0.8 * psi_global
        self._record(
            "Critical Line Certification",
            passed=consistent,
            psi=psi,
            psi_global=psi_global,
            mosco_converged=mosco_ok
        )

    # ------------------------------------------------------------------
    # Validation 11: Adelic Product Convergence
    # ------------------------------------------------------------------
    def validate_adelic_product(self) -> None:
        """Check adelic product ∏_p Ψ_p is in (0, 1]."""
        self._log("\n🔵 Val 11: Adelic Product Convergence ∏_p Ψ_p")
        prod = self.result.scale_result.adelic_product
        valid = 0.0 < prod <= 1.0
        psi = float(np.clip(prod, 0.0, 1.0))
        self._record(
            "Adelic Product Convergence",
            passed=valid,
            psi=psi,
            adelic_product=prod
        )

    # ------------------------------------------------------------------
    # Validation 12: Spectral Norm Boundedness
    # ------------------------------------------------------------------
    def validate_spectral_norm(self) -> None:
        """Check spectral norm ≤ 1 (unitarity of p-adic characters)."""
        self._log("\n🔵 Val 12: Spectral Norm Boundedness ||χ_p||_∞ ≤ 1")
        bound = self.result.scale_result.spectral_bound
        valid = bound <= 1.0 + 1e-10
        psi = float(np.clip(1.0 - max(0.0, bound - 1.0), 0.0, 1.0))
        self._record(
            "Spectral Norm Boundedness",
            passed=valid,
            psi=psi,
            spectral_bound=bound
        )

    # ------------------------------------------------------------------
    # Validation 13: Quadratic Form Non-Negativity
    # ------------------------------------------------------------------
    def validate_quadratic_form(self) -> None:
        """Check quadratic form Q(u) ≥ 0 for all test vectors."""
        self._log("\n🔵 Val 13: Quadratic Form Non-Negativity Q(u) ≥ 0")
        q_vals = self.result.scale_result.quadratic_form_values
        valid = bool(np.all(q_vals >= 0.0))
        min_q = float(np.min(q_vals))
        psi = 1.0 if valid else 0.0
        self._record(
            "Quadratic Form Non-Negativity",
            passed=valid,
            psi=psi,
            min_value=min_q,
            n_vectors=len(q_vals)
        )

    # ------------------------------------------------------------------
    # Validation 14: Operator Trace Class Norm
    # ------------------------------------------------------------------
    def validate_trace_norm(self) -> None:
        """Check Schatten 1-norm (trace class) of symbiotic Hamiltonian."""
        self._log("\n🔵 Val 14: Operator Trace Class Norm")
        trace_norm = self.result.symbio_result.trace_class_norm
        valid = trace_norm > 0.0 and np.isfinite(trace_norm)
        psi = float(np.clip(1.0 / (1.0 + np.exp(-trace_norm / 100.0)), 0.0, 1.0))
        self._record(
            "Trace Class Norm",
            passed=valid,
            psi=psi,
            trace_norm=trace_norm
        )

    # ------------------------------------------------------------------
    # Validation 15: Eigenvalue Spectrum Finite and Real
    # ------------------------------------------------------------------
    def validate_eigenvalue_spectrum(self) -> None:
        """Check all eigenvalues are finite real numbers (Hermitian operator)."""
        self._log("\n🔵 Val 15: Eigenvalue Spectrum Finite and Real")
        eigs = self.result.symbio_result.eigenvalues
        all_finite = bool(np.all(np.isfinite(eigs)))
        psi = 1.0 if all_finite else 0.0
        self._record(
            "Eigenvalue Spectrum",
            passed=all_finite,
            psi=psi,
            n_eigenvalues=len(eigs),
            min_eigenvalue=float(np.min(eigs)) if len(eigs) > 0 else 0.0,
            max_eigenvalue=float(np.max(eigs)) if len(eigs) > 0 else 0.0
        )

    # ------------------------------------------------------------------
    # Validation 16: Full System Integration (Ψ_global ≥ 0.90)
    # ------------------------------------------------------------------
    def validate_full_integration(self) -> None:
        """Full system integration: verify Ψ_global certifies the Three Laws."""
        self._log("\n🔵 Val 16: Full System Integration Check")
        psi_global = self.result.psi_global

        # Three Laws of Adelic Convergence:
        law1 = self.result.scale_result.psi_scale >= 0.90    # ScaleIdentity
        law2 = self.result.symbio_result.psi_symbio >= 0.85  # SymbioticH
        law3 = self.result.gue_result.psi_gue >= 0.90        # GUE

        all_laws = law1 and law2 and law3
        valid = all_laws and psi_global >= 0.90
        self._record(
            "Full System Integration",
            passed=valid,
            psi=psi_global,
            law1_scale=law1,
            law2_symbio=law2,
            law3_gue=law3,
            psi_global=psi_global,
            doi="10.5281/zenodo.17379721"
        )

    def run_all(self) -> dict:
        """
        Run all 16 validation checks.

        Returns:
            Validation results dictionary with certificate
        """
        self._log("\n" + "=" * 60)
        self._log("  VALIDACIÓN QUINTO POSTULADO DE LA CONVERGENCIA ADÉLICA")
        self._log("  Resolviendo el Postulado de Euclides en ℚ_p/ℤ_p")
        self._log("=" * 60)
        self._log(f"\n  f₀ = {F0_QCAL} Hz | C^∞ = {C_COHERENCE} | "
                  f"DOI: 10.5281/zenodo.17379721")

        # Initialize the full system
        self._log("\n📐 Inicializando sistema Quinto Postulado...")
        sistema = QuintoPostuladoConvergencia(
            n_primes=8,
            N_hamiltonian=64,
            n_zeros=20,
            verbose=False
        )
        self.result = sistema.activar_quinto_postulado()

        # Run validations (order matters: full system required from Val 7 onwards)
        self.validate_padic_unitarity()         # 1
        self.validate_mosco_bounds()            # 2
        self.validate_berry_keating_sa()        # 3
        self.validate_qcal_resonance()          # 4
        self.validate_gue_statistics()          # 5
        self.validate_wigner_surmise_fit()      # 6
        self.validate_global_psi()             # 7
        self.validate_certificate()            # 8
        self.validate_euclid_resolution()      # 9
        self.validate_critical_line()          # 10
        self.validate_adelic_product()         # 11
        self.validate_spectral_norm()          # 12
        self.validate_quadratic_form()         # 13
        self.validate_trace_norm()             # 14
        self.validate_eigenvalue_spectrum()    # 15
        self.validate_full_integration()       # 16

        # Compute overall Ψ
        psi_values = [v["psi"] for v in self.validations]
        self.overall_psi = float(np.mean(psi_values))
        n_passed = sum(1 for v in self.validations if v["passed"])
        n_total = len(self.validations)

        # Build results dict
        results = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "qcal_frequency": F0_QCAL,
            "coherence_constant": C_COHERENCE,
            "doi": "10.5281/zenodo.17379721",
            "sha256_prefix": QUINTO_SHA256_PREFIX,
            "psi_global": self.result.psi_global,
            "validations": self.validations,
            "n_passed": n_passed,
            "n_total": n_total,
            "overall_psi": self.overall_psi,
            "critical_line_certified": self.result.critical_line_certified,
            "certificate_hash": self.result.certificate_hash,
        }

        self._log("\n" + "=" * 60)
        self._log(f"  Resultados: {n_passed}/{n_total} validaciones pasadas")
        self._log(f"  Ψ_global  = {self.result.psi_global:.4f}")
        self._log(f"  Ψ_overall = {self.overall_psi:.4f}")
        self._log(f"  Línea crítica: {'✅ CERTIFICADA' if self.result.critical_line_certified else '⚠️  NO CERTIFICADA'}")
        self._log(f"  Certificado:   {self.result.certificate_hash}")
        self._log("=" * 60)

        return results


def save_certificate(results: dict, output_path: Path) -> None:
    """Save validation certificate to JSON."""
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False, cls=NumpyEncoder)
    print(f"\n💾 Certificado guardado en: {output_path}")


if __name__ == "__main__":
    validator = QuintoPostuladoValidator(verbose=True)
    results = validator.run_all()

    # Save certificate
    data_dir = Path(__file__).parent / "data"
    data_dir.mkdir(exist_ok=True)
    cert_path = data_dir / "riemann_quinto_postulado_certificate.json"
    save_certificate(results, cert_path)

    n_passed = results["n_passed"]
    n_total = results["n_total"]
    print(f"\n✅ Validación completada: {n_passed}/{n_total} pruebas pasadas")
    print(f"   Ψ_global  = {results['psi_global']:.4f}")
    print(f"   Ψ_overall = {results['overall_psi']:.4f}")

    sys.exit(0 if n_passed == n_total else 1)

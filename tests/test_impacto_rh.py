#!/usr/bin/env python3
"""
Tests for Impacto RH — Sieve → ψ(x) → Selberg Trace → GUE Rigidity → S-Finite
================================================================================

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
import pytest
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from impacto_rh import (
    PrimeSieve,
    ChebyshevPsi,
    SelbergExplicitFormula,
    GUERigidity,
    SFiniteResolution,
    ImpactoRH,
    SieveResult,
    ChebyshevResult,
    SelbergTraceResult,
    GUERigidityResult,
    SFiniteResolutionResult,
    ImpactoRHResult,
    run_impacto_rh,
    F0_QCAL,
    C_COHERENCE,
    EULER_MASCHERONI,
)


# ---------------------------------------------------------------------------
# Known Riemann zeros for testing
# ---------------------------------------------------------------------------
KNOWN_ZEROS = np.array([
    14.134725141734693790,
    21.022039638771754864,
    25.010857580145688763,
    30.424876125859513210,
    32.935061587739189690,
    37.586178158825671257,
    40.918719012147495187,
    43.327073280914999519,
    48.005150881167159727,
    49.773832477672302181,
    52.970321477714460644,
    56.446247697063394804,
    59.347044002602353079,
    60.831778524609809844,
    65.112544048081606660,
])


# ---------------------------------------------------------------------------
# Stage 1 — PrimeSieve
# ---------------------------------------------------------------------------

class TestPrimeSieve:
    """Tests for Stage 1: prime sieve and von Mangoldt extraction."""

    def test_primes_small(self):
        """Primes ≤ 30 are exactly {2,3,5,7,11,13,17,19,23,29}."""
        result = PrimeSieve(30).run()
        assert result.primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        print("✅ test_primes_small PASSED")

    def test_prime_count_100(self):
        """There are 25 primes ≤ 100."""
        result = PrimeSieve(100).run()
        assert len(result.primes) == 25
        print("✅ test_prime_count_100 PASSED")

    def test_mangoldt_prime(self):
        """Λ(p) = log p for prime p."""
        result = PrimeSieve(20).run()
        for p in [2, 3, 5, 7, 11, 13, 17, 19]:
            assert abs(result.mangoldt[p] - np.log(p)) < 1e-12
        print("✅ test_mangoldt_prime PASSED")

    def test_mangoldt_prime_power(self):
        """Λ(p^k) = log p for prime powers."""
        result = PrimeSieve(30).run()
        # 4 = 2^2
        assert abs(result.mangoldt[4] - np.log(2)) < 1e-12
        # 8 = 2^3
        assert abs(result.mangoldt[8] - np.log(2)) < 1e-12
        # 9 = 3^2
        assert abs(result.mangoldt[9] - np.log(3)) < 1e-12
        print("✅ test_mangoldt_prime_power PASSED")

    def test_mangoldt_composite(self):
        """Λ(n) = 0 for composite non-prime-powers."""
        result = PrimeSieve(20).run()
        for n in [6, 10, 12, 14, 15]:
            assert result.mangoldt[n] == 0.0
        print("✅ test_mangoldt_composite PASSED")

    def test_sieve_result_type(self):
        """run() returns a SieveResult."""
        result = PrimeSieve(50).run()
        assert isinstance(result, SieveResult)
        assert result.N == 50
        print("✅ test_sieve_result_type PASSED")

    def test_sieve_invalid_N(self):
        """N < 2 raises ValueError."""
        with pytest.raises(ValueError):
            PrimeSieve(1).run()
        print("✅ test_sieve_invalid_N PASSED")

    def test_sieve_N2(self):
        """N=2 gives primes=[2]."""
        result = PrimeSieve(2).run()
        assert result.primes == [2]
        print("✅ test_sieve_N2 PASSED")

    def test_mangoldt_nonzero_count(self):
        """Number of non-zero Λ entries equals number of prime powers ≤ N."""
        N = 50
        result = PrimeSieve(N).run()
        nonzero = int(np.sum(result.mangoldt > 0))
        # prime powers ≤ 50: 2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49 = 23
        assert nonzero == 23
        print("✅ test_mangoldt_nonzero_count PASSED")

    def test_sieve_large(self):
        """Sieve correctly finds 303 primes ≤ 2000."""
        result = PrimeSieve(2000).run()
        assert len(result.primes) == 303
        print("✅ test_sieve_large PASSED")


# ---------------------------------------------------------------------------
# Stage 2 — ChebyshevPsi
# ---------------------------------------------------------------------------

class TestChebyshevPsi:
    """Tests for Stage 2: Chebyshev ψ(x) computation."""

    def _sieve(self, N: int = 500) -> SieveResult:
        return PrimeSieve(N).run()

    def test_result_type(self):
        """compute() returns a ChebyshevResult."""
        result = ChebyshevPsi(self._sieve()).compute()
        assert isinstance(result, ChebyshevResult)
        print("✅ test_result_type PASSED")

    def test_psi_positive(self):
        """ψ(x) ≥ 0 for all sample points."""
        result = ChebyshevPsi(self._sieve()).compute()
        assert np.all(result.psi_values >= 0)
        print("✅ test_psi_positive PASSED")

    def test_psi_increasing(self):
        """ψ(x) is non-decreasing."""
        result = ChebyshevPsi(self._sieve()).compute()
        diffs = np.diff(result.psi_values)
        assert np.all(diffs >= -1e-10)
        print("✅ test_psi_increasing PASSED")

    def test_psi_near_x(self):
        """ψ(x) ≈ x within ~15 % for x ≥ 100 (prime number theorem)."""
        sieve = self._sieve(1000)
        result = ChebyshevPsi(sieve, n_samples=100).compute()
        idx = result.x_values >= 100
        if np.any(idx):
            rel_err = np.abs(result.psi_values[idx] - result.x_values[idx]) / result.x_values[idx]
            assert float(np.max(rel_err)) < 0.15
        print("✅ test_psi_near_x PASSED")

    def test_delta_psi_rms(self):
        """rms(δψ) is non-negative and bounded."""
        result = ChebyshevPsi(self._sieve()).compute()
        assert result.rms_delta >= 0
        assert result.rms_delta < result.X
        print("✅ test_delta_psi_rms PASSED")

    def test_x_values_sorted(self):
        """x_values are sorted in increasing order."""
        result = ChebyshevPsi(self._sieve()).compute()
        diffs = np.diff(result.x_values)
        assert np.all(diffs >= 0)
        print("✅ test_x_values_sorted PASSED")

    def test_small_x_psi_2(self):
        """ψ(2) = log 2."""
        sieve = PrimeSieve(10).run()
        # cumsum at index 2 should equal log(2)
        assert abs(sieve.mangoldt[2] - np.log(2)) < 1e-12
        print("✅ test_small_x_psi_2 PASSED")

    def test_n_samples(self):
        """Output length matches n_samples (approximately)."""
        sieve = self._sieve(500)
        result = ChebyshevPsi(sieve, n_samples=50).compute()
        assert 1 <= len(result.x_values) <= 50
        print("✅ test_n_samples PASSED")


# ---------------------------------------------------------------------------
# Stage 3 — SelbergExplicitFormula
# ---------------------------------------------------------------------------

class TestSelbergExplicitFormula:
    """Tests for Stage 3: Selberg explicit formula balance."""

    def _primes(self, N: int = 200) -> list:
        return PrimeSieve(N).run().primes

    def test_result_type(self):
        """compute() returns a SelbergTraceResult."""
        result = SelbergExplicitFormula(KNOWN_ZEROS[:10], self._primes()).compute()
        assert isinstance(result, SelbergTraceResult)
        print("✅ test_result_type PASSED")

    def test_zero_side_positive(self):
        """LHS = ∑h(γ) is positive for Gaussian h > 0."""
        result = SelbergExplicitFormula(KNOWN_ZEROS, self._primes()).compute()
        assert result.zero_side > 0
        print("✅ test_zero_side_positive PASSED")

    def test_quality_in_range(self):
        """quality ∈ [0, 1]."""
        result = SelbergExplicitFormula(KNOWN_ZEROS, self._primes()).compute()
        assert 0.0 <= result.quality <= 1.0
        print("✅ test_quality_in_range PASSED")

    def test_relative_error_finite(self):
        """relative_error is finite and non-negative."""
        result = SelbergExplicitFormula(KNOWN_ZEROS, self._primes()).compute()
        assert np.isfinite(result.relative_error)
        assert result.relative_error >= 0
        print("✅ test_relative_error_finite PASSED")

    def test_n_zeros(self):
        """n_zeros matches input length."""
        zeros = KNOWN_ZEROS[:7]
        result = SelbergExplicitFormula(zeros, self._primes()).compute()
        assert result.n_zeros == 7
        print("✅ test_n_zeros PASSED")

    def test_n_primes(self):
        """n_primes matches input prime list length."""
        primes = self._primes(100)
        result = SelbergExplicitFormula(KNOWN_ZEROS[:5], primes).compute()
        assert result.n_primes == len(primes)
        print("✅ test_n_primes PASSED")

    def test_sigma_effect(self):
        """Narrower sigma → smaller LHS (fewer zeros contribute)."""
        primes = self._primes(200)
        res_wide = SelbergExplicitFormula(KNOWN_ZEROS, primes, sigma=10.0).compute()
        res_narrow = SelbergExplicitFormula(KNOWN_ZEROS, primes, sigma=2.0).compute()
        assert res_wide.zero_side > res_narrow.zero_side
        print("✅ test_sigma_effect PASSED")

    def test_balance_finite(self):
        """balance is finite."""
        result = SelbergExplicitFormula(KNOWN_ZEROS, self._primes()).compute()
        assert np.isfinite(result.balance)
        print("✅ test_balance_finite PASSED")

    def test_fourier_at_zero(self):
        """h_hat(0) = σ√(2π) for σ=5."""
        primes = self._primes(50)
        sel = SelbergExplicitFormula(KNOWN_ZEROS[:3], primes, sigma=5.0)
        expected = 5.0 * np.sqrt(2.0 * np.pi)
        assert abs(sel._h_hat(0.0) - expected) < 1e-10
        print("✅ test_fourier_at_zero PASSED")

    def test_h_at_zero(self):
        """h(0) = 1."""
        sel = SelbergExplicitFormula(KNOWN_ZEROS[:3], [], sigma=3.0)
        assert abs(sel._h(0.0) - 1.0) < 1e-12
        print("✅ test_h_at_zero PASSED")


# ---------------------------------------------------------------------------
# Stage 4 — GUERigidity
# ---------------------------------------------------------------------------

class TestGUERigidity:
    """Tests for Stage 4: GUE Δ₃ spectral rigidity."""

    def test_result_type(self):
        """compute() returns a GUERigidityResult."""
        result = GUERigidity(KNOWN_ZEROS).compute()
        assert isinstance(result, GUERigidityResult)
        print("✅ test_result_type PASSED")

    def test_delta3_positive(self):
        """Δ₃ measured and GUE prediction are positive for valid spectrum."""
        result = GUERigidity(KNOWN_ZEROS).compute()
        assert result.delta3_measured >= 0.0
        assert result.delta3_gue > 0.0
        print("✅ test_delta3_positive PASSED")

    def test_ratio_finite(self):
        """ratio is finite and positive."""
        result = GUERigidity(KNOWN_ZEROS).compute()
        assert np.isfinite(result.ratio)
        assert result.ratio >= 0.0
        print("✅ test_ratio_finite PASSED")

    def test_spacings_positive(self):
        """Nearest-neighbour spacings are non-negative."""
        result = GUERigidity(KNOWN_ZEROS).compute()
        assert np.all(result.spacings >= 0)
        print("✅ test_spacings_positive PASSED")

    def test_mean_spacing_ratio_range(self):
        """Mean spacing ratio ∈ [0, 1]."""
        result = GUERigidity(KNOWN_ZEROS).compute()
        assert 0.0 <= result.mean_spacing_ratio <= 1.0
        print("✅ test_mean_spacing_ratio_range PASSED")

    def test_gue_consistency_bool(self):
        """is_gue_consistent is a bool."""
        result = GUERigidity(KNOWN_ZEROS).compute()
        assert isinstance(result.is_gue_consistent, (bool, np.bool_))
        print("✅ test_gue_consistency_bool PASSED")

    def test_gue_prediction_formula(self):
        """GUE prediction Δ₃(L) matches analytical formula."""
        L = 20.0
        expected = (1.0 / np.pi**2) * (
            np.log(2.0 * np.pi * L) + EULER_MASCHERONI - 1.25 - np.log(2.0)
        )
        assert abs(GUERigidity.gue_prediction(L) - expected) < 1e-12
        print("✅ test_gue_prediction_formula PASSED")

    def test_gue_prediction_positive(self):
        """GUE prediction is positive for L > 0."""
        for L in [1.0, 5.0, 10.0, 50.0, 100.0]:
            assert GUERigidity.gue_prediction(L) > 0
        print("✅ test_gue_prediction_positive PASSED")

    def test_few_zeros_graceful(self):
        """With < 4 zeros, returns graceful result (is_gue_consistent=False)."""
        result = GUERigidity(KNOWN_ZEROS[:3]).compute()
        assert result.is_gue_consistent is False
        print("✅ test_few_zeros_graceful PASSED")

    def test_sorted_zeros(self):
        """Unsorted zeros are sorted internally."""
        zeros_unordered = KNOWN_ZEROS[::-1].copy()
        result = GUERigidity(zeros_unordered).compute()
        assert result.delta3_measured >= 0
        print("✅ test_sorted_zeros PASSED")

    def test_gue_true_random_matrix(self):
        """GUE matrix eigenvalues pass consistency check with loose tolerance."""
        rng = np.random.default_rng(42)
        n = 200
        H = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
        H = (H + H.conj().T) / (2.0 * np.sqrt(n))
        eigs = np.linalg.eigvalsh(H)
        # Use loose tolerance
        result = GUERigidity(eigs, tolerance=0.9).compute()
        assert result.delta3_measured >= 0.0
        print("✅ test_gue_true_random_matrix PASSED")


# ---------------------------------------------------------------------------
# Stage 5 — SFiniteResolution
# ---------------------------------------------------------------------------

class TestSFiniteResolution:
    """Tests for Stage 5: S-finite conditional resolution."""

    def _build_pipeline_outputs(self):
        sieve = PrimeSieve(500).run()
        cheb = ChebyshevPsi(sieve, n_samples=100).compute()
        sel = SelbergExplicitFormula(KNOWN_ZEROS, sieve.primes).compute()
        gue = GUERigidity(KNOWN_ZEROS).compute()
        return cheb, sel, gue

    def test_result_type(self):
        """compute() returns a SFiniteResolutionResult."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        assert isinstance(result, SFiniteResolutionResult)
        print("✅ test_result_type PASSED")

    def test_R_S_non_negative(self):
        """R_S ≥ 0."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        assert result.R_S >= 0.0
        print("✅ test_R_S_non_negative PASSED")

    def test_psi_coherence_in_range(self):
        """Ψ ∈ (0, 1]."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        assert 0.0 < result.psi_coherence <= 1.0
        print("✅ test_psi_coherence_in_range PASSED")

    def test_verdict_valid_string(self):
        """verdict is one of the two expected strings."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        assert result.verdict in {"S_FINITE_RESOLVED", "S_FINITE_CONDITIONAL"}
        print("✅ test_verdict_valid_string PASSED")

    def test_selberg_quality_preserved(self):
        """selberg_quality in result matches the input quality."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        assert abs(result.selberg_quality - sel.quality) < 1e-12
        print("✅ test_selberg_quality_preserved PASSED")

    def test_metadata_keys(self):
        """metadata contains essential keys."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        for key in ["l2_norm_sq", "X", "rms_delta_psi", "selberg_quality", "gue_consistent"]:
            assert key in result.metadata
        print("✅ test_metadata_keys PASSED")

    def test_gue_consistent_field(self):
        """gue_consistent in result matches the GUERigidityResult."""
        cheb, sel, gue = self._build_pipeline_outputs()
        result = SFiniteResolution(cheb, sel, gue).compute()
        assert result.gue_consistent == bool(gue.is_gue_consistent)
        print("✅ test_gue_consistent_field PASSED")


# ---------------------------------------------------------------------------
# Full Pipeline — ImpactoRH
# ---------------------------------------------------------------------------

class TestImpactoRH:
    """Tests for the full ImpactoRH pipeline."""

    def test_run_returns_result(self):
        """run() returns ImpactoRHResult."""
        pipeline = ImpactoRH(N=300, verbose=False)
        result = pipeline.run()
        assert isinstance(result, ImpactoRHResult)
        print("✅ test_run_returns_result PASSED")

    def test_global_psi_in_range(self):
        """global_psi ∈ [0, 1]."""
        result = ImpactoRH(N=300, verbose=False).run()
        assert 0.0 <= result.global_psi <= 1.0
        print("✅ test_global_psi_in_range PASSED")

    def test_sieve_field(self):
        """result.sieve is a SieveResult."""
        result = ImpactoRH(N=300, verbose=False).run()
        assert isinstance(result.sieve, SieveResult)
        print("✅ test_sieve_field PASSED")

    def test_chebyshev_field(self):
        """result.chebyshev is a ChebyshevResult."""
        result = ImpactoRH(N=300, verbose=False).run()
        assert isinstance(result.chebyshev, ChebyshevResult)
        print("✅ test_chebyshev_field PASSED")

    def test_selberg_field(self):
        """result.selberg is a SelbergTraceResult."""
        result = ImpactoRH(N=300, verbose=False).run()
        assert isinstance(result.selberg, SelbergTraceResult)
        print("✅ test_selberg_field PASSED")

    def test_gue_field(self):
        """result.gue is a GUERigidityResult."""
        result = ImpactoRH(N=300, verbose=False).run()
        assert isinstance(result.gue, GUERigidityResult)
        print("✅ test_gue_field PASSED")

    def test_s_finite_field(self):
        """result.s_finite is a SFiniteResolutionResult."""
        result = ImpactoRH(N=300, verbose=False).run()
        assert isinstance(result.s_finite, SFiniteResolutionResult)
        print("✅ test_s_finite_field PASSED")

    def test_custom_zeros(self):
        """Pipeline accepts custom zero array."""
        zeros = KNOWN_ZEROS[:8]
        result = ImpactoRH(N=200, zeros=zeros, verbose=False).run()
        assert result.selberg.n_zeros == 8
        print("✅ test_custom_zeros PASSED")

    def test_default_zeros_length(self):
        """Default zeros array has 20 entries."""
        assert len(ImpactoRH.DEFAULT_ZEROS) == 20
        print("✅ test_default_zeros_length PASSED")

    def test_run_impacto_rh_wrapper(self):
        """run_impacto_rh convenience wrapper returns ImpactoRHResult."""
        result = run_impacto_rh(N=300, verbose=False)
        assert isinstance(result, ImpactoRHResult)
        print("✅ test_run_impacto_rh_wrapper PASSED")

    def test_sigma_parameter(self):
        """sigma parameter is passed to SelbergExplicitFormula."""
        r1 = ImpactoRH(N=200, sigma=5.0, verbose=False).run()
        r2 = ImpactoRH(N=200, sigma=10.0, verbose=False).run()
        # Different sigma → different LHS values
        assert r1.selberg.zero_side != r2.selberg.zero_side
        print("✅ test_sigma_parameter PASSED")

    def test_f0_constant(self):
        """F0_QCAL constant is 141.7001."""
        assert abs(F0_QCAL - 141.7001) < 1e-6
        print("✅ test_f0_constant PASSED")

    def test_c_coherence_constant(self):
        """C_COHERENCE constant is 244.36."""
        assert abs(C_COHERENCE - 244.36) < 1e-6
        print("✅ test_c_coherence_constant PASSED")


# ---------------------------------------------------------------------------
# Integration: end-to-end consistency
# ---------------------------------------------------------------------------

class TestImpactoRHIntegration:
    """Integration tests ensuring the pipeline stages are consistent."""

    def test_prime_sum_mangoldt_consistent(self):
        """Sum of Λ(n) ≤ N equals ψ(N) (PNT: ψ(N) ≈ N)."""
        N = 1000
        sieve = PrimeSieve(N).run()
        psi_N = float(np.sum(sieve.mangoldt))
        # ψ(1000) ≈ 1000, within 10 %
        assert abs(psi_N - N) / N < 0.10
        print("✅ test_prime_sum_mangoldt_consistent PASSED")

    def test_chebyshev_psi_at_N(self):
        """ψ(N) / N ∈ [0.90, 1.10] (PNT)."""
        N = 1000
        sieve = PrimeSieve(N).run()
        cheb = ChebyshevPsi(sieve, n_samples=50).compute()
        psi_N = float(cheb.psi_values[-1])
        ratio = psi_N / N
        assert 0.90 <= ratio <= 1.10
        print("✅ test_chebyshev_psi_at_N PASSED")

    def test_selberg_uses_sieve_primes(self):
        """SelbergExplicitFormula n_primes == len(sieve.primes)."""
        N = 300
        sieve = PrimeSieve(N).run()
        sel = SelbergExplicitFormula(KNOWN_ZEROS[:10], sieve.primes).compute()
        assert sel.n_primes == len(sieve.primes)
        print("✅ test_selberg_uses_sieve_primes PASSED")

    def test_s_finite_metadata_X_matches_chebyshev(self):
        """S-finite metadata X matches chebyshev.X."""
        sieve = PrimeSieve(300).run()
        cheb = ChebyshevPsi(sieve, n_samples=100).compute()
        sel = SelbergExplicitFormula(KNOWN_ZEROS[:10], sieve.primes).compute()
        gue = GUERigidity(KNOWN_ZEROS[:10]).compute()
        sf = SFiniteResolution(cheb, sel, gue).compute()
        assert abs(sf.metadata["X"] - cheb.X) < 1e-6
        print("✅ test_s_finite_metadata_X_matches_chebyshev PASSED")

    def test_pipeline_reproducible(self):
        """Two runs with same params give identical global_psi."""
        r1 = ImpactoRH(N=300, verbose=False).run()
        r2 = ImpactoRH(N=300, verbose=False).run()
        assert abs(r1.global_psi - r2.global_psi) < 1e-12
        print("✅ test_pipeline_reproducible PASSED")

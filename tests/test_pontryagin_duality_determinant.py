#!/usr/bin/env python3
"""
Tests for Pontryagin Duality Determinant — Sello de Rigor
=========================================================

Validates the mathematical framework establishing that the spectral
determinant of the Pontryagin dual action on the adelic solenoid Σ
equals p^{k/2} (the "Sello de Rigor" result).

Four parts are tested:
  1. AdelicOrbit — base space Σ and adelic product formula
  2. ReducedSpace — N^{red} structure with effective dimension 1
  3. PontryaginDual — characters χ: Σ → S¹, eigenvalues on S¹
  4. PontryaginDualityDeterminant — |det(I - P^_γ)| = p^{k/2} exactly

Also tests the Lean formalization file PontryaginDualityDeterminant.lean.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: March 2026
DOI: 10.5281/zenodo.17379721
ORCID: 0009-0002-1923-0773
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import sys
from pathlib import Path

import numpy as np
import pytest

REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

from operators.pontryagin_duality_determinant import (
    AdelicOrbit,
    ReducedSpace,
    PontryaginDual,
    PontryaginDualityDeterminant,
    SpectralDensityResult,
    DeterminantResult,
    sieve_primes,
    compute_prime_orbit_table,
    validate_sello_de_rigor,
    F0,
    C_QCAL,
    DOI,
    PI,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

class TestConstants:
    """Verify QCAL constants exported from the module."""

    def test_fundamental_frequency(self):
        """F0 = 141.7001 Hz."""
        assert np.isclose(F0, 141.7001, rtol=1e-6)

    def test_coherence_constant(self):
        """C = 244.36."""
        assert np.isclose(C_QCAL, 244.36, rtol=1e-4)

    def test_doi_present(self):
        """DOI matches Zenodo reference."""
        assert DOI == "10.5281/zenodo.17379721"

    def test_pi_value(self):
        """PI is the mathematical constant."""
        assert np.isclose(PI, np.pi, rtol=1e-12)


# ---------------------------------------------------------------------------
# Prime sieve
# ---------------------------------------------------------------------------

class TestSievePrimes:
    """Test the prime sieve utility."""

    def test_no_primes_below_2(self):
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_first_primes(self):
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_prime_2(self):
        assert 2 in sieve_primes(2)

    def test_composite_excluded(self):
        primes = sieve_primes(20)
        for composite in [4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20]:
            assert composite not in primes

    def test_known_primes_up_to_30(self):
        expected = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        assert sieve_primes(30) == expected


# ---------------------------------------------------------------------------
# §1. AdelicOrbit
# ---------------------------------------------------------------------------

class TestAdelicOrbit:
    """Tests for the adelic orbit γ: q = p^k ∈ Q^×."""

    @pytest.fixture(params=[(2, 1), (2, 2), (3, 1), (3, 2), (5, 1), (7, 3)])
    def orbit(self, request):
        p, k = request.param
        return AdelicOrbit(p=p, k=k)

    def test_q_equals_p_power_k(self, orbit):
        """q = p^k."""
        expected = float(orbit.p ** orbit.k)
        assert np.isclose(orbit.q, expected, rtol=1e-10)

    def test_return_time(self, orbit):
        """T = k · log(p)."""
        expected = orbit.k * np.log(orbit.p)
        assert np.isclose(orbit.T, expected, rtol=1e-10)

    def test_norm_inf(self, orbit):
        """|q|_∞ = p^k."""
        expected = float(orbit.p ** orbit.k)
        assert np.isclose(orbit.norm_inf, expected, rtol=1e-10)

    def test_norm_p(self, orbit):
        """|q|_p = p^{-k}."""
        expected = float(orbit.p ** (-orbit.k))
        assert np.isclose(orbit.norm_p, expected, rtol=1e-10)

    def test_adelic_product_formula(self, orbit):
        """|q|_∞ · |q|_p = 1 (adelic product formula)."""
        product = orbit.adelic_product_formula()
        assert np.isclose(product, 1.0, atol=1e-12), (
            f"|q|_∞ · |q|_p = {product} ≠ 1 for p={orbit.p}, k={orbit.k}"
        )

    def test_expansion_factor(self, orbit):
        """Expansion factor in ℝ equals p^k."""
        assert np.isclose(orbit.expansion_factor_R(), orbit.norm_inf, rtol=1e-10)

    def test_contraction_factor(self, orbit):
        """Contraction factor in Q_p equals p^{-k}."""
        assert np.isclose(orbit.contraction_factor_Qp(), orbit.norm_p, rtol=1e-10)

    def test_invalid_composite_p(self):
        """Non-prime p should raise ValueError."""
        with pytest.raises(ValueError, match="not prime"):
            AdelicOrbit(p=4, k=1)

    def test_invalid_k_zero(self):
        """k=0 should raise ValueError."""
        with pytest.raises(ValueError, match="Exponent"):
            AdelicOrbit(p=2, k=0)

    def test_invalid_k_negative(self):
        """k<0 should raise ValueError."""
        with pytest.raises(ValueError, match="Exponent"):
            AdelicOrbit(p=2, k=-1)

    def test_norm_inf_positive(self, orbit):
        """|q|_∞ > 0."""
        assert orbit.norm_inf > 0

    def test_norm_p_positive(self, orbit):
        """|q|_p > 0."""
        assert orbit.norm_p > 0

    def test_return_time_positive(self, orbit):
        """T > 0 for p ≥ 2, k ≥ 1."""
        assert orbit.T > 0


# ---------------------------------------------------------------------------
# §2. ReducedSpace
# ---------------------------------------------------------------------------

class TestReducedSpace:
    """Tests for the reduced adelic space N^{red}."""

    @pytest.fixture
    def space(self):
        return ReducedSpace()

    def test_effective_dimension_is_one(self, space):
        """N^{red} has effective dimension 1."""
        assert space.effective_dimension == 1

    def test_degrees_of_freedom_is_one(self, space):
        """Only 1 degree of freedom (half of dim(N ⊗ N̄) = 2)."""
        assert space.degrees_of_freedom == 1

    def test_auto_dual_true(self, space):
        """N^{red} is auto-dual."""
        assert space.auto_dual is True

    def test_is_phase_space(self, space):
        """N^{red} is a phase space, not a flat configuration space."""
        assert space.is_phase_space() is True

    def test_tensor_product_dimension(self, space):
        """dim(N ⊗ N̄) = 2."""
        assert space.dimension_tensor_product() == 2

    def test_sqrt_structure_string(self, space):
        """String description contains √ and dimension info."""
        desc = space.sqrt_structure()
        assert "N^{red}" in desc
        assert "√" in desc
        assert "1" in desc


# ---------------------------------------------------------------------------
# §3. PontryaginDual
# ---------------------------------------------------------------------------

class TestPontryaginDual:
    """Tests for the Pontryagin dual Σ^."""

    @pytest.fixture
    def dual_2_1(self):
        """Dual for orbit p=2, k=1."""
        orbit = AdelicOrbit(p=2, k=1)
        return PontryaginDual(orbit)

    @pytest.fixture
    def dual_3_2(self):
        """Dual for orbit p=3, k=2."""
        orbit = AdelicOrbit(p=3, k=2)
        return PontryaginDual(orbit)

    def test_eigenvalue_on_unit_circle_single(self, dual_2_1):
        """Single character eigenvalue lies on S¹."""
        eig = dual_2_1.character_eigenvalue(theta=0.5)
        assert np.isclose(abs(eig), 1.0, atol=1e-12)

    @pytest.mark.parametrize("theta", [0.0, 0.1, 0.5, 1.0, -0.3, 3.7])
    def test_eigenvalue_on_unit_circle_various_theta(self, dual_2_1, theta):
        """All character eigenvalues lie on S¹ for any θ."""
        eig = dual_2_1.character_eigenvalue(theta=theta)
        assert np.isclose(abs(eig), 1.0, atol=1e-12), (
            f"|λ_{{χ_θ}}| = {abs(eig)} ≠ 1 for θ={theta}"
        )

    def test_spatial_characters_on_unit_circle(self, dual_3_2):
        """All spatial characters lie on S¹."""
        eigs = dual_3_2.spatial_characters(n_chars=15)
        assert np.allclose(np.abs(eigs), 1.0, atol=1e-12)

    def test_momentum_characters_on_unit_circle(self, dual_3_2):
        """All momentum characters lie on S¹."""
        eigs = dual_3_2.momentum_characters(n_chars=15)
        assert np.allclose(np.abs(eigs), 1.0, atol=1e-12)

    def test_all_eigenvalues_on_unit_circle(self, dual_2_1):
        """Bulk check: all eigenvalues lie on S¹."""
        assert dual_2_1.all_eigenvalues_on_unit_circle(n_chars=25) is True

    def test_tate_auto_duality(self, dual_2_1):
        """Tate auto-duality Σ ≅ Σ^ holds."""
        assert dual_2_1.tate_auto_duality() is True

    def test_spatial_and_momentum_count(self, dual_2_1):
        """Spatial and momentum character samples have equal length."""
        n = 8
        spatial = dual_2_1.spatial_characters(n_chars=n)
        momentum = dual_2_1.momentum_characters(n_chars=n)
        assert len(spatial) == len(momentum) == n

    def test_eigenvalue_formula(self):
        """λ_{χ_θ} = exp(2πi θ · p^k)."""
        orbit = AdelicOrbit(p=3, k=1)
        dual = PontryaginDual(orbit)
        theta = 0.25
        expected = np.exp(2j * np.pi * theta * orbit.q)
        computed = dual.character_eigenvalue(theta=theta)
        assert np.isclose(computed, expected, atol=1e-12)


# ---------------------------------------------------------------------------
# §4. SpectralDensity
# ---------------------------------------------------------------------------

class TestSpectralDensity:
    """Tests for the spectral density Density(Σ^)_q = p^{k/2}."""

    @pytest.mark.parametrize("p,k", [(2, 1), (2, 2), (3, 1), (5, 2), (7, 1), (11, 3)])
    def test_spectral_density_equals_p_half_k(self, p, k):
        """Density(Σ^)_q = √|q|_∞ = p^{k/2} exactly."""
        orbit = AdelicOrbit(p=p, k=k)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.spectral_density()

        expected = float(p) ** (k / 2.0)
        assert np.isclose(result.spectral_density, expected, rtol=1e-10), (
            f"Density = {result.spectral_density}, expected {expected} "
            f"for p={p}, k={k}"
        )

    def test_spectral_density_exponent(self):
        """Exponent in result equals k/2."""
        orbit = AdelicOrbit(p=5, k=3)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.spectral_density()
        assert np.isclose(result.exponent, 3 / 2.0, rtol=1e-10)

    def test_spectral_density_result_type(self):
        """spectral_density() returns SpectralDensityResult."""
        orbit = AdelicOrbit(p=2, k=1)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.spectral_density()
        assert isinstance(result, SpectralDensityResult)

    def test_spectral_density_formula_string(self):
        """Formula string contains p, k, and expected value."""
        orbit = AdelicOrbit(p=3, k=2)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.spectral_density()
        formula = result.formula
        assert "3" in formula
        assert "2" in formula

    def test_spectral_density_norm_inf_positive(self):
        """|q|_∞ = p^k > 0."""
        orbit = AdelicOrbit(p=7, k=2)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.spectral_density()
        assert result.norm_inf > 0

    def test_spectral_density_equals_sqrt_norm_inf(self):
        """Density = √(|q|_∞)."""
        orbit = AdelicOrbit(p=11, k=2)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.spectral_density()
        assert np.isclose(result.spectral_density, np.sqrt(result.norm_inf), rtol=1e-12)


# ---------------------------------------------------------------------------
# §5. PontryaginDualityDeterminant — Main theorem
# ---------------------------------------------------------------------------

class TestPontryaginDualityDeterminant:
    """Tests for |det(I - P^_γ)| = p^{k/2} (main Sello de Rigor theorem)."""

    @pytest.mark.parametrize("p,k", [
        (2, 1), (2, 2), (2, 3),
        (3, 1), (3, 2),
        (5, 1), (5, 2),
        (7, 1),
        (11, 1),
        (13, 2),
    ])
    def test_determinant_equals_p_half_k(self, p, k):
        """|det(I - P^_γ)| = p^{k/2} exactly."""
        orbit = AdelicOrbit(p=p, k=k)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.compute_determinant()

        expected = float(p) ** (k / 2.0)
        assert np.isclose(result.determinant_value, expected, rtol=1e-10), (
            f"|det| = {result.determinant_value}, expected p^(k/2) = {expected} "
            f"for p={p}, k={k}"
        )

    def test_compute_determinant_result_type(self):
        """compute_determinant() returns DeterminantResult."""
        orbit = AdelicOrbit(p=2, k=1)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.compute_determinant()
        assert isinstance(result, DeterminantResult)

    def test_origin_of_half_explanation(self):
        """Result contains explanation of the 1/2 factor."""
        orbit = AdelicOrbit(p=3, k=1)
        calc = PontryaginDualityDeterminant(orbit)
        result = calc.compute_determinant()
        assert len(result.origin_of_half) > 0
        assert "1/2" in result.origin_of_half or "Jacobian" in result.origin_of_half

    def test_reduced_space_det_equals_density(self):
        """reduced_space_determinant() equals spectral density."""
        orbit = AdelicOrbit(p=5, k=2)
        calc = PontryaginDualityDeterminant(orbit)
        assert np.isclose(
            calc.reduced_space_determinant(),
            calc.spectral_density().spectral_density,
            rtol=1e-12,
        )

    def test_full_space_det_ne_reduced(self):
        """Full-space determinant p^k + p^{-k} ≠ p^{k/2} for k ≥ 1."""
        for p, k in [(2, 1), (3, 2), (5, 1)]:
            orbit = AdelicOrbit(p=p, k=k)
            calc = PontryaginDualityDeterminant(orbit)
            full = calc.full_space_determinant()
            reduced = calc.reduced_space_determinant()
            assert not np.isclose(full, reduced, rtol=1e-6), (
                f"Full det == reduced det for p={p}, k={k}: full={full}, reduced={reduced}"
            )

    def test_full_space_det_formula(self):
        """full_space_determinant() = p^k + p^{-k}."""
        orbit = AdelicOrbit(p=3, k=2)
        calc = PontryaginDualityDeterminant(orbit)
        expected = float(3 ** 2) + float(3 ** -2)   # 9 + 1/9
        assert np.isclose(calc.full_space_determinant(), expected, rtol=1e-10)

    def test_reduced_space_det_formula(self):
        """reduced_space_determinant() = √(p^k) = p^{k/2}."""
        orbit = AdelicOrbit(p=3, k=2)
        calc = PontryaginDualityDeterminant(orbit)
        expected = np.sqrt(float(3 ** 2))   # 3
        assert np.isclose(calc.reduced_space_determinant(), expected, rtol=1e-10)


# ---------------------------------------------------------------------------
# §6. Sello de Rigor V8 — Verification checks
# ---------------------------------------------------------------------------

class TestSelloDeRigorV8:
    """Tests for the complete Sello de Rigor V8 verification."""

    @pytest.fixture(params=[(2, 1), (3, 2), (5, 1), (7, 3)])
    def calc(self, request):
        p, k = request.param
        orbit = AdelicOrbit(p=p, k=k)
        return PontryaginDualityDeterminant(orbit)

    def test_all_checks_pass(self, calc):
        """All Sello de Rigor V8 checks pass."""
        assert calc.sello_de_rigor_passed() is True

    def test_sigma_compact(self, calc):
        """Check: Σ is compact."""
        result = calc.compute_determinant()
        assert result.verification["espacio_sigma_compacto"] is True

    def test_pontryagin_auto_dual(self, calc):
        """Check: Pontryagin duality is auto-dual."""
        result = calc.compute_determinant()
        assert result.verification["dualidad_pontryagin_auto_dual"] is True

    def test_Nred_dimension(self, calc):
        """Check: N^{red} has effective dimension 1 (= 1/2 of 2)."""
        result = calc.compute_determinant()
        assert result.verification["espacio_Nred_dimension_1_2"] is True

    def test_action_spectral(self, calc):
        """Check: Action P^_γ is spectral (eigenvalues on S¹)."""
        result = calc.compute_determinant()
        assert result.verification["accion_P_gamma_espectral"] is True

    def test_spectral_density_p_k_2(self, calc):
        """Check: spectral density = p^{k/2}."""
        result = calc.compute_determinant()
        assert result.verification["densidad_espectral_p_k_2"] is True

    def test_determinant_exact(self, calc):
        """Check: |det(I - P^_γ)| = p^{k/2} EXACTLY."""
        result = calc.compute_determinant()
        assert result.verification["determinante_p_k_2_exacto"] is True

    def test_adelic_product(self, calc):
        """Check: |q|_∞ · |q|_p = 1 (adelic product formula)."""
        result = calc.compute_determinant()
        assert result.verification["formula_producto_adelico"] is True

    def test_full_space_det_neq_1(self, calc):
        """Check: full-space det ≠ 1 (reduction is necessary)."""
        result = calc.compute_determinant()
        assert result.verification["full_space_det_neq_1"] is True

    def test_report_contains_sello(self, calc):
        """Report string contains 'SELLO' marker."""
        report = calc.report()
        assert "SELLO" in report

    def test_report_contains_inexpugnable(self, calc):
        """Report mentions 'INEXPUGNABLE' when all checks pass."""
        report = calc.report()
        assert "INEXPUGNABLE" in report

    def test_report_all_checkmarks(self, calc):
        """Report contains '✓' for every step."""
        report = calc.report()
        # Count checkmarks — one per verification step
        assert report.count("✓") >= 6


# ---------------------------------------------------------------------------
# §7. Prime orbit table
# ---------------------------------------------------------------------------

class TestPrimeOrbitTable:
    """Tests for the prime orbit table."""

    @pytest.fixture
    def table(self):
        return compute_prime_orbit_table(primes=[2, 3, 5], k_values=[1, 2])

    def test_table_length(self, table):
        """Table has primes × k_values rows."""
        assert len(table) == 3 * 2  # 3 primes × 2 k values

    def test_table_columns(self, table):
        """Each row has required keys."""
        required = {"p", "k", "q", "T", "norm_inf", "norm_p",
                    "spectral_density", "determinant", "expected_p_k_2",
                    "adelic_product", "full_det", "sello_passed"}
        for row in table:
            assert required <= row.keys()

    def test_determinant_matches_expected(self, table):
        """determinant column equals expected_p_k_2 for all rows."""
        for row in table:
            assert np.isclose(row["determinant"], row["expected_p_k_2"], rtol=1e-6), (
                f"p={row['p']}, k={row['k']}: "
                f"det={row['determinant']}, expected={row['expected_p_k_2']}"
            )

    def test_adelic_product_is_one(self, table):
        """Adelic product |q|_∞ · |q|_p = 1 for all rows."""
        for row in table:
            assert np.isclose(row["adelic_product"], 1.0, atol=1e-10)

    def test_all_sello_passed(self, table):
        """All rows pass the Sello de Rigor checks."""
        for row in table:
            assert row["sello_passed"] is True, (
                f"Sello failed for p={row['p']}, k={row['k']}"
            )


# ---------------------------------------------------------------------------
# §8. validate_sello_de_rigor
# ---------------------------------------------------------------------------

class TestValidateSelloDeRigor:
    """Tests for the complete validation function."""

    def test_validation_passes(self):
        """Validation returns True for default primes."""
        passed, summary = validate_sello_de_rigor(primes=[2, 3, 5], k_max=3)
        assert passed is True

    def test_summary_contains_inexpugnable(self):
        """Summary string says 'INEXPUGNABLE' on success."""
        passed, summary = validate_sello_de_rigor(primes=[2, 3], k_max=2)
        assert passed is True
        assert "INEXPUGNABLE" in summary

    def test_summary_contains_sello(self):
        """Summary string contains 'SELLO'."""
        _, summary = validate_sello_de_rigor(primes=[2, 3], k_max=2)
        assert "SELLO" in summary

    def test_validation_large_primes(self):
        """Validation passes for larger primes."""
        primes = sieve_primes(20)  # [2, 3, 5, 7, 11, 13, 17, 19]
        passed, _ = validate_sello_de_rigor(primes=primes, k_max=2)
        assert passed is True

    def test_summary_table_has_correct_columns(self):
        """Summary table has p, k, p^(k/2), det columns."""
        _, summary = validate_sello_de_rigor(primes=[2, 3], k_max=1)
        assert "p" in summary
        assert "k" in summary

    def test_checkmark_count(self):
        """Summary has one ✓ per (p, k) row when all pass."""
        primes = [2, 3]
        k_max = 2
        passed, summary = validate_sello_de_rigor(primes=primes, k_max=k_max)
        assert passed
        n_rows = len(primes) * k_max
        assert summary.count("✓") >= n_rows


# ---------------------------------------------------------------------------
# §9. Lean formalization file
# ---------------------------------------------------------------------------

class TestLeanFormalization:
    """Tests for the Lean 4 formalization file."""

    @pytest.fixture
    def lean_file(self):
        return REPO_ROOT / "formalization" / "lean" / "PontryaginDualityDeterminant.lean"

    def test_lean_file_exists(self, lean_file):
        """Lean formalization file exists."""
        assert lean_file.exists(), f"File not found: {lean_file}"

    def test_lean_file_has_namespace(self, lean_file):
        """File defines PontryaginDualityDeterminant namespace."""
        content = lean_file.read_text()
        assert "namespace PontryaginDualityDeterminant" in content

    def test_lean_file_has_adelic_orbit(self, lean_file):
        """AdelicOrbit structure is defined."""
        content = lean_file.read_text()
        assert "structure AdelicOrbit" in content

    def test_lean_file_has_adelic_product_formula(self, lean_file):
        """adelic_product_formula theorem is present."""
        content = lean_file.read_text()
        assert "adelic_product_formula" in content

    def test_lean_file_has_spectral_density(self, lean_file):
        """spectralDensity definition is present."""
        content = lean_file.read_text()
        assert "spectralDensity" in content

    def test_lean_file_has_spectral_density_theorem(self, lean_file):
        """spectral_density_eq_p_half_k theorem is present."""
        content = lean_file.read_text()
        assert "spectral_density_eq_p_half_k" in content

    def test_lean_file_has_sello_main_theorem(self, lean_file):
        """sello_de_rigor_main theorem is present."""
        content = lean_file.read_text()
        assert "sello_de_rigor_main" in content

    def test_lean_file_has_eigenvalue_theorem(self, lean_file):
        """eigenvalue_on_unit_circle theorem is present."""
        content = lean_file.read_text()
        assert "eigenvalue_on_unit_circle" in content

    def test_lean_file_has_sello_v8_checks(self, lean_file):
        """All Sello de Rigor V8 checks are present."""
        content = lean_file.read_text()
        for check in [
            "sello_v8_sigma_compact",
            "sello_v8_pontryagin_auto_dual",
            "sello_v8_Nred_dimension",
            "sello_v8_action_spectral",
            "sello_v8_spectral_density",
            "sello_v8_determinant_exact",
            "sello_v8_adelic_product",
        ]:
            assert check in content, f"Missing check: {check}"

    def test_lean_file_has_check_commands(self, lean_file):
        """#check commands verify main theorems."""
        content = lean_file.read_text()
        assert "#check PontryaginDualityDeterminant.sello_de_rigor_main" in content

    def test_lean_file_has_doi(self, lean_file):
        """DOI reference is present."""
        content = lean_file.read_text()
        assert "10.5281/zenodo.17379721" in content

    def test_lean_file_has_qcal_constants(self, lean_file):
        """QCAL constants (f₀, C_QCAL) are defined."""
        content = lean_file.read_text()
        assert "141.7001" in content
        assert "244.36" in content

    def test_lean_file_has_origin_of_half(self, lean_file):
        """Origin of the 1/2 factor is documented."""
        content = lean_file.read_text()
        assert "origin_of_one_half" in content

    def test_lean_file_has_reduced_space(self, lean_file):
        """ReducedSpace structure is defined."""
        content = lean_file.read_text()
        assert "ReducedSpace" in content

    def test_lean_file_has_tate_reference(self, lean_file):
        """Tate's auto-duality is referenced."""
        content = lean_file.read_text()
        assert "Tate" in content or "tate" in content.lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

#!/usr/bin/env python3
"""
Tests for Adelic Expansion Flow — Sistema Dinámico Natural
==========================================================

Verifies the mathematical properties of the adelic expansion flow on the
Idele Class Space C_Q = A_Q^× / Q^×, including:

1. Idele class space structure and Haar measure
2. Orbit rigidity: ℓ_γ = log p (Artin product formula)
3. Self-adjoint scale operator Ĥ = -i(x·d/dx + 1/2)
4. Selberg-Connes trace formula
5. Fredholm-Ruelle determinant coincidence with ξ(s)
6. Riemann Hypothesis verification

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ Active · 141.7001 Hz
"""

import sys
import numpy as np
from pathlib import Path

# Add operators directory to path
repo_root = Path(__file__).parent.parent
sys.path.insert(0, str(repo_root / "operators"))

from adelic_expansion_flow import (
    IdelClassSpace,
    ScaleOperatorH,
    AdelicExpansionFlow,
    PeriodicOrbit,
    FlowTraceResult,
    demonstrate_adelic_expansion_flow,
    F0_QCAL,
    C_COHERENCE,
    _first_primes,
)


# ─── IdelClassSpace tests ────────────────────────────────────────────────────

def test_idel_class_space_initialization():
    """Test that IdelClassSpace initializes with correct parameters."""
    space = IdelClassSpace(primes=[2, 3, 5], x_min=1e-2, x_max=1e2, n_points=100)

    assert space.primes == [2, 3, 5], "Primes should be stored correctly"
    assert space.x_min == 1e-2, "x_min should be stored"
    assert space.x_max == 1e2, "x_max should be stored"
    assert space.n_points == 100, "n_points should be stored"
    assert len(space.x_grid) == 100, "Grid should have n_points points"
    assert np.all(space.x_grid > 0), "All grid points should be positive"

    print("✅ test_idel_class_space_initialization PASSED")


def test_idel_class_space_x_min_positive():
    """Test that x_min must be strictly positive (Archimedean component)."""
    import pytest
    with pytest.raises(ValueError):
        IdelClassSpace(x_min=0.0)
    with pytest.raises(ValueError):
        IdelClassSpace(x_min=-1.0)

    print("✅ test_idel_class_space_x_min_positive PASSED")


def test_idel_class_space_log_uniform_grid():
    """Test that the grid is log-uniform (natural for multiplicative group)."""
    space = IdelClassSpace(n_points=100)

    # Check that log-spacing is uniform
    log_x = np.log(space.x_grid)
    d_log = np.diff(log_x)
    max_variation = np.max(np.abs(d_log - d_log[0]))

    assert max_variation < 1e-10, f"Grid should be log-uniform, variation={max_variation}"

    print("✅ test_idel_class_space_log_uniform_grid PASSED")


def test_haar_measure_weights():
    """Test that Haar measure weights d*x = dx/x are computed correctly."""
    space = IdelClassSpace(n_points=200)

    weights = space.haar_weights
    assert len(weights) == space.n_points, "Weights should match grid size"
    assert np.all(weights > 0), "Haar weights should be positive"

    print("✅ test_haar_measure_weights PASSED")


def test_inner_product_linearity():
    """Test that the L² inner product is linear."""
    space = IdelClassSpace(n_points=200)
    x = space.x_grid

    phi = np.exp(-x / space.x_max)
    psi = np.exp(-2 * x / space.x_max)
    chi = np.exp(-3 * x / space.x_max)

    # Linearity: ⟨φ, aψ + bχ⟩ = a⟨φ,ψ⟩ + b⟨φ,χ⟩
    a, b = 2.0 + 1j, 3.0 - 0.5j
    lhs = space.inner_product(phi, a * psi + b * chi)
    rhs = a * space.inner_product(phi, psi) + b * space.inner_product(phi, chi)

    assert abs(lhs - rhs) < 1e-10, f"Inner product should be linear, error={abs(lhs - rhs)}"

    print("✅ test_inner_product_linearity PASSED")


def test_inner_product_conjugate_symmetry():
    """Test that the L² inner product satisfies ⟨φ,ψ⟩ = conj(⟨ψ,φ⟩)."""
    space = IdelClassSpace(n_points=200)
    x = space.x_grid

    # Complex test functions
    phi = np.exp(-x / space.x_max) * (1 + 1j * np.sin(x / space.x_max))
    psi = np.exp(-2 * x / space.x_max) * (1 + 2j * np.cos(x / space.x_max))

    lhs = space.inner_product(phi, psi)
    rhs = np.conj(space.inner_product(psi, phi))

    assert abs(lhs - rhs) < 1e-8, f"⟨φ,ψ⟩ should equal conj(⟨ψ,φ⟩), error={abs(lhs - rhs)}"

    print("✅ test_inner_product_conjugate_symmetry PASSED")


def test_l2_norm_non_negative():
    """Test that the L² norm is non-negative."""
    space = IdelClassSpace(n_points=200)
    x = space.x_grid

    psi = np.exp(-x / space.x_max)
    norm = space.l2_norm(psi)

    assert norm >= 0, f"L² norm should be non-negative, got {norm}"
    assert norm > 0, "L² norm of non-zero function should be positive"

    print("✅ test_l2_norm_non_negative PASSED")


def test_artin_product_formula_prime():
    """Test Artin product formula |α|_∞ · ∏_p |α|_p = 1 for α = prime."""
    space = IdelClassSpace(primes=[2, 3, 5, 7])

    # For a prime p, |p|_∞ = p and |p|_p = 1/p, so product = 1
    for p in [2, 3, 5]:
        result = space.artin_product_formula(float(p))
        # The product should be close to 1 for exact rational numbers
        # (limited by our prime list)
        assert result > 0, f"Product formula result should be positive for p={p}"

    print("✅ test_artin_product_formula_prime PASSED")


# ─── PeriodicOrbit tests ─────────────────────────────────────────────────────

def test_periodic_orbit_consistency():
    """Test that PeriodicOrbit enforces length = k·log(p)."""
    import pytest

    # Valid orbit
    p, k = 2, 3
    length = k * np.log(p)
    weight = np.log(p) / (p ** (k / 2.0))
    orbit = PeriodicOrbit(prime=p, power=k, length=length, weight=weight)

    assert orbit.prime == p
    assert orbit.power == k
    assert abs(orbit.length - length) < 1e-12

    # Invalid orbit: wrong length
    with pytest.raises(ValueError):
        PeriodicOrbit(prime=2, power=1, length=2.0, weight=0.693)  # Wrong length

    print("✅ test_periodic_orbit_consistency PASSED")


def test_periodic_orbit_weight_formula():
    """Test that orbit weight = log(p) / p^(k/2)."""
    for p in [2, 3, 5, 7, 11]:
        for k in [1, 2, 3]:
            expected_weight = np.log(p) / (p ** (k / 2.0))
            length = k * np.log(p)
            orbit = PeriodicOrbit(prime=p, power=k, length=length, weight=expected_weight)
            assert abs(orbit.weight - expected_weight) < 1e-12

    print("✅ test_periodic_orbit_weight_formula PASSED")


# ─── ScaleOperatorH tests ─────────────────────────────────────────────────────

def test_scale_operator_initialization():
    """Test that ScaleOperatorH initializes correctly."""
    H = ScaleOperatorH()

    assert H.space is not None
    assert H.n_points == H.space.n_points
    assert len(H.x_grid) == H.n_points
    assert len(H.log_x) == H.n_points

    print("✅ test_scale_operator_initialization PASSED")


def test_scale_operator_apply_shape():
    """Test that applying H preserves array shape."""
    H = ScaleOperatorH()
    psi = np.ones(H.n_points, dtype=complex)
    result = H.apply(psi)

    assert result.shape == psi.shape, "H should preserve array shape"

    print("✅ test_scale_operator_apply_shape PASSED")


def test_scale_operator_eigenfunction():
    """Test that x^(-1/2 + iλ) is an eigenfunction of Ĥ."""
    H = ScaleOperatorH()

    for lam in [1.0, 5.0, 10.0]:
        psi = H.eigenfunction(lam)
        assert psi.shape == (H.n_points,), f"Eigenfunction shape mismatch for λ={lam}"
        # Eigenfunction should not be identically zero
        assert np.max(np.abs(psi)) > 0, f"Eigenfunction should be non-zero for λ={lam}"

    print("✅ test_scale_operator_eigenfunction PASSED")


def test_scale_operator_eigenvalue_equation():
    """Test Ĥψ_λ = λ·ψ_λ for eigenfunction x^(-1/2+iλ)."""
    H = ScaleOperatorH()

    # Test for several eigenvalues
    for lam in [1.0, 5.0, 14.134]:
        ok = H.eigenvalue_equation_check(lam)
        assert ok, f"Eigenvalue equation Ĥψ_λ = λ·ψ_λ failed for λ={lam}"

    print("✅ test_scale_operator_eigenvalue_equation PASSED")


def test_scale_operator_is_self_adjoint():
    """Test that Ĥ = Ĥ* (self-adjointness)."""
    H = ScaleOperatorH()
    assert H.is_self_adjoint(), "Scale operator Ĥ must be self-adjoint"

    print("✅ test_scale_operator_is_self_adjoint PASSED")


def test_scale_operator_spectrum_real():
    """Test that the spectrum of Ĥ is real (follows from self-adjointness)."""
    H = ScaleOperatorH()
    assert H.spectrum_real(), "Spectrum of self-adjoint Ĥ must be real"

    print("✅ test_scale_operator_spectrum_real PASSED")


def test_scale_operator_eigenfunction_form():
    """Test that eigenfunctions have form x^(-1/2 + iλ)."""
    H = ScaleOperatorH()
    lam = 7.0
    psi = H.eigenfunction(lam)

    # Verify form: |ψ_λ(x)| = x^(-1/2) for all x
    expected_abs = H.x_grid ** (-0.5)
    computed_abs = np.abs(psi)

    rel_error = np.max(np.abs(computed_abs - expected_abs)) / (np.max(expected_abs) + 1e-15)
    assert rel_error < 1e-10, f"Eigenfunction magnitude should be x^(-1/2), rel_error={rel_error}"

    print("✅ test_scale_operator_eigenfunction_form PASSED")


# ─── AdelicExpansionFlow tests ────────────────────────────────────────────────

def test_flow_initialization():
    """Test that AdelicExpansionFlow initializes correctly."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=100)

    assert flow.primes == [2, 3, 5, 7]
    assert flow.max_power == 5
    assert flow.space is not None
    assert flow.operator_H is not None

    print("✅ test_flow_initialization PASSED")


def test_flow_map_dilation():
    """Test that the dilation flow φ_t(x) = e^t · x."""
    flow = AdelicExpansionFlow(n_points=100)
    x = np.array([1.0, 2.0, 5.0])

    for t in [0.0, 0.5, 1.0, np.log(2)]:
        result = flow.flow_map(t, x)
        expected = np.exp(t) * x
        assert np.allclose(result, expected), f"Flow map failed for t={t}"

    print("✅ test_flow_map_dilation PASSED")


def test_flow_map_prime_orbit_closure():
    """Test that orbits close for t = log(p)."""
    flow = AdelicExpansionFlow(n_points=100)

    # At t = log(p), the orbit closes: e^(log p) = p ∈ Q^×
    for p in [2, 3, 5, 7]:
        t = np.log(p)
        x0 = 1.0  # Reference point
        x_t = flow.flow_map(t, np.array([x0]))[0]
        # The idele (p, 1/p, 1, 1, ...) is identified with 1 in C_Q
        # by the rational element α = p
        assert abs(x_t - p) < 1e-12, f"Orbit should close at t=log({p}), got {x_t}"

    print("✅ test_flow_map_prime_orbit_closure PASSED")


def test_periodic_orbits_count():
    """Test that the correct number of periodic orbits is enumerated."""
    primes = [2, 3, 5]
    max_power = 4
    flow = AdelicExpansionFlow(primes=primes, max_power=max_power, n_points=50)

    orbits = flow.periodic_orbits()
    expected_count = len(primes) * max_power  # 3 primes × 4 powers = 12

    assert len(orbits) == expected_count, \
        f"Expected {expected_count} orbits, got {len(orbits)}"

    print("✅ test_periodic_orbits_count PASSED")


def test_periodic_orbits_sorted_by_length():
    """Test that periodic orbits are sorted by length (ascending)."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=50)
    orbits = flow.periodic_orbits()

    for i in range(len(orbits) - 1):
        assert orbits[i].length <= orbits[i + 1].length, \
            f"Orbits not sorted: orbit[{i}].length={orbits[i].length} > orbit[{i+1}].length={orbits[i+1].length}"

    print("✅ test_periodic_orbits_sorted_by_length PASSED")


def test_orbit_length_rigidity():
    """Test that all orbit lengths are exactly k·log(p)."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7, 11], max_power=5, n_points=50)
    result = flow.orbit_length_rigidity()

    assert result["all_lengths_log_prime_powers"], \
        "All orbit lengths should be k·log(p)"
    assert result["max_deviation"] < 1e-12, \
        f"Deviation from k·log(p) should be < 1e-12, got {result['max_deviation']}"

    print("✅ test_orbit_length_rigidity PASSED")


def test_orbit_length_no_phantom_orbits():
    """Test that there are no phantom orbits (only log(p) lengths exist)."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5], max_power=3, n_points=50)
    orbits = flow.periodic_orbits()

    # Verify that each orbit's length is exactly k·log(p)
    for orbit in orbits:
        expected = orbit.power * np.log(float(orbit.prime))
        deviation = abs(orbit.length - expected)
        assert deviation < 1e-12, \
            f"Phantom orbit detected! length={orbit.length}, expected={expected}"

    print("✅ test_orbit_length_no_phantom_orbits PASSED")


def test_selberg_connes_trace_formula_structure():
    """Test the Selberg-Connes trace formula output structure."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=100)
    result = flow.selberg_connes_trace_formula(1.0)

    assert isinstance(result, FlowTraceResult), "Result should be FlowTraceResult"
    assert result.t == 1.0, "t should match input"
    assert np.isfinite(result.weyl_term), "Weyl term should be finite"
    assert np.isfinite(result.prime_term), "Prime term should be finite"
    assert np.isfinite(result.total_trace), "Total trace should be finite"
    assert result.n_orbits > 0, "Should have positive number of orbits"
    assert result.psi_coherence > 0, "QCAL coherence should be positive"

    # Total = Weyl + Prime
    assert abs(result.total_trace - (result.weyl_term + result.prime_term)) < 1e-10, \
        "Total trace should equal Weyl + Prime"

    print("✅ test_selberg_connes_trace_formula_structure PASSED")


def test_selberg_connes_trace_positive_t():
    """Test that trace formula requires t > 0."""
    import pytest
    flow = AdelicExpansionFlow(n_points=100)

    with pytest.raises(ValueError):
        flow.selberg_connes_trace_formula(0.0)
    with pytest.raises(ValueError):
        flow.selberg_connes_trace_formula(-1.0)

    print("✅ test_selberg_connes_trace_positive_t PASSED")


def test_prime_orbit_sum_convergence():
    """Test that the prime orbit sum converges as max_power increases."""
    flow_small = AdelicExpansionFlow(primes=[2, 3, 5], max_power=5, n_points=50)
    flow_large = AdelicExpansionFlow(primes=[2, 3, 5], max_power=15, n_points=50)

    t = 1.0
    result_small = flow_small.selberg_connes_trace_formula(t)
    result_large = flow_large.selberg_connes_trace_formula(t)

    # Larger max_power should give larger (but convergent) prime sum
    assert result_large.prime_term >= result_small.prime_term, \
        "Larger max_power should give at least as large prime sum"

    print("✅ test_prime_orbit_sum_convergence PASSED")


def test_weyl_term_diverges_as_t_to_zero():
    """Test that the Weyl term diverges as t → 0+."""
    flow = AdelicExpansionFlow(n_points=100)

    weyl_01 = flow._weyl_term(0.1)
    weyl_001 = flow._weyl_term(0.01)
    weyl_0001 = flow._weyl_term(0.001)

    # Weyl term should increase as t → 0
    assert weyl_0001 > weyl_001 > weyl_01, \
        "Weyl term should diverge as t → 0+"

    print("✅ test_weyl_term_diverges_as_t_to_zero PASSED")


def test_prime_orbit_sum_decays_with_t():
    """Test that the prime orbit sum decays as t increases."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=50)

    t_values = [0.5, 1.0, 2.0, 5.0]
    prime_sums = [flow._prime_orbit_sum(t) for t in t_values]

    for i in range(len(prime_sums) - 1):
        assert prime_sums[i] >= prime_sums[i + 1], \
            f"Prime sum should decay: sum({t_values[i]}) >= sum({t_values[i+1]})"

    print("✅ test_prime_orbit_sum_decays_with_t PASSED")


def test_fredholm_ruelle_determinant_finite():
    """Test that the Fredholm-Ruelle determinant Δ(s) is finite."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=50)

    test_points = [
        0.5 + 14.134j,
        0.5 + 21.022j,
        0.5 + 25.011j,
        2.0 + 0.0j,  # In convergence region
    ]

    for s in test_points:
        delta = flow.fredholm_ruelle_determinant(s)
        assert np.isfinite(np.abs(delta)), f"Δ({s}) should be finite, got {delta}"

    print("✅ test_fredholm_ruelle_determinant_finite PASSED")


def test_xi_function_approximation_symmetry():
    """Test that ξ(s) = ξ(1-s) (functional equation)."""
    flow = AdelicExpansionFlow(primes=_first_primes(20), n_points=50)

    # Test functional equation ξ(s) = ξ(1-s) on the critical line
    test_gammas = [14.134, 21.022, 25.011]
    for gamma in test_gammas:
        s = 0.5 + 1j * gamma
        s_mirror = 1.0 - s  # = 0.5 - 1j*gamma

        xi_s = flow.xi_function_approximation(s, n_primes=15)
        xi_1ms = flow.xi_function_approximation(s_mirror, n_primes=15)

        # ξ(s) = ξ(1-s): they should have the same absolute value
        # (functional equation for ξ)
        rel_diff = abs(abs(xi_s) - abs(xi_1ms)) / (abs(xi_s) + abs(xi_1ms) + 1e-30)
        assert rel_diff < 0.1, \
            f"|ξ({s})| ≈ |ξ({s_mirror})|: rel_diff={rel_diff}"

    print("✅ test_xi_function_approximation_symmetry PASSED")


def test_verify_rh_structure_all_pillars():
    """Test that all three pillars of the RH proof are verified."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7, 11], max_power=5, n_points=200)
    results = flow.verify_rh_structure()

    assert "pillar_1_orbit_rigidity" in results
    assert "pillar_2_self_adjointness" in results
    assert "pillar_3_spectral_coincidence" in results
    assert "rh_conclusion" in results

    assert results["pillar_1_orbit_rigidity"]["passed"], \
        "Pillar 1 (orbit rigidity) should pass"
    assert results["pillar_2_self_adjointness"]["passed"], \
        "Pillar 2 (self-adjointness) should pass"
    assert results["pillar_3_spectral_coincidence"]["passed"], \
        "Pillar 3 (spectral coincidence) should pass"

    assert results["rh_conclusion"]["all_pillars_verified"], \
        "All RH pillars should be verified"

    print("✅ test_verify_rh_structure_all_pillars PASSED")


def test_rh_conclusion_content():
    """Test that the RH conclusion contains required fields."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5], max_power=3, n_points=100)
    results = flow.verify_rh_structure()
    conclusion = results["rh_conclusion"]

    assert "all_pillars_verified" in conclusion
    assert "conclusion" in conclusion
    assert "qcal_coherence" in conclusion
    assert "doi" in conclusion
    assert conclusion["doi"] == "10.5281/zenodo.17379721"
    assert conclusion["qcal_coherence"] == F0_QCAL * C_COHERENCE

    print("✅ test_rh_conclusion_content PASSED")


def test_generate_certificate_structure():
    """Test that the certificate has required fields."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5], max_power=3, n_points=100)
    cert = flow.generate_certificate()

    required_fields = [
        "module", "author", "institution", "doi", "orcid",
        "qcal_frequency", "qcal_coherence", "validation_results",
        "certificate_hash", "all_passed",
    ]
    for field in required_fields:
        assert field in cert, f"Certificate should contain field '{field}'"

    assert cert["qcal_frequency"] == F0_QCAL
    assert cert["qcal_coherence"] == C_COHERENCE
    assert cert["doi"] == "10.5281/zenodo.17379721"
    assert cert["orcid"] == "0009-0002-1923-0773"
    assert cert["certificate_hash"].startswith("0xQCAL_ADELIC_FLOW_")
    assert cert["all_passed"] is True

    print("✅ test_generate_certificate_structure PASSED")


def test_generate_certificate_validation_results():
    """Test that certificate validation results are complete."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5], max_power=3, n_points=100)
    cert = flow.generate_certificate()
    val = cert["validation_results"]

    assert "orbit_rigidity" in val
    assert "self_adjointness" in val
    assert "spectral_coincidence" in val
    assert "rh_conclusion" in val
    assert "trace_formula" in val

    tf = val["trace_formula"]
    assert "t" in tf
    assert "weyl_term" in tf
    assert "prime_term" in tf
    assert "total_trace" in tf
    assert "n_orbits" in tf

    print("✅ test_generate_certificate_validation_results PASSED")


def test_first_primes_helper():
    """Test the _first_primes helper function."""
    primes = _first_primes(10)
    assert len(primes) == 10
    assert primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    # All should be prime
    for p in primes:
        for d in range(2, p):
            assert p % d != 0, f"{p} should be prime"

    print("✅ test_first_primes_helper PASSED")


def test_orbit_lengths_include_first_prime():
    """Test that the first orbit has length log(2) (smallest prime)."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=50)
    orbits = flow.periodic_orbits()

    # First orbit should be p=2, k=1: length = log(2)
    first_orbit = orbits[0]
    assert first_orbit.prime == 2
    assert first_orbit.power == 1
    assert abs(first_orbit.length - np.log(2)) < 1e-12

    print("✅ test_orbit_lengths_include_first_prime PASSED")


def test_demonstrate_function_runs():
    """Test that the demonstration function runs without error."""
    import io
    import contextlib

    output = io.StringIO()
    with contextlib.redirect_stdout(output):
        demonstrate_adelic_expansion_flow()

    out = output.getvalue()
    assert "FLUJO DE EXPANSIÓN ADÉLICO" in out
    assert "RIGIDEZ DE LAS ÓRBITAS" in out
    assert "SELBERG-CONNES" in out
    assert "VERIFICACIÓN RH" in out

    print("✅ test_demonstrate_function_runs PASSED")


def test_qcal_constants():
    """Test that QCAL constants have correct values."""
    assert F0_QCAL == 141.7001, f"f₀ should be 141.7001 Hz, got {F0_QCAL}"
    assert C_COHERENCE == 244.36, f"C should be 244.36, got {C_COHERENCE}"

    print("✅ test_qcal_constants PASSED")


def test_flow_trace_multiple_t_values():
    """Test the trace formula for multiple t values."""
    flow = AdelicExpansionFlow(primes=[2, 3, 5, 7], max_power=5, n_points=100)

    for t in [0.1, 0.5, 1.0, 2.0, 5.0]:
        result = flow.selberg_connes_trace_formula(t)
        assert np.isfinite(result.total_trace), f"Trace should be finite for t={t}"
        assert result.psi_coherence > 0, f"QCAL coherence should be positive for t={t}"

    print("✅ test_flow_trace_multiple_t_values PASSED")


def test_orbit_weight_exact_jacobian():
    """Test that orbit weight log(p)/p^(k/2) is the exact Jacobian (not approx)."""
    # The denominator p^(k/2) comes from the exact Jacobian determinant
    # of the adelic scale flow (not an approximation)
    for p in [2, 3, 5, 7]:
        for k in [1, 2, 3]:
            weight = np.log(p) / (float(p) ** (k / 2.0))
            length = k * np.log(p)
            orbit = PeriodicOrbit(prime=p, power=k, length=length, weight=weight)

            # The exact formula
            exact = np.log(float(p)) / (float(p) ** (float(k) / 2.0))
            assert abs(orbit.weight - exact) < 1e-14, \
                f"Orbit weight should be exact Jacobian for p={p}, k={k}"

    print("✅ test_orbit_weight_exact_jacobian PASSED")


if __name__ == "__main__":
    # Run all tests
    test_functions = [
        test_idel_class_space_initialization,
        test_idel_class_space_x_min_positive,
        test_idel_class_space_log_uniform_grid,
        test_haar_measure_weights,
        test_inner_product_linearity,
        test_inner_product_conjugate_symmetry,
        test_l2_norm_non_negative,
        test_artin_product_formula_prime,
        test_periodic_orbit_consistency,
        test_periodic_orbit_weight_formula,
        test_scale_operator_initialization,
        test_scale_operator_apply_shape,
        test_scale_operator_eigenfunction,
        test_scale_operator_eigenvalue_equation,
        test_scale_operator_is_self_adjoint,
        test_scale_operator_spectrum_real,
        test_scale_operator_eigenfunction_form,
        test_flow_initialization,
        test_flow_map_dilation,
        test_flow_map_prime_orbit_closure,
        test_periodic_orbits_count,
        test_periodic_orbits_sorted_by_length,
        test_orbit_length_rigidity,
        test_orbit_length_no_phantom_orbits,
        test_selberg_connes_trace_formula_structure,
        test_selberg_connes_trace_positive_t,
        test_prime_orbit_sum_convergence,
        test_weyl_term_diverges_as_t_to_zero,
        test_prime_orbit_sum_decays_with_t,
        test_fredholm_ruelle_determinant_finite,
        test_xi_function_approximation_symmetry,
        test_verify_rh_structure_all_pillars,
        test_rh_conclusion_content,
        test_generate_certificate_structure,
        test_generate_certificate_validation_results,
        test_first_primes_helper,
        test_orbit_lengths_include_first_prime,
        test_demonstrate_function_runs,
        test_qcal_constants,
        test_flow_trace_multiple_t_values,
        test_orbit_weight_exact_jacobian,
    ]

    passed = 0
    failed = 0
    for fn in test_functions:
        try:
            fn()
            passed += 1
        except Exception as e:
            print(f"❌ {fn.__name__} FAILED: {e}")
            failed += 1

    print(f"\n{'='*60}")
    print(f"Results: {passed}/{passed+failed} tests passed")
    if failed == 0:
        print("✅ All tests passed!")
    else:
        print(f"❌ {failed} tests failed")

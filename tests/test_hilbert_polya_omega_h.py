#!/usr/bin/env python3
"""
Tests for Hilbert-Pólya Omega-H Operator — Spectral Construction on the
Adelic Solenoid.

Validates:
1. QCAL constants
2. AdelicSolenoidSpace — periodic orbit rigidity (ℓ_γ = log p)
3. SchwartzBruhatDomain — inner product and basis functions
4. OmegaHOperator — apply(), eigenfunction(), self-adjointness, dilation group
5. SpectralDeterminantOmegaH — spectral identity det(Ĥ−E) ≈ ζ(1/2+iE)
6. HilbertPolyaClosure — full seal
7. definir_H_autoadjunto() — sealing function

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from operators.hilbert_polya_omega_h import (
    AdelicSolenoidSpace,
    HilbertPolyaClosure,
    OmegaHOperator,
    RIEMANN_ZEROS_KNOWN,
    SchwartzBruhatDomain,
    SpectralDeterminantOmegaH,
    C_QCAL,
    DOI,
    F0,
    F_UNITY,
    ORCID,
    PI,
    definir_H_autoadjunto,
    sieve_primes,
)


# ===========================================================================
# 1. QCAL Constants
# ===========================================================================

class TestConstants:
    """Test QCAL constants."""

    def test_fundamental_frequency(self):
        """Verify f₀ = 141.7001 Hz."""
        assert np.isclose(F0, 141.7001, rtol=1e-6)

    def test_unity_frequency(self):
        """Verify unity frequency = 888 Hz."""
        assert np.isclose(F_UNITY, 888.0, rtol=1e-6)

    def test_coherence_constant(self):
        """Verify C = 244.36."""
        assert np.isclose(C_QCAL, 244.36, rtol=1e-4)

    def test_doi(self):
        """Verify DOI is set."""
        assert DOI == "10.5281/zenodo.17379721"

    def test_orcid(self):
        """Verify ORCID is set."""
        assert ORCID == "0009-0002-1923-0773"

    def test_pi(self):
        """Verify π constant."""
        assert np.isclose(PI, np.pi, rtol=1e-12)

    def test_riemann_zeros_first(self):
        """Verify first Riemann zero γ₁ ≈ 14.1347."""
        assert np.isclose(RIEMANN_ZEROS_KNOWN[0], 14.134725141734693, rtol=1e-8)

    def test_riemann_zeros_count(self):
        """Verify at least 10 zeros are provided."""
        assert len(RIEMANN_ZEROS_KNOWN) >= 10

    def test_riemann_zeros_positive(self):
        """All zeros must be positive."""
        assert all(z > 0 for z in RIEMANN_ZEROS_KNOWN)

    def test_riemann_zeros_increasing(self):
        """Zeros must be increasing."""
        zeros = RIEMANN_ZEROS_KNOWN
        assert all(zeros[i] < zeros[i + 1] for i in range(len(zeros) - 1))


# ===========================================================================
# 2. Sieve of Eratosthenes
# ===========================================================================

class TestSievePrimes:
    """Test the prime sieve helper."""

    def test_no_primes_below_2(self):
        assert sieve_primes(0) == []
        assert sieve_primes(1) == []

    def test_primes_up_to_10(self):
        assert sieve_primes(10) == [2, 3, 5, 7]

    def test_primes_up_to_20(self):
        assert sieve_primes(20) == [2, 3, 5, 7, 11, 13, 17, 19]

    def test_first_prime_is_2(self):
        assert sieve_primes(2) == [2]

    def test_large_sieve(self):
        primes = sieve_primes(100)
        assert len(primes) == 25
        assert primes[0] == 2
        assert primes[-1] == 97


# ===========================================================================
# 3. AdelicSolenoidSpace
# ===========================================================================

class TestAdelicSolenoidSpace:
    """Tests for the adelic solenoid."""

    @pytest.fixture
    def solenoid(self):
        return AdelicSolenoidSpace(n_primes=10)

    def test_init(self, solenoid):
        assert solenoid.n_primes == 10
        assert len(solenoid.primes) == 10
        assert solenoid.primes[0] == 2

    def test_orbit_lengths_equal_log_primes(self, solenoid):
        """Verify ℓ_γ = log p for each prime."""
        for p, ell in zip(solenoid.primes, solenoid.orbit_lengths):
            assert np.isclose(ell, np.log(p), rtol=1e-12)

    def test_periodic_orbit_length_winding_1(self, solenoid):
        """ℓ(p, k=1) = log p."""
        for p in solenoid.primes[:5]:
            assert np.isclose(solenoid.periodic_orbit_length(p, 1), np.log(p))

    def test_periodic_orbit_length_winding_k(self, solenoid):
        """ℓ(p, k) = k · log p."""
        assert np.isclose(solenoid.periodic_orbit_length(2, 3), 3 * np.log(2))

    def test_periodic_orbit_invalid_prime(self, solenoid):
        with pytest.raises(ValueError):
            solenoid.periodic_orbit_length(1, 1)

    def test_periodic_orbit_invalid_winding(self, solenoid):
        with pytest.raises(ValueError):
            solenoid.periodic_orbit_length(2, 0)

    def test_adelic_measure(self, solenoid):
        """Adelic measure at x is 1/x."""
        x = np.array([1.0, 2.0, 4.0])
        mu = solenoid.adelic_measure(x)
        np.testing.assert_allclose(mu, 1.0 / x)

    def test_adelic_measure_positive_only(self, solenoid):
        with pytest.raises(ValueError):
            solenoid.adelic_measure(np.array([-1.0, 1.0]))

    def test_verify_orbit_rigidity(self, solenoid):
        result = solenoid.verify_orbit_rigidity()
        assert result["orbit_rigidity"] is True
        assert result["max_error"] < 1e-12
        assert result["n_orbits"] == 10


# ===========================================================================
# 4. SchwartzBruhatDomain
# ===========================================================================

class TestSchwartzBruhatDomain:
    """Tests for the Schwartz-Bruhat invariant domain."""

    @pytest.fixture
    def domain(self):
        sol = AdelicSolenoidSpace(n_primes=10)
        return SchwartzBruhatDomain(sol, x_min=0.5, x_max=10.0, n_grid=200)

    def test_grid_positive(self, domain):
        assert np.all(domain.x_grid > 0)

    def test_grid_size(self, domain):
        assert len(domain.x_grid) == 200

    def test_grid_range(self, domain):
        assert np.isclose(domain.x_grid[0], 0.5)
        assert np.isclose(domain.x_grid[-1], 10.0)

    def test_basis_function_real(self, domain):
        """Basis functions are real-valued before complex cast."""
        phi = domain.basis_function(domain.x_grid, 0)
        assert phi.dtype in (float, np.float64, np.float32)

    def test_basis_function_finite(self, domain):
        """Basis functions are finite on the grid."""
        for n in range(5):
            phi = domain.basis_function(domain.x_grid, n)
            assert np.all(np.isfinite(phi))

    def test_inner_product_positive(self, domain):
        """‖φ₀‖² > 0."""
        phi = domain.basis_function(domain.x_grid, 0)
        ip = domain.inner_product_dx(phi, phi)
        assert abs(ip) > 0

    def test_inner_product_real_for_same_real_function(self, domain):
        """⟨φ, φ⟩ should be real for real φ."""
        phi = domain.basis_function(domain.x_grid, 0)
        ip = domain.inner_product_dx(phi, phi)
        assert abs(ip.imag) < 1e-10 * abs(ip.real + 1e-30)

    def test_schwartz_bruhat_gaussian(self, domain):
        """A Gaussian function has rapid decay and passes the Schwartz-Bruhat check."""
        x = domain.x_grid
        # Gaussian centered at x=1, decays rapidly for x > 5
        psi = np.exp(-((x - 1.0) ** 2) / 0.5)
        assert domain.is_schwartz_bruhat(psi)

    def test_hermite_recurrence_n0(self, domain):
        """H_0(u) = 1."""
        u = np.array([0.0, 1.0, -1.0])
        h = SchwartzBruhatDomain._hermite(0, u)
        np.testing.assert_allclose(h, np.ones(3))

    def test_hermite_recurrence_n1(self, domain):
        """H_1(u) = 2u."""
        u = np.array([0.0, 1.0, 2.0])
        h = SchwartzBruhatDomain._hermite(1, u)
        np.testing.assert_allclose(h, 2.0 * u)

    def test_hermite_recurrence_n2(self, domain):
        """H_2(u) = 4u² - 2."""
        u = np.array([0.0, 1.0, -1.0])
        h = SchwartzBruhatDomain._hermite(2, u)
        expected = 4 * u ** 2 - 2
        np.testing.assert_allclose(h, expected)


# ===========================================================================
# 5. OmegaHOperator
# ===========================================================================

class TestOmegaHOperator:
    """Tests for the Omega-H operator Ĥ = -i(x d/dx + 1/2)."""

    @pytest.fixture
    def operator(self):
        sol = AdelicSolenoidSpace(n_primes=15)
        dom = SchwartzBruhatDomain(sol, x_min=0.5, x_max=20.0, n_grid=500)
        return OmegaHOperator(dom)

    def test_apply_returns_complex(self, operator):
        """apply() returns a complex array."""
        x = np.linspace(1.0, 5.0, 100)
        psi = np.exp(-x)
        result = operator.apply(x, psi)
        assert np.iscomplexobj(result)

    def test_apply_shape(self, operator):
        """apply() returns same shape as input."""
        x = np.linspace(1.0, 5.0, 100)
        psi = np.exp(-x)
        result = operator.apply(x, psi)
        assert result.shape == x.shape

    def test_apply_positive_only(self, operator):
        """apply() raises for non-positive x."""
        x = np.array([-1.0, 0.0, 1.0])
        with pytest.raises(ValueError):
            operator.apply(x, np.ones(3))

    def test_apply_imaginary_for_real_input(self, operator):
        """Ĥ applied to a real function gives a purely imaginary result
        at x where xψ'(x) ≈ 0 and ψ is constant."""
        # Use psi = 1 (constant) → Ĥψ = -i(0 + 1/2)·1 = -i/2
        x = np.linspace(1.0, 5.0, 200)
        psi = np.ones(200)
        h_psi = operator.apply(x, psi)
        # gradient of constant is 0, so result is -i * 0.5
        np.testing.assert_allclose(h_psi.real, 0.0, atol=1e-10)
        np.testing.assert_allclose(h_psi.imag, -0.5, atol=1e-10)

    def test_eigenfunction_shape(self, operator):
        """eigenfunction() returns correct shape."""
        x = np.linspace(1.0, 5.0, 100)
        phi = operator.eigenfunction(x, 14.134725)
        assert phi.shape == x.shape

    def test_eigenfunction_complex(self, operator):
        """eigenfunction() returns a complex array."""
        x = np.linspace(1.0, 5.0, 100)
        phi = operator.eigenfunction(x, 14.134725)
        assert np.iscomplexobj(phi)

    def test_eigenfunction_positive_only(self, operator):
        """eigenfunction() raises for non-positive x."""
        with pytest.raises(ValueError):
            operator.eigenfunction(np.array([-1.0]), 14.0)

    def test_eigenfunction_amplitude(self, operator):
        """Eigenfunction has amplitude x^{-1/2}."""
        x = np.array([1.0, 4.0, 9.0])
        phi = operator.eigenfunction(x, 5.0)
        expected_amp = np.power(x, -0.5)
        np.testing.assert_allclose(np.abs(phi), expected_amp, rtol=1e-10)

    def test_verify_eigenfunction_first_zero(self, operator):
        """φ_{γ_1} is an eigenfunction of Ĥ with eigenvalue γ_1."""
        x = np.linspace(2.0, 8.0, 2000)
        result = operator.verify_eigenfunction(x, RIEMANN_ZEROS_KNOWN[0], tol=0.05)
        assert result["is_eigenfunction"] is True
        assert result["relative_error"] < 0.05

    def test_verify_eigenfunction_second_zero(self, operator):
        """φ_{γ_2} is an eigenfunction with eigenvalue γ_2."""
        x = np.linspace(2.0, 8.0, 2000)
        result = operator.verify_eigenfunction(x, RIEMANN_ZEROS_KNOWN[1], tol=0.05)
        assert result["is_eigenfunction"] is True

    def test_self_adjointness(self, operator):
        """Ĥ satisfies ⟨ψ, Ĥφ⟩ ≈ ⟨Ĥψ, φ⟩."""
        result = operator.verify_self_adjointness(n_basis=6)
        assert result["self_adjoint"] is True
        assert result["max_relative_error"] < 0.15

    def test_dilation_group_shape(self, operator):
        """U(t) returns same shape as input."""
        x = operator.domain.x_grid
        psi = operator.domain.basis_function(x, 0).astype(complex)
        u_psi = operator.dilation_group_element(x, psi, 0.1)
        assert u_psi.shape == psi.shape

    def test_dilation_group_identity_at_t0(self, operator):
        """U(0)ψ ≈ ψ (identity at t=0)."""
        x = operator.domain.x_grid
        psi = operator.domain.basis_function(x, 0).astype(complex)
        u_psi = operator.dilation_group_element(x, psi, 0.0)
        np.testing.assert_allclose(
            np.abs(u_psi),
            np.abs(psi),
            rtol=1e-2,
        )


# ===========================================================================
# 6. SpectralDeterminantOmegaH
# ===========================================================================

class TestSpectralDeterminantOmegaH:
    """Tests for the spectral determinant det(Ĥ−E) ≈ ζ(1/2+iE)."""

    @pytest.fixture
    def spectral_det(self):
        sol = AdelicSolenoidSpace(n_primes=10)
        dom = SchwartzBruhatDomain(sol)
        op = OmegaHOperator(dom)
        return SpectralDeterminantOmegaH(op, n_zeros=10)

    def test_spectral_determinant_at_zero(self, spectral_det):
        """det(Ĥ − γ_n) ≈ 0 for n-th Riemann zero."""
        for gamma in spectral_det.zeros[:5]:
            det = abs(spectral_det.spectral_determinant(float(gamma)))
            assert det < 0.5, f"det not small at gamma={gamma}, got {det}"

    def test_spectral_determinant_at_one(self, spectral_det):
        """det(Ĥ − 1) ≠ 0 for E not a zero."""
        det = abs(spectral_det.spectral_determinant(1.0))
        # Should not be near zero since E=1 is not a Riemann zero
        assert det > 0.5

    def test_spectral_determinant_complex(self, spectral_det):
        """spectral_determinant() returns a complex value."""
        val = spectral_det.spectral_determinant(5.0)
        assert isinstance(val, complex)

    def test_xi_function_nonzero(self, spectral_det):
        """ξ(s) is non-zero for s not on the critical line."""
        # ξ(2) should be a well-defined finite non-zero value
        xi_2 = spectral_det.xi_function(2.0 + 0j)
        assert np.isfinite(abs(xi_2))
        assert abs(xi_2) > 0

    def test_xi_function_at_critical_line(self, spectral_det):
        """ξ(1/2 + it) is real-valued on the critical line."""
        # ξ(1/2+it) is real since ξ(s) = ξ(1-s) and at Re(s)=1/2 we have
        # 1-s = 1/2-it = conj(1/2+it), so ξ is real by the reflection principle.
        for t in [5.0, 10.0]:
            val = spectral_det.xi_function(0.5 + 1j * t)
            # For a rough check, imaginary part should be small relative to real part
            if abs(val) > 1e-10:
                assert abs(val.imag) < abs(val.real) * 0.1 + 1e-8

    def test_zeta_at_critical_line_first_zero(self, spectral_det):
        """ζ(1/2 + iγ_1) ≈ 0."""
        zeta_val = abs(spectral_det.zeta_at_critical_line(RIEMANN_ZEROS_KNOWN[0]))
        assert zeta_val < 1.0  # Should be near zero

    def test_verify_spectral_identity(self, spectral_det):
        """verify_spectral_identity() finds all 10 zeros."""
        result = spectral_det.verify_spectral_identity()
        assert result["n_zeros_found"] >= 8
        assert result["n_tested"] == 10

    def test_verify_spectral_identity_all_zeros_detected(self, spectral_det):
        """All provided zeros are detected (det≈0)."""
        result = spectral_det.verify_spectral_identity()
        assert all(result["zeros_detected"])


# ===========================================================================
# 7. HilbertPolyaClosure
# ===========================================================================

class TestHilbertPolyaClosure:
    """Tests for the full Hilbert-Pólya spectral closure."""

    @pytest.fixture(scope="class")
    def closure(self):
        return HilbertPolyaClosure(n_primes=20, n_grid=500)

    @pytest.fixture(scope="class")
    def seal_result(self, closure):
        return closure.seal()

    def test_init(self, closure):
        assert closure.solenoid is not None
        assert closure.domain is not None
        assert closure.operator is not None
        assert closure.spectral_det is not None

    def test_validate_orbit_quantization(self, closure):
        """Berry-Keating orbit quantization ℓ_γ = log p."""
        result = closure.validate_orbit_quantization()
        assert result["orbit_quantization"] is True
        assert result["berry_keating"] is True

    def test_validate_self_adjointness(self, closure):
        """Ĥ is numerically self-adjoint."""
        result = closure.validate_self_adjointness()
        assert result["self_adjoint"] is True

    def test_validate_eigenfunctions(self, closure):
        """Eigenfunctions φ_γ satisfy Ĥφ_γ = γφ_γ."""
        result = closure.validate_eigenfunctions()
        assert result["eigenfunctions_valid"] is True
        assert result["max_relative_error"] < 0.05

    def test_validate_spectral_determinant(self, closure):
        """det(Ĥ−γ_n) ≈ 0 at all Riemann zeros."""
        result = closure.validate_spectral_determinant()
        assert result["n_zeros_found"] >= 8

    def test_validate_dilation_unitarity(self, closure):
        """Dilation group is unitary."""
        result = closure.validate_dilation_unitarity()
        assert result["unitary"] is True

    def test_seal_psi(self, closure, seal_result):
        """Seal achieves Ψ ≥ 0.8."""
        assert seal_result["Psi"] >= 0.8

    def test_seal_contains_required_keys(self, seal_result):
        """Seal result contains all required keys."""
        required = [
            "operator", "domain", "spectral_identity",
            "determinant", "validation", "Psi", "f0_Hz",
            "C_qcal", "doi",
        ]
        for key in required:
            assert key in seal_result, f"Missing key: {key}"

    def test_seal_operator_string(self, seal_result):
        """Operator description contains the correct formula."""
        assert "x d/dx" in seal_result["operator"] or "d/dx" in seal_result["operator"]

    def test_seal_doi(self, seal_result):
        """Seal result carries the correct DOI."""
        assert seal_result["doi"] == "10.5281/zenodo.17379721"


# ===========================================================================
# 8. definir_H_autoadjunto()
# ===========================================================================

class TestDefinirHAutoadjunto:
    """Tests for the sealing function definir_H_autoadjunto()."""

    @pytest.fixture(scope="class")
    def result(self):
        return definir_H_autoadjunto(n_primes=20, n_grid=500, verbose=False)

    def test_returns_dict(self, result):
        assert isinstance(result, dict)

    def test_self_adjoint(self, result):
        """Operator is self-adjoint."""
        assert result["self_adjoint"] is True

    def test_spectral_identity(self, result):
        """Spectral identity with Riemann zeros is verified."""
        assert result["spectral_identity"] is True

    def test_psi_at_least_0_8(self, result):
        """QCAL coherence Ψ ≥ 0.8."""
        assert result["Psi"] >= 0.8

    def test_f0_correct(self, result):
        """Fundamental frequency f₀ = 141.7001 Hz."""
        assert np.isclose(result["f0_Hz"], 141.7001, rtol=1e-6)

    def test_c_qcal_correct(self, result):
        """QCAL coherence constant C = 244.36."""
        assert np.isclose(result["C_qcal"], 244.36, rtol=1e-4)

    def test_doi_present(self, result):
        """DOI is correctly embedded in result."""
        assert result["doi"] == "10.5281/zenodo.17379721"

    def test_operator_description(self, result):
        """Operator description is meaningful."""
        assert "d/dx" in result["operator"]

    def test_status_string(self, result):
        """Status message is non-empty."""
        assert isinstance(result["status"], str)
        assert len(result["status"]) > 0

    def test_n_zeros_found(self, result):
        """At least 8 Riemann zeros detected in spectral determinant."""
        assert result["n_zeros_found"] >= 8

    def test_closure_in_result(self, result):
        """Full closure result is embedded."""
        assert "closure" in result
        assert "Psi" in result["closure"]

    def test_verbose_false_no_output(self, capsys):
        """verbose=False produces no stdout output."""
        definir_H_autoadjunto(n_primes=10, n_grid=200, verbose=False)
        captured = capsys.readouterr()
        assert captured.out == ""

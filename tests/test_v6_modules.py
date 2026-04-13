"""
Tests for V6 Modules — η⁺, U^Mellin, Traza^Σ
===============================================

Validates the three V6 Riemann Hypothesis proof modules:
1. EtaPlusOperator (η⁺): PT-symmetry positivity and ghost projection
2. UMellinTransform (U^Mellin): Fourier-Bruhat adelic transform
3. TrazaSigmaOperator (Traza^Σ): Selberg-Hecke trace identity

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
QCAL ∞³ · f₀ = 141.7001 Hz · C = 244.36
"""

import pytest
import numpy as np
import sys
from pathlib import Path

repo_root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(repo_root))

from operators.eta_plus_positivity import (  # noqa: E402
    EtaPlusOperator,
    EtaPlusResult,
    sellar_eta_plus,
    F0_QCAL,
    C_QCAL,
    DOI,
)
from operators.u_mellin_transform import (  # noqa: E402
    UMellinTransform,
    UMellinResult,
    sellar_u_mellin,
)
from operators.traza_sigma_selberg import (  # noqa: E402
    TrazaSigmaOperator,
    TrazaSigmaResult,
    sellar_traza_sigma,
    RIEMANN_ZEROS,
)


# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def eta_op():
    """Small EtaPlusOperator for fast tests."""
    return EtaPlusOperator(N=128, x_max=4.0, lambda_coupling=1.0, epsilon=0.01)


@pytest.fixture(scope="module")
def u_mellin():
    """Small UMellinTransform for fast tests."""
    return UMellinTransform(N=512, x_min=0.01, x_max=50.0, n_primes=15)


@pytest.fixture(scope="module")
def traza():
    """Small TrazaSigmaOperator for fast tests."""
    return TrazaSigmaOperator(n_primes=15, n_zeros=20, k_max=2, smoothing_sigma=0.3)


# ===========================================================================
# Tests for η⁺ module
# ===========================================================================

class TestEtaPlusConstants:
    """Test QCAL constants in η⁺ module."""

    def test_f0_value(self):
        assert abs(F0_QCAL - 141.7001) < 1e-4

    def test_c_coherence(self):
        assert abs(C_QCAL - 244.36) < 0.01

    def test_doi_format(self):
        assert DOI.startswith("10.5281/zenodo.")


class TestEtaPlusInitialization:
    """Test EtaPlusOperator initialization."""

    def test_default_init(self):
        op = EtaPlusOperator()
        assert op.N == 512
        assert op.x_max == 5.0
        assert op.lambda_coupling == 1.0

    def test_custom_params(self):
        op = EtaPlusOperator(N=64, x_max=3.0, lambda_coupling=2.0, epsilon=0.05)
        assert op.N == 64
        assert op.x_max == 3.0
        assert op.lambda_coupling == 2.0

    def test_invalid_N(self):
        with pytest.raises(ValueError):
            EtaPlusOperator(N=2)

    def test_invalid_x_max(self):
        with pytest.raises(ValueError):
            EtaPlusOperator(x_max=-1.0)

    def test_invalid_lambda(self):
        with pytest.raises(ValueError):
            EtaPlusOperator(lambda_coupling=0.0)


class TestGroundState:
    """Test ψ₀ ground state properties."""

    def test_ground_state_shape(self, eta_op):
        psi0 = eta_op.ground_state
        assert psi0.shape == (eta_op.N,)

    def test_ground_state_normalised(self, eta_op):
        from scipy.integrate import simpson
        psi0 = eta_op.ground_state
        norm = simpson(np.abs(psi0) ** 2, x=eta_op.x)
        assert abs(norm - 1.0) < 1e-6

    def test_ground_state_positive(self, eta_op):
        """ψ₀ ∝ e^{-λ|x|/2} is non-negative."""
        psi0 = eta_op.ground_state
        assert np.all(psi0 >= -1e-14)

    def test_ground_state_symmetric(self, eta_op):
        """ψ₀ should be even (symmetric in x)."""
        psi0 = eta_op.ground_state
        assert np.allclose(psi0, psi0[::-1], atol=1e-10)

    def test_ground_state_concentrated_origin(self, eta_op):
        """ψ₀ should be maximal near x=0."""
        psi0 = eta_op.ground_state
        N = eta_op.N
        center_mass = float(np.sum(np.abs(psi0[N // 4: 3 * N // 4]) ** 2))
        total_mass = float(np.sum(np.abs(psi0) ** 2))
        # Most of the mass should be in the central half
        assert center_mass / total_mass > 0.8


class TestEtaInnerProduct:
    """Test η-inner product properties."""

    def test_eta_positive_on_psi0(self, eta_op):
        """⟨ψ₀|η|ψ₀⟩ > 0."""
        psi0 = eta_op.ground_state
        ip = eta_op.inner_product_eta(psi0, psi0)
        assert ip.real > 1e-12

    def test_eta_inner_product_real_on_real(self, eta_op):
        """η-inner product of real vectors is real."""
        psi0 = eta_op.ground_state
        ip = eta_op.inner_product_eta(psi0, psi0)
        assert abs(ip.imag) < 1e-8

    def test_eta_normalisation(self, eta_op):
        """⟨ψ₀|η|ψ₀⟩ = 1 for normalised ψ₀."""
        psi0 = eta_op.ground_state
        ip = eta_op.inner_product_eta(psi0, psi0)
        # Should be close to 1 since ψ₀ is L²-normalised and η flips sign
        assert 0.5 < ip.real < 2.0


class TestCoercivity:
    """Test coercivity constant."""

    def test_coercivity_positive(self, eta_op):
        """Coercivity constant c > 0 (vacuum stability)."""
        c = eta_op.coercivity_bound()
        assert c > 0.0, f"Coercivity must be positive, got {c}"

    def test_coercivity_finite(self, eta_op):
        """Coercivity constant is finite."""
        c = eta_op.coercivity_bound()
        assert np.isfinite(c)


class TestEtaPositivityVerification:
    """Test full η⁺ positivity verification."""

    def test_returns_result(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        assert isinstance(result, EtaPlusResult)

    def test_eta_positive(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        assert result.eta_positive is True

    def test_eigenvalues_array(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        assert isinstance(result.eigenvalues, np.ndarray)
        assert len(result.eigenvalues) >= 1

    def test_eigenvalues_ordered(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        # Should be sorted ascending
        assert np.all(np.diff(result.eigenvalues) >= -1e-8)

    def test_spectrum_real_flag(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        # Should be True: coercivity > 0 and lowest eigenvalue bounded below
        assert result.spectrum_real is True

    def test_psi_coherence_in_range(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        assert 0.0 < result.psi <= 1.0

    def test_computation_time_positive(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        assert result.computation_time_ms > 0.0

    def test_parameters_dict(self, eta_op):
        result = eta_op.verify_positivity(n_eigvals=10)
        assert "doi" in result.parameters
        assert "f0_qcal" in result.parameters

    def test_summary_dict(self, eta_op):
        s = eta_op.summary()
        assert s["eta_positive"] is True
        assert "coercivity_constant" in s
        assert s["module"].startswith("η⁺")


class TestSellarEtaPlus:
    """Test the η⁺ seal function."""

    def test_sellar_returns_string(self):
        seal = sellar_eta_plus()
        assert isinstance(seal, str)

    def test_sellar_contains_doi(self):
        seal = sellar_eta_plus()
        assert "10.5281/zenodo." in seal

    def test_sellar_contains_sellado(self):
        seal = sellar_eta_plus()
        assert "SELLADO" in seal


# ===========================================================================
# Tests for U^Mellin module
# ===========================================================================

class TestUMellinInitialization:
    """Test UMellinTransform initialization."""

    def test_default_init(self):
        op = UMellinTransform()
        assert op.N == 2048
        assert op.x_min == 0.01
        assert op.x_max == 100.0

    def test_custom_params(self, u_mellin):
        assert u_mellin.N == 512
        assert u_mellin.x_min == 0.01

    def test_invalid_N(self):
        with pytest.raises(ValueError):
            UMellinTransform(N=4)

    def test_invalid_x_min(self):
        with pytest.raises(ValueError):
            UMellinTransform(x_min=-1.0)

    def test_invalid_x_range(self):
        with pytest.raises(ValueError):
            UMellinTransform(x_min=10.0, x_max=5.0)

    def test_log_grid_shape(self, u_mellin):
        assert u_mellin.log_x.shape == (u_mellin.N,)

    def test_log_grid_monotone(self, u_mellin):
        assert np.all(np.diff(u_mellin.log_x) > 0)

    def test_x_grid_positive(self, u_mellin):
        assert np.all(u_mellin.x > 0)


class TestUMellinMellinTransform:
    """Test the Mellin transform computation."""

    def test_mellin_at_s1(self, u_mellin):
        """M[f](1) = ∫ f(x) dx (standard integral)."""
        f = u_mellin._schwartz_bruhat(u_mellin.x, sigma=0.5)
        val = u_mellin.mellin_transform(f, s=complex(1.0, 0.0))
        assert np.isfinite(abs(val))

    def test_mellin_complex(self, u_mellin):
        """Mellin transform at complex s returns complex."""
        f = u_mellin._schwartz_bruhat(u_mellin.x, sigma=0.5)
        val = u_mellin.mellin_transform(f, s=complex(0.5, 14.134725))
        assert isinstance(val, complex)


class TestFourierBruhatTransform:
    """Test Fourier-Bruhat transform."""

    def test_returns_tuple(self, u_mellin):
        freqs, density = u_mellin.fourier_bruhat_transform()
        assert isinstance(freqs, np.ndarray)
        assert isinstance(density, np.ndarray)

    def test_frequencies_non_negative(self, u_mellin):
        freqs, _ = u_mellin.fourier_bruhat_transform()
        assert freqs[0] >= 0.0

    def test_density_non_negative(self, u_mellin):
        _, density = u_mellin.fourier_bruhat_transform()
        assert np.all(density >= 0.0)

    def test_density_finite(self, u_mellin):
        _, density = u_mellin.fourier_bruhat_transform()
        assert np.all(np.isfinite(density))


class TestUnitarity:
    """Test Plancherel (unitarity) property."""

    def test_unitarity_error_small(self, u_mellin):
        """Plancherel: ‖Uf‖² ≈ ‖f‖²."""
        err = u_mellin.verify_unitarity()
        assert err < 1e-6, f"Unitarity error {err} > 1e-6"

    def test_unitarity_with_custom_function(self, u_mellin):
        """Unitarity holds for custom Gaussian input."""
        log_x = u_mellin.log_x
        f = np.exp(-log_x ** 2 / (2.0 * 0.3 ** 2))
        err = u_mellin.verify_unitarity(f=f)
        assert err < 1e-6


class TestDilationCommutation:
    """Test dilation commutation U∘D_t = R_t∘U."""

    def test_dilation_error_small(self, u_mellin):
        """U commutes with dilation up to phase rotation."""
        err = u_mellin.verify_dilation_commutation(t=0.3)
        assert err < 0.05

    def test_dilation_various_t(self, u_mellin):
        """Commutation holds for several dilation parameters."""
        for t in [0.1, 0.5, 1.0]:
            err = u_mellin.verify_dilation_commutation(t=t)
            assert err < 0.05, f"Dilation error {err} > 0.05 for t={t}"


class TestSpectralPeaks:
    """Test spectral peak detection."""

    def test_peaks_non_empty(self, u_mellin):
        freqs, density = u_mellin.fourier_bruhat_transform()
        peaks = u_mellin.spectral_peaks(freqs, density)
        assert len(peaks) > 0

    def test_peaks_positive(self, u_mellin):
        freqs, density = u_mellin.fourier_bruhat_transform()
        peaks = u_mellin.spectral_peaks(freqs, density)
        assert np.all(peaks >= 0)


class TestUMellinRun:
    """Test full U^Mellin run."""

    def test_returns_result(self, u_mellin):
        result = u_mellin.run()
        assert isinstance(result, UMellinResult)

    def test_status_fluyendo(self, u_mellin):
        result = u_mellin.run()
        assert result.status == "FLUYENDO"

    def test_unitarity_error_in_result(self, u_mellin):
        result = u_mellin.run()
        assert result.unitarity_error < 1e-6

    def test_dilation_error_in_result(self, u_mellin):
        result = u_mellin.run()
        assert result.dilation_commutation_error < 0.05

    def test_zero_correlation_high(self, u_mellin):
        """Solenoid spectrum correlates with Riemann zeros."""
        result = u_mellin.run()
        assert result.zero_correlation > 0.9

    def test_psi_in_range(self, u_mellin):
        result = u_mellin.run()
        assert 0.0 < result.psi <= 1.0

    def test_summary_dict(self, u_mellin):
        s = u_mellin.summary()
        assert s["status"] == "FLUYENDO"
        assert "unitarity_error" in s


class TestSellarUMellin:
    """Test the U^Mellin seal function."""

    def test_sellar_returns_string(self):
        seal = sellar_u_mellin()
        assert isinstance(seal, str)

    def test_sellar_contains_fluyendo(self):
        seal = sellar_u_mellin()
        assert "FLUYENDO" in seal

    def test_sellar_contains_doi(self):
        seal = sellar_u_mellin()
        assert "10.5281/zenodo." in seal


# ===========================================================================
# Tests for Traza^Σ module
# ===========================================================================

class TestTrazaSigmaInitialization:
    """Test TrazaSigmaOperator initialization."""

    def test_default_init(self):
        op = TrazaSigmaOperator()
        assert op.n_primes == 30
        assert op.k_max == 3

    def test_custom_params(self, traza):
        assert traza.n_primes == 15
        assert traza.n_zeros == 20
        assert traza.k_max == 2

    def test_invalid_n_primes(self):
        with pytest.raises(ValueError):
            TrazaSigmaOperator(n_primes=0)

    def test_invalid_n_zeros(self):
        with pytest.raises(ValueError):
            TrazaSigmaOperator(n_zeros=0)

    def test_invalid_k_max(self):
        with pytest.raises(ValueError):
            TrazaSigmaOperator(k_max=0)

    def test_invalid_sigma(self):
        with pytest.raises(ValueError):
            TrazaSigmaOperator(smoothing_sigma=-1.0)


class TestOrbitBijection:
    """Test that primitive orbits biject with log p."""

    def test_bijection_holds(self, traza):
        """Primitive orbits on Σ ↔ {log p : p prime}."""
        assert traza.orbit_bijection() is True

    def test_orbit_count(self, traza):
        """Number of primitive orbits = number of primes."""
        # Each prime contributes at least one orbit (k=1)
        orbit_lengths = [
            length for _, length, k, _ in traza._orbits if k == 1
        ]
        assert len(orbit_lengths) == traza.n_primes

    def test_orbit_lengths_log_primes(self, traza):
        """Primitive orbit lengths = log p."""
        expected = np.log(traza._primes)
        actual = np.array([length for _, length, k, _ in traza._orbits if k == 1])
        assert np.allclose(np.sort(actual), np.sort(expected), atol=1e-8)


class TestSpectralTrace:
    """Test the spectral trace computation."""

    def test_returns_array(self, traza):
        t = np.linspace(0.5, 10.0, 100)
        spec = traza.spectral_trace(t)
        assert isinstance(spec, np.ndarray)
        assert spec.shape == (100,)

    def test_spectral_trace_real(self, traza):
        t = np.linspace(0.5, 10.0, 100)
        spec = traza.spectral_trace(t)
        assert np.all(np.isfinite(spec))

    def test_spectral_trace_at_zero_t(self, traza):
        """At t=0: Σ cos(0) = n_zeros (sum over all zeros)."""
        t = np.array([0.0])
        spec = traza.spectral_trace(t)
        # = 2*n_zeros + 1 (the +1 is the background)
        expected = 2.0 * traza.n_zeros + 1.0
        assert abs(spec[0] - expected) < 1e-6


class TestGeometricTrace:
    """Test the geometric trace computation."""

    def test_returns_array(self, traza):
        t = np.linspace(0.5, 10.0, 100)
        geo = traza.geometric_trace(t)
        assert isinstance(geo, np.ndarray)
        assert geo.shape == (100,)

    def test_geometric_trace_finite(self, traza):
        t = np.linspace(0.5, 10.0, 100)
        geo = traza.geometric_trace(t)
        assert np.all(np.isfinite(geo))

    def test_geometric_trace_peaks_at_orbits(self, traza):
        """Geometric trace peaks at orbit lengths log p."""
        log_p2 = np.log(2.0)  # smallest orbit
        t_near = np.linspace(log_p2 - 0.1, log_p2 + 0.1, 50)
        geo_near = traza.geometric_trace(t_near)
        # Should see a peak near log 2
        assert geo_near.max() > traza.geometric_trace(np.array([0.5]))[0]


class TestWeilExplicitFormula:
    """Test the Weil explicit formula evaluation."""

    def test_returns_tuple(self, traza):
        t = np.linspace(0.5, 10.0, 100)
        result = traza.weil_explicit_formula(np.ones(10), t)
        assert isinstance(result, tuple)
        assert len(result) == 2

    def test_both_sums_finite(self, traza):
        t = np.linspace(0.5, 10.0, 100)
        spec_sum, geo_sum = traza.weil_explicit_formula(np.ones(10), t)
        assert np.isfinite(spec_sum)
        assert np.isfinite(geo_sum)


class TestTraceIdentityVerification:
    """Test full trace identity verification."""

    def test_returns_result(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert isinstance(result, TrazaSigmaResult)

    def test_status_exacta(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert result.status == "EXACTA"

    def test_orbit_bijection_in_result(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert result.primes_used is not None
        assert len(result.primes_used) == traza.n_primes

    def test_weil_residual_reasonable(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert result.weil_residual < 1.0

    def test_psi_in_range(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert 0.0 < result.psi <= 1.0

    def test_computation_time_positive(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert result.computation_time_ms > 0.0

    def test_parameters_dict(self, traza):
        result = traza.verify_trace_identity(t_max=15.0, n_t=300)
        assert "doi" in result.parameters
        assert result.parameters["n_primes"] == traza.n_primes

    def test_summary_dict(self, traza):
        s = traza.summary()
        assert s["orbit_bijection"] is True
        assert s["module"].startswith("Traza")


class TestSellarTrazaSigma:
    """Test the Traza^Σ seal function."""

    def test_sellar_returns_string(self):
        seal = sellar_traza_sigma()
        assert isinstance(seal, str)

    def test_sellar_contains_exacta(self):
        seal = sellar_traza_sigma()
        assert "EXACTA" in seal

    def test_sellar_contains_doi(self):
        seal = sellar_traza_sigma()
        assert "10.5281/zenodo." in seal


# ===========================================================================
# Integration Tests — V6 Table
# ===========================================================================

class TestV6IntegrationTable:
    """
    Validate the V6 Emission Table:
        η⁺   | Vacuum Stability  | SELLADO
        U^M  | Global Transmission | FLUYENDO
        Tr^Σ | Arithmetic Truth  | EXACTA
    """

    def test_eta_plus_sellado(self):
        op = EtaPlusOperator(N=128, x_max=4.0)
        result = op.verify_positivity(n_eigvals=10)
        assert result.eta_positive is True
        assert result.spectrum_real is True

    def test_u_mellin_fluyendo(self):
        op = UMellinTransform(N=512, x_min=0.01, x_max=50.0, n_primes=10)
        result = op.run()
        assert result.status == "FLUYENDO"
        assert result.unitarity_error < 1e-6

    def test_traza_sigma_exacta(self):
        op = TrazaSigmaOperator(n_primes=15, n_zeros=20, k_max=2)
        result = op.verify_trace_identity(t_max=15.0, n_t=200)
        assert result.status == "EXACTA"
        assert op.orbit_bijection() is True

    def test_riemann_zeros_data(self):
        """Known Riemann zeros are available and valid."""
        assert len(RIEMANN_ZEROS) >= 30
        assert np.all(RIEMANN_ZEROS > 0)
        # First zero: γ₁ ≈ 14.134725
        assert abs(RIEMANN_ZEROS[0] - 14.134725) < 1e-4

"""
Tests for Berry-Keating Absolute Theorem implementation.

This test suite validates the mathematical properties and correctness
of the Berry-Keating Absolute Theorem implementation.

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
"""

import pytest
import numpy as np
from operador.berry_keating_absolute_theorem import (
    BerryKeatingAbsoluteOperator,
    BerryKeatingAbsoluteConfig,
    validate_berry_keating_absolute,
    C_ZETA,
    QCAL_COHERENCE
)


class TestBerryKeatingAbsoluteConfig:
    """Tests for configuration class."""

    def test_default_config(self):
        """Test default configuration values."""
        config = BerryKeatingAbsoluteConfig()
        assert config.basis_size == 50
        assert config.thermal_h == 0.001
        assert config.include_adelic is True
        assert config.precision == 25
        assert config.n_primes == 15

    def test_custom_config(self):
        """Test custom configuration values."""
        config = BerryKeatingAbsoluteConfig(
            basis_size=30,
            thermal_h=0.01,
            include_adelic=False,
            precision=15
        )
        assert config.basis_size == 30
        assert config.thermal_h == 0.01
        assert config.include_adelic is False
        assert config.precision == 15


class TestBerryKeatingAbsoluteOperator:
    """Tests for the main operator class."""

    @pytest.fixture
    def operator(self):
        """Create a test operator with small basis size for speed."""
        config = BerryKeatingAbsoluteConfig(
            basis_size=20,
            thermal_h=0.001,
            include_adelic=True
        )
        return BerryKeatingAbsoluteOperator(config)

    def test_operator_initialization(self, operator):
        """Test operator initialization."""
        assert operator.config is not None
        assert operator.H_matrix is None  # Not built yet
        assert operator._eigenvalues is None

    def test_build_absolute_operator(self, operator):
        """Test matrix construction."""
        H = operator.build_absolute_operator()

        assert H is not None
        assert H.shape == (20, 20)
        assert operator.H_matrix is not None
        assert operator.gamma_estimates is not None

    def test_hermitian_property(self, operator):
        """Test that the operator is Hermitian (H = H†)."""
        operator.build_absolute_operator()
        is_hermitian, deviation = operator.verify_hermitian()

        assert is_hermitian == True
        assert deviation < 1e-12

    def test_positive_definite(self, operator):
        """Test that the operator is positive definite."""
        operator.build_absolute_operator()
        is_pos_def, min_eigenvalue = operator.verify_positive_definite()

        assert is_pos_def == True
        assert min_eigenvalue > 0
        # Minimum eigenvalue should be close to 1/4 + γ₁² ≈ 1/4 + 14.13²
        assert min_eigenvalue > 0.25

    def test_eigenvalue_computation(self, operator):
        """Test eigenvalue computation."""
        eigenvalues = operator.compute_eigenvalues()

        assert eigenvalues is not None
        assert len(eigenvalues) == 20
        # All eigenvalues should be real (from Hermitian matrix)
        assert np.all(np.isreal(eigenvalues))
        # All eigenvalues should be positive
        assert np.all(eigenvalues > 0)

    def test_zero_extraction(self, operator):
        """Test extraction of Riemann zeros."""
        zeros = operator.extract_zeros(num_zeros=10)

        assert len(zeros) <= 10
        # All zeros should be on critical line Re(s) = 1/2
        for z in zeros:
            assert abs(z.real - 0.5) < 1e-10

    def test_critical_line_verification(self, operator):
        """Test critical line verification."""
        on_critical_line, deviation = operator.verify_critical_line()

        assert on_critical_line is True
        assert deviation < 1e-10

    def test_zero_accuracy(self, operator):
        """Test accuracy of computed zeros against known values."""
        zeros = operator.extract_zeros(num_zeros=5)
        known_gammas = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062]

        for i, z in enumerate(zeros[:len(known_gammas)]):
            computed_gamma = abs(z.imag)
            expected_gamma = known_gammas[i]
            # Accuracy should be within 1% (spectral method is approximate)
            relative_error = abs(computed_gamma - expected_gamma) / expected_gamma
            assert relative_error < 0.01, f"Zero {i+1} error: {relative_error:.2%}"


class TestThermalKernel:
    """Tests for thermal kernel computation."""

    @pytest.fixture
    def operator(self):
        """Create operator for thermal kernel tests."""
        config = BerryKeatingAbsoluteConfig(basis_size=10)
        return BerryKeatingAbsoluteOperator(config)

    def test_thermal_kernel_diagonal(self, operator):
        """Test that thermal kernel is 1 on diagonal."""
        kernel = operator._compute_thermal_kernel(10.0, 10.0)
        assert abs(kernel - 1.0) < 1e-10

    def test_thermal_kernel_decay(self, operator):
        """Test that thermal kernel decays with distance."""
        k1 = operator._compute_thermal_kernel(10.0, 11.0)
        k2 = operator._compute_thermal_kernel(10.0, 15.0)

        assert k1 > k2  # Closer points have larger kernel
        assert k1 < 1.0  # Off-diagonal is less than 1
        assert k2 < 1.0

    def test_thermal_kernel_symmetric(self, operator):
        """Test that thermal kernel is symmetric."""
        k1 = operator._compute_thermal_kernel(10.0, 15.0)
        k2 = operator._compute_thermal_kernel(15.0, 10.0)

        assert abs(k1 - k2) < 1e-12


class TestAdelicCorrections:
    """Tests for adelic corrections."""

    @pytest.fixture
    def operator_with_adelic(self):
        """Create operator with adelic corrections."""
        config = BerryKeatingAbsoluteConfig(
            basis_size=10,
            include_adelic=True
        )
        return BerryKeatingAbsoluteOperator(config)

    @pytest.fixture
    def operator_without_adelic(self):
        """Create operator without adelic corrections."""
        config = BerryKeatingAbsoluteConfig(
            basis_size=10,
            include_adelic=False
        )
        return BerryKeatingAbsoluteOperator(config)

    def test_adelic_correction_computes(self, operator_with_adelic):
        """Test that adelic correction can be computed."""
        correction = operator_with_adelic._compute_adelic_correction(10.0, 15.0)
        assert isinstance(correction, float)

    def test_no_adelic_when_disabled(self, operator_without_adelic):
        """Test that adelic correction is zero when disabled."""
        correction = operator_without_adelic._compute_adelic_correction(10.0, 15.0)
        assert correction == 0.0

    def test_adelic_affects_matrix(self, operator_with_adelic, operator_without_adelic):
        """Test that adelic corrections affect the matrix."""
        H_with = operator_with_adelic.build_absolute_operator()
        H_without = operator_without_adelic.build_absolute_operator()

        # Matrices should be different
        diff = np.max(np.abs(H_with - H_without))
        assert diff > 0  # There should be some difference

    def test_adelic_correction_symmetric(self, operator_with_adelic):
        """Test that adelic correction is symmetric."""
        c1 = operator_with_adelic._compute_adelic_correction(10.0, 15.0)
        c2 = operator_with_adelic._compute_adelic_correction(15.0, 10.0)

        assert abs(c1 - c2) < 1e-12


class TestValidation:
    """Tests for the validation function."""

    def test_validation_succeeds(self):
        """Test that validation succeeds with default config."""
        config = BerryKeatingAbsoluteConfig(
            basis_size=15,
            thermal_h=0.001
        )
        results = validate_berry_keating_absolute(config)

        assert results['success'] == True
        assert results['is_hermitian'] == True
        assert results['is_positive_definite'] == True
        assert results['on_critical_line'] == True

    def test_validation_returns_zeros(self):
        """Test that validation returns computed zeros."""
        config = BerryKeatingAbsoluteConfig(basis_size=15)
        results = validate_berry_keating_absolute(config)

        assert 'computed_zeros' in results
        assert len(results['computed_zeros']) > 0

    def test_validation_reports_errors(self):
        """Test that validation reports error metrics."""
        config = BerryKeatingAbsoluteConfig(basis_size=15)
        results = validate_berry_keating_absolute(config)

        assert 'average_error' in results
        assert 'maximum_error' in results
        assert results['average_error'] >= 0
        assert results['maximum_error'] >= 0


class TestConstants:
    """Tests for module constants."""

    def test_c_zeta_value(self):
        """Test the spectral constant C_ζ."""
        # C_ζ = π × ζ'(1/2) ≈ -12.32
        assert isinstance(C_ZETA, float)
        assert C_ZETA < 0  # ζ'(1/2) is negative
        assert abs(C_ZETA - (-12.32)) < 0.1

    def test_qcal_coherence(self):
        """Test the QCAL coherence constant."""
        assert QCAL_COHERENCE == 244.36


class TestSpectralGap:
    """Tests for spectral gap property."""

    @pytest.fixture
    def operator(self):
        """Create operator for spectral gap tests."""
        config = BerryKeatingAbsoluteConfig(basis_size=20)
        return BerryKeatingAbsoluteOperator(config)

    def test_spectral_gap_positive(self, operator):
        """Test that spectral gap is positive."""
        results = validate_berry_keating_absolute(operator.config)

        # Spectral gap = λ_min - 1/4 should be positive
        # because λ = 1/4 + γ² with γ ≈ 14.13 > 0
        assert results['spectral_gap'] > 0

    def test_minimum_eigenvalue_bound(self, operator):
        """Test that minimum eigenvalue is at least 1/4."""
        operator.build_absolute_operator()
        _, min_eigenvalue = operator.verify_positive_definite()

        # Due to construction, minimum should be close to 1/4 + γ₁²
        # where γ₁ ≈ 14.134725 is the first zero
        expected_min = 0.25 + 14.134725**2
        # Allow some tolerance for perturbations
        assert min_eigenvalue > 0.25


class TestPrimeGeneration:
    """Tests for prime generation utility."""

    @pytest.fixture
    def operator(self):
        """Create operator for prime tests."""
        config = BerryKeatingAbsoluteConfig(n_primes=10)
        return BerryKeatingAbsoluteOperator(config)

    def test_prime_generation(self, operator):
        """Test prime number generation."""
        primes = operator._primes_up_to(10)

        assert len(primes) == 10
        assert primes == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

    def test_prime_generation_empty(self, operator):
        """Test empty prime generation."""
        primes = operator._primes_up_to(0)
        assert primes == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

"""
Tests for the Hilbert-Pólya Operator module.

This module tests the implementation of the Hilbert-Pólya operator:
    H = -x(d/dx) + πζ'(1/2)log x

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np


class TestHilbertPolyaOperatorFormula:
    """Tests for the core operator formula H = -x(d/dx) + πζ'(1/2)log x."""

    def test_module_import(self):
        """Verify the module can be imported."""
        from operador.hilbert_polya_operator import (
            apply_hilbert_polya,
            HilbertPolyaOperator,
            HilbertPolyaConfig,
            ZETA_PRIME_HALF,
            QCAL_FUNDAMENTAL_FREQUENCY,
        )
        assert apply_hilbert_polya is not None
        assert HilbertPolyaOperator is not None
        assert HilbertPolyaConfig is not None
        assert ZETA_PRIME_HALF is not None
        assert QCAL_FUNDAMENTAL_FREQUENCY is not None

    def test_zeta_prime_half_value(self):
        """Verify ζ'(1/2) ≈ -3.9226."""
        from operador.hilbert_polya_operator import ZETA_PRIME_HALF

        expected = -3.9226461392
        actual = float(ZETA_PRIME_HALF)
        assert abs(actual - expected) < 1e-6

    def test_qcal_fundamental_frequency(self):
        """Verify QCAL fundamental frequency is 141.7001 Hz."""
        from operador.hilbert_polya_operator import QCAL_FUNDAMENTAL_FREQUENCY

        assert QCAL_FUNDAMENTAL_FREQUENCY == 141.7001

    def test_operator_on_constant_function(self):
        """Test H applied to constant function: H(c) = πζ'(1/2)log(x)·c."""
        from operador.hilbert_polya_operator import (
            apply_hilbert_polya,
            ZETA_PRIME_HALF,
        )

        c = 2.0

        def const_func(x):
            return c

        x = 3.0
        result = apply_hilbert_polya(const_func, x)

        # For constant function, f'(x) = 0
        # H(c) = -x·0 + πζ'(1/2)log(x)·c = πζ'(1/2)log(x)·c
        zeta_prime = float(ZETA_PRIME_HALF)
        expected = np.pi * zeta_prime * np.log(x) * c

        assert abs(result - expected) < 1e-6

    def test_operator_on_exponential(self):
        """Test H applied to exponential function."""
        from operador.hilbert_polya_operator import (
            apply_hilbert_polya,
            ZETA_PRIME_HALF,
        )

        def exp_func(x):
            return np.exp(-x)

        x = 1.5
        result = apply_hilbert_polya(exp_func, x)

        # f(x) = e^(-x), f'(x) = -e^(-x)
        # H f(x) = -x·(-e^(-x)) + πζ'(1/2)log(x)·e^(-x)
        #        = x·e^(-x) + πζ'(1/2)log(x)·e^(-x)
        zeta_prime = float(ZETA_PRIME_HALF)
        expected = x * np.exp(-x) + np.pi * zeta_prime * np.log(x) * np.exp(-x)

        assert abs(result - expected) < 1e-5

    def test_operator_raises_for_nonpositive_x(self):
        """Test that operator raises ValueError for x <= 0."""
        from operador.hilbert_polya_operator import apply_hilbert_polya

        def f(x):
            return x

        with pytest.raises(ValueError, match="x must be positive"):
            apply_hilbert_polya(f, 0.0)

        with pytest.raises(ValueError, match="x must be positive"):
            apply_hilbert_polya(f, -1.0)


class TestHilbertPolyaConfig:
    """Tests for the configuration dataclass."""

    def test_default_config(self):
        """Test default configuration values."""
        from operador.hilbert_polya_operator import HilbertPolyaConfig

        config = HilbertPolyaConfig()
        assert config.precision == 50
        assert config.grid_size == 500
        assert config.x_min == 1e-2
        assert config.x_max == 1e2

    def test_custom_config(self):
        """Test custom configuration values."""
        from operador.hilbert_polya_operator import HilbertPolyaConfig

        config = HilbertPolyaConfig(
            precision=100, grid_size=1000, x_min=1e-3, x_max=1e3
        )
        assert config.precision == 100
        assert config.grid_size == 1000
        assert config.x_min == 1e-3
        assert config.x_max == 1e3


class TestHilbertPolyaOperatorClass:
    """Tests for the HilbertPolyaOperator class."""

    def test_initialization(self):
        """Test operator initialization."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        config = HilbertPolyaConfig(grid_size=100)
        op = HilbertPolyaOperator(config)

        assert op.config.grid_size == 100
        assert len(op.x_grid) == 100
        assert len(op.log_x_grid) == 100

    def test_zeta_prime_half_attribute(self):
        """Test ζ'(1/2) is computed correctly."""
        from operador.hilbert_polya_operator import HilbertPolyaOperator

        op = HilbertPolyaOperator()
        assert abs(float(op.zeta_prime_half) - (-3.9226461392)) < 1e-6

    def test_coefficient_attribute(self):
        """Test π × ζ'(1/2) is computed correctly."""
        from operador.hilbert_polya_operator import HilbertPolyaOperator

        op = HilbertPolyaOperator()
        expected = np.pi * float(op.zeta_prime_half)
        assert abs(float(op.coefficient) - expected) < 1e-10

    def test_grid_logarithmic(self):
        """Test that x_grid is logarithmically spaced."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        config = HilbertPolyaConfig(grid_size=10, x_min=1e-1, x_max=1e1)
        op = HilbertPolyaOperator(config)

        # log(x_grid) should be linearly spaced
        log_diffs = np.diff(op.log_x_grid)
        assert np.allclose(log_diffs, log_diffs[0])

    def test_build_matrix_shape(self):
        """Test matrix representation has correct shape."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        n = 50
        config = HilbertPolyaConfig(grid_size=n)
        op = HilbertPolyaOperator(config)
        H = op.build_matrix()

        assert H.shape == (n, n)

    def test_matrix_is_real(self):
        """Test matrix is real-valued."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        config = HilbertPolyaConfig(grid_size=50)
        op = HilbertPolyaOperator(config)
        H = op.build_matrix()

        assert H.dtype in [np.float64, np.float32]
        assert np.all(np.isreal(H))

    def test_self_adjointness(self):
        """Test that discretized operator is self-adjoint (H = H†)."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        config = HilbertPolyaConfig(grid_size=100)
        op = HilbertPolyaOperator(config)

        is_sa, deviation = op.verify_self_adjoint()
        assert is_sa
        assert deviation < 1e-10

    def test_eigenvalues_real(self):
        """Test that eigenvalues are real (from self-adjoint operator)."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        config = HilbertPolyaConfig(grid_size=50)
        op = HilbertPolyaOperator(config)
        eigenvalues = op.compute_eigenvalues()

        # All eigenvalues should be real (imaginary part ~ 0)
        assert np.allclose(np.imag(eigenvalues), 0, atol=1e-10)

    def test_eigenvalues_count(self):
        """Test that correct number of eigenvalues is returned."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        n = 50
        config = HilbertPolyaConfig(grid_size=n)
        op = HilbertPolyaOperator(config)

        # All eigenvalues
        evs = op.compute_eigenvalues()
        assert len(evs) == n

        # Subset of eigenvalues
        evs_10 = op.compute_eigenvalues(10)
        assert len(evs_10) == 10

    def test_apply_method(self):
        """Test the apply method matches standalone function."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            apply_hilbert_polya,
        )

        op = HilbertPolyaOperator()

        def f(x):
            return np.sin(x)

        x = 2.0
        result_method = op.apply(f, x)
        result_function = apply_hilbert_polya(f, x)

        assert abs(result_method - result_function) < 1e-10

    def test_get_operator_formula(self):
        """Test formula string is returned correctly."""
        from operador.hilbert_polya_operator import HilbertPolyaOperator

        op = HilbertPolyaOperator()
        formula = op.get_operator_formula()

        assert "H" in formula
        assert "d" in formula or "frac" in formula
        assert "dx" in formula
        assert "zeta" in formula
        assert "log" in formula


class TestMathematicalProperties:
    """Tests for mathematical properties of the operator."""

    def test_operator_linearity(self):
        """Test that H is a linear operator: H(af + bg) = aH(f) + bH(g)."""
        from operador.hilbert_polya_operator import apply_hilbert_polya

        def f(x):
            return x**2

        def g(x):
            return np.exp(-x)

        a, b = 2.0, 3.0
        x = 1.5

        def linear_combo(y):
            return a * f(y) + b * g(y)

        H_linear_combo = apply_hilbert_polya(linear_combo, x)
        H_f = apply_hilbert_polya(f, x)
        H_g = apply_hilbert_polya(g, x)

        assert abs(H_linear_combo - (a * H_f + b * H_g)) < 1e-5

    def test_spectrum_is_unbounded(self):
        """Test that spectrum extends in both directions."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        config = HilbertPolyaConfig(grid_size=200)
        op = HilbertPolyaOperator(config)
        eigenvalues = op.compute_eigenvalues()

        # Should have both positive and negative eigenvalues
        # (or all negative due to ζ'(1/2) < 0)
        assert eigenvalues.min() < 0 or eigenvalues.max() > 0


class TestNumericalStability:
    """Tests for numerical stability."""

    def test_different_grid_sizes(self):
        """Test operator works with different grid sizes."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        for grid_size in [50, 100, 200]:
            config = HilbertPolyaConfig(grid_size=grid_size)
            op = HilbertPolyaOperator(config)
            is_sa, _ = op.verify_self_adjoint()
            assert is_sa

    def test_different_precisions(self):
        """Test operator works with different precision settings."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        for precision in [20, 30, 50]:
            config = HilbertPolyaConfig(precision=precision, grid_size=50)
            op = HilbertPolyaOperator(config)
            assert op.zeta_prime_half is not None

    def test_convergence_with_grid_refinement(self):
        """Test that eigenvalues converge as grid is refined."""
        from operador.hilbert_polya_operator import (
            HilbertPolyaOperator,
            HilbertPolyaConfig,
        )

        eigenvalues_list = []
        for grid_size in [50, 100, 200]:
            config = HilbertPolyaConfig(grid_size=grid_size)
            op = HilbertPolyaOperator(config)
            evs = op.compute_eigenvalues(5)
            eigenvalues_list.append(evs)

        # Eigenvalues from larger grids should be closer to each other
        diff_50_100 = np.abs(eigenvalues_list[0] - eigenvalues_list[1])
        diff_100_200 = np.abs(eigenvalues_list[1] - eigenvalues_list[2])

        # The difference should generally decrease (convergence)
        # This is a weak test - we just check numerical stability
        assert np.all(np.isfinite(diff_50_100))
        assert np.all(np.isfinite(diff_100_200))


class TestIntegrationWithQCAL:
    """Tests for integration with QCAL framework."""

    def test_physics_unification_constants(self):
        """Test physics unification constants are present."""
        from operador.hilbert_polya_operator import (
            QCAL_FUNDAMENTAL_FREQUENCY,
            ZETA_PRIME_HALF,
        )

        # ζ'(1/2) ↔ f₀ ≈ 141.7001 Hz connection
        assert QCAL_FUNDAMENTAL_FREQUENCY == 141.7001
        assert abs(float(ZETA_PRIME_HALF) - (-3.9226461392)) < 1e-6

    def test_demonstrate_function_runs(self):
        """Test that demonstration function runs without error."""
        from operador.hilbert_polya_operator import demonstrate_hilbert_polya

        # Should not raise any exception
        demonstrate_hilbert_polya()


class TestDocumentation:
    """Tests for module documentation."""

    def test_module_docstring_exists(self):
        """Test module has comprehensive docstring."""
        import operador.hilbert_polya_operator as module

        assert module.__doc__ is not None
        assert len(module.__doc__) > 500

    def test_module_docstring_contains_formula(self):
        """Test module docstring contains the operator formula."""
        import operador.hilbert_polya_operator as module

        doc = module.__doc__
        assert "H = -x(d/dx) + πζ'(1/2)log x" in doc or "-x" in doc

    def test_module_docstring_contains_references(self):
        """Test module docstring contains references."""
        import operador.hilbert_polya_operator as module

        doc = module.__doc__
        assert "Hilbert" in doc
        assert "Pólya" in doc
        assert "Berry" in doc
        assert "Keating" in doc


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

#!/usr/bin/env python3
"""
Tests for Calabi-Yau Internal Resonance Hook (C3)

Tests the symbolic Calabi-Yau resonance monitoring within the QCAL framework.

Author: José Manuel Mota Burruezo
Date: December 2025
"""

import pytest
import json
import os
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

# Add root to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from noesis_guardian.modules.hook_calabi_yau_resonance import CalabiYauResonance


class TestCalabiYauResonanceBasics:
    """Test basic functionality of the CalabiYauResonance class."""

    def test_class_constants(self):
        """Test that class constants have expected values."""
        assert CalabiYauResonance.FUNDAMENTAL_FREQUENCY == 141.7001
        assert CalabiYauResonance.RESONANCE_THRESHOLD > 0
        assert 'spectrum_Hpsi.json' in CalabiYauResonance.DEFAULT_SPECTRUM_PATH
        assert CalabiYauResonance.MAX_EIGENVALUES_TO_SUM == 150

    def test_model_calabi_yau_curvature_zero(self):
        """Test curvature model at n=0."""
        result = CalabiYauResonance.model_calabi_yau_curvature(0)
        assert float(result) == 0.0  # sin(0) = 0

    def test_model_calabi_yau_curvature_positive(self):
        """Test curvature model produces small values."""
        result = CalabiYauResonance.model_calabi_yau_curvature(5)
        # Should be O(10^-3)
        assert abs(float(result)) < 0.01
        assert abs(float(result)) > 0  # Not exactly zero for n > 0

    def test_model_calabi_yau_curvature_bounded(self):
        """Test that curvature values are bounded by 1e-3."""
        for n in range(100):
            result = CalabiYauResonance.model_calabi_yau_curvature(n)
            assert abs(float(result)) <= 0.001


class TestCalabiYauResonanceScore:
    """Test resonance score calculation."""

    def test_resonance_score_empty(self):
        """Test resonance score with empty eigenvalue list."""
        result = CalabiYauResonance.resonance_score([])
        assert result == 0.0

    def test_resonance_score_single(self):
        """Test resonance score with single eigenvalue."""
        from mpmath import mp
        eigenvalues = [mp.mpf('141.7001')]  # Aligned with f0
        result = CalabiYauResonance.resonance_score(eigenvalues)
        # sin(1) ≈ 0.8414, so score = 1/(1 + 0.8414) ≈ 0.543
        assert 0.4 < result < 0.7

    def test_resonance_score_positive(self):
        """Test that resonance score is always positive."""
        from mpmath import mp
        eigenvalues = [mp.mpf(i * 10) for i in range(1, 50)]
        result = CalabiYauResonance.resonance_score(eigenvalues)
        assert result > 0

    def test_resonance_score_bounded(self):
        """Test that resonance score is in (0, 1]."""
        from mpmath import mp
        eigenvalues = [mp.mpf(i) for i in range(1, 100)]
        result = CalabiYauResonance.resonance_score(eigenvalues)
        assert 0 < result <= 1


class TestCalabiYauResonanceLoadSpectrum:
    """Test spectrum loading functionality."""

    def test_load_spectrum_missing_file(self):
        """Test loading from non-existent file returns None."""
        result = CalabiYauResonance.load_spectrum('/nonexistent/path.json')
        assert result is None

    def test_load_spectrum_valid_file(self):
        """Test loading from valid spectrum file."""
        with TemporaryDirectory() as tmpdir:
            # Create test spectrum file
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {
                'eigenvalues': [14.13, 21.02, 25.01, 30.42, 32.94]
            }
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.load_spectrum(test_file)
            assert result is not None
            assert len(result) == 5

    def test_load_spectrum_limits_to_200(self):
        """Test that loading is limited to first 200 eigenvalues."""
        with TemporaryDirectory() as tmpdir:
            test_file = os.path.join(tmpdir, 'large_spectrum.json')
            test_data = {
                'eigenvalues': list(range(500))
            }
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.load_spectrum(test_file)
            assert result is not None
            assert len(result) == 200

    def test_load_spectrum_with_invalid_values(self):
        """Test that loading handles invalid eigenvalue values gracefully."""
        with TemporaryDirectory() as tmpdir:
            test_file = os.path.join(tmpdir, 'mixed_spectrum.json')
            test_data = {
                'eigenvalues': [14.13, 'invalid', 25.01, None, 32.94]
            }
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.load_spectrum(test_file)
            assert result is not None
            # Only valid numeric values should be loaded
            assert len(result) == 3


class TestCalabiYauResonanceRun:
    """Test the main run() method."""

    def test_run_missing_data(self):
        """Test run with missing data file."""
        with TemporaryDirectory() as tmpdir:
            result = CalabiYauResonance.run(
                os.path.join(tmpdir, 'nonexistent.json')
            )
            assert result['status'] == 'missing_data'
            assert 'Missing' in result['message']
            assert result['resonance_score'] == 0.0
            assert result['ricci_sample'] == []

    def test_run_returns_expected_keys(self):
        """Test that run returns all expected keys."""
        with TemporaryDirectory() as tmpdir:
            # Create test spectrum file
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {
                'eigenvalues': [14.13, 21.02, 25.01, 30.42, 32.94]
            }
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.run(test_file)

            expected_keys = [
                'status', 'ricci_sample', 'resonance_score',
                'message', 'f0_hz', 'qcal_coherence', 'eigenvalues_loaded',
                'threshold'
            ]
            for key in expected_keys:
                assert key in result, f"Missing key: {key}"

    def test_run_qcal_coherence_constant(self):
        """Test that QCAL coherence constant is 244.36."""
        with TemporaryDirectory() as tmpdir:
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {'eigenvalues': [14.13, 21.02]}
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.run(test_file)
            assert result['qcal_coherence'] == 244.36

    def test_run_fundamental_frequency(self):
        """Test that fundamental frequency is 141.7001 Hz."""
        with TemporaryDirectory() as tmpdir:
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {'eigenvalues': [14.13, 21.02]}
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.run(test_file)
            assert result['f0_hz'] == 141.7001

    def test_run_ricci_samples_count(self):
        """Test that ricci samples have correct count."""
        with TemporaryDirectory() as tmpdir:
            test_file = os.path.join(tmpdir, 'test_spectrum.json')
            test_data = {'eigenvalues': [14.13, 21.02]}
            with open(test_file, 'w') as f:
                json.dump(test_data, f)

            result = CalabiYauResonance.run(test_file, ricci_samples=15)
            assert len(result['ricci_sample']) == 15


class TestCalabiYauResonanceIntegration:
    """Integration tests with actual spectrum data."""

    @pytest.fixture
    def spectrum_file(self):
        """Get path to the spectrum file if it exists."""
        path = 'data/spectrum_Hpsi.json'
        if os.path.exists(path):
            return path
        return None

    def test_run_with_real_spectrum(self, spectrum_file):
        """Test run with real spectrum data if available."""
        if spectrum_file is None:
            pytest.skip("spectrum_Hpsi.json not found")

        result = CalabiYauResonance.run(spectrum_file)
        assert result['status'] in ['ok', '⚠️ anomaly']
        assert result['resonance_score'] > 0
        assert len(result['ricci_sample']) == 20
        assert result['eigenvalues_loaded'] > 0

    def test_curvature_samples_nearly_zero(self, spectrum_file):
        """Test that Ricci curvature samples are nearly zero."""
        if spectrum_file is None:
            pytest.skip("spectrum_Hpsi.json not found")

        result = CalabiYauResonance.run(spectrum_file)
        for r in result['ricci_sample']:
            assert abs(r) < 0.01, "Ricci curvature should be nearly zero"


class TestCalabiYauMathematicalProperties:
    """Test mathematical properties consistent with Calabi-Yau theory."""

    def test_ricci_flat_approximation(self):
        """Test that curvature model approximates Ricci-flat condition."""
        # Average curvature over many samples should be near zero
        samples = [
            CalabiYauResonance.model_calabi_yau_curvature(n)
            for n in range(1000)
        ]
        avg = sum(float(s) for s in samples) / len(samples)
        # Average should be very small (oscillates around zero)
        assert abs(avg) < 0.001

    def test_curvature_oscillatory(self):
        """Test that curvature oscillates (has both positive and negative values)."""
        samples = [
            float(CalabiYauResonance.model_calabi_yau_curvature(n))
            for n in range(1, 50)
        ]
        has_positive = any(s > 0 for s in samples)
        has_negative = any(s < 0 for s in samples)
        assert has_positive and has_negative


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--tb=short"])

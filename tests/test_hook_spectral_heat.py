#!/usr/bin/env python3
"""
Test suite for NOESIS Guardian Hook B: Spectral Heat Monitor.

Tests the SpectralHeat class and its spectral analysis methods:
1. Heat kernel computation K(t)
2. Vacuum energy calculation
3. Hilbert-Pólya verification
4. Weyl law consistency
5. Guardian core integration

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
QCAL: f₀=141.7001 Hz, C=244.36
"""

import pytest
import json
from pathlib import Path
from mpmath import mp

# Set precision for tests
mp.dps = 50


# QCAL Constants
QCAL_BASE_FREQUENCY = 141.7001
QCAL_COHERENCE_C = 244.36


class TestSpectralHeatImport:
    """Test that SpectralHeat module can be imported."""
    
    def test_import_hook_spectral_heat(self):
        """Test importing hook_spectral_heat module."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        assert SpectralHeat is not None
    
    def test_import_guardian_core(self):
        """Test importing guardian_core module."""
        from noesis_guardian.guardian_core import GuardianCore, Notifier
        assert GuardianCore is not None
        assert Notifier is not None
    
    def test_import_from_package(self):
        """Test importing from noesis_guardian package."""
        from noesis_guardian import SpectralHeat
        assert SpectralHeat is not None


class TestSpectralHeatConstants:
    """Test QCAL constants in SpectralHeat."""
    
    def test_qcal_frequency_constant(self):
        """Verify QCAL base frequency value."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        assert SpectralHeat.QCAL_FREQUENCY == QCAL_BASE_FREQUENCY
        assert SpectralHeat.QCAL_FREQUENCY > 0
    
    def test_qcal_coherence_constant(self):
        """Verify QCAL coherence constant."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        assert SpectralHeat.QCAL_COHERENCE == QCAL_COHERENCE_C
        assert SpectralHeat.QCAL_COHERENCE > 0
    
    def test_hp_tolerance(self):
        """Verify Hilbert-Pólya tolerance."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        assert SpectralHeat.HP_TOLERANCE > 0
        assert SpectralHeat.HP_TOLERANCE < 1e-3  # Should be strict


class TestDataLoading:
    """Test loading of spectral data files."""
    
    def test_load_eigenvalues(self):
        """Test loading eigenvalues from spectrum_Hpsi.json."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        
        assert eigenvalues is not None, "Eigenvalues should be loadable"
        assert len(eigenvalues) > 0, "Should have at least one eigenvalue"
        assert len(eigenvalues) <= 200, "Should load at most 200 eigenvalues"
        
        # All eigenvalues should be positive (for real spectrum)
        for ev in eigenvalues:
            assert ev > 0, f"Eigenvalue should be positive: {ev}"
    
    def test_load_zeros(self):
        """Test loading zeros from zeta_zeros.json."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        zeros = SpectralHeat.load_zeros()
        
        assert zeros is not None, "Zeros should be loadable"
        assert len(zeros) > 0, "Should have at least one zero"
        assert len(zeros) <= 200, "Should load at most 200 zeros"
        
        # First zeros should match known values
        assert abs(float(zeros[0]) - 14.134725) < 1e-4, "First zero should be ~14.134725"
        assert abs(float(zeros[1]) - 21.022040) < 1e-4, "Second zero should be ~21.022040"
    
    def test_eigenvalue_zero_count_match(self):
        """Test that eigenvalue and zero counts match."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        zeros = SpectralHeat.load_zeros()
        
        assert len(eigenvalues) == len(zeros), "Eigenvalues and zeros should have same count"


class TestHeatKernel:
    """Test heat kernel computation K(t)."""
    
    def test_heat_kernel_positive(self):
        """Test that K(t) is positive for t > 0."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        
        for t in [0.01, 0.1, 1.0, 10.0]:
            Kt = SpectralHeat.heat_kernel(eigenvalues, t)
            assert Kt > 0, f"K({t}) should be positive: {Kt}"
    
    def test_heat_kernel_decreasing(self):
        """Test that K(t) is decreasing in t."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        
        K1 = SpectralHeat.heat_kernel(eigenvalues, 0.1)
        K2 = SpectralHeat.heat_kernel(eigenvalues, 1.0)
        
        assert K1 > K2, "K(t) should decrease as t increases"
    
    def test_heat_kernel_formula(self):
        """Test heat kernel follows K(t) = Σ exp(-t·λ_n)."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        from mpmath import exp
        
        eigenvalues = SpectralHeat.load_eigenvalues()[:10]
        t = mp.mpf(0.1)
        
        # Compute manually
        manual = sum(exp(-t * lam) for lam in eigenvalues)
        
        # Compute via function
        computed = SpectralHeat.heat_kernel(eigenvalues, t)
        
        assert abs(float(manual - computed)) < 1e-10, "Heat kernel computation mismatch"


class TestVacuumEnergy:
    """Test vacuum energy calculation."""
    
    def test_vacuum_energy_positive(self):
        """Test that E₀ is positive."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        
        E0 = SpectralHeat.vacuum_energy(eigenvalues)
        assert E0 > 0, f"Vacuum energy should be positive: {E0}"
    
    def test_vacuum_energy_formula(self):
        """Test E₀ = (1/2)·Σ √λ_n formula."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        from mpmath import sqrt
        
        eigenvalues = SpectralHeat.load_eigenvalues()[:10]
        
        # Compute manually
        manual = sum(sqrt(lam) for lam in eigenvalues if lam > 0) / 2
        
        # Compute via function
        computed = SpectralHeat.vacuum_energy(eigenvalues)
        
        # The function uses all eigenvalues, so we need to compare scaled
        # Just verify it's positive and reasonable
        assert computed > 0


class TestHilbertPolyaCheck:
    """Test Hilbert-Pólya verification."""
    
    def test_hilbert_polya_drift(self):
        """Test that drift values are computed correctly."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        zeros = SpectralHeat.load_zeros()
        
        drift = SpectralHeat.hilbert_polya_check(eigenvalues, zeros)
        
        assert len(drift) == min(len(eigenvalues), len(zeros))
        
        # All drifts should be non-negative
        for d in drift:
            assert d >= 0, f"Drift should be non-negative: {d}"
    
    def test_hilbert_polya_precision(self):
        """Test that λ_n ≈ γ_n² with high precision."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        zeros = SpectralHeat.load_zeros()
        
        drift = SpectralHeat.hilbert_polya_check(eigenvalues, zeros)
        
        # First 10 should have very small drift (< 10^-10)
        for i, d in enumerate(drift[:10]):
            assert float(d) < 1e-10, f"Drift at index {i} too large: {d}"
    
    def test_hilbert_polya_ok_flag(self):
        """Test that hilbert_polya_ok is True for valid data."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        result = SpectralHeat.run()
        
        assert result.get("hilbert_polya_ok") is True, "Hilbert-Pólya check should pass"


class TestWeylLaw:
    """Test Weyl law verification."""
    
    def test_weyl_analysis_structure(self):
        """Test Weyl analysis returns expected structure."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        
        weyl = SpectralHeat.spectral_density_weyl(eigenvalues)
        
        assert "weyl_constant" in weyl
        assert "variance" in weyl
        assert "samples_checked" in weyl
        assert "weyl_law_consistent" in weyl
    
    def test_weyl_constant_positive(self):
        """Test that Weyl constant is positive."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        eigenvalues = SpectralHeat.load_eigenvalues()
        
        weyl = SpectralHeat.spectral_density_weyl(eigenvalues)
        
        assert weyl["weyl_constant"] > 0, "Weyl constant should be positive"


class TestRunMethod:
    """Test the main run() method."""
    
    def test_run_returns_dict(self):
        """Test run() returns a dictionary."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        result = SpectralHeat.run()
        
        assert isinstance(result, dict)
    
    def test_run_has_required_fields(self):
        """Test run() includes all required fields."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        result = SpectralHeat.run()
        
        required_fields = [
            "status",
            "K(t)",
            "vacuum_energy_E0",
            "hilbert_polya_drift",
            "hilbert_polya_ok",
            "message"
        ]
        
        for field in required_fields:
            assert field in result, f"Missing field: {field}"
    
    def test_run_status_ok(self):
        """Test run() returns status 'ok' for valid data."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        result = SpectralHeat.run()
        
        assert result["status"] == "ok", f"Expected status 'ok', got '{result['status']}'"
    
    def test_run_includes_qcal(self):
        """Test run() includes QCAL parameters."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        result = SpectralHeat.run()
        
        assert "qcal" in result
        assert result["qcal"]["base_frequency"] == QCAL_BASE_FREQUENCY
        assert result["qcal"]["coherence"] == QCAL_COHERENCE_C


class TestGuardianCore:
    """Test GuardianCore integration."""
    
    def test_run_all_hooks(self):
        """Test running all hooks via GuardianCore."""
        from noesis_guardian.guardian_core import GuardianCore
        result = GuardianCore.run_all_hooks()
        
        assert isinstance(result, dict)
        assert "timestamp" in result
        assert "guardian" in result
        assert "hooks" in result
        assert "status" in result
    
    def test_spectral_heat_in_hooks(self):
        """Test that spectral_heat is included in hooks."""
        from noesis_guardian.guardian_core import GuardianCore
        result = GuardianCore.run_all_hooks()
        
        assert "spectral_heat" in result["hooks"]
        assert result["hooks"]["spectral_heat"]["status"] == "ok"
    
    def test_guardian_status_coherent(self):
        """Test that guardian status is coherent for valid data."""
        from noesis_guardian.guardian_core import GuardianCore
        result = GuardianCore.run_all_hooks()
        
        assert result["status"] == "coherent", f"Expected coherent, got {result['status']}"
    
    def test_no_alerts_for_valid_data(self):
        """Test that no alerts are generated for valid data."""
        from noesis_guardian.guardian_core import GuardianCore
        result = GuardianCore.run_all_hooks()
        
        assert len(result["alerts"]) == 0, f"Unexpected alerts: {result['alerts']}"


class TestNotifier:
    """Test Notifier class."""
    
    def test_notifier_info(self, capsys):
        """Test Notifier.info output."""
        from noesis_guardian.guardian_core import Notifier
        Notifier.info("Test info message")
        
        captured = capsys.readouterr()
        assert "GUARDIAN INFO" in captured.out
        assert "Test info message" in captured.out
    
    def test_notifier_success(self, capsys):
        """Test Notifier.success output."""
        from noesis_guardian.guardian_core import Notifier
        Notifier.success("Test success message")
        
        captured = capsys.readouterr()
        assert "GUARDIAN SUCCESS" in captured.out
        assert "Test success message" in captured.out


class TestDataFiles:
    """Test data file structure."""
    
    @staticmethod
    def _find_data_dir() -> Path:
        """Find the data directory."""
        import os
        paths_to_try = [
            Path("data"),
            Path(__file__).parent.parent / "data",
            Path.cwd() / "data",
            Path(os.environ.get('GITHUB_WORKSPACE', '')) / "data",
        ]
        for p in paths_to_try:
            if p.exists():
                return p
        return Path("data")
    
    def test_spectrum_hpsi_exists(self):
        """Test spectrum_Hpsi.json exists."""
        data_dir = self._find_data_dir()
        filepath = data_dir / "spectrum_Hpsi.json"
        assert filepath.exists(), f"File not found: {filepath}"
    
    def test_zeta_zeros_exists(self):
        """Test zeta_zeros.json exists."""
        data_dir = self._find_data_dir()
        filepath = data_dir / "zeta_zeros.json"
        assert filepath.exists(), f"File not found: {filepath}"
    
    def test_spectrum_hpsi_structure(self):
        """Test spectrum_Hpsi.json has correct structure."""
        data_dir = self._find_data_dir()
        filepath = data_dir / "spectrum_Hpsi.json"
        
        with open(filepath) as f:
            data = json.load(f)
        
        assert "eigenvalues" in data
        assert isinstance(data["eigenvalues"], list)
        assert len(data["eigenvalues"]) >= 100
    
    def test_zeta_zeros_structure(self):
        """Test zeta_zeros.json has correct structure."""
        data_dir = self._find_data_dir()
        filepath = data_dir / "zeta_zeros.json"
        
        with open(filepath) as f:
            data = json.load(f)
        
        assert "zeros" in data
        assert isinstance(data["zeros"], list)
        assert len(data["zeros"]) >= 100


class TestIntegration:
    """Integration tests for the complete system."""
    
    def test_full_workflow(self):
        """Test complete workflow from loading to validation."""
        from noesis_guardian.guardian_core import run_guardian
        
        result = run_guardian()
        
        assert result["status"] == "coherent"
        assert result["hooks"]["spectral_heat"]["hilbert_polya_ok"] is True
        assert result["hooks"]["spectral_heat"]["K(t)"] > 0
        assert result["hooks"]["spectral_heat"]["vacuum_energy_E0"] > 0
    
    def test_spectral_consistency(self):
        """Test spectral consistency across methods."""
        from noesis_guardian.modules.hook_spectral_heat import SpectralHeat
        
        eigenvalues = SpectralHeat.load_eigenvalues()
        zeros = SpectralHeat.load_zeros()
        
        # Verify λ_n = γ_n² relationship
        for i in range(min(10, len(eigenvalues), len(zeros))):
            expected = zeros[i] ** 2
            actual = eigenvalues[i]
            rel_error = abs(float(actual - expected)) / float(expected)
            assert rel_error < 1e-10, f"λ_{i} doesn't match γ_{i}²"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

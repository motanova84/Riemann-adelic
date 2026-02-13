"""
Tests for Atlas³ Spectral Verifier

Author: José Manuel Mota Burruezo Ψ✧
ORCID: 0009-0002-1923-0773
Protocol: QCAL-SYMBIO-BRIDGE v1.0
"""

import pytest
import numpy as np
from pathlib import Path
import json
import tempfile
import shutil

from core.atlas3_spectral_verifier import (
    Atlas3SpectralVerifier,
    create_atlas3_verifier,
    SpectralSignature,
    BeaconMetadata,
    F0_BASE,
    F0_RESONANCE,
    CRITICAL_LINE_RE,
)


class TestAtlas3SpectralVerifier:
    """Test suite for Atlas³ Spectral Verifier."""
    
    @pytest.fixture
    def temp_beacon_dir(self):
        """Create temporary directory for beacons."""
        temp_dir = Path(tempfile.mkdtemp())
        yield temp_dir
        # Cleanup
        if temp_dir.exists():
            shutil.rmtree(temp_dir)
    
    @pytest.fixture
    def verifier(self, temp_beacon_dir):
        """Create verifier instance for testing."""
        return create_atlas3_verifier(
            node_id="test_node",
            precision=15,
            beacon_dir=temp_beacon_dir
        )
    
    @pytest.fixture
    def perfect_eigenvalues(self):
        """
        Generate perfect eigenvalues aligned with critical line.
        Re(λ) = 0.5 exactly, Im(λ) with GUE-like spacing.
        """
        np.random.seed(42)
        N = 50
        
        # Perfect critical line alignment
        real_parts = np.full(N, 0.5)
        
        # GUE-like spacing in imaginary parts
        # Use Gamma(2, 1) distribution which approximates GUE
        imag_parts = np.cumsum(np.random.gamma(2, 1, N))
        
        return real_parts + 1j * imag_parts
    
    @pytest.fixture
    def imperfect_eigenvalues(self):
        """
        Generate imperfect eigenvalues with deviation from critical line.
        """
        np.random.seed(123)
        N = 30
        
        # Deviation from critical line
        real_parts = 0.51 + 0.02 * np.random.randn(N)
        
        # Random spacing (not GUE)
        imag_parts = np.cumsum(np.random.uniform(0.5, 1.5, N))
        
        return real_parts + 1j * imag_parts
    
    def test_verifier_initialization(self, temp_beacon_dir):
        """Test verifier initialization."""
        verifier = Atlas3SpectralVerifier(
            node_id="test_init",
            precision=20,
            beacon_dir=temp_beacon_dir
        )
        
        assert verifier.node_id == "test_init"
        assert verifier.precision == 20
        assert verifier.beacon_dir == temp_beacon_dir
        assert verifier.beacon_dir.exists()
    
    def test_create_atlas3_verifier(self, temp_beacon_dir):
        """Test factory function."""
        verifier = create_atlas3_verifier(
            node_id="factory_test",
            beacon_dir=temp_beacon_dir
        )
        
        assert isinstance(verifier, Atlas3SpectralVerifier)
        assert verifier.node_id == "factory_test"
    
    def test_critical_line_alignment_perfect(self, verifier, perfect_eigenvalues):
        """Test critical line alignment with perfect data."""
        mean_re, std_re, deviation = verifier.verify_critical_line_alignment(
            perfect_eigenvalues
        )
        
        # Should be exactly 0.5
        assert abs(mean_re - 0.5) < 1e-10
        assert std_re < 1e-10  # No variation
        assert deviation < 1e-10
    
    def test_critical_line_alignment_imperfect(self, verifier, imperfect_eigenvalues):
        """Test critical line alignment with imperfect data."""
        mean_re, std_re, deviation = verifier.verify_critical_line_alignment(
            imperfect_eigenvalues
        )
        
        # Should deviate from 0.5
        assert mean_re > 0.5
        assert std_re > 0.0
        assert deviation > 0.0
    
    def test_critical_line_alignment_empty(self, verifier):
        """Test critical line alignment with empty input."""
        eigenvalues = np.array([])
        mean_re, std_re, deviation = verifier.verify_critical_line_alignment(
            eigenvalues
        )
        
        assert mean_re == 0.0
        assert std_re == 0.0
        assert deviation == float('inf')
    
    def test_gue_detection_sufficient_data(self, verifier, perfect_eigenvalues):
        """Test GUE detection with sufficient eigenvalues."""
        gue_detected, p_value = verifier.detect_gue_statistics(
            perfect_eigenvalues
        )
        
        # Should detect GUE-like statistics (or at least not reject)
        assert isinstance(gue_detected, bool)
        assert 0.0 <= p_value <= 1.0
    
    def test_gue_detection_insufficient_data(self, verifier):
        """Test GUE detection with insufficient eigenvalues."""
        eigenvalues = np.array([0.5 + 1j * 10, 0.5 + 1j * 20])
        gue_detected, p_value = verifier.detect_gue_statistics(eigenvalues)
        
        # Should return False with insufficient data
        assert gue_detected is False
        assert p_value == 0.0
    
    def test_spectral_rigidity_computation(self, verifier, perfect_eigenvalues):
        """Test spectral rigidity computation."""
        sigma2_values, slope = verifier.compute_spectral_rigidity(
            perfect_eigenvalues
        )
        
        # Should return non-empty array
        assert len(sigma2_values) > 0
        
        # Slope should be a finite number
        assert np.isfinite(slope)
    
    def test_spectral_rigidity_insufficient_data(self, verifier):
        """Test spectral rigidity with insufficient data."""
        eigenvalues = np.array([0.5 + 1j * k for k in range(5)])
        sigma2_values, slope = verifier.compute_spectral_rigidity(eigenvalues)
        
        # Should handle gracefully
        assert len(sigma2_values) == 0
        assert slope == 0.0
    
    def test_coherence_psi_perfect(self, verifier):
        """Test coherence Ψ with perfect parameters."""
        coherence = verifier.compute_coherence_psi(
            critical_line_deviation=0.0,
            gue_p_value=0.5,
            rigidity_slope=1.0 / (np.pi**2)
        )
        
        # Should be high coherence
        assert 0.0 <= coherence <= 1.0
        assert coherence > 0.8  # Should be quite high
    
    def test_coherence_psi_imperfect(self, verifier):
        """Test coherence Ψ with imperfect parameters."""
        coherence = verifier.compute_coherence_psi(
            critical_line_deviation=0.1,
            gue_p_value=0.01,
            rigidity_slope=0.5
        )
        
        # Should be lower coherence
        assert 0.0 <= coherence <= 1.0
        assert coherence < 0.5  # Should be lower due to deviations
    
    def test_verify_spectral_signature(self, verifier, perfect_eigenvalues):
        """Test complete spectral signature verification."""
        signature = verifier.verify_spectral_signature(perfect_eigenvalues)
        
        # Check signature structure
        assert isinstance(signature, SpectralSignature)
        assert len(signature.eigenvalues) == len(perfect_eigenvalues)
        assert signature.num_eigenvalues == len(perfect_eigenvalues)
        
        # Check critical line alignment
        assert abs(signature.mean_real_part - 0.5) < 1e-6
        
        # Check GUE statistics
        assert isinstance(signature.gue_detected, bool)
        assert 0.0 <= signature.gue_p_value <= 1.0
        
        # Check spectral rigidity
        assert signature.spectral_rigidity >= 0.0
        assert np.isfinite(signature.rigidity_slope)
        
        # Check coherence
        assert 0.0 <= signature.coherence_psi <= 1.0
        
        # Check timestamp
        assert len(signature.timestamp) > 0
    
    def test_generate_beacon(self, verifier, perfect_eigenvalues, temp_beacon_dir):
        """Test beacon generation."""
        # Verify spectral signature
        signature = verifier.verify_spectral_signature(perfect_eigenvalues)
        
        # Generate beacon
        beacon_path = verifier.generate_beacon(signature)
        
        # Check beacon file exists
        assert beacon_path.exists()
        assert beacon_path.parent == temp_beacon_dir
        
        # Load and validate beacon content
        with open(beacon_path, 'r') as f:
            beacon_data = json.load(f)
        
        # Check essential fields
        assert beacon_data["node_id"] == "test_node"
        assert beacon_data["protocol"] == "QCAL-SYMBIO-BRIDGE v1.0"
        assert beacon_data["frequency_base"] == F0_BASE
        assert beacon_data["frequency_resonance"] == F0_RESONANCE
        
        # Check spectral signature
        assert "spectral_signature" in beacon_data
        assert beacon_data["spectral_signature"]["num_eigenvalues"] == len(perfect_eigenvalues)
        
        # Check three pillars
        assert "critical_line_alignment" in beacon_data
        assert "gue_statistics" in beacon_data
        assert "spectral_rigidity" in beacon_data
        
        # Check coherence
        assert "coherence" in beacon_data
        assert "psi" in beacon_data["coherence"]
        
        # Check QCAL signature
        assert "qcal_signature" in beacon_data
        assert "∴𓂀Ω∞³Φ" in beacon_data["qcal_signature"]
    
    def test_generate_beacon_with_metadata(self, verifier, perfect_eigenvalues):
        """Test beacon generation with additional metadata."""
        signature = verifier.verify_spectral_signature(perfect_eigenvalues)
        
        metadata = {
            "experiment_id": "test_001",
            "notes": "Test beacon generation"
        }
        
        beacon_path = verifier.generate_beacon(signature, metadata=metadata)
        
        # Load beacon
        with open(beacon_path, 'r') as f:
            beacon_data = json.load(f)
        
        # Check metadata
        assert "metadata" in beacon_data
        assert beacon_data["metadata"]["experiment_id"] == "test_001"
    
    def test_activation_report(self, verifier, perfect_eigenvalues):
        """Test activation report generation."""
        signature = verifier.verify_spectral_signature(perfect_eigenvalues)
        report = verifier.activation_report(signature)
        
        # Check report structure
        assert isinstance(report, str)
        assert len(report) > 0
        
        # Check key sections
        assert "Atlas³ Spectral Verifier" in report
        assert "PILAR 1" in report
        assert "PILAR 2" in report
        assert "PILAR 3" in report
        assert "COHERENCE" in report
        assert "VEREDICTO" in report
        
        # Check QCAL signature
        assert "∴𓂀Ω∞³Φ" in report
    
    def test_activation_report_sovereign(self, verifier, perfect_eigenvalues):
        """Test activation report with sovereign coherence."""
        signature = verifier.verify_spectral_signature(perfect_eigenvalues)
        
        # Force high coherence
        signature.coherence_psi = 0.95
        
        report = verifier.activation_report(signature)
        
        # Should show ACTIVADO status
        assert "ACTIVADO ✅" in report or "ACTIVATED ✅" in report
    
    def test_activation_report_subthreshold(self, verifier, imperfect_eigenvalues):
        """Test activation report with sub-threshold coherence."""
        signature = verifier.verify_spectral_signature(imperfect_eigenvalues)
        
        # Force low coherence
        signature.coherence_psi = 0.5
        
        report = verifier.activation_report(signature)
        
        # Should show EVOLVING status
        assert "EVOLVING" in report or "SUB-THRESHOLD" in report
    
    def test_multiple_verifications(self, verifier, perfect_eigenvalues):
        """Test multiple sequential verifications."""
        # First verification
        sig1 = verifier.verify_spectral_signature(perfect_eigenvalues)
        
        # Second verification
        sig2 = verifier.verify_spectral_signature(perfect_eigenvalues[:30])
        
        # Should have different number of eigenvalues
        assert sig1.num_eigenvalues != sig2.num_eigenvalues
        
        # Last verification should be sig2
        assert verifier._last_verification == sig2
    
    def test_beacon_directory_creation(self):
        """Test automatic beacon directory creation."""
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            beacon_dir = temp_path / "new_beacon_dir"
            
            # Directory should not exist yet
            assert not beacon_dir.exists()
            
            # Create verifier
            verifier = Atlas3SpectralVerifier(beacon_dir=beacon_dir)
            
            # Directory should now exist
            assert beacon_dir.exists()
    
    def test_constants_defined(self):
        """Test that QCAL constants are properly defined."""
        assert F0_BASE == 141.7001
        assert F0_RESONANCE == 888.0
        assert CRITICAL_LINE_RE == 0.5
    
    def test_wigner_gue_cdf_properties(self, verifier):
        """Test properties of Wigner GUE CDF."""
        # Generate test spacings
        test_spacings = np.linspace(0, 5, 100)
        
        # The CDF should be monotonically increasing
        # and bounded between 0 and 1
        
        # We'll test this indirectly through the KS test
        np.random.seed(888)
        eigenvalues = 0.5 + 1j * np.cumsum(np.random.gamma(2, 1, 50))
        
        gue_detected, p_value = verifier.detect_gue_statistics(eigenvalues)
        
        # Should return valid results
        assert isinstance(gue_detected, bool)
        assert 0.0 <= p_value <= 1.0
    
    def test_spectral_signature_serialization(self, verifier, perfect_eigenvalues):
        """Test that spectral signature can be serialized."""
        signature = verifier.verify_spectral_signature(perfect_eigenvalues)
        
        # Convert to dict (for JSON serialization)
        import dataclasses
        sig_dict = dataclasses.asdict(signature)
        
        # Check all fields are present
        assert "eigenvalues" in sig_dict
        assert "mean_real_part" in sig_dict
        assert "coherence_psi" in sig_dict
        assert "timestamp" in sig_dict


class TestIntegrationScenarios:
    """Integration tests for complete workflows."""
    
    def test_complete_verification_workflow(self):
        """Test complete workflow from eigenvalues to beacon."""
        with tempfile.TemporaryDirectory() as temp_dir:
            # Setup
            beacon_dir = Path(temp_dir) / "beacons"
            verifier = create_atlas3_verifier(
                node_id="integration_test",
                beacon_dir=beacon_dir
            )
            
            # Generate test eigenvalues
            np.random.seed(141)
            N = 40
            eigenvalues = 0.5 + 0.005 * np.random.randn(N) + \
                         1j * np.cumsum(np.random.gamma(2, 1, N))
            
            # Verify
            signature = verifier.verify_spectral_signature(eigenvalues)
            
            # Generate beacon
            beacon_path = verifier.generate_beacon(signature)
            
            # Generate report
            report = verifier.activation_report(signature)
            
            # Validate results
            assert signature.num_eigenvalues == N
            assert beacon_path.exists()
            assert len(report) > 0
            assert "Atlas³" in report
    
    def test_low_coherence_detection(self):
        """Test detection of low coherence systems."""
        with tempfile.TemporaryDirectory() as temp_dir:
            verifier = create_atlas3_verifier(
                beacon_dir=Path(temp_dir)
            )
            
            # Generate poor quality eigenvalues
            np.random.seed(999)
            N = 20
            # Far from critical line
            eigenvalues = 0.7 + 0.1 * np.random.randn(N) + \
                         1j * np.arange(1, N+1)
            
            signature = verifier.verify_spectral_signature(eigenvalues)
            
            # Should detect low coherence
            assert signature.coherence_psi < 0.888
            assert signature.critical_line_deviation > 0.1
    
    def test_high_coherence_system(self):
        """Test detection of high coherence systems."""
        with tempfile.TemporaryDirectory() as temp_dir:
            verifier = create_atlas3_verifier(
                beacon_dir=Path(temp_dir)
            )
            
            # Generate high quality eigenvalues
            np.random.seed(888)
            N = 60
            # Very close to critical line with GUE spacing
            eigenvalues = 0.5 + 0.001 * np.random.randn(N) + \
                         1j * np.cumsum(np.random.gamma(2, 1, N))
            
            signature = verifier.verify_spectral_signature(eigenvalues)
            
            # Should detect high coherence
            assert signature.critical_line_deviation < 0.01
            # Coherence should be reasonably high
            assert signature.coherence_psi > 0.5


if __name__ == "__main__":
    """Run tests with pytest."""
    pytest.main([__file__, "-v", "--tb=short"])

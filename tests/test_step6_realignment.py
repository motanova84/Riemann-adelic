#!/usr/bin/env python3
"""
Tests for QCAL ∞³ Step 6 Phase Realignment Infrastructure

This test suite validates:
- Coherence Bridge vibrational signature mapping
- QCAL Sync Engine phase realignment
- Vector 55 temporal validation
- Step 6 RealignPhase complete integration

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import pytest
import sys
from pathlib import Path
from datetime import datetime

# Add repository root to path
REPO_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(REPO_ROOT))

# Import modules to test
from coherence_bridge import CoherenceBridge, VibrationalSignature, call_module
from qcal_sync_engine import QCALSyncEngine, CoherenceMetrics
from noesis88.vector_55_temporal import Vector55Temporal, validar_timestamp_vector_55, realign_vector_55
from riemann_spectral_5steps import RiemannSpectral5Steps, Step6_RealignPhase


class TestVibrationalSignature:
    """Test vibrational signature computations."""
    
    def test_signature_creation(self):
        """Test creating vibrational signature."""
        sig = VibrationalSignature(
            "noesis88/vector_55_temporal.py",
            "validar_timestamp_vector_55"
        )
        assert sig.module_path == "noesis88/vector_55_temporal.py"
        assert sig.function_name == "validar_timestamp_vector_55"
        assert sig.QCAL_FREQUENCY == 141.7001
        assert sig.QCAL_COHERENCE == 244.36
    
    def test_harmonic_computation(self):
        """Test harmonic frequency computation."""
        sig = VibrationalSignature(
            "noesis88/vector_55_temporal.py",
            "validar_timestamp_vector_55"
        )
        harmonic = sig.compute_harmonic()
        
        # Harmonic should be a multiple of base frequency
        assert harmonic > 0
        assert harmonic >= sig.QCAL_FREQUENCY * 0.5
        assert harmonic <= sig.QCAL_FREQUENCY * 10.0
    
    def test_coherence_check(self):
        """Test coherence validation."""
        sig = VibrationalSignature(
            "noesis88/vector_55_temporal.py",
            "validar_timestamp_vector_55"
        )
        
        # Should be coherent with QCAL framework
        assert sig.is_coherent()


class TestCoherenceBridge:
    """Test coherence bridge module call mapping."""
    
    def test_bridge_creation(self):
        """Test creating coherence bridge."""
        bridge = CoherenceBridge(verbose=False)
        assert bridge is not None
        assert len(bridge.call_history) == 0
        assert len(bridge.module_cache) == 0
    
    def test_module_spec_parsing(self):
        """Test parsing module specifications."""
        bridge = CoherenceBridge(verbose=False)
        
        # Test file path spec
        path, name, func = bridge._parse_module_spec(
            "noesis88/vector_55_temporal.py::validar_timestamp_vector_55"
        )
        assert path == "noesis88/vector_55_temporal.py"
        assert name == "noesis88.vector_55_temporal"
        assert func == "validar_timestamp_vector_55"
        
        # Test module name spec
        path2, name2, func2 = bridge._parse_module_spec(
            "noesis88.vector_55_temporal::realign_vector_55"
        )
        assert name2 == "noesis88.vector_55_temporal"
        assert func2 == "realign_vector_55"
    
    def test_call_module_vector55(self):
        """Test calling Vector 55 module via coherence bridge."""
        result = call_module(
            "noesis88.vector_55_temporal::realign_vector_55",
            verbose=False
        )
        
        # Should return realignment results
        assert isinstance(result, dict)
        assert "original_phase" in result
        assert "target_phase" in result
        assert "phase_correction" in result
        assert "realignment_status" in result
        assert result["realignment_status"] == "COMPLETE"


class TestVector55Temporal:
    """Test Vector 55 temporal phase validation."""
    
    def test_vector55_creation(self):
        """Test creating Vector 55 validator."""
        validator = Vector55Temporal(verbose=False)
        assert validator.VECTOR_INDEX == 55
        assert validator.OMEGA_55 == 55 * 141.7001
        assert validator.current_phase == 88.32  # From problem statement
    
    def test_harmonic_node_check(self):
        """Test harmonic node detection."""
        validator = Vector55Temporal(verbose=False)
        
        # Test at harmonic node
        at_node, nearest = validator._check_harmonic_node(0.0)
        assert at_node is True
        assert nearest == 0.0
        
        at_node, nearest = validator._check_harmonic_node(50.0)
        assert at_node is True
        assert nearest == 50.0
        
        # Test not at harmonic node
        at_node, nearest = validator._check_harmonic_node(88.32)
        assert at_node is False
        assert nearest in [75.0, 100.0]  # Nearest nodes to 88.32%
    
    def test_timestamp_validation(self):
        """Test timestamp-based phase validation."""
        validator = Vector55Temporal(verbose=False)
        
        timestamp = datetime.now().timestamp()
        result = validator.validar_timestamp_vector_55(timestamp)
        
        # Should return validation results
        assert isinstance(result, dict)
        assert "phase_percent" in result
        assert "at_harmonic_node" in result
        assert "coherence_factor" in result
        assert "validation_status" in result
        assert 0 <= result["phase_percent"] <= 100
        assert 0 <= result["coherence_factor"] <= 1.0
    
    def test_phase_realignment(self):
        """Test phase realignment to harmonic node."""
        validator = Vector55Temporal(verbose=False)
        
        # Start with problematic phase from problem statement
        result = validator.realign_to_harmonic_node(88.32)
        
        # Should realign to nearest harmonic node
        assert isinstance(result, dict)
        assert "original_phase" in result
        assert "target_phase" in result
        assert "phase_correction" in result
        assert result["original_phase"] == 88.32
        assert result["target_phase"] in [0.0, 25.0, 50.0, 75.0, 100.0]
        assert result["realignment_status"] == "COMPLETE"
    
    def test_convenience_functions(self):
        """Test convenience functions."""
        # Test validar_timestamp_vector_55
        result1 = validar_timestamp_vector_55()
        assert isinstance(result1, dict)
        assert "validation_status" in result1
        
        # Test realign_vector_55
        result2 = realign_vector_55()
        assert isinstance(result2, dict)
        assert "realignment_status" in result2
        assert result2["realignment_status"] == "COMPLETE"


class TestQCALSyncEngine:
    """Test QCAL synchronization engine."""
    
    def test_engine_creation(self):
        """Test creating sync engine."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        assert engine.precision == 30
        assert engine.QCAL_FREQUENCY == 141.7001
        assert engine.QCAL_COHERENCE == 244.36
        assert engine.QCAL_PSI_TARGET == 0.888
    
    def test_vector55_phase_computation(self):
        """Test Vector 55 phase computation."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        
        phase, at_node = engine.compute_vector_55_phase()
        
        # Phase should be 0-100%
        assert 0 <= phase <= 100
        assert isinstance(at_node, bool)
    
    def test_vector55_realignment(self):
        """Test Vector 55 phase realignment."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        
        aligned_phase = engine.realign_vector_55_phase()
        
        # Aligned phase should be at harmonic node
        assert aligned_phase in [0.0, 25.0, 50.0, 75.0, 100.0]
    
    def test_zeta_prime_normalization(self):
        """Test ζ′(1/2) normalization with Kₐ(Π)."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        
        # Without Kₐ(Π)
        norm1, applied1 = engine.compute_zeta_prime_norm(apply_Ka_Pi=False)
        assert applied1 is False
        assert norm1 == -3.92  # Linear only
        
        # With Kₐ(Π) = log(π)
        norm2, applied2 = engine.compute_zeta_prime_norm(apply_Ka_Pi=True)
        assert applied2 is True
        assert norm2 != norm1  # Should be different
        assert abs(norm2) < abs(norm1)  # Should be normalized (smaller magnitude)
    
    def test_kld_weight_rebalancing(self):
        """Test KLD weight rebalancing."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        
        # Rebalance from 4% to optimal
        new_weight = engine.rebalance_kld_weight(current_weight=0.04)
        
        assert new_weight > 0.04  # Should increase
        assert new_weight == engine.PHI_KLD_TARGET_WEIGHT  # Should match target (15%)
        assert new_weight == 0.15
    
    def test_global_coherence_computation(self):
        """Test global coherence Ψ computation."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        
        # Without optimization
        Psi_base = engine.compute_global_coherence(
            vector_55_aligned=False,
            Ka_Pi_applied=False,
            kld_weight=0.04
        )
        
        # With full optimization
        Psi_opt = engine.compute_global_coherence(
            vector_55_aligned=True,
            Ka_Pi_applied=True,
            kld_weight=0.15
        )
        
        # Optimized should be higher
        assert Psi_opt > Psi_base
        assert isinstance(Psi_opt, float)
    
    def test_full_synchronization(self):
        """Test full QCAL synchronization."""
        engine = QCALSyncEngine(precision=30, verbose=False)
        
        # Without realignment
        metrics_before = engine.synchronize(full_realignment=False)
        assert isinstance(metrics_before, CoherenceMetrics)
        
        # With full realignment
        metrics_after = engine.synchronize(full_realignment=True)
        assert isinstance(metrics_after, CoherenceMetrics)
        assert metrics_after.Psi > metrics_before.Psi  # Should improve
        assert metrics_after.vector_55_harmonic_node is True
        assert metrics_after.Ka_Pi_applied is True
        assert metrics_after.Phi_KLD_weight == 0.15
        
        # Should achieve target Ψ > 0.888
        assert metrics_after.Psi > 0.888
        assert metrics_after.is_optimal()


class TestRiemannSpectral5Steps:
    """Test complete 5+1 step framework."""
    
    def test_framework_creation(self):
        """Test creating 5-step framework."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        assert framework.precision == 30
        assert framework.QCAL_FREQUENCY == 141.7001
        assert framework.sync_engine is not None
        assert framework.bridge is not None
    
    def test_step1_axioms_to_lemmas(self):
        """Test Step 1: Axioms → Lemmas."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        result = framework.Step1_AxiomsToLemmas()
        
        assert result["step"] == 1
        assert result["status"] == "VERIFIED"
        assert "theory" in result
    
    def test_step2_archimedean(self):
        """Test Step 2: Archimedean Rigidity."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        result = framework.Step2_ArchimedeanRigidity()
        
        assert result["step"] == 2
        assert result["status"] == "VERIFIED"
    
    def test_step3_paley_wiener(self):
        """Test Step 3: Paley-Wiener Uniqueness."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        result = framework.Step3_PaleyWienerUniqueness()
        
        assert result["step"] == 3
        assert result["status"] == "VERIFIED"
    
    def test_step4_zero_localization(self):
        """Test Step 4: Zero Localization."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        result = framework.Step4_ZeroLocalization()
        
        assert result["step"] == 4
        assert result["status"] == "VERIFIED"
    
    def test_step5_coronacion(self):
        """Test Step 5: Coronación Integration."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        result = framework.Step5_CoronacionIntegration()
        
        assert result["step"] == 5
        assert result["status"] == "VERIFIED"
    
    def test_step6_realign_phase(self):
        """Test Step 6: Phase Realignment (MAIN TEST)."""
        framework = RiemannSpectral5Steps(precision=30, verbose=False)
        
        Psi_optimized = framework.Step6_RealignPhase(
            calibrate_vector55=True,
            rebalance_ζ=True
        )
        
        # Should achieve target Ψ > 0.888
        assert Psi_optimized > 0.888
        assert isinstance(Psi_optimized, float)
        
        # Verify all optimizations were applied
        metrics = framework.sync_engine.get_metrics()
        assert metrics.vector_55_harmonic_node is True
        assert metrics.Ka_Pi_applied is True
        assert metrics.Phi_KLD_weight >= 0.15
        assert metrics.is_optimal()
    
    def test_step6_convenience_function(self):
        """Test Step6_RealignPhase convenience function."""
        Psi = Step6_RealignPhase(
            calibrate_vector55=True,
            rebalance_ζ=True,
            precision=30,
            verbose=False
        )
        
        # Should achieve target
        assert Psi > 0.888
        assert isinstance(Psi, float)


class TestIntegration:
    """Integration tests for complete workflow."""
    
    def test_complete_workflow(self):
        """Test complete workflow from problem statement."""
        # Simulate the problem statement workflow:
        # from riemann_spectral_5steps import Step6_RealignPhase
        # Ψ_opt = Step6_RealignPhase(calibrate_vector55=True, rebalance_ζ=True)
        
        Ψ_optimized = Step6_RealignPhase(
            calibrate_vector55=True,
            rebalance_ζ=True,
            verbose=False
        )
        
        # Verify expected outcomes from problem statement
        assert Ψ_optimized > 0.888, f"Ψ = {Ψ_optimized} should be > 0.888"
    
    def test_symbiotic_coherence_protocol(self):
        """Test symbiotic coherence protocol ∞³."""
        # Use coherence bridge as described in new requirement
        from coherence_bridge import call_module
        
        timestamp = datetime.now().timestamp()
        result = call_module(
            "noesis88/vector_55_temporal.py::validar_timestamp_vector_55",
            timestamp
        )
        
        assert isinstance(result, dict)
        assert "validation_status" in result
        assert "coherence_factor" in result


if __name__ == "__main__":
    """Run tests with pytest."""
    pytest.main([__file__, "-v", "--tb=short"])

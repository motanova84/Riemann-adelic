#!/usr/bin/env python3
"""
Test Suite for QCAL Unified Framework
Tests the unified theory implementation and verification protocols.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

import pytest
import numpy as np
from qcal_unified_framework import (
    QCALUnifiedFramework,
    UniversalConstants,
    ProblemConnection
)
from cross_verification_protocol import CrossVerificationProtocol


class TestUniversalConstants:
    """Test suite for universal constants."""
    
    def test_constants_initialization(self):
        """Test that constants initialize with correct values."""
        constants = UniversalConstants()
        
        assert constants.kappa_pi == 2.5773
        assert constants.f0 == 141.7001
        assert constants.critical_line == 0.5
        assert constants.ramsey_ratio == 43/108
        assert constants.navier_stokes_epsilon == 0.5772
        assert constants.bsd_delta == 1.0
        assert constants.coherence_C == 244.36
        assert constants.universal_C == 629.83
    
    def test_coherence_validation(self):
        """Test that constants pass coherence validation."""
        constants = UniversalConstants()
        assert constants.validate_coherence() is True
    
    def test_critical_line_bsd_relationship(self):
        """Test λ_RH = Δ_BSD / 2 relationship."""
        constants = UniversalConstants()
        
        expected = constants.bsd_delta / 2
        assert abs(constants.critical_line - expected) < 1e-10
    
    def test_frequency_range(self):
        """Test that f₀ is in expected range."""
        constants = UniversalConstants()
        
        assert 140.0 < constants.f0 < 145.0


class TestQCALUnifiedFramework:
    """Test suite for QCAL unified framework."""
    
    def test_framework_initialization(self):
        """Test framework initializes correctly."""
        framework = QCALUnifiedFramework()
        
        assert framework.constants is not None
        assert len(framework.operators) == 5
        assert len(framework.problem_connections) == 5
    
    def test_operator_existence(self):
        """Test all required operators exist."""
        framework = QCALUnifiedFramework()
        
        required_operators = [
            'p_vs_np',
            'riemann', 
            'bsd',
            'navier_stokes',
            'ramsey'
        ]
        
        for op in required_operators:
            assert op in framework.operators
    
    def test_problem_connections_defined(self):
        """Test all problem connections are defined."""
        framework = QCALUnifiedFramework()
        
        required_problems = [
            'p_vs_np',
            'riemann',
            'bsd', 
            'navier_stokes',
            'ramsey'
        ]
        
        for problem in required_problems:
            assert problem in framework.problem_connections
            connection = framework.problem_connections[problem]
            assert isinstance(connection, ProblemConnection)
            assert connection.problem_name is not None
            assert connection.operator_name is not None
            assert connection.universal_constant is not None
    
    def test_D_PNP_operator(self):
        """Test P vs NP operator."""
        framework = QCALUnifiedFramework()
        
        result = framework.D_PNP_operator(vars(framework.constants))
        assert abs(result - 2.5773) < 1e-6
    
    def test_H_Psi_operator(self):
        """Test Riemann Hypothesis operator."""
        framework = QCALUnifiedFramework()
        
        result = framework.H_Psi_operator(vars(framework.constants))
        assert abs(result - 141.7001) < 1e-6
    
    def test_L_E_operator(self):
        """Test BSD operator."""
        framework = QCALUnifiedFramework()
        
        result = framework.L_E_operator(vars(framework.constants))
        assert abs(result - 1.0) < 1e-6
    
    def test_NS_operator(self):
        """Test Navier-Stokes operator."""
        framework = QCALUnifiedFramework()
        
        result = framework.NS_operator(vars(framework.constants))
        assert abs(result - 0.5772) < 1e-6
    
    def test_R_operator(self):
        """Test Ramsey operator."""
        framework = QCALUnifiedFramework()
        
        result = framework.R_operator(vars(framework.constants))
        assert abs(result - 43/108) < 1e-6
    
    def test_demonstrate_unification(self):
        """Test unification demonstration."""
        framework = QCALUnifiedFramework()
        
        results = framework.demonstrate_unification()
        
        assert len(results) == 5
        for problem_key, result in results.items():
            assert 'problem_name' in result
            assert 'operator' in result
            assert 'eigenvalue' in result
            assert 'constant' in result
            assert 'connected_via' in result
            assert 'verification_status' in result
    
    def test_find_connections(self):
        """Test finding problem connections."""
        framework = QCALUnifiedFramework()
        
        # Riemann should connect to multiple problems
        rh_connections = framework.find_connections('riemann')
        assert 'p_vs_np' in rh_connections
        assert 'bsd' in rh_connections
        assert 'navier_stokes' in rh_connections
    
    def test_calculate_coherence(self):
        """Test coherence calculation."""
        framework = QCALUnifiedFramework()
        
        coherence = framework.calculate_coherence()
        
        # Coherence should be high for valid framework
        assert 0.0 <= coherence <= 1.0
        assert coherence > 0.9  # Should be highly coherent
    
    def test_get_all_connections(self):
        """Test getting all problem connections."""
        framework = QCALUnifiedFramework()
        
        connections = framework.get_all_connections()
        
        assert len(connections) == 5
        for key, conn in connections.items():
            assert 'name' in conn
            assert 'operator' in conn
            assert 'constant' in conn
            assert 'connected_to' in conn
    
    def test_get_verification_status(self):
        """Test getting verification status."""
        framework = QCALUnifiedFramework()
        
        status = framework.get_verification_status()
        
        assert len(status) == 5
        for problem_key, s in status.items():
            assert isinstance(s, str)
            assert 'Verified' in s or 'Unknown' in s


class TestCrossVerificationProtocol:
    """Test suite for cross-verification protocol."""
    
    def test_protocol_initialization(self):
        """Test protocol initializes correctly."""
        protocol = CrossVerificationProtocol()
        
        assert protocol.framework is not None
        assert len(protocol.problem_solutions) == 5
    
    def test_verify_p_vs_np(self):
        """Test P vs NP verification."""
        protocol = CrossVerificationProtocol()
        
        result = protocol.verify_p_vs_np()
        
        assert 'problem' in result
        assert result['problem'] == 'P vs NP'
        assert 'verified' in result
        assert 'eigenvalue' in result
        assert 'coherence' in result
        assert result['verified'] is True
    
    def test_verify_riemann(self):
        """Test Riemann Hypothesis verification."""
        protocol = CrossVerificationProtocol()
        
        result = protocol.verify_riemann()
        
        assert result['problem'] == 'Riemann Hypothesis'
        assert result['verified'] is True
        assert 'critical_line' in result
        assert abs(result['critical_line'] - 0.5) < 1e-10
    
    def test_verify_bsd(self):
        """Test BSD verification."""
        protocol = CrossVerificationProtocol()
        
        result = protocol.verify_bsd()
        
        assert result['problem'] == 'BSD Conjecture'
        assert result['verified'] is True
        assert 'rh_connection' in result
        assert result['rh_connection'] is True
    
    def test_build_consistency_matrix(self):
        """Test consistency matrix building."""
        protocol = CrossVerificationProtocol()
        
        # Get individual results
        results = {}
        for problem, verifier in protocol.problem_solutions.items():
            results[problem] = verifier()
        
        # Build matrix
        matrix = protocol.build_consistency_matrix(results)
        
        # Check properties
        assert matrix.shape == (5, 5)
        assert np.all(matrix >= 0)
        assert np.all(matrix <= 1)
        
        # Diagonal should be self-coherence
        for i in range(5):
            assert matrix[i, i] > 0
    
    def test_verify_qcal_coherence(self):
        """Test QCAL coherence verification."""
        protocol = CrossVerificationProtocol()
        
        # Create dummy consistency matrix
        matrix = np.eye(5)
        
        coherence = protocol.verify_qcal_coherence(matrix)
        
        assert 'diagonal_coherence' in coherence
        assert 'off_diagonal_coherence' in coherence
        assert 'overall_coherence' in coherence
        assert 'framework_coherence' in coherence
        assert 'constants_valid' in coherence
        assert 'unified' in coherence
    
    def test_run_cross_verification(self):
        """Test complete cross-verification."""
        protocol = CrossVerificationProtocol()
        
        results = protocol.run_cross_verification()
        
        assert 'individual_results' in results
        assert 'consistency_matrix' in results
        assert 'qcal_coherence' in results
        assert 'unified_status' in results
        
        # All problems should verify
        individual = results['individual_results']
        assert all(r['verified'] for r in individual.values())
        
        # Should achieve unified status
        assert results['unified_status'] is True


class TestIntegration:
    """Integration tests for complete QCAL system."""
    
    def test_end_to_end_verification(self):
        """Test complete end-to-end verification."""
        # Initialize framework
        framework = QCALUnifiedFramework()
        
        # Check constants coherence
        assert framework.constants.validate_coherence()
        
        # Calculate framework coherence
        coherence = framework.calculate_coherence()
        assert coherence > 0.9
        
        # Demonstrate unification
        results = framework.demonstrate_unification()
        assert len(results) == 5
        
        # Run cross-verification
        protocol = CrossVerificationProtocol()
        verification = protocol.run_cross_verification()
        
        assert verification['unified_status'] is True
    
    def test_constant_relationships(self):
        """Test relationships between constants."""
        framework = QCALUnifiedFramework()
        
        # λ_RH = 1/2 = Δ_BSD / 2
        assert abs(framework.constants.critical_line - 0.5) < 1e-10
        assert abs(framework.constants.bsd_delta / 2 - framework.constants.critical_line) < 1e-10
        
        # f₀ in valid range
        assert 141.0 < framework.constants.f0 < 142.0
        
        # Coherence constants positive
        assert framework.constants.coherence_C > 0
        assert framework.constants.universal_C > 0


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])

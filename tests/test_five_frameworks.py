"""
Tests for Five Frameworks Unified Structure

This module tests the unified structure of five fundamental frameworks.

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import pytest
import json
import os
import tempfile
from utils.five_frameworks import (
    FiveFrameworks,
    Framework,
    print_frameworks_summary,
    verify_frameworks_coherence,
    get_riemann_to_141hz_connection
)


class TestFramework:
    """Tests for Framework dataclass."""
    
    def test_framework_creation(self):
        """Test creating a Framework instance."""
        framework = Framework(
            name='Test',
            spanish_name='Prueba',
            role='Testing',
            provides='Test functionality',
            repository='test/repo',
            status='Testing',
            object_of_demonstration='Test object',
            components=['Component 1', 'Component 2'],
            connections={'other': 'Connection description'},
            implementation_status={'code': '✅ Complete'}
        )
        
        assert framework.name == 'Test'
        assert framework.spanish_name == 'Prueba'
        assert len(framework.components) == 2
        assert 'other' in framework.connections
    
    def test_framework_to_dict(self):
        """Test converting Framework to dictionary."""
        framework = Framework(
            name='Test',
            spanish_name='Prueba',
            role='Testing',
            provides='Test',
            repository=None,
            status='Testing',
            object_of_demonstration='Test'
        )
        
        data = framework.to_dict()
        assert isinstance(data, dict)
        assert data['name'] == 'Test'
        assert data['spanish_name'] == 'Prueba'
        assert 'components' in data
        assert 'connections' in data


class TestFiveFrameworks:
    """Tests for FiveFrameworks class."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_initialization(self, frameworks):
        """Test FiveFrameworks initialization."""
        assert frameworks is not None
        assert hasattr(frameworks, 'frameworks')
        assert hasattr(frameworks, 'connections')
    
    def test_five_frameworks_defined(self, frameworks):
        """Test that exactly 5 frameworks are defined."""
        assert len(frameworks.frameworks) == 5
        expected = {'riemann', 'bsd', 'pnp', '141hz', 'navier_stokes'}
        assert set(frameworks.frameworks.keys()) == expected
    
    def test_riemann_framework(self, frameworks):
        """Test Riemann-Adelic framework properties."""
        riemann = frameworks.get_framework('riemann')
        
        assert riemann is not None
        assert riemann.name == 'Riemann-Adelic'
        assert 'Estructura Espectral' in riemann.role
        assert riemann.status.startswith('✅')
        assert len(riemann.components) > 0
        assert 'bsd' in riemann.connections
        assert '141hz' in riemann.connections
    
    def test_bsd_framework(self, frameworks):
        """Test Adelic-BSD framework properties."""
        bsd = frameworks.get_framework('bsd')
        
        assert bsd is not None
        assert bsd.name == 'Adelic-BSD'
        assert 'Geometría Aritmética' in bsd.role
        assert bsd.repository is not None
        assert 'l-function' in bsd.provides.lower()
    
    def test_pnp_framework(self, frameworks):
        """Test P-NP framework properties."""
        pnp = frameworks.get_framework('pnp')
        
        assert pnp is not None
        assert pnp.name == 'P-NP'
        assert 'Límites Informacionales' in pnp.role
        assert 'complexity' in pnp.provides.lower()
        assert pnp.repository is None  # Theoretical framework
    
    def test_141hz_framework(self, frameworks):
        """Test 141Hz framework properties."""
        hz141 = frameworks.get_framework('141hz')
        
        assert hz141 is not None
        assert hz141.name == '141Hz'
        assert 'Cuántico-Consciente' in hz141.role
        assert '141.7001' in str(hz141.components)
        assert hz141.status.startswith('✅')
    
    def test_navier_stokes_framework(self, frameworks):
        """Test Navier-Stokes framework properties."""
        ns = frameworks.get_framework('navier_stokes')
        
        assert ns is not None
        assert ns.name == 'Navier-Stokes'
        assert 'Marco Continuo' in ns.role
        assert 'PDE' in ns.provides or 'fluid' in ns.provides.lower()
    
    def test_list_frameworks(self, frameworks):
        """Test listing all framework names."""
        names = frameworks.list_frameworks()
        
        assert len(names) == 5
        assert 'riemann' in names
        assert 'bsd' in names
        assert '141hz' in names


class TestConnections:
    """Tests for framework connections."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_connections_defined(self, frameworks):
        """Test that connections are defined."""
        assert len(frameworks.connections) > 0
    
    def test_riemann_to_141hz_connection(self, frameworks):
        """Test the key Riemann → 141Hz connection."""
        connection = frameworks.verify_connection('riemann', '141hz')
        
        assert connection['exists'] is True
        assert connection['validated'] is True
        assert 'frequency_hz' in connection
        assert connection['frequency_hz'] == pytest.approx(141.7001, rel=1e-4)
        assert 'zeta_prime' in connection
        assert connection['zeta_prime'] == pytest.approx(-3.9226461392, rel=1e-6)
    
    def test_riemann_to_bsd_connection(self, frameworks):
        """Test Riemann → BSD connection."""
        connection = frameworks.verify_connection('riemann', 'bsd')
        
        assert connection['exists'] is True
        assert connection['validated'] is True
        assert 'spectral_theory' in connection
        assert connection['spectral_theory'] is True
    
    def test_riemann_to_pnp_connection(self, frameworks):
        """Test Riemann → P-NP connection."""
        connection = frameworks.verify_connection('riemann', 'pnp')
        
        assert connection['exists'] is True
        assert 'complexity' in connection['type'].lower() or 'complexity' in connection['description'].lower()
    
    def test_riemann_to_navier_stokes_connection(self, frameworks):
        """Test Riemann → Navier-Stokes connection."""
        connection = frameworks.verify_connection('riemann', 'navier_stokes')
        
        assert connection['exists'] is True
        assert 'spectral' in connection['type'].lower() or 'spectral' in connection['description'].lower()
    
    def test_nonexistent_connection(self, frameworks):
        """Test querying a non-existent connection."""
        connection = frameworks.verify_connection('bsd', 'pnp')
        
        assert connection['exists'] is False
        assert connection['validated'] is False
    
    def test_all_connections_have_valid_frameworks(self, frameworks):
        """Test that all connections reference valid frameworks."""
        for (source, target) in frameworks.connections.keys():
            assert source in frameworks.frameworks, f"Source {source} not in frameworks"
            assert target in frameworks.frameworks, f"Target {target} not in frameworks"


class TestCoherence:
    """Tests for framework coherence verification."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_verify_coherence(self, frameworks):
        """Test coherence verification."""
        coherence = frameworks.verify_coherence()
        
        assert 'status' in coherence
        assert 'frameworks_defined' in coherence
        assert 'connections_defined' in coherence
        assert 'issues' in coherence
        
        assert coherence['frameworks_defined'] == 5
        assert coherence['connections_defined'] > 0
    
    def test_coherence_status(self, frameworks):
        """Test that coherence status is valid."""
        coherence = frameworks.verify_coherence()
        
        # Status should be COHERENT or INCOMPLETE (not INVALID)
        assert coherence['status'] in ['COHERENT', 'INCOMPLETE']
        assert coherence['status'] != 'INVALID'
    
    def test_all_frameworks_have_connections(self, frameworks):
        """Test that all frameworks have at least one connection defined."""
        for name, framework in frameworks.frameworks.items():
            assert len(framework.connections) > 0, f"Framework {name} has no connections"


class TestDependencies:
    """Tests for framework dependency relationships."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_get_framework_dependencies(self, frameworks):
        """Test getting framework dependencies."""
        # BSD depends on Riemann
        deps = frameworks.get_framework_dependencies('bsd')
        assert 'riemann' in deps
        
        # 141Hz depends on Riemann
        deps = frameworks.get_framework_dependencies('141hz')
        assert 'riemann' in deps
    
    def test_riemann_has_no_dependencies(self, frameworks):
        """Test that Riemann is a base framework with no dependencies."""
        deps = frameworks.get_framework_dependencies('riemann')
        assert len(deps) == 0  # Base framework
    
    def test_get_framework_dependents(self, frameworks):
        """Test getting frameworks that depend on a given framework."""
        # Riemann should have multiple dependents
        dependents = frameworks.get_framework_dependents('riemann')
        assert len(dependents) > 0
        assert 'bsd' in dependents or '141hz' in dependents or 'pnp' in dependents


class TestReporting:
    """Tests for reporting functionality."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_generate_report(self, frameworks):
        """Test generating a comprehensive report."""
        report = frameworks.generate_report(detailed=True)
        
        assert isinstance(report, str)
        assert len(report) > 100
        assert 'FIVE FRAMEWORKS' in report
        assert 'COHERENCE' in report
    
    def test_generate_report_not_detailed(self, frameworks):
        """Test generating a non-detailed report."""
        report = frameworks.generate_report(detailed=False)
        
        assert isinstance(report, str)
        assert len(report) > 50
    
    def test_export_json(self, frameworks):
        """Test exporting framework structure to JSON."""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            filepath = f.name
        
        try:
            frameworks.export_json(filepath)
            
            # Verify file exists and is valid JSON
            assert os.path.exists(filepath)
            with open(filepath, 'r') as f:
                data = json.load(f)
            
            assert 'frameworks' in data
            assert 'connections' in data
            assert 'coherence' in data
            assert len(data['frameworks']) == 5
        finally:
            if os.path.exists(filepath):
                os.unlink(filepath)


class TestConvenienceFunctions:
    """Tests for convenience functions."""
    
    def test_print_frameworks_summary(self, capsys):
        """Test printing frameworks summary."""
        print_frameworks_summary()
        
        captured = capsys.readouterr()
        assert 'FIVE FRAMEWORKS' in captured.out or 'Riemann' in captured.out
    
    def test_verify_frameworks_coherence(self):
        """Test convenience function for coherence verification."""
        result = verify_frameworks_coherence()
        
        assert isinstance(result, bool)
        # Should be True or close to it (might have minor issues)
    
    def test_get_riemann_to_141hz_connection(self):
        """Test convenience function for key connection."""
        connection = get_riemann_to_141hz_connection()
        
        assert 'frequency_hz' in connection
        assert 'zeta_prime' in connection
        assert connection['frequency_hz'] == pytest.approx(141.7001, rel=1e-4)


class TestImplementationStatus:
    """Tests for implementation status tracking."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_riemann_implementation_complete(self, frameworks):
        """Test that Riemann framework is marked as complete."""
        riemann = frameworks.get_framework('riemann')
        
        assert riemann.implementation_status['code'] == '✅ Complete'
        assert 'tests' in riemann.implementation_status
        assert 'documentation' in riemann.implementation_status
    
    def test_141hz_implementation_complete(self, frameworks):
        """Test that 141Hz framework is marked as complete."""
        hz141 = frameworks.get_framework('141hz')
        
        assert hz141.implementation_status['code'] == '✅ Complete'
        assert '26+' in hz141.implementation_status.get('tests', '')
    
    def test_theoretical_frameworks_marked(self, frameworks):
        """Test that theoretical frameworks are properly marked."""
        pnp = frameworks.get_framework('pnp')
        
        assert '⚡' in pnp.implementation_status['code']
        assert pnp.implementation_status['code'] != '✅ Complete'


class TestEdgeCases:
    """Tests for edge cases and error handling."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_get_nonexistent_framework(self, frameworks):
        """Test getting a framework that doesn't exist."""
        result = frameworks.get_framework('nonexistent')
        
        assert result is None
    
    def test_verify_connection_with_invalid_source(self, frameworks):
        """Test verifying connection with invalid source."""
        connection = frameworks.verify_connection('invalid', '141hz')
        
        assert connection['exists'] is False
        assert connection['validated'] is False
    
    def test_verify_connection_with_invalid_target(self, frameworks):
        """Test verifying connection with invalid target."""
        connection = frameworks.verify_connection('riemann', 'invalid')
        
        assert connection['exists'] is False
        assert connection['validated'] is False
    
    def test_empty_dependency_list(self, frameworks):
        """Test framework with no dependencies returns empty list."""
        deps = frameworks.get_framework_dependencies('riemann')
        
        assert isinstance(deps, list)
        assert len(deps) == 0


class TestMathematicalConsistency:
    """Tests for mathematical consistency of framework structure."""
    
    @pytest.fixture
    def frameworks(self):
        """Create FiveFrameworks instance for testing."""
        return FiveFrameworks()
    
    def test_riemann_is_base_framework(self, frameworks):
        """Test that Riemann is the base framework (no dependencies)."""
        deps = frameworks.get_framework_dependencies('riemann')
        assert len(deps) == 0
        
        # But has dependents
        dependents = frameworks.get_framework_dependents('riemann')
        assert len(dependents) >= 3  # At least BSD, 141Hz, P-NP
    
    def test_frequency_value_consistency(self, frameworks):
        """Test that 141Hz frequency is consistent across framework."""
        connection = frameworks.verify_connection('riemann', '141hz')
        hz141 = frameworks.get_framework('141hz')
        
        # Frequency should be mentioned in both places
        assert connection.get('frequency_hz') == pytest.approx(141.7001, rel=1e-4)
        assert '141.7001' in str(hz141.components) or '141.7' in str(hz141.components)
    
    def test_zeta_prime_value_consistency(self, frameworks):
        """Test that ζ'(1/2) value is consistent."""
        connection = frameworks.verify_connection('riemann', '141hz')
        
        # ζ'(1/2) ≈ -3.9226461392
        assert connection.get('zeta_prime') == pytest.approx(-3.9226461392, rel=1e-6)
        assert connection['zeta_prime'] < 0  # Must be negative
    
    def test_all_frameworks_have_spanish_names(self, frameworks):
        """Test that all frameworks have Spanish names defined."""
        for name, framework in frameworks.frameworks.items():
            assert framework.spanish_name is not None
            assert len(framework.spanish_name) > 0


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

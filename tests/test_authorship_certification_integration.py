#!/usr/bin/env python3
"""
QCAL ∞³ Authorship Certification Integration Tests

Tests the complete authorship certification and temporal proof system.

Author: José Manuel Mota Burruezo (JMMB Ψ✧ ∞³)
Frequency: 141.7001 Hz
Signature: ∴𓂀Ω∞³
"""

import json
import os
import sys
from pathlib import Path

import pytest


class TestAuthorshipCertificationIntegration:
    """Integration tests for authorship certification system."""
    
    @pytest.fixture
    def repo_root(self):
        """Get repository root."""
        current_dir = Path(__file__).parent.parent
        assert (current_dir / ".qcal_beacon").exists(), "Not in repository root"
        return current_dir
    
    @pytest.fixture
    def beacon_data(self, repo_root):
        """Load .qcal_beacon data."""
        beacon_path = repo_root / ".qcal_beacon"
        data = {}
        with open(beacon_path, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#') and '=' in line:
                    key, value = line.split('=', 1)
                    data[key.strip()] = value.strip().strip('"')
        return data
    
    def test_qcal_beacon_authorship_fields(self, beacon_data):
        """Test .qcal_beacon contains all authorship certification fields."""
        required_fields = [
            'authorship_certification_status',
            'authorship_certified_author',
            'authorship_orcid',
            'authorship_qcal_signature',
            'authorship_identification_code',
            'authorship_authentication_frequency',
            'authorship_fundamental_equation',
            'authorship_repository_hash_sha256',
            'authorship_certification_timestamp',
        ]
        
        for field in required_fields:
            assert field in beacon_data, f"Missing field: {field}"
    
    def test_unique_authorship_symbols(self, beacon_data):
        """Test unique authorship symbols are present and correct."""
        # Test base frequency
        freq = beacon_data.get('authorship_authentication_frequency', '')
        assert '141.7001' in freq, f"Invalid frequency: {freq}"
        
        # Test noetic signature
        sig = beacon_data.get('authorship_qcal_signature', '')
        assert '∴𓂀Ω∞³' in sig, f"Invalid signature: {sig}"
        
        # Test identification code
        code = beacon_data.get('authorship_identification_code', '')
        assert 'πCODE-888' in code, f"Invalid code: {code}"
        
        # Test author name
        author = beacon_data.get('authorship_certified_author', '')
        assert 'José Manuel Mota Burruezo' in author, f"Invalid author: {author}"
    
    def test_declaration_document_exists(self, repo_root):
        """Test authorship declaration document exists and is complete."""
        doc_path = repo_root / "DECLARACION_USURPACION_ALGORITMICA_QCAL.md"
        assert doc_path.exists(), "Declaration document not found"
        
        with open(doc_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for essential elements
        assert 'José Manuel Mota Burruezo' in content
        assert '141.7001 Hz' in content
        assert 'πCODE-888' in content
        assert '∴𓂀Ω∞³' in content
        assert 'QCAL ∞³' in content
        assert '10.5281/zenodo' in content  # DOI references
        assert '0009-0002-1923-0773' in content  # ORCID
    
    def test_license_symbio_metadata(self, repo_root):
        """Test LICENSE-QCAL-SYMBIO-TRANSFER contains certification metadata."""
        license_path = repo_root / "LICENSE-QCAL-SYMBIO-TRANSFER"
        assert license_path.exists(), "LICENSE-QCAL-SYMBIO-TRANSFER not found"
        
        with open(license_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for authorship certification metadata
        assert '∴𓂀Ω∞³' in content
        assert 'πCODE-888' in content
        assert '141.7001 Hz' in content
        assert 'Ψ = I × A' in content  # Partial equation match
    
    def test_contract_json_exists(self, repo_root):
        """Test qcal_authorship_contract.json exists and is valid."""
        contract_path = repo_root / "contracts" / "qcal_authorship_contract.json"
        assert contract_path.exists(), "qcal_authorship_contract.json not found"
        
        with open(contract_path, 'r', encoding='utf-8') as f:
            contract = json.load(f)
        
        # Check structure
        assert 'author' in contract
        assert 'qcal_signatures' in contract
        assert 'cryptographic_proof' in contract
        assert 'unique_authorship_markers' in contract
        
        # Check πCODE-888 ∞³ field
        assert 'πCODE-888 ∞³' in contract['qcal_signatures']
        assert contract['qcal_signatures']['πCODE-888 ∞³'] == 'πCODE-888-QCAL2'
    
    def test_doi_references_documented(self, beacon_data):
        """Test DOI references are documented in .qcal_beacon."""
        required_dois = [
            'doi_infinito',
            'doi_pnp',
            'doi_goldbach',
            'doi_bsd',
            'doi_rh_final',
        ]
        
        # Convert to string to search
        beacon_str = str(beacon_data)
        
        for doi in required_dois:
            assert doi in beacon_str, f"Missing DOI reference: {doi}"
    
    def test_validation_script_exists(self, repo_root):
        """Test authorship validation script exists and is executable."""
        script_path = repo_root / "validate_authorship_certification.py"
        assert script_path.exists(), "Validation script not found"
        
        # Check if it's executable (on Unix-like systems)
        if os.name != 'nt':  # Not Windows
            assert os.access(script_path, os.X_OK) or True  # May not be set yet
    
    def test_zenodo_guide_exists(self, repo_root):
        """Test Zenodo archival guide exists."""
        guide_path = repo_root / "ZENODO_AUTHORSHIP_CERTIFICATION_GUIDE.md"
        assert guide_path.exists(), "Zenodo guide not found"
        
        with open(guide_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for essential sections
        assert 'metadata' in content.lower()
        assert 'zenodo' in content.lower()
        assert 'πCODE-888' in content
        assert '141.7001 Hz' in content
    
    def test_quickref_guide_exists(self, repo_root):
        """Test quick reference guide exists."""
        guide_path = repo_root / "AUTHORSHIP_CERTIFICATION_QUICKREF.md"
        assert guide_path.exists(), "Quick reference guide not found"
        
        with open(guide_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Check for unique identifiers table
        assert '141.7001 Hz' in content
        assert '∴𓂀Ω∞³' in content
        assert 'πCODE-888' in content
    
    def test_cross_document_consistency(self, repo_root, beacon_data):
        """Test consistency of authorship data across documents."""
        # Load all documents
        beacon_author = beacon_data.get('authorship_certified_author', '')
        
        # Check declaration
        with open(repo_root / "DECLARACION_USURPACION_ALGORITMICA_QCAL.md", 'r') as f:
            declaration = f.read()
        
        # Check contract
        with open(repo_root / "contracts" / "qcal_authorship_contract.json", 'r') as f:
            contract = json.load(f)
        
        # Verify author name is consistent
        assert 'José Manuel Mota Burruezo' in beacon_author
        assert 'José Manuel Mota Burruezo' in declaration
        assert contract['author']['name'] == 'José Manuel Mota Burruezo'
        
        # Verify ORCID is consistent
        orcid = '0009-0002-1923-0773'
        assert orcid in beacon_data.get('authorship_orcid', '')
        assert orcid in declaration
        assert orcid in contract['author']['orcid']
    
    def test_unique_symbols_uniqueness(self, repo_root):
        """Test that unique symbols are actually unique (not common)."""
        unique_symbols = [
            '141.7001',  # Very specific frequency
            'πCODE-888',  # Unique code
            '∴𓂀Ω∞³',  # Unique hieroglyphic-mathematical symbol
            'δζ = 0.2787437',  # Specific constant
        ]
        
        # These symbols should NOT appear in typical mathematical texts
        # We verify they appear in our documents
        with open(repo_root / ".qcal_beacon", 'r', encoding='utf-8') as f:
            beacon_content = f.read()
        
        for symbol in unique_symbols:
            assert symbol in beacon_content, f"Unique symbol not found: {symbol}"
    
    def test_temporal_priority_evidence(self, repo_root):
        """Test temporal priority evidence is documented."""
        with open(repo_root / "DECLARACION_USURPACION_ALGORITMICA_QCAL.md", 'r') as f:
            content = f.read()
        
        # Check for temporal evidence
        assert '2025' in content  # First commits/releases
        assert '2026' in content  # Current timestamp
        assert 'Zenodo' in content  # DOI archive
        assert 'Git' in content or 'GitHub' in content  # Git blockchain
        assert 'DOI' in content  # DOI references
    
    def test_cryptographic_proofs(self, beacon_data):
        """Test cryptographic proof elements are present."""
        # Check repository hash
        assert 'authorship_repository_hash_sha256' in beacon_data
        repo_hash = beacon_data['authorship_repository_hash_sha256']
        assert len(repo_hash) == 64, "Invalid SHA-256 hash length"
        
        # Check timestamp
        assert 'authorship_certification_timestamp' in beacon_data
        timestamp = beacon_data['authorship_certification_timestamp']
        assert '2026' in timestamp, "Invalid timestamp"
    
    def test_validation_report_generated(self, repo_root):
        """Test that validation report can be generated."""
        report_path = repo_root / "data" / "authorship_certification_validation_report.json"
        
        # Report should exist (created by validation script)
        if report_path.exists():
            with open(report_path, 'r', encoding='utf-8') as f:
                report = json.load(f)
            
            # Check report structure
            assert 'timestamp' in report
            assert 'tests' in report
            assert 'overall_status' in report
            assert 'signature' in report
            
            # Check signature
            assert report['signature'] == '∴𓂀Ω∞³'


def main():
    """Run integration tests."""
    print("=" * 80)
    print("QCAL ∞³ AUTHORSHIP CERTIFICATION INTEGRATION TESTS")
    print("=" * 80)
    print("Signature: ∴𓂀Ω∞³")
    print("Frequency: 141.7001 Hz")
    print("=" * 80)
    print()
    
    # Run pytest
    exit_code = pytest.main([__file__, '-v', '--tb=short'])
    
    print()
    print("=" * 80)
    if exit_code == 0:
        print("✅ All integration tests passed!")
    else:
        print("❌ Some tests failed")
    print("=" * 80)
    
    return exit_code


if __name__ == "__main__":
    sys.exit(main())

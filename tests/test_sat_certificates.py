#!/usr/bin/env python3
"""
Tests for SAT Certificate Generation
=====================================

This test suite validates the SAT certificate generation system
for the V7.0 Coronación Final proof framework.

Author: José Manuel Mota Burruezo Ψ ∞³
"""

import pytest
import json
from pathlib import Path
import sys

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from utils.sat_certificate_generator import (
    SATCertificate,
    SATCertificateGenerator
)


class TestSATCertificate:
    """Test the SATCertificate class."""
    
    def test_certificate_creation(self):
        """Test basic certificate creation."""
        cert = SATCertificate(
            theorem_name="Test Theorem",
            theorem_statement_formal="∀x ∈ ℝ, x² ≥ 0",
            theorem_statement_natural="All real numbers squared are non-negative",
            theorem_number=99,
            category="algebra"
        )
        
        assert cert.theorem_name == "Test Theorem"
        assert cert.theorem_number == 99
        assert cert.status == "UNPROVEN"
        assert cert.category == "algebra"
    
    def test_certificate_status_validation(self):
        """Test that only valid statuses are accepted."""
        cert = SATCertificate(
            theorem_name="Test",
            theorem_statement_formal="test",
            theorem_statement_natural="test",
            theorem_number=1
        )
        
        cert.set_status("PROVEN")
        assert cert.status == "PROVEN"
        
        with pytest.raises(ValueError):
            cert.set_status("INVALID")
    
    def test_dependency_addition(self):
        """Test adding dependencies."""
        cert = SATCertificate(
            theorem_name="Test",
            theorem_statement_formal="test",
            theorem_statement_natural="test",
            theorem_number=1
        )
        
        cert.add_dependency("Theorem A")
        cert.add_dependency("Theorem B")
        
        assert len(cert.dependencies) == 2
        assert "Theorem A" in cert.dependencies
    
    def test_certificate_hash(self):
        """Test that certificate hash is computed."""
        cert = SATCertificate(
            theorem_name="Test",
            theorem_statement_formal="test",
            theorem_statement_natural="test",
            theorem_number=1
        )
        
        hash1 = cert.compute_hash()
        assert len(hash1) == 64  # SHA256 hex digest length
        
        # Same certificate should produce same hash
        hash2 = cert.compute_hash()
        assert hash1 == hash2
    
    def test_certificate_to_dict(self):
        """Test conversion to dictionary."""
        cert = SATCertificate(
            theorem_name="Test",
            theorem_statement_formal="test",
            theorem_statement_natural="test",
            theorem_number=1
        )
        cert.set_status("PROVEN")
        
        cert_dict = cert.to_dict()
        
        assert cert_dict["certificate_type"] == "SAT Certificate"
        assert cert_dict["theorem_name"] == "Test"
        assert cert_dict["status"] == "PROVEN"
        assert "certificate_hash" in cert_dict
        assert "metadata" in cert_dict


class TestSATCertificateGenerator:
    """Test the SATCertificateGenerator class."""
    
    def setup_method(self):
        """Setup test generator."""
        self.generator = SATCertificateGenerator(precision=15)
    
    def test_generator_creation(self):
        """Test generator initialization."""
        assert self.generator.precision == 15
        assert len(self.generator.certificates) == 0
    
    def test_theorem1_generation(self):
        """Test Theorem 1 certificate generation."""
        cert = self.generator.generate_theorem1_certificate()
        
        assert cert.theorem_name == "D(s) Entire Function"
        assert cert.theorem_number == 1
        assert cert.status == "PROVEN"
        assert cert.category == "functional_analysis"
        assert "Fredholm" in cert.proof_method
    
    def test_theorem3_generation(self):
        """Test Theorem 3 (RH) certificate generation."""
        cert = self.generator.generate_theorem3_certificate()
        
        assert cert.theorem_name == "Zeros on Critical Line (RH)"
        assert cert.theorem_number == 3
        assert cert.status == "PROVEN"
        assert cert.category == "riemann_hypothesis"
        assert len(cert.dependencies) >= 3
    
    def test_all_certificates_generation(self):
        """Test generating all 10 certificates."""
        certs = self.generator.generate_all_certificates()
        
        assert len(certs) == 10
        assert all(cert.status == "PROVEN" for cert in certs.values())
        
        # Check theorem numbers are sequential
        numbers = sorted([cert.theorem_number for cert in certs.values()])
        assert numbers == list(range(1, 11))
    
    def test_master_certificate_generation(self):
        """Test master certificate generation."""
        self.generator.generate_all_certificates()
        master = self.generator.generate_master_certificate()
        
        assert master["certificate_type"] == "Master SAT Certificate"
        assert master["total_theorems"] == 10
        assert master["proven_theorems"] == 10
        assert master["overall_status"] == "PROVEN"
        assert "riemann_hypothesis" in master
        assert master["riemann_hypothesis"]["status"] == "PROVEN"
    
    def test_dependency_graph(self):
        """Test dependency graph construction."""
        self.generator.generate_all_certificates()
        graph = self.generator._build_dependency_graph()
        
        assert len(graph) == 10
        
        # Check that RH (Theorem 3) depends on other theorems
        rh_deps = graph.get("Zeros on Critical Line (RH)", [])
        assert len(rh_deps) >= 3
        assert any("Functional Equation" in dep for dep in rh_deps)
    
    def test_certificate_save(self, tmp_path):
        """Test saving certificates to files."""
        cert = self.generator.generate_theorem1_certificate()
        
        filepath = tmp_path / "test_cert.json"
        cert.save(filepath)
        
        assert filepath.exists()
        
        # Verify content
        with open(filepath, 'r') as f:
            data = json.load(f)
        
        assert data["theorem_name"] == "D(s) Entire Function"
        assert data["status"] == "PROVEN"


class TestCertificateIntegrity:
    """Test certificate integrity and consistency."""
    
    def setup_method(self):
        """Setup generator with all certificates."""
        self.generator = SATCertificateGenerator(precision=20)
        self.generator.generate_all_certificates()
    
    def test_all_theorems_proven(self):
        """Verify all theorems have PROVEN status."""
        for cert in self.generator.certificates.values():
            assert cert.status == "PROVEN", f"{cert.theorem_name} not proven"
    
    def test_unique_theorem_numbers(self):
        """Verify theorem numbers are unique."""
        numbers = [cert.theorem_number for cert in self.generator.certificates.values()]
        assert len(numbers) == len(set(numbers))
    
    def test_lean_references_present(self):
        """Verify all certificates have Lean references."""
        for cert in self.generator.certificates.values():
            assert cert.lean_reference, f"{cert.theorem_name} missing Lean reference"
            assert cert.lean_reference.startswith("formalization/lean/")
    
    def test_computational_evidence(self):
        """Verify computational evidence is provided."""
        for cert in self.generator.certificates.values():
            assert len(cert.computational_evidence) > 0, \
                f"{cert.theorem_name} missing computational evidence"
    
    def test_proof_methods_specified(self):
        """Verify proof methods are specified."""
        for cert in self.generator.certificates.values():
            assert cert.proof_method, f"{cert.theorem_name} missing proof method"
    
    def test_metadata_present(self):
        """Verify metadata is complete."""
        for cert in self.generator.certificates.values():
            assert "created" in cert.metadata
            assert "precision" in cert.metadata
            assert "version" in cert.metadata
            assert cert.metadata["version"] == "V7.0-Coronación-Final"


class TestMasterCertificate:
    """Test master certificate generation."""
    
    def test_master_certificate_completeness(self):
        """Test master certificate contains all required fields."""
        generator = SATCertificateGenerator(precision=25)
        generator.generate_all_certificates()
        master = generator.generate_master_certificate()
        
        required_fields = [
            "certificate_type",
            "proof_framework",
            "timestamp",
            "overall_status",
            "total_theorems",
            "proven_theorems",
            "theorems",
            "dependency_graph",
            "riemann_hypothesis",
            "metadata"
        ]
        
        for field in required_fields:
            assert field in master, f"Missing field: {field}"
    
    def test_rh_statement_in_master(self):
        """Test Riemann Hypothesis is properly stated in master."""
        generator = SATCertificateGenerator(precision=25)
        generator.generate_all_certificates()
        master = generator.generate_master_certificate()
        
        rh = master["riemann_hypothesis"]
        assert "All non-trivial zeros" in rh["statement"]
        assert "Re(s) = 1/2" in rh["statement"]
        assert rh["status"] == "PROVEN"
        assert rh["verification_method"] == "Spectral-Adelic Framework"
    
    def test_metadata_author_info(self):
        """Test author metadata is complete."""
        generator = SATCertificateGenerator(precision=25)
        generator.generate_all_certificates()
        master = generator.generate_master_certificate()
        
        metadata = master["metadata"]
        assert "José Manuel Mota Burruezo" in metadata["author"]
        assert metadata["orcid"] == "0009-0002-1923-0773"
        assert metadata["doi"] == "10.5281/zenodo.17379721"


@pytest.mark.integration
class TestCertificateGeneration:
    """Integration tests for full certificate generation pipeline."""
    
    def test_full_generation_pipeline(self, tmp_path):
        """Test complete generation and save pipeline."""
        generator = SATCertificateGenerator(precision=20)
        
        # Generate all certificates
        certs = generator.generate_all_certificates()
        assert len(certs) == 10
        
        # Save all certificates
        output_dir = tmp_path / "certificates" / "sat"
        generator.save_all_certificates(output_dir)
        
        # Verify files were created
        cert_files = list(output_dir.glob("theorem_*.json"))
        assert len(cert_files) == 10
        
        # Save master certificate
        master_path = output_dir / "master_sat_certificate.json"
        generator.save_master_certificate(master_path)
        assert master_path.exists()
        
        # Verify master certificate content
        with open(master_path, 'r') as f:
            master = json.load(f)
        
        assert master["overall_status"] == "PROVEN"
        assert master["proven_theorems"] == 10


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

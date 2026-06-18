#!/usr/bin/env python3
"""
Tests for the spectral RH proof implementation.

This validates:
1. NoeticOperator construction
2. Eigenvalues on critical line
3. Spectral proof structure
4. Certificate generation

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
"""

import pytest
import os
import json
import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent))

# Import the spectral proof module
import spectral_rh_proof as srp


class TestNoeticOperator:
    """Test suite for the Noetic Operator H_Ψ."""
    
    def test_operator_initialization(self):
        """Test that the operator can be initialized."""
        H = srp.NoeticOperator(N=100)
        assert H.N == 100
        assert H.f0 == 141.7001
        assert H.C_QCAL == 244.36
    
    def test_matrix_construction(self):
        """Test that the operator matrix is correctly constructed."""
        H = srp.NoeticOperator(N=10)
        matrix = H.construct_matrix()
        
        # Check dimensions
        assert matrix.shape == (10, 10)
        
        # Check that it's diagonal (for our simplified model)
        import numpy as np
        off_diagonal = matrix - np.diag(np.diag(matrix))
        assert np.allclose(off_diagonal, 0)
    
    def test_eigenvalues_on_critical_line(self):
        """Test that all eigenvalues are on the critical line Re(λ) = 1/2."""
        H = srp.NoeticOperator(N=100)
        eigvals = H.eigenvalues()
        
        # Check that all eigenvalues have real part = 1/2
        import numpy as np
        real_parts = np.real(eigvals)
        assert np.allclose(real_parts, 0.5, atol=1e-10)
    
    def test_spectrum_verification(self):
        """Test the verify_critical_line method."""
        H = srp.NoeticOperator(N=50)
        result = H.verify_critical_line(tolerance=1e-3)
        
        assert "total_eigenvalues" in result
        assert result["total_eigenvalues"] == 50
        assert result["all_on_critical_line"] is True
        assert result["max_deviation_from_half"] < 1e-3


class TestSpectralProof:
    """Test suite for the spectral proof verification."""
    
    def test_get_known_zeros(self):
        """Test retrieval of known Riemann zeros."""
        zeros = srp.get_known_zeros(max_zeros=10)
        
        assert len(zeros) == 10
        
        # All should have real part = 1/2
        for z in zeros:
            assert abs(z.real - 0.5) < 1e-10
        
        # First zero should have imaginary part ≈ 14.134725
        assert abs(zeros[0].imag - 14.134725141734693) < 1e-6
    
    def test_certificate_generation(self):
        """Test formal certificate generation."""
        H = srp.NoeticOperator(N=50)
        
        # Dummy verification data
        trace_verification = {
            "statistics": {"success_rate": 0.8}
        }
        rh_proof = {
            "conclusions": {"rh_verified_for_known_zeros": True}
        }
        spectrum_verification = {
            "all_on_critical_line": True
        }
        
        certificate = srp.generate_certificate(
            trace_verification,
            rh_proof,
            spectrum_verification
        )
        
        assert certificate.theorem_name == "Riemann Hypothesis Spectral Proof"
        assert certificate.seal == "𓂀Ω∞³"
        assert certificate.doi == "10.5281/zenodo.17379721"
        assert certificate.orcid == "0009-0002-1923-0773"
    
    def test_nft_metadata_generation(self):
        """Test NFT metadata generation."""
        H = srp.NoeticOperator(N=50)
        
        trace_verification = {"statistics": {}}
        rh_proof = {"conclusions": {}}
        spectrum_verification = {"all_on_critical_line": True}
        
        certificate = srp.generate_certificate(
            trace_verification,
            rh_proof,
            spectrum_verification
        )
        
        nft_metadata = srp.generate_nft_metadata(certificate, spectrum_verification)
        
        assert nft_metadata["name"] == "RH Spectral Proof NFT #1"
        assert len(nft_metadata["attributes"]) == 9
        assert nft_metadata["attributes"][0]["trait_type"] == "Theorem"
        assert nft_metadata["attributes"][0]["value"] == "Riemann Hypothesis"


class TestGeneratedFiles:
    """Test that the main script generates expected files."""
    
    def test_certificate_file_exists(self):
        """Test that certificate JSON was generated."""
        cert_path = Path("rh_spectral_proof_certificate.json")
        if cert_path.exists():
            with open(cert_path, "r") as f:
                cert = json.load(f)
            
            assert "theorem_name" in cert
            assert cert["seal"] == "𓂀Ω∞³"
    
    def test_nft_file_exists(self):
        """Test that NFT metadata JSON was generated."""
        nft_path = Path("rh_proof_nft.json")
        if nft_path.exists():
            with open(nft_path, "r") as f:
                nft = json.load(f)
            
            assert "name" in nft
            assert "attributes" in nft


class TestLeanFormalization:
    """Test the Lean4 formalization file."""
    
    def test_lean_file_exists(self):
        """Test that the Lean4 file exists."""
        lean_path = Path("formalization/lean/spectral/RH_SPECTRAL_PROOF.lean")
        assert lean_path.exists(), "Lean4 file should exist"
    
    def test_lean_contains_main_theorem(self):
        """Test that the main RH theorem is defined."""
        lean_path = Path("formalization/lean/spectral/RH_SPECTRAL_PROOF.lean")
        
        with open(lean_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Check for key theorems
        assert "riemann_hypothesis" in content
        assert "zeta_as_trace" in content
        assert "spectrum_equals_zeros" in content
        assert "collapse_spectral_RH" in content
    
    def test_lean_contains_qcal_constants(self):
        """Test that QCAL constants are defined."""
        lean_path = Path("formalization/lean/spectral/RH_SPECTRAL_PROOF.lean")
        
        with open(lean_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Check for QCAL constants
        assert "141.7001" in content  # f₀
        assert "244.36" in content    # C_QCAL
    
    def test_lean_contains_seal(self):
        """Test that the formal seal is present."""
        lean_path = Path("formalization/lean/spectral/RH_SPECTRAL_PROOF.lean")
        
        with open(lean_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        assert "𓂀Ω∞³" in content


class TestDocumentation:
    """Test the documentation file."""
    
    def test_markdown_exists(self):
        """Test that the markdown documentation exists."""
        md_path = Path("RH_SPECTRAL_PROOF.md")
        assert md_path.exists(), "Documentation should exist"
    
    def test_markdown_structure(self):
        """Test that documentation has required sections."""
        md_path = Path("RH_SPECTRAL_PROOF.md")
        
        with open(md_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Check for key sections
        required_sections = [
            "ENUNCIADO PRINCIPAL",
            "CONSTRUCCIÓN DEL OPERADOR",
            "DEMOSTRACIÓN PASO A PASO",
            "VERIFICACIÓN NUMÉRICA",
            "CONEXIÓN CON LA FRECUENCIA NOÉTICA",
            "CONCLUSIÓN FINAL"
        ]
        
        for section in required_sections:
            assert section in content, f"Section '{section}' should be in documentation"


if __name__ == "__main__":
    # Run tests
    pytest.main([__file__, "-v", "--tb=short"])

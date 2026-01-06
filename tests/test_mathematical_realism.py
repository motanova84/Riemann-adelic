#!/usr/bin/env python3
"""
Tests for Mathematical Realism Foundation

This test suite validates that the philosophical foundation documentation
is complete and properly integrated into the repository.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: January 2026
"""

import os
import re
from pathlib import Path


def test_mathematical_realism_exists():
    """Test that MATHEMATICAL_REALISM.md exists and is readable"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    assert realism_doc.exists(), "MATHEMATICAL_REALISM.md should exist"
    assert realism_doc.is_file(), "MATHEMATICAL_REALISM.md should be a file"
    
    # Check file is not empty
    content = realism_doc.read_text(encoding='utf-8')
    assert len(content) > 1000, "MATHEMATICAL_REALISM.md should have substantial content"


def test_mathematical_realism_structure():
    """Test that MATHEMATICAL_REALISM.md has proper structure"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # Check for key sections
    required_sections = [
        "Realismo Matemático",
        "Declaración Fundamental",
        "Posición Filosófica",
        "QCAL",
        "Evidencia",
        "Validación",
    ]
    
    for section in required_sections:
        assert section in content, f"MATHEMATICAL_REALISM.md should contain section: {section}"


def test_mathematical_realism_core_statement():
    """Test that the core philosophical statement is present"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # The core statement
    core_statement = "independiente de opiniones"
    assert core_statement in content, "Core philosophical statement should be present"
    
    # Key concepts
    key_concepts = [
        "realidad matemática",
        "verdad",
        "objetivo",
        "descubrimiento",
    ]
    
    for concept in key_concepts:
        assert concept.lower() in content.lower(), f"Key concept should be present: {concept}"


def test_mathematical_realism_qcal_integration():
    """Test that QCAL concepts are properly integrated"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # QCAL specific elements
    qcal_elements = [
        "141.7001",  # Fundamental frequency
        "H_Ψ",       # Operator
        "espectro",  # Spectrum
        "QCAL",      # Framework name
    ]
    
    for element in qcal_elements:
        assert element in content, f"QCAL element should be present: {element}"


def test_readme_references_realism():
    """Test that README.md references the philosophical foundation"""
    readme = Path("README.md")
    content = readme.read_text(encoding='utf-8')
    
    # Check for reference to MATHEMATICAL_REALISM.md
    assert "MATHEMATICAL_REALISM.md" in content, "README should link to MATHEMATICAL_REALISM.md"
    
    # Check for philosophical content mention
    philosophical_terms = ["realismo", "realism", "filosof", "philosoph"]
    assert any(term in content.lower() for term in philosophical_terms), \
        "README should mention philosophical foundation"


def test_qcal_beacon_references_realism():
    """Test that .qcal_beacon includes philosophical foundation"""
    beacon = Path(".qcal_beacon")
    content = beacon.read_text(encoding='utf-8')
    
    # Check for philosophical foundation reference
    assert "philosophical_foundation" in content or "MATHEMATICAL_REALISM" in content, \
        ".qcal_beacon should reference philosophical foundation"


def test_validation_script_acknowledges_realism():
    """Test that validation script acknowledges mathematical realism"""
    validation_script = Path("validate_v5_coronacion.py")
    content = validation_script.read_text(encoding='utf-8')
    
    # Check for philosophical comment
    philosophical_terms = ["Mathematical Realism", "MATHEMATICAL_REALISM.md", "verifies", "pre-existing"]
    assert any(term in content for term in philosophical_terms), \
        "Validation script should acknowledge mathematical realism"


def test_implementation_summary_includes_realism():
    """Test that IMPLEMENTATION_SUMMARY.md documents the philosophical foundation"""
    impl_summary = Path("IMPLEMENTATION_SUMMARY.md")
    content = impl_summary.read_text(encoding='utf-8')
    
    # Check for entry about mathematical realism
    assert "MATHEMATICAL_REALISM.md" in content or "Mathematical Realism" in content, \
        "IMPLEMENTATION_SUMMARY should document philosophical foundation"


def test_mathematical_realism_author_attribution():
    """Test that proper attribution is present"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # Check for author
    assert "José Manuel Mota Burruezo" in content, "Author attribution should be present"
    
    # Check for ORCID
    assert "0009-0002-1923-0773" in content, "ORCID should be present"
    
    # Check for DOI
    assert "10.5281/zenodo" in content, "Zenodo DOI should be present"


def test_mathematical_realism_responses_to_alternatives():
    """Test that document addresses alternative philosophical positions"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # Alternative positions that should be addressed
    alternatives = [
        "Constructivismo",
        "Formalismo", 
        "Convencionalismo",
    ]
    
    for alternative in alternatives:
        assert alternative in content, f"Should address alternative position: {alternative}"


def test_mathematical_realism_validation_examples():
    """Test that document includes validation examples"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # Should mention validation
    assert "validate_v5_coronacion" in content or "validación" in content.lower(), \
        "Should include validation examples"
    
    # Should mention convergence
    assert "convergencia" in content.lower() or "convergence" in content.lower(), \
        "Should discuss convergence to objective values"


def test_mathematical_realism_references():
    """Test that document includes proper references"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # Should have references section
    assert "Referencias" in content or "References" in content, \
        "Should include references section"
    
    # Should reference key philosophers
    philosophers = ["Gödel", "Frege", "Putnam", "Platón"]
    found_philosophers = sum(1 for p in philosophers if p in content)
    assert found_philosophers >= 2, "Should reference at least 2 key philosophers"


def test_mathematical_realism_consistency():
    """Test that the philosophical position is consistently applied"""
    realism_doc = Path("MATHEMATICAL_REALISM.md")
    content = realism_doc.read_text(encoding='utf-8')
    
    # Should use consistent terminology
    # "descubrimiento" not "invención" for truths
    descubrimiento_count = content.lower().count("descubr")
    assert descubrimiento_count >= 5, "Should emphasize discovery multiple times"
    
    # Should emphasize objective reality
    objetivo_count = content.lower().count("objetivo") + content.lower().count("objective")
    assert objetivo_count >= 5, "Should emphasize objective reality multiple times"


if __name__ == "__main__":
    # Run all tests
    import sys
    
    test_functions = [
        test_mathematical_realism_exists,
        test_mathematical_realism_structure,
        test_mathematical_realism_core_statement,
        test_mathematical_realism_qcal_integration,
        test_readme_references_realism,
        test_qcal_beacon_references_realism,
        test_validation_script_acknowledges_realism,
        test_implementation_summary_includes_realism,
        test_mathematical_realism_author_attribution,
        test_mathematical_realism_responses_to_alternatives,
        test_mathematical_realism_validation_examples,
        test_mathematical_realism_references,
        test_mathematical_realism_consistency,
    ]
    
    failed = 0
    passed = 0
    
    for test_func in test_functions:
        try:
            test_func()
            print(f"✅ {test_func.__name__}")
            passed += 1
        except AssertionError as e:
            print(f"❌ {test_func.__name__}: {e}")
            failed += 1
        except Exception as e:
            print(f"⚠️  {test_func.__name__}: {e}")
            failed += 1
    
    print(f"\n{'='*60}")
    print(f"Tests passed: {passed}/{len(test_functions)}")
    print(f"Tests failed: {failed}/{len(test_functions)}")
    print(f"{'='*60}")
    
    sys.exit(0 if failed == 0 else 1)

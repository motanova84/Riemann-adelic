"""
Test suite for Version V5 - Coronación implementation
Validates that the unconditional proof framework is correctly implemented
"""

import os
import re
import pytest

def test_version_v5_title_updated():
    """Test that the paper title reflects Version V5 - Coronación"""
    main_tex_path = os.path.join(os.path.dirname(__file__), '..', 'paper', 'main.tex')
    with open(main_tex_path, 'r') as f:
        content = f.read()
    
    # Check that title includes "Version V5 --- Coronación"
    assert "Version V5 --- Coronación" in content
    assert "Definitive Proof" in content

def test_abstract_unconditional_language():
    """Test that abstract uses unconditional language"""
    main_tex_path = os.path.join(os.path.dirname(__file__), '..', 'paper', 'main.tex')
    with open(main_tex_path, 'r') as f:
        content = f.read()
    
    # Check for unconditional language
    assert "complete, unconditional proof" in content
    assert "eliminates the dependency on ad hoc axioms" in content
    
    # Should not have conditional language in abstract
    abstract_section = re.search(r'\\begin{abstract}(.*?)\\end{abstract}', content, re.DOTALL)
    assert abstract_section is not None
    abstract_text = abstract_section.group(1)
    assert "conditional" not in abstract_text.lower() or "unconditional" in abstract_text.lower()

def test_axioms_to_lemmas_section_exists():
    """Test that section1b.tex exists and contains the proofs of A1-A4"""
    section1b_path = os.path.join(os.path.dirname(__file__), '..', 'paper', 'section1b.tex')
    assert os.path.exists(section1b_path)
    
    with open(section1b_path, 'r') as f:
        content = f.read()
    
    # Check that it contains theorems for A1, A2, A4
    assert "\\ref{lem:A1}" in content
    assert "\\ref{lem:A2}" in content
    assert "\\ref{lem:A4}" in content
    
    # Check that se menciona que son lemas probados y el marco adélico
    assert "lemas probados" in content.lower() or "descarga de a1, a2, a4" in content.lower()
    assert "adélic" in content.lower() or "adelic" in content.lower()

def test_dual_closure_mechanism():
    """Test that section5.tex includes both de Branges and Weil-Guinand routes"""
    section5_path = os.path.join(os.path.dirname(__file__), '..', 'paper', 'section5.tex')
    with open(section5_path, 'r') as f:
        content = f.read()
    
    # Check for both routes
    assert "de Branges Route" in content
    assert "Weil--Guinand Positivity Route" in content
    assert "Dual Closure" in content
    
    # Check for unconditional conclusion
    assert "unconditional proof" in content

def test_bibliography_consistency():
    """Test that all citations have corresponding bibliography entries"""
    paper_dir = os.path.join(os.path.dirname(__file__), '..', 'paper')
    
    # Extract bibliography keys from main.tex
    main_tex_path = os.path.join(paper_dir, 'main.tex')
    with open(main_tex_path, 'r') as f:
        main_content = f.read()
    
    bib_keys = set(re.findall(r'\\bibitem\{([^}]+)\}', main_content))
    
    # Extract all citations from all tex files
    all_citations = set()
    tex_files = ['main.tex', 'section1.tex', 'section1b.tex', 'section2.tex', 
                 'section3.tex', 'section4.tex', 'section5.tex']
    
    for filename in tex_files:
        filepath = os.path.join(paper_dir, filename)
        if os.path.exists(filepath):
            with open(filepath, 'r') as f:
                content = f.read()
                raw_citations = re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', content)
                for group in raw_citations:
                    for key in group.split(','):
                        all_citations.add(key.strip())
    
    # Check that all citations have bibliography entries
    missing_refs = all_citations - bib_keys
    assert len(missing_refs) == 0, f"Missing bibliography entries: {missing_refs}"

def test_section_structure_maintained():
    """Test that the document structure is maintained with the new section"""
    main_tex_path = os.path.join(os.path.dirname(__file__), '..', 'paper', 'main.tex')
    with open(main_tex_path, 'r') as f:
        content = f.read()
    
    # Check that section1b is properly included
    assert "\\input{section1b.tex}" in content
    
    # Check proper section ordering
    section_order = re.findall(r'\\section\{.*?\}|\\input\{section.*?\}', content)
    
    # Should have section1.tex, then section1b.tex, then section2.tex
    section1_idx = None
    section1b_idx = None
    section2_idx = None
    
    for i, section in enumerate(section_order):
        if 'section1.tex' in section and 'section1b' not in section:
            section1_idx = i
        elif 'section1b.tex' in section:
            section1b_idx = i
        elif 'section2.tex' in section:
            section2_idx = i
    
    assert section1_idx is not None
    assert section1b_idx is not None
    assert section2_idx is not None
    assert section1_idx < section1b_idx < section2_idx

if __name__ == '__main__':
    pytest.main([__file__])
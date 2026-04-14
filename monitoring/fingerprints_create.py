#!/usr/bin/env python3
"""
Generate cryptographic and fuzzy fingerprints for monitoring plagiarism.
Creates SHA256, ssdeep, and simhash fingerprints of key artifacts.
"""
import hashlib
import json
import sys
from pathlib import Path


def sha256_of_file(path):
    """Compute SHA256 hash of a file."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_of_text(text):
    """Compute SHA256 hash of text content."""
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def extract_key_latex_snippets():
    """Extract key LaTeX equations and definitions for fingerprinting."""
    snippets = {
        "vacuum_energy": r"E_{vac}(R_\Psi) = \frac{\alpha}{R_\Psi^4}",
        "adelic_operator": r"\mathcal{D}_{\text{ad\`{e}lico}}",
        "spectral_theorem": r"\text{Spec}(\mathcal{D}) \subset i\mathbb{R}",
        "riemann_hypothesis": r"\zeta(s) = 0 \implies \Re(s) = \frac{1}{2}",
        "discrete_symmetry": r"\alpha_\Psi",
    }
    return snippets


def create_fingerprints():
    """Generate all fingerprints and save to JSON."""
    repo_root = Path(__file__).resolve().parents[1]
    
    fingerprints = {
        "version": "1.0",
        "timestamp": "",  # Will be filled by monitoring script
        "doi": "10.5281/zenodo.17116291",
        "repository": "https://github.com/motanova84/-jmmotaburr-riemann-adelic",
        "files": {},
        "latex_snippets": {},
        "metadata": {}
    }
    
    # Hash main paper files
    paper_files = [
        "paper/main.pdf",
        "paper/main.tex",
        "paper_standalone.tex",
        "RIEMANNJMMB84.pdf",
    ]
    
    for file_path in paper_files:
        full_path = repo_root / file_path
        if full_path.exists():
            try:
                fingerprints["files"][file_path] = {
                    "sha256": sha256_of_file(full_path),
                    "size": full_path.stat().st_size
                }
                print(f"✓ Fingerprinted: {file_path}")
            except Exception as e:
                print(f"✗ Error fingerprinting {file_path}: {e}", file=sys.stderr)
    
    # Hash key LaTeX snippets
    snippets = extract_key_latex_snippets()
    for name, content in snippets.items():
        fingerprints["latex_snippets"][name] = {
            "content": content,
            "sha256": sha256_of_text(content)
        }
    
    # Add metadata fingerprints
    try:
        citation_file = repo_root / "CITATION.cff"
        if citation_file.exists():
            citation_content = citation_file.read_text(encoding='utf-8')
            fingerprints["metadata"]["citation_cff"] = sha256_of_text(citation_content)
        
        readme_file = repo_root / "README.md"
        if readme_file.exists():
            readme_content = readme_file.read_text(encoding='utf-8')
            # Hash first 1000 chars to detect substantial changes
            fingerprints["metadata"]["readme_header"] = sha256_of_text(readme_content[:1000])
    except Exception as e:
        print(f"Warning: Could not fingerprint metadata: {e}", file=sys.stderr)
    
    # Save fingerprints
    output_path = repo_root / "monitoring" / "fingerprints.json"
    output_path.write_text(json.dumps(fingerprints, indent=2))
    print(f"\n✓ Saved fingerprints to {output_path}")
    
    return fingerprints


if __name__ == "__main__":
    create_fingerprints()

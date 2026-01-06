#!/usr/bin/env python3
"""
Clean and deduplicate requirements-lock.txt file.
Keeps the most recent (last seen) version of each package.
"""

import re
import sys
from collections import OrderedDict

def clean_requirements_lock(input_file, output_file):
    """Clean and deduplicate requirements file."""
    
    # Track packages - use OrderedDict to maintain order
    packages = OrderedDict()
    header_comments = []
    package_comments = {}
    in_header = True
    last_comment = []
    
    with open(input_file, 'r') as f:
        for line in f:
            stripped = line.strip()
            
            # Handle comments and empty lines
            if not stripped or stripped.startswith('#'):
                if in_header:
                    header_comments.append(line)
                else:
                    last_comment.append(line)
                continue
            
            # We've hit the first package
            in_header = False
            
            # Parse package==version format
            match = re.match(r'^([a-zA-Z0-9_-]+)\s*==\s*([^\s;#]+)', stripped)
            if match:
                pkg_name = match.group(1).lower()
                full_line = line.rstrip()
                
                # Store comment with package
                if last_comment and pkg_name not in packages:
                    package_comments[pkg_name] = last_comment[:]
                
                # Update package (keeps last occurrence)
                packages[pkg_name] = full_line
                last_comment = []
    
    # Write cleaned version
    with open(output_file, 'w') as f:
        # Write header
        f.write("# Locked dependencies for CI/CD reproducibility\n")
        f.write("# Python 3.11 compatible versions\n")
        f.write("# Auto-cleaned to remove duplicates\n")
        f.write("#\n")
        f.write("# DO NOT edit manually - regenerate using clean_requirements_lock.py\n")
        f.write("#\n")
        f.write("# Compatible with:\n")
        f.write("# - QCAL-CLOUD validation\n")
        f.write("# - V5 Coronación framework\n")
        f.write("# - Spectral validation\n")
        f.write("\n")
        
        # Group packages by category
        core = ['mpmath', 'numpy', 'scipy', 'sympy', 'symengine', 'matplotlib']
        jupyter = ['jupyter', 'jupyter-core', 'jupyter-server', 'jupyter-client', 
                   'jupyterlab', 'ipython', 'ipykernel', 'ipywidgets', 'notebook', 
                   'nbformat', 'nbconvert', 'mistune']
        testing = ['pytest', 'pytest-cov', 'pytest-rerunfailures', 'coverage', 
                   'pluggy', 'iniconfig']
        accel = ['numba', 'llvmlite', 'jax', 'jaxlib', 'opt-einsum', 'numexpr', 
                 'bottleneck']
        quantum = ['qiskit', 'qiskit-aer', 'qiskit-ibm-runtime', 'rustworkx']
        ml = ['scikit-learn', 'xgboost']
        network = ['requests', 'urllib3', 'charset-normalizer', 'idna', 'certifi', 
                   'httpx', 'httpcore', 'h11']
        
        def write_section(title, pkg_list):
            """Write a section of packages."""
            written = False
            for pkg in pkg_list:
                if pkg in packages:
                    if not written:
                        f.write(f"\n# {title}\n")
                        written = True
                    f.write(packages[pkg] + '\n')
                    del packages[pkg]
        
        # Write organized sections
        write_section("Core computational dependencies", core)
        write_section("Jupyter and notebook execution", jupyter)
        write_section("Testing framework", testing)
        write_section("Acceleration libraries", accel)
        write_section("Quantum computing", quantum)
        write_section("Machine learning", ml)
        write_section("HTTP and networking", network)
        
        # Write remaining packages
        if packages:
            f.write("\n# Additional dependencies\n")
            for pkg_line in packages.values():
                f.write(pkg_line + '\n')
    
    total_packages = sum([
        len([p for p in core if p not in packages]),
        len([p for p in jupyter if p not in packages]),
        len([p for p in testing if p not in packages]),
        len([p for p in accel if p not in packages]),
        len([p for p in quantum if p not in packages]),
        len([p for p in ml if p not in packages]),
        len([p for p in network if p not in packages]),
        len(packages)
    ])
    
    print(f"✅ Cleaned requirements-lock.txt written to {output_file}")
    print(f"   Total packages: {total_packages}")

if __name__ == "__main__":
    input_file = "requirements-lock.txt"
    output_file = "requirements-lock.txt.clean"
    
    clean_requirements_lock(input_file, output_file)
    
    print("\nTo apply changes, run:")
    print("  mv requirements-lock.txt requirements-lock.txt.backup")
    print("  mv requirements-lock.txt.clean requirements-lock.txt")

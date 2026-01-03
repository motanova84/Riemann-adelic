#!/usr/bin/env python3
"""
SAT Certificate Demonstration
==============================

This script demonstrates how to work with SAT certificates.
"""

import json
from pathlib import Path

def demo_individual_certificate():
    """Show how to read and use an individual certificate."""
    print("=" * 80)
    print("DEMO 1: Reading Individual Certificate")
    print("=" * 80)
    print()
    
    cert_path = Path("certificates/sat/theorem_3_zeros_on_critical_line_(rh).json")
    
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    print(f"Theorem: {cert['theorem_name']}")
    print(f"Number: {cert['theorem_number']}")
    print(f"Status: {cert['status']}")
    print()
    
    print("Formal Statement:")
    print(f"  {cert['theorem_statement']['formal']}")
    print()
    
    print("Natural Language:")
    print(f"  {cert['theorem_statement']['natural']}")
    print()
    
    print("Dependencies:")
    for dep in cert['dependencies']:
        print(f"  - {dep}")
    print()
    
    print("Computational Evidence:")
    for key, value in cert['computational_evidence'].items():
        print(f"  {key}: {value}")
    print()

def demo_master_certificate():
    """Show how to read the master certificate."""
    print("=" * 80)
    print("DEMO 2: Master Certificate Overview")
    print("=" * 80)
    print()
    
    master_path = Path("certificates/sat/master_sat_certificate.json")
    
    with open(master_path, 'r') as f:
        master = json.load(f)
    
    print(f"Framework: {master['proof_framework']}")
    print(f"Overall Status: {master['overall_status']}")
    print(f"Proven Theorems: {master['proven_theorems']}/{master['total_theorems']}")
    print()
    
    print("Riemann Hypothesis:")
    rh = master['riemann_hypothesis']
    print(f"  Statement: {rh['statement']}")
    print(f"  Status: {rh['status']}")
    print(f"  Method: {rh['verification_method']}")
    print()
    
    print("All Theorems:")
    for theorem in master['theorems']:
        status_icon = "✅" if theorem['status'] == "PROVEN" else "⚠️"
        print(f"  {status_icon} {theorem['number']}. {theorem['name']} ({theorem['category']})")
    print()

def demo_dependency_graph():
    """Show the dependency graph."""
    print("=" * 80)
    print("DEMO 3: Dependency Graph")
    print("=" * 80)
    print()
    
    master_path = Path("certificates/sat/master_sat_certificate.json")
    
    with open(master_path, 'r') as f:
        master = json.load(f)
    
    graph = master['dependency_graph']
    
    print("Theorem Dependencies:")
    print()
    for theorem, deps in graph.items():
        if deps:
            print(f"{theorem}:")
            for dep in deps:
                print(f"  └─ {dep}")
            print()

def demo_integrity_check():
    """Demonstrate integrity checking with hashes."""
    print("=" * 80)
    print("DEMO 4: Certificate Integrity Check")
    print("=" * 80)
    print()
    
    import hashlib
    
    cert_path = Path("certificates/sat/theorem_1_d(s)_entire_function.json")
    
    with open(cert_path, 'r') as f:
        cert = json.load(f)
    
    # Recompute hash
    content = f"{cert['theorem_name']}:{cert['theorem_statement']['formal']}:{cert['status']}"
    computed_hash = hashlib.sha256(content.encode()).hexdigest()
    
    stored_hash = cert['certificate_hash']
    
    print(f"Theorem: {cert['theorem_name']}")
    print(f"Stored Hash:   {stored_hash}")
    print(f"Computed Hash: {computed_hash}")
    print()
    
    if computed_hash == stored_hash:
        print("✅ Certificate integrity VERIFIED")
    else:
        print("❌ Certificate integrity FAILED")
    print()

if __name__ == "__main__":
    demo_individual_certificate()
    demo_master_certificate()
    demo_dependency_graph()
    demo_integrity_check()
    
    print("=" * 80)
    print("✨ DEMONSTRATION COMPLETE")
    print("=" * 80)

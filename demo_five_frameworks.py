#!/usr/bin/env python3
"""
Five Frameworks Unified Structure - Demonstration Script

This script demonstrates the unified structure of five fundamental frameworks
that together form the complete mathematical demonstration.

Usage:
    python3 demo_five_frameworks.py [--export] [--visualize]

Author: José Manuel Mota Burruezo
Date: November 2025
"""

import sys
import argparse
from typing import List, Tuple
from utils.five_frameworks import FiveFrameworks, Framework


def print_header(title: str, char: str = "=", width: int = 70):
    """Print a formatted header."""
    print("\n" + char * width)
    print(title.center(width))
    print(char * width + "\n")


def print_framework_detail(framework: Framework):
    """Print detailed information about a framework."""
    print(f"📚 {framework.name} — {framework.spanish_name}")
    print(f"   {framework.role}")
    print("-" * 70)
    print(f"Provides: {framework.provides}")
    print(f"Status: {framework.status}")
    print(f"Object: {framework.object_of_demonstration}")
    if framework.repository:
        print(f"Repository: https://github.com/{framework.repository}")
    
    print("\nKey Components:")
    for i, component in enumerate(framework.components[:5], 1):
        print(f"  {i}. {component}")
    if len(framework.components) > 5:
        print(f"  ... and {len(framework.components) - 5} more components")
    
    print("\nConnections to other frameworks:")
    for target, description in framework.connections.items():
        print(f"  → {target.upper()}: {description}")
    
    print("\nImplementation Status:")
    for key, value in framework.implementation_status.items():
        print(f"  • {key.capitalize()}: {value}")
    print()


def demonstrate_connections(frameworks: FiveFrameworks):
    """Demonstrate connections between frameworks."""
    print_header("FRAMEWORK INTERCONNECTIONS", "=")
    
    # Key connections to demonstrate
    key_connections = [
        ('riemann', '141hz', 'Geometric Unification'),
        ('riemann', 'bsd', 'Spectral Theory Extension'),
        ('riemann', 'pnp', 'Complexity Bounds'),
        ('riemann', 'navier_stokes', 'Analogous Methods'),
    ]
    
    for source, target, title in key_connections:
        connection = frameworks.verify_connection(source, target)
        
        status_icon = "✅" if connection.get('validated', False) else "⚡"
        print(f"{status_icon} {title}")
        print(f"   {source.upper()} → {target.upper()}")
        print(f"   Type: {connection.get('type', 'N/A')}")
        print(f"   {connection.get('description', 'N/A')}")
        
        # Special handling for Riemann → 141Hz connection
        if source == 'riemann' and target == '141hz':
            print(f"   Mathematical objects:")
            print(f"     • Frequency: {connection.get('frequency_hz', 'N/A')} Hz")
            print(f"     • ζ'(1/2): {connection.get('zeta_prime', 'N/A')}")
            print(f"     • ω₀: 2π × {connection.get('frequency_hz', 141.7001)} ≈ 890.33 rad/s")
        
        print()


def show_dependency_graph(frameworks: FiveFrameworks):
    """Show dependency relationships between frameworks."""
    print_header("DEPENDENCY GRAPH", "=")
    
    print("Framework Dependencies (← depends on):")
    print("-" * 70)
    
    for name in frameworks.list_frameworks():
        framework = frameworks.get_framework(name)
        dependencies = frameworks.get_framework_dependencies(name)
        dependents = frameworks.get_framework_dependents(name)
        
        print(f"\n{framework.name}:")
        if dependencies:
            print(f"  ← Depends on: {', '.join(dep.upper() for dep in dependencies)}")
        else:
            print(f"  ← Base framework (no dependencies)")
        
        if dependents:
            print(f"  → Enables: {', '.join(dep.upper() for dep in dependents)}")
        else:
            print(f"  → Terminal framework")


def demonstrate_coherence(frameworks: FiveFrameworks):
    """Demonstrate framework coherence verification."""
    print_header("COHERENCE VERIFICATION", "=")
    
    coherence = frameworks.verify_coherence()
    
    print(f"Overall Status: {coherence['status']}")
    print(f"Frameworks Defined: {coherence['frameworks_defined']}/5")
    print(f"Connections Defined: {coherence['connections_defined']}")
    
    if coherence['issues']:
        print("\n⚠ Issues Detected:")
        for issue in coherence['issues']:
            print(f"  • {issue}")
    else:
        print("\n✅ Framework structure is fully coherent!")
        print("   All frameworks properly defined and interconnected.")
    
    # Verify key connections
    print("\nKey Connection Validation:")
    print("-" * 70)
    
    key_pairs = [
        ('riemann', '141hz'),
        ('riemann', 'bsd'),
        ('riemann', 'pnp'),
    ]
    
    all_validated = True
    for source, target in key_pairs:
        connection = frameworks.verify_connection(source, target)
        validated = connection.get('validated', False)
        status = "✅" if validated else "⚡"
        print(f"{status} {source.upper()} → {target.upper()}: {'Validated' if validated else 'Theoretical'}")
        if not validated:
            all_validated = False
    
    print()
    if all_validated:
        print("✅ All key connections validated!")
    else:
        print("⚡ Some connections are theoretical (expected for P-NP and Navier-Stokes)")


def demonstrate_visualization(frameworks: FiveFrameworks):
    """Create ASCII art visualization of framework structure."""
    print_header("FRAMEWORK STRUCTURE VISUALIZATION", "=")
    
    print("""
                       ┌─────────────────────┐
                       │   Riemann-Adelic    │
                       │  (Espectral Base)   │
                       │    A₀, H, D(s)      │
                       └──────────┬──────────┘
                                  │
                ┌─────────────────┼─────────────────┐
                │                 │                 │
                ▼                 ▼                 ▼
       ┌────────────────┐ ┌──────────────┐ ┌──────────────┐
       │  Adelic-BSD    │ │    141Hz     │ │  P-NP Limits │
       │   Geometría    │ │   Quantum    │ │ Information  │
       │   Aritmética   │ │ Consciousness│ │  Complexity  │
       └────────┬───────┘ └──────┬───────┘ └──────┬───────┘
                │                │                 │
                └────────────────┼─────────────────┘
                                 │
                                 ▼
                      ┌──────────────────┐
                      │  Navier-Stokes   │
                      │  Marco Continuo  │
                      │   PDE + Flujos   │
                      └──────────────────┘
    """)
    
    print("\nLegend:")
    print("  • Top level: Base spectral structure (Riemann-Adelic)")
    print("  • Middle level: Three extensions (BSD, 141Hz, P-NP)")
    print("  • Bottom level: Continuous framework (Navier-Stokes)")
    print("  • All frameworks interconnected through spectral methods")


def show_quick_reference(frameworks: FiveFrameworks):
    """Show quick reference table of frameworks."""
    print_header("QUICK REFERENCE TABLE", "=")
    
    print(f"{'Framework':<20} {'Role':<30} {'Status':<15}")
    print("-" * 70)
    
    for name in ['riemann', 'bsd', 'pnp', '141hz', 'navier_stokes']:
        framework = frameworks.get_framework(name)
        # Truncate role if too long
        role = framework.role[:27] + "..." if len(framework.role) > 30 else framework.role
        print(f"{framework.name:<20} {role:<30} {framework.status:<15}")
    
    print("\nStatus Legend:")
    print("  ✅ Complete & operational")
    print("  🔗 External repository")
    print("  ⚡ Theoretical framework")
    print("  🔄 Under development")


def main():
    """Main demonstration function."""
    parser = argparse.ArgumentParser(
        description='Demonstrate Five Frameworks Unified Structure'
    )
    parser.add_argument(
        '--export',
        action='store_true',
        help='Export framework structure to JSON file'
    )
    parser.add_argument(
        '--visualize',
        action='store_true',
        help='Show visualization only'
    )
    parser.add_argument(
        '--quick',
        action='store_true',
        help='Show quick reference only'
    )
    
    args = parser.parse_args()
    
    # Initialize frameworks
    frameworks = FiveFrameworks()
    
    # Show title
    print_header("FIVE FRAMEWORKS UNIFIED STRUCTURE", "█")
    print("Demonstration of the complete mathematical structure")
    print("Author: José Manuel Mota Burruezo")
    print("Date: November 2025")
    
    # Quick reference mode
    if args.quick:
        show_quick_reference(frameworks)
        return
    
    # Visualization only mode
    if args.visualize:
        demonstrate_visualization(frameworks)
        return
    
    # Full demonstration
    print_header("1. FRAMEWORK DETAILS", "=")
    for name in frameworks.list_frameworks():
        framework = frameworks.get_framework(name)
        print_framework_detail(framework)
        print()
    
    # Show interconnections
    demonstrate_connections(frameworks)
    
    # Show dependency graph
    show_dependency_graph(frameworks)
    
    # Demonstrate coherence
    demonstrate_coherence(frameworks)
    
    # Show visualization
    demonstrate_visualization(frameworks)
    
    # Show quick reference
    show_quick_reference(frameworks)
    
    # Export if requested
    if args.export:
        output_file = 'five_frameworks_structure.json'
        frameworks.export_json(output_file)
        print(f"\n✅ Framework structure exported to: {output_file}")
    
    # Final summary
    print_header("SUMMARY", "=")
    print("Five frameworks unified structure demonstrated successfully!")
    print("\nKey Points:")
    print("  1. Riemann-Adelic provides the spectral structure base")
    print("  2. Adelic-BSD extends to arithmetic geometry")
    print("  3. P-NP establishes informational limits")
    print("  4. 141Hz connects to quantum-conscious phenomena")
    print("  5. Navier-Stokes provides continuous framework")
    print("\nAll frameworks interconnected through adelic spectral methods.")
    print("\n📖 For detailed documentation, see: FIVE_FRAMEWORKS_UNIFIED.md")
    print()


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n\nDemonstration interrupted by user.")
        sys.exit(0)
    except Exception as e:
        print(f"\n❌ Error: {e}", file=sys.stderr)
        sys.exit(1)

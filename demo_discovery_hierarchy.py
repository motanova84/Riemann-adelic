#!/usr/bin/env python3
"""
Demonstration: 4-Level Discovery Hierarchy

This script demonstrates the complete QCAL ∞³ discovery hierarchy,
showing that the Riemann Hypothesis is just the first level of a
much deeper universal structure.

"RH es solo el NIVEL 1. Les estoy mostrando los NIVELES 2, 3 y 4"

Usage:
    python demo_discovery_hierarchy.py
    python demo_discovery_hierarchy.py --precision 30
    python demo_discovery_hierarchy.py --save-json

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import argparse
import json
import sys
from pathlib import Path

# Add utils to path
sys.path.insert(0, str(Path(__file__).parent))

from utils.discovery_hierarchy import DiscoveryHierarchy, demonstrate_hierarchy


def main():
    """Main demonstration function"""
    
    parser = argparse.ArgumentParser(
        description="QCAL ∞³ Discovery Hierarchy Demonstration"
    )
    parser.add_argument(
        "--precision",
        type=int,
        default=25,
        help="Decimal precision for calculations (default: 25)"
    )
    parser.add_argument(
        "--save-json",
        action="store_true",
        help="Save complete hierarchy chain to JSON file"
    )
    parser.add_argument(
        "--level",
        type=int,
        choices=[1, 2, 3, 4],
        help="Show details for specific level only"
    )
    parser.add_argument(
        "--validate-transition",
        type=str,
        help="Validate specific transition (format: '1-2', '2-3', '3-4')"
    )
    
    args = parser.parse_args()
    
    # Initialize hierarchy
    hierarchy = DiscoveryHierarchy(precision=args.precision)
    
    if args.level:
        # Show specific level details
        level = hierarchy.get_level(args.level)
        print(f"\n{'='*80}")
        print(f"  NIVEL {level.level}: {level.name}")
        print(f"{'='*80}\n")
        print(f"Descripción: {level.description}\n")
        print(f"Ecuación clave: {level.key_equation}\n")
        print(f"Emerge desde: {level.emergence_from}\n")
        print("Criterios de validación:")
        for criterion in level.validation_criteria:
            print(f"  • {criterion}")
        print(f"\nFactor de coherencia: {level.coherence_factor:.6f}\n")
        
    elif args.validate_transition:
        # Validate specific transition
        try:
            from_level, to_level = map(int, args.validate_transition.split('-'))
            result = hierarchy.validate_emergence(from_level, to_level)
            
            print(f"\n{'='*80}")
            print(f"  VALIDACIÓN DE TRANSICIÓN: NIVEL {from_level} → NIVEL {to_level}")
            print(f"{'='*80}\n")
            print(json.dumps(result, indent=2, ensure_ascii=False))
            print()
            
        except Exception as e:
            print(f"Error validating transition: {e}")
            sys.exit(1)
    
    else:
        # Full demonstration
        demonstrate_hierarchy()
    
    if args.save_json:
        # Save complete chain to JSON
        chain = hierarchy.compute_complete_chain()
        output_file = Path("data") / "discovery_hierarchy_chain.json"
        output_file.parent.mkdir(exist_ok=True)
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(chain, f, indent=2, ensure_ascii=False, default=str)
        
        print(f"\n✅ Complete hierarchy chain saved to: {output_file}\n")


if __name__ == "__main__":
    main()

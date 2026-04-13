#!/usr/bin/env python3
"""
QCAL Unification Interactive Demonstration
Shows how millennium problems connect through QCAL framework.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

from qcal_unified_framework import QCALUnifiedFramework
from typing import Dict


class QCALUnificationDemo:
    """Interactive demonstration of QCAL unification."""
    
    def __init__(self):
        """Initialize demonstration."""
        self.framework = QCALUnifiedFramework()
        self.problems = [
            "P vs NP",
            "Riemann Hypothesis", 
            "BSD Conjecture",
            "Navier-Stokes",
            "Ramsey Numbers"
        ]
        self.problem_keys = {
            "P vs NP": "p_vs_np",
            "Riemann Hypothesis": "riemann",
            "BSD Conjecture": "bsd",
            "Navier-Stokes": "navier_stokes",
            "Ramsey Numbers": "ramsey"
        }
    
    def get_qcal_connections(self, problem: str) -> Dict:
        """
        Get QCAL connections for a specific problem.
        
        Args:
            problem: Problem name
        
        Returns:
            Dictionary with connection details
        """
        problem_key = self.problem_keys.get(problem)
        if not problem_key:
            return {}
        
        connection = self.framework.get_problem_connection(problem_key)
        if not connection:
            return {}
        
        return {
            'operator': connection.operator_name,
            'constant': connection.universal_constant,
            'equation': connection.eigenvalue_relation,
            'verification': connection.verification_protocol,
            'connected_to': [self.get_problem_name(k) 
                           for k in connection.connected_problems]
        }
    
    def get_problem_name(self, key: str) -> str:
        """Get problem name from key."""
        reverse_map = {v: k for k, v in self.problem_keys.items()}
        return reverse_map.get(key, key)
    
    def show_qcal_connection(self, problem: str):
        """
        Display how a problem connects through QCAL.
        
        Args:
            problem: Problem name to display
        """
        print("\n" + "=" * 70)
        print(f"{problem} in QCAL Unified Framework")
        print("=" * 70)
        
        connections = self.get_qcal_connections(problem)
        
        if not connections:
            print(f"Problem '{problem}' not found in framework.")
            return
        
        print(f"\n**QCAL Operator**: {connections['operator']}")
        print(f"\n**Universal Constant**: {connections['constant']}")
        
        print(f"\n**Connection Equation**:")
        print(f"```")
        print(f"{connections['equation']}")
        print(f"```")
        
        print(f"\n**Verification Protocol**: {connections['verification']}")
        
        if connections['connected_to']:
            print(f"\n**Connected Problems**:")
            for connected in connections['connected_to']:
                print(f"  - {connected}")
        
        print("\n" + "=" * 70)
    
    def show_all_connections(self):
        """Display connections for all problems."""
        print("\n" + "=" * 70)
        print("QCAL UNIFIED FRAMEWORK - ALL CONNECTIONS")
        print("=" * 70)
        
        for problem in self.problems:
            self.show_qcal_connection(problem)
    
    def show_connection_graph(self):
        """Display connection graph between problems."""
        print("\n" + "=" * 70)
        print("QCAL CONNECTION GRAPH")
        print("=" * 70)
        print()
        
        # Build adjacency representation
        for problem in self.problems:
            key = self.problem_keys[problem]
            connection = self.framework.get_problem_connection(key)
            
            if connection:
                connected = [self.get_problem_name(k) 
                           for k in connection.connected_problems]
                
                print(f"{problem}:")
                print(f"  Operator: {connection.operator_name}")
                print(f"  Constant: {connection.universal_constant}")
                
                if connected:
                    print(f"  Connects to:")
                    for c in connected:
                        print(f"    → {c}")
                else:
                    print(f"  (No direct connections)")
                print()
        
        print("=" * 70)
    
    def show_constants_table(self):
        """Display table of universal constants."""
        print("\n" + "=" * 70)
        print("UNIVERSAL CONSTANTS TABLE")
        print("=" * 70)
        print()
        print(f"{'Constant':<20} {'Symbol':<15} {'Value':<15} {'Problem':<25}")
        print("-" * 70)
        
        constants_info = [
            ("κ_Π", "kappa_pi", self.framework.constants.kappa_pi, "P vs NP"),
            ("f₀", "f0", self.framework.constants.f0, "Riemann Hypothesis"),
            ("λ_RH", "critical_line", self.framework.constants.critical_line, "Riemann Hypothesis"),
            ("ε_NS", "navier_stokes_epsilon", self.framework.constants.navier_stokes_epsilon, "Navier-Stokes"),
            ("φ_Ramsey", "ramsey_ratio", self.framework.constants.ramsey_ratio, "Ramsey Numbers"),
            ("Δ_BSD", "bsd_delta", self.framework.constants.bsd_delta, "BSD Conjecture"),
            ("C", "coherence_C", self.framework.constants.coherence_C, "QCAL Coherence"),
        ]
        
        for name, _, value, problem in constants_info:
            print(f"{name:<20} {str(value):<15} {problem:<25}")
        
        print()
        print("=" * 70)
    
    def interactive_menu(self):
        """Run interactive menu."""
        while True:
            print("\n" + "=" * 70)
            print("QCAL UNIFICATION - INTERACTIVE MENU")
            print("=" * 70)
            print("\nSelect an option:")
            print("  1. Show all problem connections")
            print("  2. Show specific problem connection")
            print("  3. Show connection graph")
            print("  4. Show universal constants")
            print("  5. Show framework coherence")
            print("  6. Exit")
            print()
            
            choice = input("Enter choice (1-6): ").strip()
            
            if choice == "1":
                self.show_all_connections()
            elif choice == "2":
                print("\nAvailable problems:")
                for i, prob in enumerate(self.problems, 1):
                    print(f"  {i}. {prob}")
                
                prob_choice = input("\nEnter problem number: ").strip()
                try:
                    idx = int(prob_choice) - 1
                    if 0 <= idx < len(self.problems):
                        self.show_qcal_connection(self.problems[idx])
                    else:
                        print("Invalid choice.")
                except ValueError:
                    print("Invalid input.")
            elif choice == "3":
                self.show_connection_graph()
            elif choice == "4":
                self.show_constants_table()
            elif choice == "5":
                self.show_framework_coherence()
            elif choice == "6":
                print("\nExiting QCAL demonstration.")
                break
            else:
                print("Invalid choice. Please try again.")
    
    def show_framework_coherence(self):
        """Display framework coherence metrics."""
        print("\n" + "=" * 70)
        print("QCAL FRAMEWORK COHERENCE")
        print("=" * 70)
        print()
        
        coherence = self.framework.calculate_coherence()
        constants_valid = self.framework.constants.validate_coherence()
        
        print(f"Overall Coherence: {coherence:.6f}")
        print(f"Constants Valid: {'✓ Yes' if constants_valid else '✗ No'}")
        print()
        print(f"Coherence Interpretation:")
        if coherence > 0.95:
            print("  ✓ Excellent - Framework highly coherent")
        elif coherence > 0.85:
            print("  ✓ Good - Framework coherent")
        elif coherence > 0.70:
            print("  ~ Fair - Some coherence issues")
        else:
            print("  ✗ Poor - Framework needs adjustment")
        
        print()
        print("=" * 70)


def main():
    """Main entry point for demonstration."""
    print("\n" + "=" * 70)
    print("QCAL UNIFIED FRAMEWORK - INTERACTIVE DEMONSTRATION")
    print("Quantum Coherent Algebraic Logic")
    print("=" * 70)
    print()
    print("Author: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institution: Instituto de Conciencia Cuántica (ICQ)")
    print()
    
    demo = QCALUnificationDemo()
    
    # Show quick overview
    print("\n" + "=" * 70)
    print("QUICK OVERVIEW")
    print("=" * 70)
    demo.show_connection_graph()
    demo.show_constants_table()
    demo.show_framework_coherence()
    
    # Ask if user wants interactive mode
    print("\n" + "=" * 70)
    response = input("Enter interactive mode? (y/n): ").strip().lower()
    
    if response == 'y':
        demo.interactive_menu()
    else:
        print("\nExiting demonstration.")
    
    print("\n" + "=" * 70)
    print("© 2026 José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("=" * 70 + "\n")


if __name__ == "__main__":
    main()

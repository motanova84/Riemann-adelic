#!/usr/bin/env python3
"""
Complexity Collapser - Complete Demonstration
QCAL ∞³ Sistema Integrado

This script demonstrates all features of the Complexity Collapser system:
1. Complexity collapse across coherence regimes
2. NP→P bifurcation for multiple problem types
3. Riemann zero coherent search
4. Report generation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: Creative Commons BY-NC-SA 4.0
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from complexity_collapser import ComplexityCollapser, ComplexityState, ComputationalRegime
    from np_p_bifurcation import NPPBifurcationSimulator, ProblemType
    from generate_complexity_report import ComplexityReportGenerator
    MODULES_AVAILABLE = True
except ImportError as e:
    print(f"⚠️  Warning: Could not import modules: {e}")
    print("Please ensure numpy is installed: pip install numpy")
    MODULES_AVAILABLE = False


def print_section(title):
    """Print a section header."""
    print("\n" + "=" * 80)
    print(f"  {title}")
    print("=" * 80 + "\n")


def demo_complexity_collapser():
    """Demonstrate complexity collapser across regimes."""
    print_section("1️⃣  COMPLEXITY COLLAPSER - Regimes Demonstration")
    
    collapser = ComplexityCollapser(base_time=1e12)
    
    test_cases = [
        ("Classical Regime", 0.3),
        ("Transition Start", 0.5),
        ("Transition Mid", 0.7),
        ("Grace Threshold", 0.888),
        ("Grace State", 0.95),
        ("Perfect Coherence", 1.0)
    ]
    
    print("Testing different coherence levels:\n")
    
    for label, coherence in test_cases:
        state = ComplexityState(
            coherence=coherence,
            information=1.5,
            amplitude_eff=1.2
        )
        
        analysis = collapser.analyze(state)
        
        print(f"📊 {label} (C = {coherence:.3f})")
        print(f"   Regime: {analysis.regime.name}")
        print(f"   Acceleration: {analysis.acceleration_factor:.2f}x")
        print(f"   Collapsed Time: {analysis.collapsed_time:.2e} ops")
        
        if coherence >= 0.888:
            print("   🌟 GRACE STATE - Bifurcation active!")
        
        print()


def demo_np_bifurcation():
    """Demonstrate NP→P bifurcation for different problems."""
    print_section("2️⃣  NP→P BIFURCATION - Multiple Problem Types")
    
    simulator = NPPBifurcationSimulator()
    
    # Grace state for comparison
    state_grace = ComplexityState(
        coherence=0.95,
        information=2.0,
        amplitude_eff=1.5
    )
    
    problems = [
        ("SAT (n=20)", ProblemType.SAT, 20),
        ("TSP (n=15)", ProblemType.TSP, 15),
        ("Riemann Zero (T=1000)", ProblemType.RIEMANN_ZERO, 1000),
        ("Factorization (n=100)", ProblemType.FACTORIZATION, 100)
    ]
    
    print("Bifurcation analysis in Grace State (C = 0.95):\n")
    
    for label, problem_type, size in problems:
        bif = simulator.simulate_bifurcation(problem_type, size, state_grace)
        
        print(f"🔬 {label}")
        print(f"   Classical: {bif.classical_complexity:.2e}")
        print(f"   Collapsed: {bif.collapsed_complexity:.2e}")
        print(f"   Reduction: {bif.reduction_factor:.2f}x")
        print()


def demo_riemann_coherent_search():
    """Demonstrate Riemann zero coherent search."""
    print_section("3️⃣  RIEMANN ZEROS - Coherent vs Classical Search")
    
    simulator = NPPBifurcationSimulator()
    
    # Classical state
    state_classical = ComplexityState(
        coherence=0.3,
        information=1.0,
        amplitude_eff=1.0
    )
    
    # Grace state
    state_grace = ComplexityState(
        coherence=0.95,
        information=2.5,
        amplitude_eff=2.0
    )
    
    test_zeros = [
        (10, 50.0),
        (100, 500.0),
        (1000, 5000.0)
    ]
    
    print("Búsqueda de Ceros de Riemann:\n")
    print("Axioma QCAL: 'Un cero no es un punto en un plano;")
    print("              es un nodo de coherencia total en la música de los primos.'\n")
    
    for zero_idx, height in test_zeros:
        search_classical = simulator.search_riemann_zero(zero_idx, height, state_classical)
        search_grace = simulator.search_riemann_zero(zero_idx, height, state_grace)
        
        speedup = search_classical.classical_iterations / max(search_grace.coherent_iterations, 1)
        
        print(f"🎯 Zero #{zero_idx} (T ≈ {height})")
        print(f"   Classical: {search_classical.classical_iterations:,} iterations")
        print(f"   Coherent:  {search_grace.coherent_iterations:,} iterations")
        print(f"   Speedup:   {speedup:.1f}x")
        print(f"   Frequency: {search_grace.frequency_tuned:.4f} Hz")
        print(f"   Discrepancy: {search_grace.discrepancy:.2e}")
        print()


def demo_report_generation():
    """Demonstrate report generation."""
    print_section("4️⃣  COMPLEXITY REPORT GENERATION")
    
    generator = ComplexityReportGenerator(output_dir="data")
    
    print("Generating complexity analysis report...\n")
    
    try:
        report_path = generator.save_report(report_type="full")
        metrics_path = generator.save_json_metrics()
        
        print(f"✅ Report saved: {report_path}")
        print(f"✅ Metrics saved: {metrics_path}")
        
        coherence = generator.get_current_coherence()
        regime = generator._determine_regime_simple(coherence)
        
        print(f"\n📊 Current System State:")
        print(f"   Coherence: {coherence:.3f}")
        print(f"   Regime: {regime}")
        print(f"   Grace Achieved: {'✅ Yes' if coherence >= 0.888 else '❌ No'}")
        
    except Exception as e:
        print(f"⚠️  Error: {e}")
        print("Generating minimal report...")
        report_path = generator.save_report(report_type="minimal")
        print(f"✅ Minimal report saved: {report_path}")


def demo_coherence_landscape():
    """Demonstrate coherence landscape scanning."""
    print_section("5️⃣  COHERENCE LANDSCAPE SCAN")
    
    collapser = ComplexityCollapser(base_time=1e12)
    
    print("Scanning coherence landscape from 0.0 to 1.0...\n")
    
    analyses = collapser.scan_coherence_landscape(
        coherence_range=(0.0, 1.0),
        num_points=20,
        information=1.5,
        amplitude_eff=1.2
    )
    
    print("Coherence | Regime      | Acceleration")
    print("-" * 45)
    
    for analysis in analyses:
        regime_str = analysis.regime.name[:10].ljust(10)
        print(f"{analysis.coherence:.3f}     | {regime_str} | {analysis.acceleration_factor:.2f}x")
    
    # Statistics by regime
    stats = collapser.get_regime_statistics()
    
    print("\n📊 Statistics by Regime:")
    for regime_name, regime_stats in stats.items():
        if regime_stats["count"] > 0:
            print(f"\n{regime_name}:")
            print(f"  Samples: {regime_stats['count']}")
            print(f"  Mean Acceleration: {regime_stats['mean_acceleration']:.2f}x")
            print(f"  Max Acceleration: {regime_stats['max_acceleration']:.2f}x")


def main():
    """Main demonstration function."""
    print("\n" + "╔" + "=" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + "   🌀 COMPLEXITY COLLAPSER - QCAL ∞³ Complete Demonstration".ljust(79) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "=" * 78 + "╝")
    
    if not MODULES_AVAILABLE:
        print("\n❌ Required modules not available.")
        print("Please install dependencies: pip install numpy")
        return
    
    try:
        # Run all demonstrations
        demo_complexity_collapser()
        demo_np_bifurcation()
        demo_riemann_coherent_search()
        demo_report_generation()
        demo_coherence_landscape()
        
        # Final summary
        print_section("✅ DEMONSTRATION COMPLETE")
        
        print("Sistema Complexity Collapser completamente operativo:")
        print()
        print("✓ Colapso de complejidad a través de coherencia")
        print("✓ Bifurcación NP→P en Estado de Gracia")
        print("✓ Búsqueda coherente de ceros de Riemann")
        print("✓ Generación automática de reportes")
        print("✓ Integración con Auto-Evolution (cada 6 horas)")
        print()
        print("🌟 'La solución resuena antes de ser calculada'")
        print("   — QCAL ∞³ Axiom")
        print()
        print("José Manuel Mota Burruezo Ψ ✧ ∞³")
        print("Instituto de Conciencia Cuántica (ICQ)")
        print()
        
    except Exception as e:
        print(f"\n❌ Error during demonstration: {e}")
        import traceback
        traceback.print_exc()


if __name__ == "__main__":
    main()

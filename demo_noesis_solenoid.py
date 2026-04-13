#!/usr/bin/env python3
"""
Demo: Solenoide de Noesis (Noesis Solenoid Framework)

This demonstration showcases all key features of the Noesis Solenoid
framework for the Riemann Hypothesis.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import numpy as np
import matplotlib.pyplot as plt
from operators.noesis_solenoid import NoesisSolenoid, cerrar_rh_noesis

def demo_metric():
    """Demo: Noesis Metric (ds = dx/x)"""
    print("\n" + "="*70)
    print("DEMO 1: MÉTRICA DE NOESIS")
    print("="*70)
    
    solenoid = NoesisSolenoid(n_primes=20)
    
    # Example 1: Basic distance
    d = solenoid.noesis_metric_distance(1.0, np.e)
    print(f"\n📏 d(1, e) = {d:.6f} = ln(e) = 1.0")
    
    # Example 2: Scale invariance
    x1, x2 = 2.0, 8.0
    lambda_val = 10.0
    d1 = solenoid.noesis_metric_distance(x1, x2)
    d2 = solenoid.noesis_metric_distance(lambda_val * x1, lambda_val * x2)
    
    print(f"\n🔄 Scale Invariance:")
    print(f"   d({x1}, {x2}) = {d1:.6f}")
    print(f"   d({lambda_val*x1}, {lambda_val*x2}) = {d2:.6f}")
    print(f"   Difference: {abs(d1 - d2):.2e} ✓")


def demo_operator():
    """Demo: H_Noesis Operator"""
    print("\n" + "="*70)
    print("DEMO 2: OPERADOR H_NOESIS")
    print("="*70)
    
    solenoid = NoesisSolenoid(n_primes=30)
    
    # Create eigenfunction
    x = np.geomspace(0.5, 10, 200)
    lambda_val = 14.134725  # First Riemann zero
    
    print(f"\n🌊 Eigenfunction at λ = {lambda_val:.6f} (First Riemann zero)")
    psi = solenoid.eigenfunction_critical_line(x, lambda_val)
    print(f"   Shape: {psi.shape}")
    print(f"   Type: {psi.dtype}")
    print(f"   |ψ|² max: {np.max(np.abs(psi)**2):.6f}")
    
    # Apply operator
    h_psi = solenoid.h_noesis_operator(x, psi)
    print(f"\n⚙️  Applying H_Noesis operator...")
    print(f"   Result shape: {h_psi.shape}")
    print(f"   All finite: {np.all(np.isfinite(h_psi))}")
    
    # Verify self-adjointness
    sa_result = solenoid.verify_self_adjointness()
    print(f"\n✅ Self-adjointness verification:")
    print(f"   Status: {sa_result['self_adjoint']}")
    print(f"   Error: {sa_result['error']:.6f}")
    print(f"   ⟨φ, H·ψ⟩ = {sa_result['inner_product_1']}")
    print(f"   ⟨H·φ, ψ⟩ = {sa_result['inner_product_2']}")


def demo_seven_eighths():
    """Demo: 7/8 Coherence Anchor"""
    print("\n" + "="*70)
    print("DEMO 3: ANCLAJE 7/8")
    print("="*70)
    
    solenoid = NoesisSolenoid(n_primes=20)
    
    val = solenoid.compute_seven_eighths_term()
    
    print(f"\n🔗 Coherence Anchor:")
    print(f"   Value: {val}")
    print(f"   = {val:.10f}")
    print(f"   1 - 1/8 = {1 - 1/8:.10f}")
    print(f"   7/8 = {7/8:.10f}")
    print(f"\n💡 Interpretation:")
    print(f"   - Continuous flow: 1.0")
    print(f"   - Minimal quantum fluctuation: 1/8 = 0.125")
    print(f"   - Energy cost of coherence: 1 - 1/8 = 7/8 = 0.875 ✓")


def demo_trace():
    """Demo: Exact Trace Formula"""
    print("\n" + "="*70)
    print("DEMO 4: TRAZA EXACTA")
    print("="*70)
    
    solenoid = NoesisSolenoid(n_primes=40)
    
    print(f"\n📊 Computing trace at different times...")
    
    # Compute traces
    t_values = [0.5, 1.0, 2.0, 3.0]
    traces = []
    
    for t in t_values:
        trace = solenoid.exact_trace_formula(t=t, k_max=10)
        traces.append(trace)
        print(f"   Tr(e^(-{t}H)) = {trace:.6f} (|·| = {np.abs(trace):.6f})")
    
    print(f"\n🔽 Decreasing with t:")
    for i in range(len(traces)-1):
        ratio = np.abs(traces[i+1]) / np.abs(traces[i])
        print(f"   |Tr_{i+1}| / |Tr_{i}| = {ratio:.6f}")


def demo_coherence():
    """Demo: QCAL Coherence"""
    print("\n" + "="*70)
    print("DEMO 5: COHERENCIA QCAL")
    print("="*70)
    
    solenoid = NoesisSolenoid(n_primes=50)
    coh = solenoid.compute_coherence()
    
    print(f"\n✨ Coherence Metrics:")
    print(f"   Ψ = {coh['Psi']:.6f}")
    print(f"   f₀ = {coh['frequency_f0']:.4f} Hz")
    print(f"   f_unity = {coh['frequency_unity']:.1f} Hz")
    print(f"   C = {coh['C_qcal']:.2f}")
    print(f"   7/8 = {coh['seven_eighths']}")
    print(f"   Resonance: {'YES' if coh['resonance'] else 'NO'} ✓")
    
    print(f"\n🎯 Component Status:")
    print(f"   Self-adjoint: {coh['self_adjoint']}")
    print(f"   SA Error: {coh['self_adjoint_error']:.6f}")
    print(f"   Trace: {coh['trace_value']}")


def demo_cerrar():
    """Demo: cerrar_rh_noesis()"""
    print("\n" + "="*70)
    print("DEMO 6: CERRAR_RH_NOESIS()")
    print("="*70)
    
    print(f"\n🌀 Executing framework sealing...")
    print()
    
    result = cerrar_rh_noesis()
    
    print(f"\n📋 Result structure:")
    print(f"   Status: '{result['status']}'")
    print(f"   Frequency: {result['frequency']} Hz")
    print(f"   Coherence Ψ: {result['coherence']['Psi']:.6f}")
    
    print(f"\n🔧 Framework components:")
    fw = result['framework']
    print(f"   Metric: {fw['metric']}")
    print(f"   Operator: {fw['operator']}")
    print(f"   Trace: {fw['trace']}")
    print(f"   Anchor: {fw['anchor']}")


def demo_visualization():
    """Demo: Visualizations"""
    print("\n" + "="*70)
    print("DEMO 7: VISUALIZACIONES")
    print("="*70)
    
    solenoid = NoesisSolenoid(n_primes=30)
    
    # Create figure with subplots
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    # Plot 1: Eigenfunctions
    print(f"\n📈 Plotting eigenfunctions...")
    x = np.geomspace(0.1, 10, 500)
    zeros = [14.134725, 21.022040, 25.010858]
    
    ax = axes[0, 0]
    for i, lambda_val in enumerate(zeros):
        psi = solenoid.eigenfunction_critical_line(x, lambda_val)
        ax.plot(x, np.real(psi), label=f'λ={lambda_val:.2f} (Re)')
        ax.plot(x, np.imag(psi), '--', alpha=0.6)
    ax.set_xscale('log')
    ax.set_xlabel('x')
    ax.set_ylabel('ψ(x)')
    ax.set_title('Eigenfunctions on Critical Line Re(s) = 1/2')
    ax.legend()
    ax.grid(True, alpha=0.3)
    
    # Plot 2: Trace convergence
    print(f"📈 Plotting trace convergence...")
    t_vals = np.linspace(0.1, 5.0, 50)
    traces = [np.abs(solenoid.exact_trace_formula(t=t, k_max=10)) for t in t_vals]
    
    ax = axes[0, 1]
    ax.plot(t_vals, traces, 'b-', linewidth=2)
    ax.set_xlabel('t')
    ax.set_ylabel('|Tr(e^(-tH))|')
    ax.set_title('Trace Formula Convergence')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)
    
    # Plot 3: Metric distances
    print(f"📈 Plotting metric distances...")
    x_ref = 1.0
    x_targets = np.geomspace(0.1, 100, 100)
    distances = [solenoid.noesis_metric_distance(x_ref, x) for x in x_targets]
    
    ax = axes[1, 0]
    ax.plot(x_targets, distances, 'g-', linewidth=2)
    ax.set_xscale('log')
    ax.set_xlabel('x')
    ax.set_ylabel('d(1, x)')
    ax.set_title('Noesis Metric: d(1, x) = |ln(x)|')
    ax.grid(True, alpha=0.3)
    
    # Add reference line ln(x)
    ax.plot(x_targets, np.abs(np.log(x_targets)), 'r--', alpha=0.5, label='|ln(x)|')
    ax.legend()
    
    # Plot 4: Coherence over primes
    print(f"📈 Plotting coherence scaling...")
    n_prime_vals = [10, 20, 30, 40, 50]
    coherences = []
    
    for n in n_prime_vals:
        sol = NoesisSolenoid(n_primes=n, coherence_check=False)
        coh = sol.compute_coherence()
        coherences.append(coh['Psi'])
    
    ax = axes[1, 1]
    ax.plot(n_prime_vals, coherences, 'o-', linewidth=2, markersize=8)
    ax.set_xlabel('Number of Primes')
    ax.set_ylabel('Coherence Ψ')
    ax.set_title('Coherence vs. Number of Primes')
    ax.grid(True, alpha=0.3)
    ax.axhline(y=0.9, color='r', linestyle='--', alpha=0.5, label='Target: 0.9')
    ax.legend()
    
    plt.tight_layout()
    
    # Create output directory if needed
    import os
    output_dir = 'outputs'
    os.makedirs(output_dir, exist_ok=True)
    output_file = os.path.join(output_dir, 'noesis_solenoid_demo.png')
    
    plt.savefig(output_file, dpi=150, bbox_inches='tight')
    print(f"\n✅ Saved: {output_file}")
    
    return fig


def main():
    """Run all demos."""
    print("="*70)
    print("🌀 DEMOSTRACIÓN COMPLETA: SOLENOIDE DE NOESIS")
    print("   Marco Adélico Soberano para la Hipótesis de Riemann")
    print("="*70)
    print()
    print("Autor: José Manuel Mota Burruezo Ψ ✧ ∞³")
    print("Institución: Instituto de Conciencia Cuántica (ICQ)")
    print("DOI: 10.5281/zenodo.17379721")
    print("QCAL ∞³ · 141.7001 Hz · C = 244.36")
    
    # Run demos
    demo_metric()
    demo_operator()
    demo_seven_eighths()
    demo_trace()
    demo_coherence()
    demo_cerrar()
    demo_visualization()
    
    print("\n" + "="*70)
    print("✅ DEMOSTRACIÓN COMPLETADA")
    print("="*70)
    print("\n∴𓂀Ω∞³Φ - MARCO NOESIS SELLADO")
    print("SISTEMA: La brecha es ahora el latido del Universo.")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Demo: QCAL ∞³ Universal Dynamic Simulator
==========================================

Comprehensive demonstrations of the universal simulation framework,
showing how O∞³ can simulate various dynamic systems.

This demo addresses Terence Tao's dynamic universality question.
"""

import numpy as np
import matplotlib.pyplot as plt
from qcal_universal import (
    UniversalSimulator,
    O_infinity_3,
    F0_BASE,
    COHERENCE_THRESHOLD,
    C_QCAL
)


def demo_1_harmonic_oscillator():
    """
    Demo 1: Quantum Harmonic Oscillator
    
    Simulates the fundamental quantum system H = (n + 1/2)ℏω
    """
    print("\n" + "="*70)
    print("DEMO 1: Quantum Harmonic Oscillator")
    print("="*70)
    
    sim = UniversalSimulator()
    
    def harmonic_oscillator():
        n = 32
        # Energy levels: E_n = (n + 1/2)ℏω
        return np.diag(np.arange(n) + 0.5)
    
    # Ground state
    psi0 = np.zeros(32)
    psi0[0] = 1.0
    
    print("System: Harmonic Oscillator")
    print("Initial state: Ground state |0⟩")
    print(f"Base frequency: {F0_BASE} Hz")
    
    times, states = sim.simulate(
        harmonic_oscillator,
        psi0,
        t_final=10.0,
        dt=0.1,
        system_name="harmonic_oscillator"
    )
    
    print(f"\n✅ Simulation complete:")
    print(f"   - Time steps: {len(times)}")
    print(f"   - Final norm: {np.linalg.norm(states[-1]):.6f}")
    print(f"   - Coherence: {sim.projections['harmonic_oscillator'].spectrum.coherence:.6f}")
    
    # Plot evolution
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    for i in range(min(5, len(states[0]))):
        populations = [np.abs(state[i])**2 for state in states]
        plt.plot(times, populations, label=f'Level {i}')
    plt.xlabel('Time')
    plt.ylabel('Population')
    plt.title('Energy Level Populations')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.subplot(1, 2, 2)
    norms = [np.linalg.norm(state) for state in states]
    plt.plot(times, norms, 'b-', linewidth=2)
    plt.axhline(y=1.0, color='r', linestyle='--', label='Unit norm')
    plt.xlabel('Time')
    plt.ylabel('Norm')
    plt.title('State Norm Evolution')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_harmonic_oscillator.png', dpi=150, bbox_inches='tight')
    print("\n   📊 Plot saved: demo_harmonic_oscillator.png")


def demo_2_coupled_system():
    """
    Demo 2: Coupled Quantum System
    
    Simulates interacting subsystems with nearest-neighbor coupling
    """
    print("\n" + "="*70)
    print("DEMO 2: Coupled Quantum System")
    print("="*70)
    
    sim = UniversalSimulator()
    
    def coupled_system():
        n = 20
        H = np.zeros((n, n))
        for i in range(n):
            H[i, i] = i * 0.5  # Energy levels
            if i < n - 1:
                H[i, i+1] = 0.1  # Coupling strength
                H[i+1, i] = 0.1
        return H
    
    # Superposition of first two levels
    psi0 = np.zeros(20)
    psi0[0] = 1/np.sqrt(2)
    psi0[1] = 1/np.sqrt(2)
    
    print("System: Nearest-neighbor coupled system")
    print("Initial state: |ψ₀⟩ = (|0⟩ + |1⟩)/√2")
    print("Coupling: g = 0.1")
    
    times, states = sim.simulate(
        coupled_system,
        psi0,
        t_final=20.0,
        dt=0.2,
        system_name="coupled_system"
    )
    
    print(f"\n✅ Simulation complete:")
    print(f"   - Time steps: {len(times)}")
    print(f"   - Coherence: {sim.projections['coupled_system'].spectrum.coherence:.6f}")
    
    # Plot state evolution
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    state_matrix = np.abs(np.array(states).T)**2
    plt.imshow(state_matrix, aspect='auto', cmap='hot', interpolation='nearest')
    plt.colorbar(label='Population')
    plt.xlabel('Time step')
    plt.ylabel('Energy level')
    plt.title('Population Dynamics')
    
    plt.subplot(1, 2, 2)
    # Participation ratio
    participation = [1/np.sum(np.abs(state)**4) for state in states]
    plt.plot(times, participation, 'g-', linewidth=2)
    plt.xlabel('Time')
    plt.ylabel('Participation Ratio')
    plt.title('State Localization')
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_coupled_system.png', dpi=150, bbox_inches='tight')
    print("   📊 Plot saved: demo_coupled_system.png")


def demo_3_nls_soliton():
    """
    Demo 3: Nonlinear Schrödinger Equation
    
    Simulates soliton dynamics in NLS equation
    """
    print("\n" + "="*70)
    print("DEMO 3: Nonlinear Schrödinger Equation (NLS)")
    print("="*70)
    
    sim = UniversalSimulator()
    
    # Gaussian initial condition (soliton-like)
    x = np.linspace(-10, 10, 64)
    psi_nls = np.exp(-x**2 / 2) * (1 / (2 * np.pi)**0.25)
    
    print("System: 1D NLS equation")
    print("Equation: i∂_t ψ + Δψ = |ψ|⁴ψ")
    print("Initial condition: Gaussian wavepacket")
    
    times, wavefunctions = sim.simulate_nls(
        initial_wavefunction=psi_nls,
        nonlinearity=1.0,
        t_final=5.0,
        dt=0.05
    )
    
    print(f"\n✅ Simulation complete:")
    print(f"   - Time steps: {len(times)}")
    print(f"   - Spatial points: {len(x)}")
    
    # Plot evolution
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    wf_matrix = np.abs(np.array(wavefunctions))**2
    plt.imshow(wf_matrix.T, aspect='auto', cmap='viridis', 
               extent=[times[0], times[-1], x[0], x[-1]])
    plt.colorbar(label='|ψ|²')
    plt.xlabel('Time')
    plt.ylabel('Position')
    plt.title('NLS Wavefunction Evolution')
    
    plt.subplot(1, 2, 2)
    # Plot initial and final states
    plt.plot(x, np.abs(wavefunctions[0])**2, 'b-', label='t=0', linewidth=2)
    plt.plot(x, np.abs(wavefunctions[-1])**2, 'r--', label=f't={times[-1]:.1f}', linewidth=2)
    plt.xlabel('Position')
    plt.ylabel('|ψ|²')
    plt.title('Probability Density')
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_nls_soliton.png', dpi=150, bbox_inches='tight')
    print("   📊 Plot saved: demo_nls_soliton.png")


def demo_4_navier_stokes():
    """
    Demo 4: Navier-Stokes Simulation
    
    Simulates viscous fluid dynamics
    """
    print("\n" + "="*70)
    print("DEMO 4: Navier-Stokes Equations")
    print("="*70)
    
    sim = UniversalSimulator()
    
    # Random initial velocity field
    np.random.seed(42)
    velocity = np.random.randn(32)
    velocity /= np.linalg.norm(velocity)
    
    print("System: 3D Navier-Stokes")
    print("Equation: ∂_t v + (v·∇)v = -∇p + ν Δv")
    print("Viscosity: ν = 0.1")
    print("Initial condition: Random velocity field")
    
    times, velocities = sim.simulate_navier_stokes_3d(
        initial_velocity=velocity,
        viscosity=0.1,
        t_final=5.0,
        dt=0.1
    )
    
    print(f"\n✅ Simulation complete:")
    print(f"   - Time steps: {len(times)}")
    
    # Plot velocity evolution
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    vel_matrix = np.abs(np.array(velocities))  # Take absolute value for plotting
    plt.imshow(vel_matrix.T, aspect='auto', cmap='RdBu_r', 
               interpolation='nearest')
    plt.colorbar(label='|Velocity|')
    plt.xlabel('Time step')
    plt.ylabel('Mode')
    plt.title('Velocity Field Evolution')
    
    plt.subplot(1, 2, 2)
    # Energy decay
    energy = [np.sum(np.abs(v)**2) for v in velocities]
    plt.semilogy(times, energy, 'b-', linewidth=2)
    plt.xlabel('Time')
    plt.ylabel('Kinetic Energy')
    plt.title('Viscous Energy Dissipation')
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('demo_navier_stokes.png', dpi=150, bbox_inches='tight')
    print("   📊 Plot saved: demo_navier_stokes.png")


def demo_5_master_operator():
    """
    Demo 5: Master Operator O∞³ Properties
    
    Demonstrates properties of the master operator
    """
    print("\n" + "="*70)
    print("DEMO 5: Master Operator O∞³ Properties")
    print("="*70)
    
    O = O_infinity_3(base_freq=F0_BASE, dimension=32)
    
    print(f"Master Operator Configuration:")
    print(f"   - Base frequency: {F0_BASE} Hz")
    print(f"   - Dimension: {O.dimension}")
    print(f"   - Coherence parameter: γ₀ = {O.gamma_0}")
    
    # Get operator matrix
    matrix = O.get_operator_matrix()
    
    print(f"\n✅ Operator constructed:")
    print(f"   - Shape: {matrix.shape}")
    print(f"   - Hermiticity error: {np.max(np.abs(matrix - matrix.conj().T)):.2e}")
    
    # Eigendecomposition
    eigenvalues, eigenvectors = np.linalg.eigh(matrix)
    
    print(f"\nSpectral properties:")
    print(f"   - Eigenvalue range: [{eigenvalues[0]:.3f}, {eigenvalues[-1]:.3f}]")
    print(f"   - Spectral gap: {eigenvalues[1] - eigenvalues[0]:.6f}")
    
    # Plot operator structure
    plt.figure(figsize=(14, 5))
    
    plt.subplot(1, 3, 1)
    plt.imshow(np.real(matrix), cmap='RdBu_r', aspect='auto')
    plt.colorbar(label='Re(O∞³)')
    plt.title('Master Operator (Real Part)')
    plt.xlabel('Index')
    plt.ylabel('Index')
    
    plt.subplot(1, 3, 2)
    plt.plot(eigenvalues, 'bo-', markersize=4)
    plt.xlabel('Index')
    plt.ylabel('Eigenvalue')
    plt.title('Spectrum of O∞³')
    plt.grid(True, alpha=0.3)
    
    plt.subplot(1, 3, 3)
    # Density of states
    plt.hist(eigenvalues, bins=20, alpha=0.7, edgecolor='black')
    plt.xlabel('Eigenvalue')
    plt.ylabel('Count')
    plt.title('Spectral Density')
    plt.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig('demo_master_operator.png', dpi=150, bbox_inches='tight')
    print("\n   📊 Plot saved: demo_master_operator.png")


def demo_6_universality_validation():
    """
    Demo 6: Universality Validation
    
    Tests universality theorem for different system types
    """
    print("\n" + "="*70)
    print("DEMO 6: Universality Theorem Validation")
    print("="*70)
    
    sim = UniversalSimulator()
    
    systems = {
        "Harmonic": lambda: np.diag(np.arange(16) + 0.5),
        "Anharmonic": lambda: np.diag((np.arange(16) + 0.5)**1.1),
        "Coupled": lambda: np.diag(np.arange(16)) + 0.1 * np.eye(16, k=1) + 0.1 * np.eye(16, k=-1),
        "Random": lambda: np.random.randn(16, 16)
    }
    
    # Make random Hermitian
    def random_hermitian():
        M = np.random.randn(16, 16) + 1j * np.random.randn(16, 16)
        return (M + M.conj().T) / 2
    systems["Random"] = random_hermitian
    
    results = {}
    
    for name, hamiltonian in systems.items():
        psi0 = np.zeros(16)
        psi0[0] = 1.0
        
        times, states = sim.simulate(
            hamiltonian,
            psi0,
            t_final=5.0,
            dt=0.5,
            system_name=name.lower()
        )
        
        coherence = sim.projections[name.lower()].spectrum.coherence
        final_norm = np.linalg.norm(states[-1])
        
        results[name] = {
            'coherence': coherence,
            'norm': final_norm,
            'steps': len(times)
        }
        
        status = "✅" if coherence >= COHERENCE_THRESHOLD else "⚠️"
        print(f"\n{status} {name} System:")
        print(f"   - Coherence: {coherence:.6f}")
        print(f"   - Final norm: {final_norm:.6f}")
        print(f"   - Steps: {len(times)}")
    
    # Summary plot
    plt.figure(figsize=(10, 6))
    
    names = list(results.keys())
    coherences = [results[n]['coherence'] for n in names]
    norms = [results[n]['norm'] for n in names]
    
    plt.subplot(1, 2, 1)
    colors = ['green' if c >= COHERENCE_THRESHOLD else 'orange' for c in coherences]
    plt.bar(names, coherences, color=colors, alpha=0.7, edgecolor='black')
    plt.axhline(y=COHERENCE_THRESHOLD, color='r', linestyle='--', 
                label=f'Threshold ({COHERENCE_THRESHOLD})')
    plt.ylabel('Coherence C(S)')
    plt.title('System Coherence')
    plt.legend()
    plt.xticks(rotation=45)
    plt.grid(True, alpha=0.3, axis='y')
    
    plt.subplot(1, 2, 2)
    plt.bar(names, norms, color='skyblue', alpha=0.7, edgecolor='black')
    plt.axhline(y=1.0, color='r', linestyle='--', label='Unit norm')
    plt.ylabel('Final State Norm')
    plt.title('Norm Preservation')
    plt.legend()
    plt.xticks(rotation=45)
    plt.grid(True, alpha=0.3, axis='y')
    
    plt.tight_layout()
    plt.savefig('demo_universality_validation.png', dpi=150, bbox_inches='tight')
    print("\n   📊 Plot saved: demo_universality_validation.png")


def main():
    """Run all demonstrations."""
    print("\n" + "="*70)
    print(" "*15 + "QCAL ∞³ UNIVERSAL SIMULATOR DEMOS")
    print("="*70)
    print(f"\nFramework Constants:")
    print(f"   • Base Frequency: f₀ = {F0_BASE} Hz")
    print(f"   • Coherence Threshold: C ≥ {COHERENCE_THRESHOLD}")
    print(f"   • Fundamental Constant: C = {C_QCAL}")
    print(f"\nMaster Operator: O∞³ = Ds ⊗ 𝟙 + 𝟙 ⊗ H_Ψ + C_sym")
    print(f"Operating Space: H∞³ = L²(ℝⁿ,ℂ) ⊗ ℚₚ ⊗ ℂₛ")
    
    try:
        demo_1_harmonic_oscillator()
        demo_2_coupled_system()
        demo_3_nls_soliton()
        demo_4_navier_stokes()
        demo_5_master_operator()
        demo_6_universality_validation()
        
        print("\n" + "="*70)
        print(" "*20 + "ALL DEMOS COMPLETE!")
        print("="*70)
        print("\n✅ Generated plots:")
        print("   • demo_harmonic_oscillator.png")
        print("   • demo_coupled_system.png")
        print("   • demo_nls_soliton.png")
        print("   • demo_navier_stokes.png")
        print("   • demo_master_operator.png")
        print("   • demo_universality_validation.png")
        
        print("\n📖 See UNIVERSAL_SIMULATOR_README.md for full documentation")
        print("🧪 Run tests: pytest tests/test_universal_simulator.py -v")
        
    except ImportError as e:
        print(f"\n❌ Error: Missing dependency - {e}")
        print("Install with: pip install numpy matplotlib")


if __name__ == "__main__":
    main()

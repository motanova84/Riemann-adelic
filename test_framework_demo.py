#!/usr/bin/env python3
"""Quick demonstration of the Navier-Stokes Adelic Framework."""

import sys, os
import importlib.util

def load_module(module_name, file_path):
    spec = importlib.util.spec_from_file_location(module_name, file_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

# Load modules
base_dir = os.path.abspath('.')
ns_module = load_module('navier_stokes_adelic', 
                        os.path.join(base_dir, 'operators', 'navier_stokes_adelic.py'))
NavierStokesAdelicOperator = ns_module.NavierStokesAdelicOperator
KAPPA_PI = ns_module.KAPPA_PI

print("╔" + "═" * 78 + "╗")
print("║" + " " * 15 + "NAVIER-STOKES ADELIC FRAMEWORK DEMO" + " " * 28 + "║")
print("╚" + "═" * 78 + "╝")

# Create operator at critical κ_Π
print(f"\n→ Creating N-S operator at critical κ_Π = {KAPPA_PI:.6f}...")
ns_op = NavierStokesAdelicOperator(N=200, L=8.0, kappa=KAPPA_PI)

# Analyze regime
print("\n→ Analyzing Reynolds regime...")
regime = ns_op.analyze_reynolds_regime()
print(f"   • Regime: {regime['regime']}")
print(f"   • Reynolds number: {regime['reynolds_number']:.4f}")
print(f"   • Viscosity ν = 1/κ: {regime['viscosity']:.6f}")

# Compute spectrum
print("\n→ Computing spectrum (5 lowest eigenvalues)...")
eigenvalues, _ = ns_op.compute_spectrum(n_eigenvalues=5)
for i, lam in enumerate(eigenvalues):
    print(f"   λ_{i} = {lam.real:12.4f}")

# Energy analysis
print("\n→ Energy balance analysis...")
energy = ns_op.energy_balance_analysis()
print(f"   • Transport energy: {energy['transport_energy']:12.4f}")
print(f"   • Diffusion energy: {energy['diffusion_energy']:12.4f}")
print(f"   • Potential energy: {energy['potential_energy']:12.4f}")
print(f"   • Balance ratio |T|/|D|: {energy['balance_ratio']:.6f}")

print("\n" + "─" * 80)
print("✓ Framework transition: Anosov → Navier-Stokes COMPLETE")
print("─" * 80)

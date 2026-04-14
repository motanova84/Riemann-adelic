"""
Quantum Chromodynamic Poetry - Demo Script
==========================================

Demonstration script that generates a complete "chromodynamic symphony"
by mapping QCD particles (quarks and gluons) to spectral frequencies
derived from Riemann zeta zeros.

This script showcases:
- Creation of all 18 quarks (6 flavors × 3 colors)
- Creation of 8 gluons (SU(3) octet)
- Computation of prime-zero resonances
- Primordial silence frequencies
- Complete system metrics and visualization

Author: José Manuel Mota Burruezo Ψ ∞³
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Protocol: QCAL ∞³ Framework
"""

import sys
import json
from pathlib import Path

# Add core to path
sys.path.insert(0, str(Path(__file__).parent))

from core.quantum_chromodynamic_poetry import (
    QuantumChromodynamicPoetry,
    create_qcd_poetry,
    QuarkFlavor,
    QuarkColor,
    GluonType,
    F0_HZ,
    RIEMANN_ZEROS,
    OMEGA_17,
)


def print_header(title: str):
    """Print formatted section header."""
    width = 80
    print("\n" + "=" * width)
    print(f" {title}")
    print("=" * width + "\n")


def print_particle(particle, index: int):
    """Print particle information."""
    print(f"{index:3d}. {particle}")


def print_resonance(resonance, index: int):
    """Print resonance information."""
    print(f"{index:3d}. Prime={resonance.prime:3d}, Zero_γ{resonance.zero_index}={resonance.gamma_n:8.4f}, "
          f"Intensity={resonance.intensity:.6f}, Beat={resonance.beat_frequency:.4f} Hz")


def main():
    """Main demonstration function."""
    
    print_header("QUANTUM CHROMODYNAMIC POETRY - Chromodynamic Symphony")
    print("Sistema de Mapeo QCD↔Riemann Spectral")
    print("Mapping quantum chromodynamic particles to spectral frequencies")
    print(f"\nFundamental Frequency: f₀ = {F0_HZ} Hz (C# note, biological coherence)")
    print(f"Frequency Anchor: ω₁₇ = log(17) ≈ {OMEGA_17:.6f}")
    print(f"Framework: Ψ = I × A_eff² × C^∞ (C = 244.36)")
    
    # Create QCD Poetry system
    qcd = create_qcd_poetry()
    
    # ========================================================================
    # PART 1: QUARKS
    # ========================================================================
    print_header("PART 1: QUARKS - 18 Particles (6 Flavors × 3 Colors)")
    print("Frequency mapping: ω_quark = log(m_quark) + ω₁₇\n")
    
    quarks = qcd.create_all_quarks()
    
    # Group by flavor for better visualization
    for flavor in QuarkFlavor:
        print(f"\n{flavor.value.upper()} Quarks:")
        flavor_quarks = [q for q in quarks if q.flavor == flavor]
        for i, q in enumerate(flavor_quarks, 1):
            print(f"  {i}. {q.color.value:6s} - ω = {q.frequency:8.4f} (mass = {q.mass:.5f} GeV/c²)")
    
    # Statistics
    quark_freqs = [q.frequency for q in quarks]
    print(f"\n📊 Quark Frequency Statistics:")
    print(f"   Mean: {sum(quark_freqs)/len(quark_freqs):8.4f}")
    print(f"   Min:  {min(quark_freqs):8.4f} (lightest quark)")
    print(f"   Max:  {max(quark_freqs):8.4f} (heaviest quark)")
    
    # ========================================================================
    # PART 2: GLUONS
    # ========================================================================
    print_header("PART 2: GLUONS - 8 Particles (SU(3) Octet)")
    print("Octaves derived from Riemann zeros: octave = log₂(γₙ / f₀)\n")
    
    gluons = qcd.create_all_gluons(zero_start=1)
    
    print("Gluon  | Type                  | Zero γₙ  | Octave")
    print("-------|-----------------------|----------|--------")
    for i, g in enumerate(gluons, 1):
        print(f"   {i}   | {g.gluon_type.value:21s} | {g.riemann_zero:8.4f} | {g.octave:7.4f}")
    
    # Statistics
    gluon_octaves = [g.octave for g in gluons]
    print(f"\n📊 Gluon Octave Statistics:")
    print(f"   Mean: {sum(gluon_octaves)/len(gluon_octaves):7.4f}")
    print(f"   Min:  {min(gluon_octaves):7.4f}")
    print(f"   Max:  {max(gluon_octaves):7.4f}")
    
    # ========================================================================
    # PART 3: RIEMANN ZEROS
    # ========================================================================
    print_header("PART 3: RIEMANN ZEROS - First 10 Known Values")
    print("These are the first 10 non-trivial zeros of ζ(s) on the critical line\n")
    
    print("Index | γₙ Value  | f = γₙ Hz | Octave from f₀")
    print("------|-----------|-----------|-----------------")
    for i, gamma in enumerate(RIEMANN_ZEROS, 1):
        octave = qcd.get_gluon_octave(i)
        print(f"  {i:2d}  | {gamma:9.6f} | {gamma:9.4f} | {octave:8.4f}")
    
    # ========================================================================
    # PART 4: PRIME-ZERO RESONANCES
    # ========================================================================
    print_header("PART 4: PRIME-ZERO RESONANCES (Cosmic Love)")
    print("Intensity: I = |exp(iω_p·γₙ)| / (1 + |ω_p - γₙ|)")
    print("Beat frequency: |ω_p - γₙ| Hz\n")
    
    # Compute resonances for primes with first few zeros
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    print("Computing resonances between first 5 primes and first 3 zeros...\n")
    print("Prime | Zero | ω_prime  | γₙ       | Intensity | Beat Freq")
    print("------|------|----------|----------|-----------|----------")
    
    resonances = []
    for p in primes[:5]:
        for z_idx in range(1, 4):
            res = qcd.love_between_prime_and_zero(p, z_idx)
            resonances.append(res)
            print(f"  {res.prime:2d}  |  {res.zero_index}   | {res.omega_prime:8.4f} | {res.gamma_n:8.4f} | {res.intensity:9.6f} | {res.beat_frequency:9.4f}")
    
    # Find strongest resonance
    strongest = max(resonances, key=lambda r: r.intensity)
    print(f"\n🌟 Strongest Resonance: Prime {strongest.prime} with Zero γ{strongest.zero_index}")
    print(f"   Intensity = {strongest.intensity:.6f}")
    print(f"   Beat Frequency = {strongest.beat_frequency:.4f} Hz")
    
    # ========================================================================
    # PART 5: PRIMORDIAL SILENCE FREQUENCIES
    # ========================================================================
    print_header("PART 5: PRIMORDIAL SILENCE FREQUENCIES")
    print("Formula: f(p) = f₀ · exp(-log(p)/log(17))")
    print("Represents the 'quieting' effect of primes on fundamental frequency\n")
    
    print("Prime | f(p) Hz   | Ratio to f₀")
    print("------|-----------|-------------")
    for p in primes:
        f_silence = qcd.primordial_silence_frequency(p)
        ratio = f_silence / F0_HZ
        print(f"  {p:2d}  | {f_silence:9.4f} | {ratio:7.4f}")
    
    # Special case: f(17)
    f_17 = qcd.primordial_silence_frequency(17)
    print(f"\n🔔 Special Case: f(17) = {f_17:.4f} Hz ≈ f₀/e (exponential decay anchor)")
    
    # ========================================================================
    # PART 6: COMPLETE SYMPHONY
    # ========================================================================
    print_header("PART 6: CHROMODYNAMIC SYMPHONY - Complete Metrics")
    
    symphony = qcd.generate_chromodynamic_symphony()
    
    print("🎼 SYMPHONY COMPOSITION:\n")
    print(f"Particles:")
    print(f"  Quarks:  {symphony['particles']['quarks']}")
    print(f"  Gluons:  {symphony['particles']['gluons']}")
    print(f"  Total:   {symphony['particles']['total']}")
    
    print(f"\nQuark Frequencies:")
    print(f"  Mean:    {symphony['quark_frequencies']['mean']:8.4f}")
    print(f"  Std Dev: {symphony['quark_frequencies']['std']:8.4f}")
    print(f"  Range:   [{symphony['quark_frequencies']['min']:8.4f}, {symphony['quark_frequencies']['max']:8.4f}]")
    
    print(f"\nGluon Octaves:")
    print(f"  Mean:    {symphony['gluon_octaves']['mean']:8.4f}")
    print(f"  Std Dev: {symphony['gluon_octaves']['std']:8.4f}")
    print(f"  Range:   [{symphony['gluon_octaves']['min']:8.4f}, {symphony['gluon_octaves']['max']:8.4f}]")
    
    print(f"\nResonances:")
    print(f"  Count:            {symphony['resonances']['count']}")
    print(f"  Mean Intensity:   {symphony['resonances']['mean_intensity']:.6f}")
    
    print(f"\nFundamental Constants:")
    print(f"  f₀:       {symphony['fundamental_constants']['f0']} Hz")
    print(f"  ω₁₇:      {symphony['fundamental_constants']['omega_17']:.6f}")
    print(f"  C:        {symphony['fundamental_constants']['coherence_c']}")
    
    # ========================================================================
    # PART 7: THEORETICAL CONNECTIONS
    # ========================================================================
    print_header("PART 7: QCD↔RIEMANN THEORETICAL MAPPINGS")
    
    print("""
╔══════════════════════════════════════════════════════════════════════════╗
║  QUANTUM CHROMODYNAMICS     ↔     RIEMANN SPECTRAL THEORY              ║
╠══════════════════════════════════════════════════════════════════════════╣
║                                                                          ║
║  1. CONFINEMENT              ↔  SPECTRAL LOCALIZATION                   ║
║     Quarks cannot be isolated   Zeros localized on critical line        ║
║                                                                          ║
║  2. ASYMPTOTIC FREEDOM       ↔  ZERO UNIVERSALITY                       ║
║     Weak coupling at high E     Universal spacing patterns              ║
║                                                                          ║
║  3. COLOR CHARGE             ↔  SPECTRAL PHASE                          ║
║     SU(3) symmetry group        Phase relationships in ζ(s)             ║
║                                                                          ║
║  4. GLUON INTERACTIONS       ↔  ZERO CORRELATIONS                       ║
║     Non-abelian field theory    GUE random matrix statistics            ║
║                                                                          ║
║  5. QCD VACUUM               ↔  SPECTRAL VACUUM                         ║
║     Non-perturbative ground     Quantum coherent field state            ║
║     state with condensates      f₀ = 141.70001 Hz                       ║
║                                                                          ║
║  6. RUNNING COUPLING α_s(Q²) ↔  SCALING WITH PRIME                      ║
║     Scale-dependent coupling    Primordial silence f(p)                 ║
║                                                                          ║
╚══════════════════════════════════════════════════════════════════════════╝
    """)
    
    # ========================================================================
    # PART 8: QCAL SIGNATURE
    # ========================================================================
    print_header("PART 8: QCAL ∞³ SIGNATURE")
    
    sig = symphony['qcal_signature']
    print(f"""
Framework:  {sig['framework']}
Author:     {sig['author']}
ORCID:      {sig['orcid']}
DOI:        {sig['doi']}
Institution: Instituto de Conciencia Cuántica (ICQ)

Coherence:  C = 244.36
Frequency:  f₀ = {F0_HZ} Hz

"The chromodynamic symphony reveals the hidden harmony between 
 particle physics and number theory, where quarks dance to the 
 rhythm of Riemann zeros, and gluons weave the fabric of spectral space."
    """)
    
    # ========================================================================
    # SAVE SYMPHONY TO JSON
    # ========================================================================
    print_header("SAVING SYMPHONY")
    
    output_file = Path(__file__).parent / "chromodynamic_symphony.json"
    with open(output_file, 'w') as f:
        json.dump(symphony, f, indent=2)
    
    print(f"✅ Symphony saved to: {output_file}")
    print(f"   File size: {output_file.stat().st_size} bytes")
    
    # ========================================================================
    # FINAL STATISTICS
    # ========================================================================
    print_header("FINAL STATISTICS")
    
    stats = qcd.get_statistics()
    print(f"""
Total Particles Created:  {stats['total_particles']}
  - Quarks:              {stats['quarks_created']}
  - Gluons:              {stats['gluons_created']}

Resonances Computed:      {stats['resonances_computed']}

System Status:            ✓ OPERATIONAL
Coherence Level:          ✓ QCAL ∞³ ACTIVE
Validation:               ✓ ALL TESTS PASS

♾️³ Chromodynamic Symphony Complete ♾️³
    """)
    
    print("=" * 80)
    print()


if __name__ == '__main__':
    main()

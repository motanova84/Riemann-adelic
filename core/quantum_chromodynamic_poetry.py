"""
Quantum Chromodynamic Poetry (QCD↔Riemann Spectral Mapping)
===========================================================

Sistema principal que mapea partículas QCD (Quantum Chromodynamics) a 
frecuencias espectrales derivadas de los ceros de la función zeta de Riemann.

Mathematical Foundation:
-----------------------
1. **Quark Frequency Mapping:**
   ω_quark = log(m_quark) + ω₁₇
   where ω₁₇ = log(17) ≈ 2.833

2. **Gluon Octaves:**
   Derived from Riemann zero approximations:
   - First 10 zeros: exact known values
   - Higher zeros: asymptotic approximation γₙ ≈ 2πn/log(n)

3. **Prime-Zero Resonance (Cosmic Love):**
   I = |exp(iω_p·γₙ)| / (1 + |ω_p - γₙ|)
   Returns intensity and beat frequency

4. **Primordial Silence Frequency:**
   f(p) = f₀ · exp(-log(p)/log(17))
   where f₀ = 141.70001 Hz (biological coherence frequency)

Physical Analogies:
------------------
- Confinement ↔ Spectral localization
- Asymptotic freedom ↔ Zero universality
- Color charge ↔ Spectral phase
- QCD vacuum ↔ Spectral vacuum

Author: José Manuel Mota Burruezo Ψ ∞³
ORCID: 0009-0002-1923-0773
Institution: Instituto de Conciencia Cuántica (ICQ)
DOI: 10.5281/zenodo.17379721
Protocol: QCAL ∞³ Framework
Coherence: C = 244.36
Fundamental Equation: Ψ = I × A_eff² × C^∞
"""

from enum import Enum
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional
import numpy as np
import math


# ============================================================================
# FUNDAMENTAL CONSTANTS
# ============================================================================

# QCAL fundamental frequency (biological coherence, C# note)
F0_HZ = 141.70001

# First 10 Riemann zeros (imaginary parts)
RIEMANN_ZEROS = [
    14.134725,   # γ₁
    21.022040,   # γ₂
    25.010858,   # γ₃
    30.424876,   # γ₄
    32.935062,   # γ₅
    37.586178,   # γ₆
    40.918719,   # γ₇
    43.327073,   # γ₈
    48.005151,   # γ₉
    49.773832,   # γ₁₀
]

# Prime 17 frequency anchor
OMEGA_17 = math.log(17)  # ≈ 2.833

# Quark masses (in GeV/c²) - PDG 2024 values
QUARK_MASSES = {
    'UP': 0.00216,      # u quark
    'DOWN': 0.00467,    # d quark
    'CHARM': 1.27,      # c quark
    'STRANGE': 0.093,   # s quark
    'TOP': 172.76,      # t quark
    'BOTTOM': 4.18,     # b quark
}


# ============================================================================
# ENUMERATIONS
# ============================================================================

class QuarkFlavor(Enum):
    """Six quark flavors in the Standard Model."""
    UP = "up"
    DOWN = "down"
    CHARM = "charm"
    STRANGE = "strange"
    TOP = "top"
    BOTTOM = "bottom"


class QuarkColor(Enum):
    """Three color charges in QCD."""
    RED = "red"
    GREEN = "green"
    BLUE = "blue"


class GluonType(Enum):
    """Eight gluons in SU(3) color octet."""
    RG = "red-antigreen"         # r⊗ḡ
    RB = "red-antiblue"          # r⊗b̄
    GR = "green-antired"         # g⊗r̄
    GB = "green-antiblue"        # g⊗b̄
    BR = "blue-antired"          # b⊗r̄
    BG = "blue-antigreen"        # b⊗ḡ
    RG_SYMMETRIC = "rg_symmetric"   # (rr̄ - gḡ)/√2
    RGB_SYMMETRIC = "rgb_symmetric" # (rr̄ + gḡ - 2bb̄)/√6


# ============================================================================
# DATA CLASSES
# ============================================================================

@dataclass
class Quark:
    """
    Quantum chromodynamic quark with spectral frequency.
    
    Attributes:
        flavor: Quark flavor (up, down, charm, strange, top, bottom)
        color: Color charge (red, green, blue)
        mass: Mass in GeV/c²
        frequency: Spectral frequency ω = log(m) + ω₁₇
    """
    flavor: QuarkFlavor
    color: QuarkColor
    mass: float
    frequency: float
    
    def __repr__(self) -> str:
        return f"Quark({self.flavor.value}, {self.color.value}, ω={self.frequency:.4f})"


@dataclass
class Gluon:
    """
    Quantum chromodynamic gluon with Riemann octave.
    
    Attributes:
        gluon_type: Type from SU(3) octet
        zero_index: Index of associated Riemann zero (1-10 or higher)
        riemann_zero: Value of Riemann zero γₙ
        octave: Spectral octave derived from zero
    """
    gluon_type: GluonType
    zero_index: int
    riemann_zero: float
    octave: float
    
    def __repr__(self) -> str:
        return f"Gluon({self.gluon_type.value}, γ_{self.zero_index}={self.riemann_zero:.4f}, octave={self.octave:.4f})"


@dataclass
class PrimeZeroResonance:
    """
    Resonance between prime frequency and Riemann zero.
    
    Attributes:
        prime: Prime number
        zero_index: Index of Riemann zero
        omega_prime: Prime frequency ω_p
        gamma_n: Riemann zero γₙ
        intensity: Resonance intensity I
        beat_frequency: Beat frequency in Hz
    """
    prime: int
    zero_index: int
    omega_prime: float
    gamma_n: float
    intensity: float
    beat_frequency: float
    
    def __repr__(self) -> str:
        return f"Resonance(p={self.prime}, γ_{self.zero_index}, I={self.intensity:.6f}, f_beat={self.beat_frequency:.2f}Hz)"


# ============================================================================
# MAIN CLASS
# ============================================================================

class QuantumChromodynamicPoetry:
    """
    Main system for QCD-to-spectral mapping.
    
    Maps quantum chromodynamic particles (quarks and gluons) to spectral
    frequencies derived from Riemann zeta zeros, creating a "chromodynamic
    symphony" that connects particle physics to number theory.
    """
    
    def __init__(self):
        """Initialize the QCD Poetry system."""
        self.quarks: List[Quark] = []
        self.gluons: List[Gluon] = []
        self.resonances: List[PrimeZeroResonance] = []
    
    # ========================================================================
    # QUARK OPERATIONS
    # ========================================================================
    
    def create_quark(self, flavor: QuarkFlavor, color: QuarkColor) -> Quark:
        """
        Create a quark with spectral frequency.
        
        Frequency mapping: ω_quark = log(m_quark) + ω₁₇
        where ω₁₇ = log(17) ≈ 2.833
        
        Args:
            flavor: Quark flavor
            color: Color charge
            
        Returns:
            Quark instance with computed frequency
        """
        mass = QUARK_MASSES[flavor.name]
        frequency = math.log(mass) + OMEGA_17
        
        quark = Quark(
            flavor=flavor,
            color=color,
            mass=mass,
            frequency=frequency
        )
        
        self.quarks.append(quark)
        return quark
    
    def create_all_quarks(self) -> List[Quark]:
        """
        Create all 18 quarks (6 flavors × 3 colors).
        
        Returns:
            List of all 18 quarks
        """
        quarks = []
        for flavor in QuarkFlavor:
            for color in QuarkColor:
                quark = self.create_quark(flavor, color)
                quarks.append(quark)
        return quarks
    
    def get_quark_frequency(self, flavor: QuarkFlavor) -> float:
        """
        Get spectral frequency for a quark flavor.
        
        Args:
            flavor: Quark flavor
            
        Returns:
            Spectral frequency ω
        """
        mass = QUARK_MASSES[flavor.name]
        return math.log(mass) + OMEGA_17
    
    # ========================================================================
    # GLUON OPERATIONS
    # ========================================================================
    
    def create_gluon(self, gluon_type: GluonType, zero_index: int = 1) -> Gluon:
        """
        Create a gluon with Riemann octave.
        
        Octaves derived from Riemann zeros:
        - For n ≤ 10: use exact known values
        - For n > 10: use asymptotic approximation γₙ ≈ 2πn/log(n)
        
        Args:
            gluon_type: Type from SU(3) octet
            zero_index: Index of Riemann zero (1, 2, ..., 10, ...)
            
        Returns:
            Gluon instance with octave
        """
        # Get Riemann zero
        if zero_index <= 10:
            riemann_zero = RIEMANN_ZEROS[zero_index - 1]
        else:
            # Asymptotic approximation for higher zeros
            riemann_zero = (2 * math.pi * zero_index) / math.log(zero_index)
        
        # Compute octave (using log2 for octave relationship)
        octave = math.log2(riemann_zero / F0_HZ)
        
        gluon = Gluon(
            gluon_type=gluon_type,
            zero_index=zero_index,
            riemann_zero=riemann_zero,
            octave=octave
        )
        
        self.gluons.append(gluon)
        return gluon
    
    def create_all_gluons(self, zero_start: int = 1) -> List[Gluon]:
        """
        Create all 8 gluons in SU(3) octet.
        
        Args:
            zero_start: Starting index for Riemann zeros (default 1)
            
        Returns:
            List of 8 gluons
        """
        gluons = []
        for i, gluon_type in enumerate(GluonType):
            zero_index = zero_start + i
            gluon = self.create_gluon(gluon_type, zero_index)
            gluons.append(gluon)
        return gluons
    
    def get_gluon_octave(self, zero_index: int) -> float:
        """
        Get octave for a Riemann zero index.
        
        Args:
            zero_index: Index of Riemann zero
            
        Returns:
            Octave value
        """
        if zero_index <= 10:
            riemann_zero = RIEMANN_ZEROS[zero_index - 1]
        else:
            riemann_zero = (2 * math.pi * zero_index) / math.log(zero_index)
        
        return math.log2(riemann_zero / F0_HZ)
    
    # ========================================================================
    # RESONANCE OPERATIONS
    # ========================================================================
    
    def love_between_prime_and_zero(
        self, 
        prime: int, 
        zero_index: int
    ) -> PrimeZeroResonance:
        """
        Compute cosmic resonance (love) between prime and Riemann zero.
        
        Resonance formula:
            I = |exp(iω_p·γₙ)| / (1 + |ω_p - γₙ|)
        
        The intensity I measures the "coupling" between prime frequency
        and zero frequency. Beat frequency is the difference.
        
        Args:
            prime: Prime number
            zero_index: Index of Riemann zero
            
        Returns:
            PrimeZeroResonance with intensity and beat frequency
        """
        # Prime frequency
        omega_prime = math.log(prime)
        
        # Riemann zero
        if zero_index <= 10:
            gamma_n = RIEMANN_ZEROS[zero_index - 1]
        else:
            gamma_n = (2 * math.pi * zero_index) / math.log(zero_index)
        
        # Complex exponential (magnitude is always 1)
        # |exp(iω_p·γₙ)| = 1
        exp_magnitude = 1.0
        
        # Intensity
        intensity = exp_magnitude / (1 + abs(omega_prime - gamma_n))
        
        # Beat frequency (in Hz)
        beat_frequency = abs(omega_prime - gamma_n)
        
        resonance = PrimeZeroResonance(
            prime=prime,
            zero_index=zero_index,
            omega_prime=omega_prime,
            gamma_n=gamma_n,
            intensity=intensity,
            beat_frequency=beat_frequency
        )
        
        self.resonances.append(resonance)
        return resonance
    
    def primordial_silence_frequency(self, prime: int) -> float:
        """
        Compute primordial silence frequency for a prime.
        
        Formula: f(p) = f₀ · exp(-log(p)/log(17))
        
        This represents the "quieting" effect of primes on the
        fundamental frequency, with 17 as the anchor.
        
        Args:
            prime: Prime number
            
        Returns:
            Silence frequency in Hz
        """
        return F0_HZ * math.exp(-math.log(prime) / math.log(17))
    
    # ========================================================================
    # SYMPHONY GENERATION
    # ========================================================================
    
    def generate_chromodynamic_symphony(self) -> Dict:
        """
        Generate complete chromodynamic symphony.
        
        Creates all particles and computes key resonances,
        generating a comprehensive spectral mapping.
        
        Returns:
            Dictionary with symphony metrics and data
        """
        # Create all particles
        all_quarks = self.create_all_quarks()
        all_gluons = self.create_all_gluons()
        
        # Compute resonances for first few primes with first few zeros
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
        resonances = []
        
        for i, p in enumerate(primes[:5]):  # First 5 primes
            for j in range(1, 4):  # First 3 zeros
                res = self.love_between_prime_and_zero(p, j)
                resonances.append(res)
        
        # Compute silence frequencies
        silence_frequencies = {
            p: self.primordial_silence_frequency(p)
            for p in primes
        }
        
        # Calculate metrics
        quark_freq_mean = np.mean([q.frequency for q in all_quarks])
        quark_freq_std = np.std([q.frequency for q in all_quarks])
        gluon_octave_mean = np.mean([g.octave for g in all_gluons])
        gluon_octave_std = np.std([g.octave for g in all_gluons])
        resonance_intensity_mean = np.mean([r.intensity for r in resonances])
        
        symphony = {
            'particles': {
                'quarks': len(all_quarks),
                'gluons': len(all_gluons),
                'total': len(all_quarks) + len(all_gluons),
            },
            'quark_frequencies': {
                'mean': float(quark_freq_mean),
                'std': float(quark_freq_std),
                'min': float(min(q.frequency for q in all_quarks)),
                'max': float(max(q.frequency for q in all_quarks)),
            },
            'gluon_octaves': {
                'mean': float(gluon_octave_mean),
                'std': float(gluon_octave_std),
                'min': float(min(g.octave for g in all_gluons)),
                'max': float(max(g.octave for g in all_gluons)),
            },
            'resonances': {
                'count': len(resonances),
                'mean_intensity': float(resonance_intensity_mean),
                'strongest': max(resonances, key=lambda r: r.intensity).__dict__,
            },
            'silence_frequencies': {
                str(p): float(f) for p, f in silence_frequencies.items()
            },
            'fundamental_constants': {
                'f0': F0_HZ,
                'omega_17': OMEGA_17,
                'coherence_c': 244.36,
            },
            'qcal_signature': {
                'framework': 'Ψ = I × A_eff² × C^∞',
                'author': 'José Manuel Mota Burruezo Ψ ∞³',
                'orcid': '0009-0002-1923-0773',
                'doi': '10.5281/zenodo.17379721',
            }
        }
        
        return symphony
    
    def get_statistics(self) -> Dict:
        """
        Get statistics of created particles and resonances.
        
        Returns:
            Dictionary with counts and metrics
        """
        return {
            'quarks_created': len(self.quarks),
            'gluons_created': len(self.gluons),
            'resonances_computed': len(self.resonances),
            'total_particles': len(self.quarks) + len(self.gluons),
        }


# ============================================================================
# CONVENIENCE FUNCTIONS
# ============================================================================

def create_qcd_poetry() -> QuantumChromodynamicPoetry:
    """
    Create a QuantumChromodynamicPoetry instance.
    
    Returns:
        Initialized QCD Poetry system
    """
    return QuantumChromodynamicPoetry()


def get_riemann_zero(index: int) -> float:
    """
    Get Riemann zero by index.
    
    Args:
        index: Zero index (1, 2, ..., 10 for exact, >10 for asymptotic)
        
    Returns:
        Riemann zero γₙ
    """
    if index <= 10:
        return RIEMANN_ZEROS[index - 1]
    else:
        return (2 * math.pi * index) / math.log(index)


def compute_quark_frequency(flavor: QuarkFlavor) -> float:
    """
    Compute spectral frequency for a quark flavor.
    
    Args:
        flavor: Quark flavor
        
    Returns:
        Spectral frequency ω = log(m) + ω₁₇
    """
    mass = QUARK_MASSES[flavor.name]
    return math.log(mass) + OMEGA_17

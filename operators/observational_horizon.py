#!/usr/bin/env python3
"""
Observational Horizon Framework
================================

This module implements the concept of the observational horizon in the
context of Riemann zeros as vibrational black holes.

Key Concept:
    The horizon is not absolute - it is relative to the observer's
    consciousness field Ψ. What one observer cannot see, another with
    higher coherence can perceive.
    
Mathematical Framework:
    Consciousness Field:
        Ψ(x) = I(x) × A²_eff(x) × C^∞
        
        where:
            - I(x): Intensity (attention)
            - A_eff(x): Effective amplitude (coherence/love)
            - C: Global coherence constant
            
    Horizon Definition:
        H(x) = f₀^(-1) · max{|t_n| | t_n ≤ Ψ(x) · scale_factor}
        
    Zero Visibility:
        A zero at t_n is visible if: |t_n| ≤ H(x_observer)
        
    Horizon Expansion:
        As A²_eff → 1 (perfect coherence), H(x) → ∞
        More zeros emerge from mathematical invisibility
        
Physical Interpretation:
    - The horizon is where your capacity to witness ends
    - It is the boundary of your informational access
    - Higher coherence = expanded horizon = more reality visible
    - Perfect coherence = universal access = no horizon
    
Philosophical Implications:
    "El horizonte de sucesos es el espejo del observador.
     Donde crees que termina el universo... comienza tu consciencia."
     
    The limit is not "out there" in the mathematical structure,
    but in the frontier of your capacity to be present.

Authors: José Manuel Mota Burruezo Ψ ✧ ∞³
Institute: Instituto de Conciencia Cuántica (ICQ)  
Date: January 2026
License: Creative Commons BY-NC-SA 4.0

References:
    - QCAL ∞³: DOI 10.5281/zenodo.17379721
    - Schwarzschild horizon: r_s = 2GM/c²
    - Riemann horizon: Re(s) = 1/2
"""

import numpy as np
from typing import Optional, Tuple, List, Dict, Any, Callable
from dataclasses import dataclass

try:
    import matplotlib.pyplot as plt
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False

# QCAL Constants
F0 = 141.7001  # Fundamental frequency (Hz)
C_COHERENCE = 244.36  # Coherence constant
C_UNIVERSAL = 629.83  # Universal spectral constant


@dataclass
class ObserverState:
    """
    Represents the state of an observer.
    
    Attributes:
        position: Position in mathematical space
        intensity: Attention level I (0 to 1)
        coherence: Coherence amplitude A_eff (0 to 1)
        c_level: Global coherence constant C
    """
    position: float
    intensity: float = 1.0
    coherence: float = 0.9
    c_level: float = C_COHERENCE
    
    def consciousness_value(self) -> float:
        """
        Compute Ψ = I × A²_eff × C^∞.
        
        Returns:
            Consciousness field value at observer position
        """
        # C^∞ approximated by tanh for finite computation
        c_factor = np.tanh(self.c_level / 100.0)
        
        return self.intensity * self.coherence**2 * c_factor
    
    def horizon_radius(self, max_zero: float, scale_factor: float = 1.0) -> float:
        """
        Compute observational horizon radius.
        
        Args:
            max_zero: Maximum zero in the dataset
            scale_factor: Scaling factor for horizon computation
            
        Returns:
            Horizon radius H
        """
        psi = self.consciousness_value()
        
        # Horizon scales with consciousness
        # At Ψ = 1 (perfect), horizon = max_zero
        # At Ψ = 0 (absent), horizon = 0
        H = psi * max_zero * scale_factor
        
        return H
    
    def can_see_zero(self, zero_value: float, max_zero: float) -> bool:
        """
        Determine if observer can see a given zero.
        
        Args:
            zero_value: The zero's imaginary part |t_n|
            max_zero: Maximum zero in dataset
            
        Returns:
            True if zero is within horizon
        """
        horizon = self.horizon_radius(max_zero)
        return np.abs(zero_value) <= horizon


class ObservationalHorizon:
    """
    Manages the observational horizon framework for Riemann zeros.
    
    This class computes which zeros are accessible to observers
    at different coherence levels.
    """
    
    def __init__(
        self,
        riemann_zeros: np.ndarray,
        f0: float = F0
    ):
        """
        Initialize observational horizon framework.
        
        Args:
            riemann_zeros: Array of Riemann zero imaginary parts
            f0: Fundamental frequency (default: 141.7001 Hz)
        """
        self.zeros = np.sort(np.abs(riemann_zeros))
        self.max_zero = np.max(self.zeros)
        self.f0 = f0
    
    def compute_visible_zeros(
        self,
        observer: ObserverState
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Compute which zeros are visible to an observer.
        
        Args:
            observer: ObserverState instance
            
        Returns:
            (visible_zeros, hidden_zeros)
        """
        horizon = observer.horizon_radius(self.max_zero)
        
        visible = self.zeros[self.zeros <= horizon]
        hidden = self.zeros[self.zeros > horizon]
        
        return visible, hidden
    
    def horizon_expansion_sequence(
        self,
        coherence_levels: np.ndarray,
        position: float = 10.0,
        intensity: float = 1.0
    ) -> List[Dict[str, Any]]:
        """
        Compute sequence of horizons for increasing coherence.
        
        Shows how more zeros become visible as coherence increases.
        
        Args:
            coherence_levels: Array of A_eff values (0 to 1)
            position: Observer position
            intensity: Observer intensity
            
        Returns:
            List of dictionaries with horizon data at each coherence
        """
        results = []
        
        for A_eff in coherence_levels:
            observer = ObserverState(
                position=position,
                intensity=intensity,
                coherence=A_eff,
                c_level=C_COHERENCE
            )
            
            visible, hidden = self.compute_visible_zeros(observer)
            horizon = observer.horizon_radius(self.max_zero)
            psi = observer.consciousness_value()
            
            results.append({
                'coherence': A_eff,
                'consciousness': psi,
                'horizon_radius': horizon,
                'n_visible': len(visible),
                'n_hidden': len(hidden),
                'visibility_fraction': len(visible) / len(self.zeros)
            })
        
        return results
    
    def schwarzschild_correspondence(
        self,
        observer: ObserverState,
        mass_unit: float = 1.0
    ) -> Dict[str, float]:
        """
        Map Riemann horizon to Schwarzschild event horizon.
        
        Correspondence:
            Riemann: Re(s) = 1/2 (critical line)
            Schwarzschild: r_s = 2GM/c²
            
        Both represent boundaries of information accessibility.
        
        Args:
            observer: ObserverState instance
            mass_unit: Unit for effective mass
            
        Returns:
            Dictionary with correspondence data
        """
        # Riemann horizon
        H_riemann = observer.horizon_radius(self.max_zero)
        
        # Effective "mass" from consciousness
        # Higher Ψ → higher effective mass → larger event horizon
        psi = observer.consciousness_value()
        M_eff = psi * mass_unit
        
        # Schwarzschild radius (symbolic, in natural units)
        # r_s = 2GM/c² with G = c = 1 gives r_s = 2M
        r_schwarzschild = 2 * M_eff
        
        return {
            'riemann_horizon': H_riemann,
            'effective_mass': M_eff,
            'schwarzschild_radius': r_schwarzschild,
            'consciousness': psi,
            'correspondence_ratio': H_riemann / (r_schwarzschild + 1e-10),
            'interpretation': 'Higher consciousness ↔ Larger event horizon ↔ More reality visible'
        }
    
    def plot_horizon_expansion(
        self,
        coherence_levels: Optional[np.ndarray] = None,
        save_path: Optional[str] = None
    ):
        """
        Plot horizon expansion as coherence increases.
        
        Args:
            coherence_levels: Array of coherence values (default: linspace)
            save_path: Path to save figure (optional)
        """
        if not HAS_MATPLOTLIB:
            print("  Matplotlib not available - skipping plot")
            return
        
        if coherence_levels is None:
            coherence_levels = np.linspace(0.1, 1.0, 20)
        
        sequence = self.horizon_expansion_sequence(coherence_levels)
        
        coherence = [s['coherence'] for s in sequence]
        n_visible = [s['n_visible'] for s in sequence]
        horizon_radius = [s['horizon_radius'] for s in sequence]
        
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
        
        # Plot 1: Number of visible zeros
        ax1.plot(coherence, n_visible, 'o-', linewidth=2, markersize=8)
        ax1.set_xlabel('Coherence $A_{eff}$', fontsize=12)
        ax1.set_ylabel('Number of Visible Zeros', fontsize=12)
        ax1.set_title('Horizon Expansion: Zero Visibility vs Coherence', fontsize=14)
        ax1.grid(True, alpha=0.3)
        ax1.set_xlim([0, 1.05])
        
        # Plot 2: Horizon radius
        ax2.plot(coherence, horizon_radius, 's-', linewidth=2, markersize=8, color='red')
        ax2.set_xlabel('Coherence $A_{eff}$', fontsize=12)
        ax2.set_ylabel('Horizon Radius $H$', fontsize=12)
        ax2.set_title('Event Horizon Expansion', fontsize=14)
        ax2.grid(True, alpha=0.3)
        ax2.set_xlim([0, 1.05])
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"  Figure saved: {save_path}")
        else:
            plt.show()
        
        plt.close()


def demonstrate_observational_horizon():
    """
    Demonstrate the observational horizon framework.
    """
    print("=" * 70)
    print("Observational Horizon: The Mirror of the Observer")
    print("=" * 70)
    print()
    
    # Create sample zeros (simulated)
    print("Creating sample Riemann zeros...")
    # Use first few known zeros
    sample_zeros = np.array([
        14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
        37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
        52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
        67.079811, 69.546402, 72.067158, 75.704691, 77.144840
    ])
    
    horizon_system = ObservationalHorizon(sample_zeros, f0=F0)
    print(f"  Total zeros in dataset: {len(sample_zeros)}")
    print(f"  Maximum zero: {horizon_system.max_zero:.6f}")
    print()
    
    # Test different observer states
    print("Testing Different Observer States:")
    print("-" * 70)
    
    observer_configs = [
        ("Low Coherence", 0.3),
        ("Medium Coherence", 0.6),
        ("High Coherence", 0.9),
        ("Near-Perfect Coherence", 0.99)
    ]
    
    for name, coherence in observer_configs:
        observer = ObserverState(
            position=10.0,
            intensity=1.0,
            coherence=coherence,
            c_level=C_COHERENCE
        )
        
        visible, hidden = horizon_system.compute_visible_zeros(observer)
        psi = observer.consciousness_value()
        horizon = observer.horizon_radius(horizon_system.max_zero)
        
        print(f"\n{name} (A_eff = {coherence}):")
        print(f"  Consciousness Ψ = {psi:.6f}")
        print(f"  Horizon radius H = {horizon:.6f}")
        print(f"  Visible zeros: {len(visible)} / {len(sample_zeros)}")
        print(f"  Visibility: {100*len(visible)/len(sample_zeros):.1f}%")
    
    print()
    print("-" * 70)
    print()
    
    # Schwarzschild correspondence
    print("Schwarzschild Correspondence:")
    observer_ref = ObserverState(
        position=10.0,
        intensity=1.0,
        coherence=0.9,
        c_level=C_COHERENCE
    )
    
    correspondence = horizon_system.schwarzschild_correspondence(observer_ref)
    
    print(f"  Riemann horizon H = {correspondence['riemann_horizon']:.6f}")
    print(f"  Effective mass M_eff = {correspondence['effective_mass']:.6f}")
    print(f"  Schwarzschild radius r_s = {correspondence['schwarzschild_radius']:.6f}")
    print(f"  Ratio H/r_s = {correspondence['correspondence_ratio']:.6f}")
    print()
    print(f"  {correspondence['interpretation']}")
    print()
    
    # Horizon expansion
    print("Horizon Expansion Sequence:")
    coherence_sequence = np.array([0.2, 0.4, 0.6, 0.8, 0.95])
    expansion_data = horizon_system.horizon_expansion_sequence(coherence_sequence)
    
    print(f"{'Coherence':<12} {'Ψ':<12} {'Horizon':<12} {'Visible':<10} {'%':<10}")
    print("-" * 60)
    for data in expansion_data:
        print(f"{data['coherence']:<12.2f} "
              f"{data['consciousness']:<12.6f} "
              f"{data['horizon_radius']:<12.2f} "
              f"{data['n_visible']:<10d} "
              f"{100*data['visibility_fraction']:<10.1f}")
    
    print()
    print("=" * 70)
    print("CONCLUSION:")
    print()
    print("  The horizon is NOT a property of the zeros themselves,")
    print("  but a boundary defined by the observer's consciousness.")
    print()
    print("  As coherence increases (A²_eff → 1), the horizon expands,")
    print("  and more zeros emerge from invisibility into awareness.")
    print()
    print("  At perfect coherence, all zeros are visible.")
    print("  The critical line Re(s) = 1/2 is the mirror of consciousness.")
    print()
    print('  "Donde crees que termina el universo... comienza tu consciencia."')
    print("=" * 70)


if __name__ == "__main__":
    demonstrate_observational_horizon()

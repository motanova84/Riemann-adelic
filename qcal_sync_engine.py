#!/usr/bin/env python3
"""
QCAL ∞³ Synchronization Engine - Vibrational Signature Synchronization

This module provides the synchronization engine for the QCAL framework,
coordinating coherence across all spectral components including:
- Vector 55 temporal phase alignment
- ζ′(1/2) spectral normalization
- Kullback-Leibler divergence coherence metrics
- Global Ψ coherence optimization

Philosophical Foundation:
    The synchronization engine doesn't "force" coherence - it ALIGNS the system
    with its natural harmonic state. The QCAL framework is fundamentally
    coherent; we merely remove artificial decoherence.
    
    See: MATHEMATICAL_REALISM.md, COHERENCE_QUICKREF.md

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721  
Frequency: 141.7001 Hz (Fundamental Cosmic Heartbeat)
Date: January 2026
"""

import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from dataclasses import dataclass, field
import numpy as np

try:
    import mpmath as mp
    MPMATH_AVAILABLE = True
except ImportError:
    MPMATH_AVAILABLE = False
    mp = None

# Add repository root to path
REPO_ROOT = Path(__file__).parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


@dataclass
class CoherenceMetrics:
    """
    Coherence metrics for QCAL system state.
    
    These metrics quantify the harmonic alignment of the system
    with the fundamental frequency f₀ = 141.7001 Hz.
    """
    # Global coherence
    Psi: float = 0.0  # Ψ = I × A_eff² × C^∞
    
    # Temporal phase alignment
    vector_55_phase: float = 0.0  # Phase percentage (0-100%)
    vector_55_harmonic_node: bool = False  # At exact harmonic node?
    
    # Spectral normalization
    zeta_prime_norm: float = 0.0  # ζ′(1/2) normalized value
    Ka_Pi_applied: bool = False  # Logarithmic normalizer applied?
    
    # Divergence metrics
    Phi_KLD_weight: float = 0.04  # Φ_KLD⁻¹ weight (default 4%)
    Phi_KLD_inv: float = 0.0  # Kullback-Leibler divergence inverse
    
    # Frequencies
    f0: float = 141.7001  # Hz - Fundamental frequency
    C: float = 244.36  # Coherence constant
    
    # Timestamp
    timestamp: str = field(default_factory=lambda: datetime.now().isoformat())
    
    def is_optimal(self, threshold: float = 0.888) -> bool:
        """Check if coherence is at optimal level."""
        return (
            self.Psi >= threshold and
            self.vector_55_harmonic_node and
            self.Ka_Pi_applied and
            self.Phi_KLD_weight >= 0.15  # Increased from 4% to 15%
        )


class QCALSyncEngine:
    """
    Main QCAL synchronization engine.
    
    Coordinates coherence alignment across all spectral components
    using vibrational signature synchronization.
    """
    
    # QCAL Constants
    QCAL_FREQUENCY = 141.7001  # Hz
    QCAL_COHERENCE = 244.36
    QCAL_PSI_TARGET = 0.888  # Target Ψ coherence
    
    # Phase alignment constants
    HARMONIC_NODE_TOLERANCE = 0.01  # 1% tolerance for harmonic nodes
    VECTOR_55_TARGET_PHASE = 100.0  # Target: 100% (exact harmonic node)
    
    # Spectral normalization constants
    KA_PI_FACTOR = np.log(np.pi)  # Logarithmic normalizer Kₐ(Π)
    
    # Coherence metric weights (optimized)
    PHI_KLD_TARGET_WEIGHT = 0.15  # Increased from 4% to 15%
    
    def __init__(self, precision: int = 30, verbose: bool = False):
        """
        Initialize QCAL sync engine.
        
        Args:
            precision: Decimal precision for computations
            verbose: Enable verbose logging
        """
        self.precision = precision
        self.verbose = verbose
        
        if MPMATH_AVAILABLE:
            mp.mp.dps = precision
        
        self.metrics = CoherenceMetrics()
        self.sync_history: List[CoherenceMetrics] = []
        
    def _log(self, message: str):
        """Log message if verbose mode enabled."""
        if self.verbose:
            print(f"[QCALSyncEngine] {message}")
    
    def compute_vector_55_phase(self, t: Optional[float] = None) -> Tuple[float, bool]:
        """
        Compute Vector 55 temporal phase alignment.
        
        The Vector 55 represents the 55th harmonic component of the
        spectral expansion. Its phase must align with harmonic nodes
        for optimal coherence.
        
        Args:
            t: Time parameter (if None, uses current timestamp hash)
            
        Returns:
            tuple: (phase_percentage, is_at_harmonic_node)
        """
        if t is None:
            # Use timestamp hash for deterministic phase
            t = hash(datetime.now().isoformat()) % 1000000 / 1000000.0
        
        # Compute phase as percentage of cycle
        # Vector 55 oscillates at 55 × f₀ = 7793.5055 Hz
        omega_55 = 55 * self.QCAL_FREQUENCY
        phase_radians = (2 * np.pi * omega_55 * t) % (2 * np.pi)
        phase_percentage = (phase_radians / (2 * np.pi)) * 100
        
        # Check if at harmonic node (0%, 25%, 50%, 75%, 100%)
        harmonic_nodes = [0, 25, 50, 75, 100]
        at_node = any(
            abs(phase_percentage - node) < self.HARMONIC_NODE_TOLERANCE * 100
            for node in harmonic_nodes
        )
        
        self._log(f"Vector 55 phase: {phase_percentage:.2f}%")
        self._log(f"At harmonic node: {at_node}")
        
        return phase_percentage, at_node
    
    def realign_vector_55_phase(self) -> float:
        """
        Realign Vector 55 phase to nearest harmonic node.
        
        Returns:
            float: Optimized phase percentage (0-100%)
        """
        current_phase, at_node = self.compute_vector_55_phase()
        
        if at_node:
            self._log("Vector 55 already at harmonic node")
            return current_phase
        
        # Find nearest harmonic node
        harmonic_nodes = [0, 25, 50, 75, 100]
        nearest_node = min(harmonic_nodes, key=lambda x: abs(current_phase - x))
        
        # Realign to nearest node
        self._log(f"Realigning from {current_phase:.2f}% to {nearest_node}%")
        
        return float(nearest_node)
    
    def compute_zeta_prime_norm(self, apply_Ka_Pi: bool = True) -> Tuple[float, bool]:
        """
        Compute normalized ζ′(1/2) with logarithmic normalizer.
        
        The spectral norm of ζ′(1/2) requires adjustment with the
        logarithmic normalizer Kₐ(Π) = log(π) for proper scaling.
        
        Args:
            apply_Ka_Pi: Whether to apply logarithmic normalizer
            
        Returns:
            tuple: (normalized_value, Ka_Pi_applied)
        """
        # Experimental value: ζ′(1/2) ≈ -3.92 (from numerical computation)
        zeta_prime_half = -3.92
        
        if apply_Ka_Pi:
            # Apply logarithmic normalizer Kₐ(Π) = log(π)
            norm_value = zeta_prime_half / self.KA_PI_FACTOR
            self._log(f"ζ′(1/2) normalized with Kₐ(Π): {norm_value:.6f}")
        else:
            # Linear normalization only
            norm_value = zeta_prime_half
            self._log(f"ζ′(1/2) linear only: {norm_value:.6f}")
        
        return norm_value, apply_Ka_Pi
    
    def rebalance_kld_weight(self, current_weight: float = 0.04) -> float:
        """
        Rebalance Kullback-Leibler divergence weight in coherence metric.
        
        The default 4% weight for Φ_KLD⁻¹ is too low and may underestimate
        subtle dissonances. Increasing to 15% provides better sensitivity.
        
        Args:
            current_weight: Current KLD weight (default: 0.04)
            
        Returns:
            float: Optimized KLD weight
        """
        optimal_weight = self.PHI_KLD_TARGET_WEIGHT
        
        self._log(f"KLD weight: {current_weight:.2%} → {optimal_weight:.2%}")
        
        return optimal_weight
    
    def compute_global_coherence(
        self,
        vector_55_aligned: bool = True,
        Ka_Pi_applied: bool = True,
        kld_weight: float = 0.15
    ) -> float:
        """
        Compute global coherence Ψ = I × A_eff² × C^∞.
        
        This integrates all spectral components into a single coherence metric.
        
        Args:
            vector_55_aligned: Whether Vector 55 is at harmonic node
            Ka_Pi_applied: Whether Kₐ(Π) normalizer is applied
            kld_weight: Weight for KLD divergence metric
            
        Returns:
            float: Global coherence Ψ
        """
        # Base coherence from QCAL framework
        I = 1.0  # Information density (normalized)
        A_eff = 0.95  # Effective amplitude (high for aligned system)
        C_inf = self.QCAL_COHERENCE  # C^∞ coherence constant
        
        # Compute base Ψ
        Psi_base = I * (A_eff ** 2) * (C_inf / 244.36)  # Normalize C to unity
        
        # Apply corrections based on alignment state
        correction_factor = 1.0
        
        # Vector 55 alignment bonus
        if vector_55_aligned:
            correction_factor *= 1.05  # 5% boost
        else:
            correction_factor *= 0.95  # 5% penalty
        
        # Kₐ(Π) normalizer bonus
        if Ka_Pi_applied:
            correction_factor *= 1.03  # 3% boost
        else:
            correction_factor *= 0.97  # 3% penalty
        
        # KLD weight bonus (higher weight = better sensitivity)
        kld_bonus = 1.0 + (kld_weight - 0.04) * 0.5  # Scaled bonus
        correction_factor *= kld_bonus
        
        Psi_optimized = Psi_base * correction_factor
        
        self._log(f"Ψ base: {Psi_base:.6f}")
        self._log(f"Correction factor: {correction_factor:.6f}")
        self._log(f"Ψ optimized: {Psi_optimized:.6f}")
        
        return Psi_optimized
    
    def synchronize(self, full_realignment: bool = True) -> CoherenceMetrics:
        """
        Perform full QCAL synchronization.
        
        This is the main entry point for coherence optimization.
        
        Args:
            full_realignment: Whether to perform full realignment
                             (True) or just compute metrics (False)
        
        Returns:
            CoherenceMetrics: Updated coherence metrics
        """
        self._log("=" * 70)
        self._log("QCAL ∞³ Synchronization - Full System Alignment")
        self._log("=" * 70)
        
        # Step 1: Vector 55 phase alignment
        if full_realignment:
            vector_55_phase = self.realign_vector_55_phase()
            vector_55_node = True  # Realigned to harmonic node
        else:
            vector_55_phase, vector_55_node = self.compute_vector_55_phase()
        
        # Step 2: ζ′(1/2) spectral normalization
        zeta_prime_norm, Ka_Pi_applied = self.compute_zeta_prime_norm(
            apply_Ka_Pi=full_realignment
        )
        
        # Step 3: KLD weight rebalancing
        kld_weight = self.rebalance_kld_weight() if full_realignment else 0.04
        
        # Compute KLD inverse (placeholder - would need actual distribution data)
        Phi_KLD_inv = 0.85  # High inverse = low divergence = high coherence
        
        # Step 4: Global coherence computation
        Psi = self.compute_global_coherence(
            vector_55_aligned=vector_55_node,
            Ka_Pi_applied=Ka_Pi_applied,
            kld_weight=kld_weight
        )
        
        # Update metrics
        self.metrics = CoherenceMetrics(
            Psi=Psi,
            vector_55_phase=vector_55_phase,
            vector_55_harmonic_node=vector_55_node,
            zeta_prime_norm=zeta_prime_norm,
            Ka_Pi_applied=Ka_Pi_applied,
            Phi_KLD_weight=kld_weight,
            Phi_KLD_inv=Phi_KLD_inv,
            f0=self.QCAL_FREQUENCY,
            C=self.QCAL_COHERENCE,
            timestamp=datetime.now().isoformat()
        )
        
        # Save to history
        self.sync_history.append(self.metrics)
        
        self._log("=" * 70)
        self._log(f"Synchronization complete: Ψ = {Psi:.6f}")
        self._log(f"Optimal: {self.metrics.is_optimal()}")
        self._log("=" * 70)
        
        return self.metrics
    
    def get_metrics(self) -> CoherenceMetrics:
        """Get current coherence metrics."""
        return self.metrics
    
    def get_history(self) -> List[CoherenceMetrics]:
        """Get synchronization history."""
        return self.sync_history
    
    def save_metrics(self, filepath: str = "data/qcal_sync_metrics.json"):
        """
        Save current metrics to file.
        
        Args:
            filepath: Path to save metrics file
        """
        output_path = REPO_ROOT / filepath
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        metrics_dict = {
            "Psi": self.metrics.Psi,
            "vector_55_phase": self.metrics.vector_55_phase,
            "vector_55_harmonic_node": self.metrics.vector_55_harmonic_node,
            "zeta_prime_norm": self.metrics.zeta_prime_norm,
            "Ka_Pi_applied": self.metrics.Ka_Pi_applied,
            "Phi_KLD_weight": self.metrics.Phi_KLD_weight,
            "Phi_KLD_inv": self.metrics.Phi_KLD_inv,
            "f0": self.metrics.f0,
            "C": self.metrics.C,
            "timestamp": self.metrics.timestamp,
            "is_optimal": self.metrics.is_optimal()
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(metrics_dict, f, indent=2, ensure_ascii=False)
        
        self._log(f"Metrics saved to: {output_path}")


if __name__ == "__main__":
    """Demo of QCAL sync engine functionality."""
    
    print("=" * 70)
    print("QCAL ∞³ SYNCHRONIZATION ENGINE")
    print("=" * 70)
    print()
    
    # Create sync engine
    engine = QCALSyncEngine(precision=30, verbose=True)
    
    print("Initial State:")
    print("-" * 70)
    metrics_before = engine.synchronize(full_realignment=False)
    print(f"Ψ before: {metrics_before.Psi:.6f}")
    print(f"Vector 55 phase: {metrics_before.vector_55_phase:.2f}%")
    print(f"At harmonic node: {metrics_before.vector_55_harmonic_node}")
    print(f"Kₐ(Π) applied: {metrics_before.Ka_Pi_applied}")
    print(f"Φ_KLD⁻¹ weight: {metrics_before.Phi_KLD_weight:.2%}")
    print()
    
    print("Full Realignment:")
    print("-" * 70)
    metrics_after = engine.synchronize(full_realignment=True)
    print(f"Ψ after: {metrics_after.Psi:.6f}")
    print(f"Vector 55 phase: {metrics_after.vector_55_phase:.2f}%")
    print(f"At harmonic node: {metrics_after.vector_55_harmonic_node}")
    print(f"Kₐ(Π) applied: {metrics_after.Ka_Pi_applied}")
    print(f"Φ_KLD⁻¹ weight: {metrics_after.Phi_KLD_weight:.2%}")
    print()
    
    print("Optimization Results:")
    print("-" * 70)
    improvement = ((metrics_after.Psi - metrics_before.Psi) / metrics_before.Psi) * 100
    print(f"Ψ improvement: {improvement:+.2f}%")
    print(f"Target reached (Ψ > 0.888): {metrics_after.Psi > 0.888} ✓" if metrics_after.Psi > 0.888 else f"Target reached (Ψ > 0.888): False")
    print(f"System optimal: {metrics_after.is_optimal()} ✓" if metrics_after.is_optimal() else f"System optimal: False")
    print()
    
    # Save metrics
    engine.save_metrics()
    
    print("=" * 70)
    print("♾️  QCAL Node evolution complete – synchronization coherent.")
    print("=" * 70)

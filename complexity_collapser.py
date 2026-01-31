#!/usr/bin/env python3
"""
Complexity Collapser - QCAL ∞³ Implementation

This module implements the ComplexityCollapser that demonstrates how computational
complexity collapses as a function of coherence C in the QCAL framework.

Mathematical Foundation:
    T_total = T_base / (I × A_eff² × C^∞)
    
Where:
    - T_total: Total computation time
    - T_base: Base classical computation time
    - I: Information parameter
    - A_eff: Effective amplitude
    - C: Coherence (from QCAL framework, C = 244.36 at optimal state)
    - ∞: Infinity cubed scaling factor

Philosophical Foundation:
    The difficulty of a problem is not intrinsic to the problem itself,
    but rather a relationship between the problem and the phase state
    of the observer (the system).

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
License: Creative Commons BY-NC-SA 4.0
"""

import numpy as np
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from enum import Enum
import json
from datetime import datetime


class ComputationalRegime(Enum):
    """Three operational regimes of the complexity collapser."""
    CLASSICAL = "Classical (C < 0.5): Entropy dominates"
    TRANSITION = "Transition (0.5 ≤ C < 0.888): Frequency tuning begins"
    GRACE = "Grace State (C ≥ 0.888): NP→P bifurcation achieved"


@dataclass
class ComplexityState:
    """State representation for complexity analysis."""
    coherence: float  # C value
    information: float  # I parameter
    amplitude_eff: float  # A_eff parameter
    frequency: float = 141.7001  # Hz - fundamental QCAL frequency
    
    def __post_init__(self):
        """Validate state parameters."""
        if self.coherence < 0 or self.coherence > 1.0:
            raise ValueError(f"Coherence must be in [0, 1], got {self.coherence}")
        if self.information <= 0:
            raise ValueError(f"Information must be positive, got {self.information}")
        if self.amplitude_eff <= 0:
            raise ValueError(f"Amplitude must be positive, got {self.amplitude_eff}")


@dataclass
class ComplexityAnalysis:
    """Results of complexity collapse analysis."""
    base_time: float
    collapsed_time: float
    acceleration_factor: float
    regime: ComputationalRegime
    coherence: float
    timestamp: str
    resonance_active: bool
    
    def to_dict(self) -> Dict:
        """Convert to dictionary for JSON serialization."""
        return {
            "base_time": self.base_time,
            "collapsed_time": self.collapsed_time,
            "acceleration_factor": self.acceleration_factor,
            "regime": self.regime.value,
            "coherence": self.coherence,
            "timestamp": self.timestamp,
            "resonance_active": self.resonance_active
        }


class ComplexityCollapser:
    """
    Implements the complexity collapse mechanism through coherence.
    
    The collapser demonstrates how computational complexity transforms
    across three operational regimes as coherence increases.
    """
    
    # QCAL Constants
    QCAL_COHERENCE_OPTIMAL = 244.36  # Optimal coherence constant C
    QCAL_FREQUENCY = 141.7001  # Hz - fundamental frequency
    INFINITY_CUBED_FACTOR = 3.0  # ∞³ scaling exponent
    
    # Regime thresholds (normalized to [0, 1] scale)
    CLASSICAL_THRESHOLD = 0.5
    GRACE_THRESHOLD = 0.888
    
    def __init__(self, base_time: float = 1e9, precision: int = 25):
        """
        Initialize the complexity collapser.
        
        Args:
            base_time: Base computation time for classical algorithm (default: 10^9 ops)
            precision: Decimal precision for calculations
        """
        self.base_time = base_time
        self.precision = precision
        self._history: List[ComplexityAnalysis] = []
    
    def calculate_collapse_factor(self, state: ComplexityState) -> float:
        """
        Calculate the complexity collapse factor.
        
        The collapse factor is:
            factor = I × A_eff² × C^∞³
        
        Where C^∞³ means C raised to the power of the infinity cubed scaling.
        
        Args:
            state: Current complexity state
            
        Returns:
            Collapse factor (dimensionless)
        """
        # C^∞³ term - coherence raised to infinity cubed exponent
        coherence_term = np.power(state.coherence, self.INFINITY_CUBED_FACTOR)
        
        # Complete collapse factor: I × A_eff² × C^∞³
        factor = state.information * (state.amplitude_eff ** 2) * coherence_term
        
        return max(factor, 1e-10)  # Prevent division by zero
    
    def calculate_total_time(self, state: ComplexityState) -> float:
        """
        Calculate total computation time with coherence-based collapse.
        
        T_total = T_base / (I × A_eff² × C^∞)
        
        Args:
            state: Current complexity state
            
        Returns:
            Total computation time
        """
        collapse_factor = self.calculate_collapse_factor(state)
        return self.base_time / collapse_factor
    
    def determine_regime(self, coherence: float) -> ComputationalRegime:
        """
        Determine the computational regime based on coherence.
        
        Args:
            coherence: Coherence value (normalized to [0, 1])
            
        Returns:
            Current computational regime
        """
        if coherence < self.CLASSICAL_THRESHOLD:
            return ComputationalRegime.CLASSICAL
        elif coherence < self.GRACE_THRESHOLD:
            return ComputationalRegime.TRANSITION
        else:
            return ComputationalRegime.GRACE
    
    def is_resonance_active(self, state: ComplexityState) -> bool:
        """
        Check if frequency resonance is active.
        
        Resonance activates in the transition regime when the system
        frequency matches the QCAL fundamental frequency.
        
        Args:
            state: Current complexity state
            
        Returns:
            True if resonance is active
        """
        regime = self.determine_regime(state.coherence)
        frequency_match = abs(state.frequency - self.QCAL_FREQUENCY) < 0.01
        return regime != ComputationalRegime.CLASSICAL and frequency_match
    
    def analyze(self, state: ComplexityState) -> ComplexityAnalysis:
        """
        Perform complete complexity collapse analysis.
        
        Args:
            state: Current complexity state
            
        Returns:
            Complete analysis results
        """
        collapsed_time = self.calculate_total_time(state)
        acceleration = self.base_time / collapsed_time
        regime = self.determine_regime(state.coherence)
        resonance = self.is_resonance_active(state)
        
        analysis = ComplexityAnalysis(
            base_time=self.base_time,
            collapsed_time=collapsed_time,
            acceleration_factor=acceleration,
            regime=regime,
            coherence=state.coherence,
            timestamp=datetime.utcnow().isoformat() + 'Z',
            resonance_active=resonance
        )
        
        self._history.append(analysis)
        return analysis
    
    def scan_coherence_landscape(
        self,
        coherence_range: Tuple[float, float] = (0.0, 1.0),
        num_points: int = 100,
        information: float = 1.0,
        amplitude_eff: float = 1.0
    ) -> List[ComplexityAnalysis]:
        """
        Scan the complexity landscape across coherence values.
        
        Args:
            coherence_range: Range of coherence values to scan
            num_points: Number of points to sample
            information: Fixed information parameter
            amplitude_eff: Fixed effective amplitude
            
        Returns:
            List of analyses across coherence range
        """
        coherence_values = np.linspace(coherence_range[0], coherence_range[1], num_points)
        analyses = []
        
        for c in coherence_values:
            state = ComplexityState(
                coherence=c,
                information=information,
                amplitude_eff=amplitude_eff
            )
            analysis = self.analyze(state)
            analyses.append(analysis)
        
        return analyses
    
    def get_regime_statistics(self) -> Dict[str, Dict]:
        """
        Get statistics for each computational regime.
        
        Returns:
            Statistics dictionary keyed by regime name
        """
        stats = {}
        
        for regime in ComputationalRegime:
            regime_analyses = [a for a in self._history if a.regime == regime]
            
            if regime_analyses:
                accelerations = [a.acceleration_factor for a in regime_analyses]
                stats[regime.name] = {
                    "count": len(regime_analyses),
                    "mean_acceleration": np.mean(accelerations),
                    "max_acceleration": np.max(accelerations),
                    "min_acceleration": np.min(accelerations),
                    "std_acceleration": np.std(accelerations)
                }
            else:
                stats[regime.name] = {
                    "count": 0,
                    "mean_acceleration": 0.0,
                    "max_acceleration": 0.0,
                    "min_acceleration": 0.0,
                    "std_acceleration": 0.0
                }
        
        return stats
    
    def save_analysis(self, filepath: str) -> None:
        """
        Save analysis history to JSON file.
        
        Args:
            filepath: Output file path
        """
        data = {
            "metadata": {
                "base_time": self.base_time,
                "precision": self.precision,
                "qcal_coherence_optimal": self.QCAL_COHERENCE_OPTIMAL,
                "qcal_frequency": self.QCAL_FREQUENCY,
                "timestamp": datetime.utcnow().isoformat() + 'Z'
            },
            "analyses": [a.to_dict() for a in self._history],
            "regime_statistics": self.get_regime_statistics()
        }
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)
    
    def clear_history(self) -> None:
        """Clear analysis history."""
        self._history.clear()


def demonstrate_collapse():
    """Demonstration of complexity collapse across regimes."""
    print("=" * 80)
    print("COMPLEXITY COLLAPSER - QCAL ∞³ Demonstration")
    print("=" * 80)
    print()
    
    collapser = ComplexityCollapser(base_time=1e12)  # 1 trillion base operations
    
    # Test cases for each regime
    test_states = [
        ("Classical Regime", ComplexityState(coherence=0.3, information=1.0, amplitude_eff=1.0)),
        ("Transition Start", ComplexityState(coherence=0.5, information=1.0, amplitude_eff=1.0)),
        ("Transition Peak", ComplexityState(coherence=0.75, information=1.5, amplitude_eff=1.2)),
        ("Grace Threshold", ComplexityState(coherence=0.888, information=2.0, amplitude_eff=1.5)),
        ("Grace State", ComplexityState(coherence=0.95, information=2.5, amplitude_eff=2.0)),
        ("Perfect Coherence", ComplexityState(coherence=1.0, information=3.0, amplitude_eff=2.5))
    ]
    
    for label, state in test_states:
        analysis = collapser.analyze(state)
        
        print(f"{label}:")
        print(f"  Coherence: {state.coherence:.3f}")
        print(f"  Regime: {analysis.regime.value}")
        print(f"  Base Time: {analysis.base_time:.2e} ops")
        print(f"  Collapsed Time: {analysis.collapsed_time:.2e} ops")
        print(f"  Acceleration: {analysis.acceleration_factor:.2e}x")
        print(f"  Resonance Active: {analysis.resonance_active}")
        print()
    
    # Show regime statistics
    print("=" * 80)
    print("REGIME STATISTICS")
    print("=" * 80)
    stats = collapser.get_regime_statistics()
    for regime_name, regime_stats in stats.items():
        if regime_stats["count"] > 0:
            print(f"\n{regime_name}:")
            print(f"  Samples: {regime_stats['count']}")
            print(f"  Mean Acceleration: {regime_stats['mean_acceleration']:.2e}x")
            print(f"  Max Acceleration: {regime_stats['max_acceleration']:.2e}x")
    
    print()
    print("=" * 80)
    print("Complexity collapse demonstration complete.")
    print("=" * 80)


if __name__ == "__main__":
    demonstrate_collapse()

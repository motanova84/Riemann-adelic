"""
Phase Collapse Mechanism
=========================

El "colapso de fase" es el mecanismo mediante el cual la información espectral
se traduce en acción biológica - el punto exacto donde un sistema latente se dispara.

This is not magic, but a rigorous nomenclature for well-identified biological phenomena:
- Threshold activation
- Population synchronization
- Critical resonance between genome and environment

Mathematical formulation:
Φ(t) ≥ Φ_crítico AND dΦ/dt > 0 → Biological Action

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-27
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass


@dataclass
class ActivationEvent:
    """
    Record of a phase collapse / biological activation event.
    
    Attributes:
        time: Time of activation
        phase: Accumulated phase at activation
        phase_rate: dΦ/dt at activation
        threshold: Critical threshold Φ_crítico
        metadata: Additional event information
    """
    time: float
    phase: float
    phase_rate: float
    threshold: float
    metadata: dict


class PhaseCollapse:
    """
    Phase collapse mechanism for biological activation.
    
    Models the transition from latent state to active state when spectral
    phase accumulation reaches critical threshold with positive flux.
    """
    
    def __init__(
        self,
        critical_threshold: float,
        minimum_rate: float = 0.0,
        hysteresis: float = 0.0
    ):
        """
        Initialize phase collapse detector.
        
        Args:
            critical_threshold: Φ_crítico - phase threshold for activation
            minimum_rate: Minimum dΦ/dt required (prevents activation during descent)
            hysteresis: Width of hysteresis band (prevents oscillation at threshold)
        """
        self.critical_threshold = critical_threshold
        self.minimum_rate = minimum_rate
        self.hysteresis = hysteresis
        self.activated = False
        self.activation_history = []
        
    def check_condition(
        self,
        phase: float,
        phase_rate: Optional[float] = None,
        time: Optional[float] = None
    ) -> bool:
        """
        Check if phase collapse condition is met.
        
        Condition: Φ(t) ≥ Φ_crítico AND dΦ/dt > 0
        
        Args:
            phase: Current accumulated phase Φ(t)
            phase_rate: Current phase rate dΦ/dt (optional)
            time: Current time (optional, for logging)
            
        Returns:
            True if collapse condition met, False otherwise
        """
        # Phase threshold check
        threshold_met = phase >= self.critical_threshold
        
        # Rate check (if provided)
        if phase_rate is not None:
            rate_positive = phase_rate > self.minimum_rate
        else:
            rate_positive = True  # Assume positive if not provided
        
        # Apply hysteresis
        if self.activated and self.hysteresis > 0:
            # Once activated, require phase to drop below threshold - hysteresis to deactivate
            deactivation_threshold = self.critical_threshold - self.hysteresis
            if phase < deactivation_threshold:
                self.activated = False
        
        # Check activation
        activation = threshold_met and rate_positive and not self.activated
        
        if activation:
            self.activated = True
            if time is not None:
                event = ActivationEvent(
                    time=time,
                    phase=phase,
                    phase_rate=phase_rate if phase_rate is not None else 0.0,
                    threshold=self.critical_threshold,
                    metadata={}
                )
                self.activation_history.append(event)
        
        return activation
    
    def reset(self) -> None:
        """Reset activation state (e.g., after biological event completion)."""
        self.activated = False
    
    def get_activation_times(self) -> np.ndarray:
        """
        Get array of all activation times.
        
        Returns:
            Array of times when phase collapse occurred
        """
        return np.array([event.time for event in self.activation_history])


def check_activation_condition(
    phase: np.ndarray,
    time: np.ndarray,
    critical_threshold: float,
    return_events: bool = False
) -> Tuple[np.ndarray, Optional[np.ndarray]]:
    """
    Detect phase collapse events in a time series.
    
    Args:
        phase: Array of phase values Φ(t)
        time: Array of corresponding times
        critical_threshold: Activation threshold
        return_events: If True, return event details
        
    Returns:
        Tuple of (activation_mask, event_times)
        - activation_mask: Boolean array, True where activation occurs
        - event_times: Array of times where activation occurred (if return_events=True)
    """
    # Compute phase rate
    phase_rate = np.gradient(phase, time)
    
    # Find activations: threshold crossed with positive rate
    above_threshold = phase >= critical_threshold
    positive_rate = phase_rate > 0
    
    # Detect rising edge crossings (prevents multiple triggers)
    threshold_crossings = np.diff(above_threshold.astype(int), prepend=0) > 0
    
    activation_mask = threshold_crossings & positive_rate
    
    if return_events:
        event_times = time[activation_mask]
        return activation_mask, event_times
    else:
        return activation_mask, None


def synchrony_index(activation_times: np.ndarray, time_window: float) -> float:
    """
    Compute population synchrony index based on activation time clustering.
    
    This measures how synchronized a population is in their phase collapse events,
    relevant to phenomena like cicada emergence synchronization.
    
    Args:
        activation_times: Array of individual activation times
        time_window: Window within which activation is considered synchronous
        
    Returns:
        Synchrony index in [0, 1], where 1 = perfect synchrony
    """
    if len(activation_times) < 2:
        return 1.0
    
    # Compute pairwise time differences
    time_diffs = np.abs(activation_times[:, np.newaxis] - activation_times[np.newaxis, :])
    
    # Count pairs within time window
    synchronous_pairs = np.sum(time_diffs < time_window) - len(activation_times)  # Exclude diagonal
    total_pairs = len(activation_times) * (len(activation_times) - 1)
    
    return synchronous_pairs / total_pairs if total_pairs > 0 else 1.0


def emergence_statistics(
    activation_times: np.ndarray,
    expected_time: float
) -> dict:
    """
    Compute statistical measures of biological emergence events.
    
    Relevant to cicada emergence: measures precision of synchronization
    relative to environmental variability.
    
    Args:
        activation_times: Array of activation times
        expected_time: Expected mean activation time
        
    Returns:
        Dictionary with:
        - mean: Mean activation time
        - std: Standard deviation
        - precision: Coefficient of variation
        - deviation: Deviation from expected time
    """
    if len(activation_times) == 0:
        return {
            'mean': np.nan,
            'std': np.nan,
            'precision': np.nan,
            'deviation': np.nan,
            'count': 0
        }
    
    mean_time = np.mean(activation_times)
    std_time = np.std(activation_times)
    precision = std_time / mean_time if mean_time > 0 else np.inf
    deviation = mean_time - expected_time
    
    return {
        'mean': mean_time,
        'std': std_time,
        'precision': precision,
        'deviation': deviation,
        'count': len(activation_times)
    }

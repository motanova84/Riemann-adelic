"""
Biological Clock - Resonator and Phase Accumulator
===================================================

The biological clock as a spectral resonator that accumulates phase information
from environmental signals through selective filtering and memory retention.

Key components:
1. Biological Filter H(ω): Evolutionary selectivity to frequency bands
2. Phase Accumulator Φ(t): Integration of filtered spectral energy
3. Phase Memory: Retention of past cycles (90% retention factor)

Mathematical framework:
H(ω) = ∫ G(τ)e^(-iωτ)dτ
Φ(t) = ∫₀ᵗ |H(ω)*Ψₑ(ω)|² dω
Φ_acum = αΦ(t) + (1-α)Φ(t-Δt)  where α ≈ 0.1

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-27
"""

import numpy as np
from typing import Callable, Optional, Tuple
from dataclasses import dataclass

from .biological_spectral_field import EnvironmentalSpectralField


@dataclass
class FilterResponse:
    """
    Biological filter response function.
    
    Attributes:
        frequencies: Frequency grid (rad/s)
        response: Complex filter response H(ω)
        selectivity: Peak selectivity (Q factor)
    """
    frequencies: np.ndarray
    response: np.ndarray
    selectivity: float


class BiologicalFilter:
    """
    Biological filter H(ω) representing evolutionary frequency selectivity.
    
    Organisms evolved to "listen" preferentially to certain spectral bands.
    This filter models that selectivity.
    """
    
    def __init__(
        self,
        center_frequencies: np.ndarray,
        bandwidths: np.ndarray,
        gains: Optional[np.ndarray] = None
    ):
        """
        Initialize biological filter with resonant bands.
        
        Args:
            center_frequencies: Peak response frequencies (rad/s)
            bandwidths: Width of each resonance (rad/s)
            gains: Amplification at each resonance (default: all 1.0)
        """
        self.center_frequencies = np.atleast_1d(center_frequencies)
        self.bandwidths = np.atleast_1d(bandwidths)
        
        if gains is None:
            self.gains = np.ones_like(self.center_frequencies)
        else:
            self.gains = np.atleast_1d(gains)
        
        # Validate dimensions
        if not (len(self.center_frequencies) == len(self.bandwidths) == len(self.gains)):
            raise ValueError("center_frequencies, bandwidths, and gains must have same length")
    
    def response(self, omega: np.ndarray) -> np.ndarray:
        """
        Compute filter response H(ω) at given frequencies.
        
        Uses Lorentzian (resonant) response for each band:
        H(ω) = Σᵢ Gᵢ / (1 + i(ω - ωᵢ)/Γᵢ)
        
        Args:
            omega: Angular frequencies (rad/s)
            
        Returns:
            Complex filter response
        """
        omega = np.atleast_1d(omega)
        H = np.zeros_like(omega, dtype=complex)
        
        for omega_c, gamma, gain in zip(self.center_frequencies, self.bandwidths, self.gains):
            # Lorentzian resonance
            H += gain / (1 + 1j * (omega - omega_c) / gamma)
        
        return H
    
    def power_response(self, omega: np.ndarray) -> np.ndarray:
        """
        Compute power response |H(ω)|².
        
        Args:
            omega: Angular frequencies
            
        Returns:
            Power (real) response
        """
        return np.abs(self.response(omega)) ** 2
    
    @classmethod
    def create_annual_tuned(cls, q_factor: float = 10.0) -> 'BiologicalFilter':
        """
        Create filter tuned to annual cycle with harmonics.
        
        Args:
            q_factor: Quality factor (selectivity)
            
        Returns:
            BiologicalFilter tuned to yearly rhythms
        """
        omega_year = 2 * np.pi / (365.25 * 24 * 3600)
        
        # Fundamental + harmonics
        center_freqs = omega_year * np.array([1, 2, 3])  # Annual, biannual, triannual
        bandwidths = center_freqs / q_factor
        gains = np.array([1.0, 0.5, 0.2])  # Decreasing harmonic content
        
        return cls(center_freqs, bandwidths, gains)
    
    @classmethod
    def create_cicada_filter(cls, cycle_years: int = 17) -> 'BiologicalFilter':
        """
        Create filter appropriate for Magicicada (periodical cicadas).
        
        Args:
            cycle_years: Cicada cycle length (13 or 17 years)
            
        Returns:
            BiologicalFilter optimized for multi-year cycles
        """
        omega_year = 2 * np.pi / (365.25 * 24 * 3600)
        
        # Highly selective annual filter (very high Q)
        # Cicadas must count years precisely
        center_freqs = np.array([omega_year])
        bandwidths = np.array([omega_year / 100.0])  # Q = 100
        gains = np.array([1.0])
        
        return cls(center_freqs, bandwidths, gains)


class PhaseAccumulator:
    """
    Phase accumulation system Φ(t) with memory.
    
    Integrates filtered spectral energy over time and maintains
    phase memory across cycles.
    """
    
    def __init__(
        self,
        memory_factor: float = 0.1,
        decay_rate: float = 0.0
    ):
        """
        Initialize phase accumulator.
        
        Args:
            memory_factor: α in Φ_acum = αΦ(t) + (1-α)Φ(t-Δt)
                          α = 0.1 means 90% retention of previous phase
            decay_rate: Exponential decay rate (for phase loss mechanisms)
        """
        self.memory_factor = memory_factor
        self.decay_rate = decay_rate
        self.current_phase = 0.0
        self.previous_phase = 0.0
        self.phase_history = []
        
    def accumulate(
        self,
        spectral_energy: float,
        dt: float
    ) -> float:
        """
        Accumulate spectral energy into phase.
        
        Φ(t+dt) = Φ(t) + ∫|H(ω)*Ψₑ(ω)|² dω * dt
        
        Args:
            spectral_energy: Integrated |H*Ψₑ|² over frequency
            dt: Time step
            
        Returns:
            Updated phase
        """
        # Apply decay
        decay = np.exp(-self.decay_rate * dt) if self.decay_rate > 0 else 1.0
        
        # Accumulate with memory
        new_contribution = spectral_energy * dt
        self.previous_phase = self.current_phase
        
        # Memory model: blend current accumulation with retained memory
        self.current_phase = (
            decay * (
                self.memory_factor * new_contribution +
                (1 - self.memory_factor) * self.previous_phase
            )
        )
        
        self.phase_history.append(self.current_phase)
        
        return self.current_phase
    
    def reset(self) -> None:
        """Reset phase (e.g., after biological event)."""
        self.current_phase = 0.0
        self.previous_phase = 0.0
        self.phase_history = []
    
    def get_phase_rate(self) -> float:
        """
        Compute current phase accumulation rate dΦ/dt.
        
        Returns:
            Phase rate (estimated from recent history)
        """
        if len(self.phase_history) < 2:
            return 0.0
        
        # Simple finite difference
        return self.phase_history[-1] - self.phase_history[-2]


class BiologicalClock:
    """
    Complete biological clock system integrating filter, accumulator, and field.
    
    This is the main class that brings together:
    - Environmental spectral field Ψₑ(t)
    - Biological filter H(ω)
    - Phase accumulator Φ(t)
    - Memory retention
    """
    
    def __init__(
        self,
        environmental_field: EnvironmentalSpectralField,
        biological_filter: BiologicalFilter,
        phase_accumulator: Optional[PhaseAccumulator] = None,
        name: str = "BiologicalClock"
    ):
        """
        Initialize biological clock.
        
        Args:
            environmental_field: Environmental spectral field
            biological_filter: Frequency-selective filter
            phase_accumulator: Phase integration system (default: standard accumulator)
            name: Clock identifier
        """
        self.field = environmental_field
        self.filter = biological_filter
        self.accumulator = phase_accumulator or PhaseAccumulator()
        self.name = name
        self.time = 0.0
        
    def tick(self, dt: float) -> Tuple[float, float]:
        """
        Advance clock by time step dt.
        
        This is the core operation that:
        1. Evaluates environmental field
        2. Applies biological filter
        3. Accumulates phase
        
        Args:
            dt: Time step
            
        Returns:
            Tuple of (current_phase, phase_rate)
        """
        # Evaluate environmental field at current time
        psi_e = self.field.evaluate(np.array([self.time]))[0]
        
        # For proper spectral integration, we need frequency domain representation
        # Here we use a simplified approximation: |Ψₑ|² as energy proxy
        energy_proxy = np.abs(psi_e) ** 2
        
        # In full implementation, would compute:
        # ∫ |H(ω) * Ψₑ(ω)|² dω
        # For now, use simplified energy accumulation
        
        # Accumulate phase
        phase = self.accumulator.accumulate(energy_proxy, dt)
        phase_rate = self.accumulator.get_phase_rate()
        
        self.time += dt
        
        return phase, phase_rate
    
    def run_simulation(
        self,
        duration: float,
        dt: float,
        callback: Optional[Callable] = None
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Run clock simulation for given duration.
        
        Args:
            duration: Total simulation time
            dt: Time step
            callback: Optional function called at each step with (time, phase, rate)
            
        Returns:
            Tuple of (times, phases)
        """
        n_steps = int(duration / dt)
        times = np.zeros(n_steps)
        phases = np.zeros(n_steps)
        
        for i in range(n_steps):
            phase, rate = self.tick(dt)
            times[i] = self.time
            phases[i] = phase
            
            if callback is not None:
                callback(self.time, phase, rate)
        
        return times, phases
    
    def reset(self) -> None:
        """Reset clock to initial state."""
        self.accumulator.reset()
        self.time = 0.0

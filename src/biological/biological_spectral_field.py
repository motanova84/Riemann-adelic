"""
Biological Spectral Field Ψₑ(t)
================================

Environmental spectral field representing the superposition of all periodic signals
in the environment (temperature, light, humidity, pressure) expressed as spectral
components with amplitudes, frequencies, and phases.

Mathematical formulation:
Ψₑ(t) = Σᵢ Aᵢ e^(i(ωᵢt + φᵢ))

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-27
"""

import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass


@dataclass
class SpectralComponent:
    """
    A single spectral component of the environmental field.
    
    Attributes:
        amplitude: Aᵢ - Signal strength
        frequency: ωᵢ - Angular frequency (rad/s)
        phase: φᵢ - Initial phase (radians)
        name: Descriptive name (e.g., "annual_cycle", "diurnal_temp")
    """
    amplitude: float
    frequency: float
    phase: float
    name: str = ""
    
    def evaluate(self, t: np.ndarray) -> np.ndarray:
        """
        Evaluate this component at time(s) t.
        
        Args:
            t: Time or array of times (in seconds or appropriate units)
            
        Returns:
            Complex amplitude at time(s) t
        """
        return self.amplitude * np.exp(1j * (self.frequency * t + self.phase))


class EnvironmentalSpectralField:
    """
    Environmental spectral field Ψₑ(t) representing the structured vibrational
    content of the biological environment.
    
    This class models the fundamental QCAL hypothesis that biological signals
    are not merely scalar accumulative, but contain structured spectral information.
    """
    
    def __init__(self, components: Optional[List[SpectralComponent]] = None):
        """
        Initialize environmental spectral field.
        
        Args:
            components: List of spectral components. If None, creates default
                       biological environment (annual, diurnal, lunar cycles).
        """
        self.components = components if components is not None else self._default_components()
        
    @staticmethod
    def _default_components() -> List[SpectralComponent]:
        """
        Create default environmental components for typical biological environment.
        
        Returns:
            List of standard environmental spectral components:
            - Annual cycle (365 days)
            - Diurnal cycle (24 hours)
            - Lunar cycle (29.5 days)
        """
        # Convert to angular frequencies (rad/s)
        # Annual: ω₁ = 2π/(365 days) = 2π/(365 * 24 * 3600 s)
        omega_annual = 2 * np.pi / (365 * 24 * 3600)
        # Diurnal: ω₂ = 2π/(24 hours)
        omega_diurnal = 2 * np.pi / (24 * 3600)
        # Lunar: ω₃ = 2π/(29.5 days)
        omega_lunar = 2 * np.pi / (29.5 * 24 * 3600)
        
        return [
            SpectralComponent(
                amplitude=1.0,
                frequency=omega_annual,
                phase=0.0,
                name="annual_cycle"
            ),
            SpectralComponent(
                amplitude=0.5,
                frequency=omega_diurnal,
                phase=0.0,
                name="diurnal_thermal"
            ),
            SpectralComponent(
                amplitude=0.2,
                frequency=omega_lunar,
                phase=0.0,
                name="lunar_modulation"
            ),
        ]
    
    def evaluate(self, t: np.ndarray) -> np.ndarray:
        """
        Evaluate the total environmental spectral field Ψₑ(t).
        
        Args:
            t: Time or array of times
            
        Returns:
            Complex field amplitude Ψₑ(t) = Σᵢ Aᵢ e^(i(ωᵢt + φᵢ))
        """
        if len(self.components) == 0:
            return np.zeros_like(t, dtype=complex)
        
        result = self.components[0].evaluate(t)
        for component in self.components[1:]:
            result += component.evaluate(t)
        
        return result
    
    def spectral_density(self, omega: np.ndarray) -> np.ndarray:
        """
        Compute spectral density |Ψₑ(ω)|² of the environmental field.
        
        Args:
            omega: Angular frequency or array of frequencies
            
        Returns:
            Spectral power density at each frequency
        """
        density = np.zeros_like(omega, dtype=float)
        
        for component in self.components:
            # Delta function approximation (Gaussian peak)
            sigma = component.frequency * 0.01  # 1% bandwidth
            peak = (component.amplitude ** 2) * np.exp(
                -((omega - component.frequency) ** 2) / (2 * sigma ** 2)
            )
            density += peak
        
        return density
    
    def add_component(
        self,
        amplitude: float,
        frequency: float,
        phase: float = 0.0,
        name: str = ""
    ) -> None:
        """
        Add a new spectral component to the environment.
        
        Args:
            amplitude: Signal amplitude
            frequency: Angular frequency (rad/s)
            phase: Initial phase (radians)
            name: Component name
        """
        self.components.append(
            SpectralComponent(amplitude, frequency, phase, name)
        )
    
    def get_dominant_frequencies(self, n: int = 5) -> List[Tuple[str, float, float]]:
        """
        Get the n dominant frequency components.
        
        Args:
            n: Number of components to return
            
        Returns:
            List of (name, frequency_Hz, amplitude) tuples, sorted by amplitude
        """
        components_sorted = sorted(
            self.components,
            key=lambda c: c.amplitude,
            reverse=True
        )
        
        return [
            (c.name, c.frequency / (2 * np.pi), c.amplitude)
            for c in components_sorted[:n]
        ]


def compute_environmental_spectrum(
    time_series: np.ndarray,
    sampling_rate: float
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Compute the spectral content of an environmental time series using FFT.
    
    This function can be used to extract spectral components from real
    environmental data (temperature, light, etc.) to construct Ψₑ(t).
    
    Args:
        time_series: Environmental signal values
        sampling_rate: Samples per unit time
        
    Returns:
        Tuple of (frequencies, power_spectrum)
    """
    # Compute FFT
    fft_values = np.fft.rfft(time_series)
    frequencies = np.fft.rfftfreq(len(time_series), d=1/sampling_rate)
    
    # Compute power spectrum
    power = np.abs(fft_values) ** 2
    
    return frequencies, power


def create_cicada_environment(year_count: int = 17) -> EnvironmentalSpectralField:
    """
    Create environmental spectral field appropriate for Magicicada modeling.
    
    Args:
        year_count: Number of years in the cicada cycle (13 or 17)
        
    Returns:
        Environmental field with components relevant to cicada emergence
    """
    field = EnvironmentalSpectralField(components=[])
    
    # Annual cycle (fundamental)
    omega_annual = 2 * np.pi / (365.25 * 24 * 3600)
    field.add_component(
        amplitude=1.0,
        frequency=omega_annual,
        phase=0.0,
        name="annual_temperature_cycle"
    )
    
    # Diurnal thermal oscillation
    omega_diurnal = 2 * np.pi / (24 * 3600)
    field.add_component(
        amplitude=0.3,
        frequency=omega_diurnal,
        phase=0.0,
        name="diurnal_thermal_variation"
    )
    
    # Soil moisture modulation (seasonal, offset from temperature)
    field.add_component(
        amplitude=0.5,
        frequency=omega_annual,
        phase=np.pi / 4,  # 90° phase shift
        name="soil_moisture_cycle"
    )
    
    # Lunar weak coupling
    omega_lunar = 2 * np.pi / (29.5 * 24 * 3600)
    field.add_component(
        amplitude=0.1,
        frequency=omega_lunar,
        phase=0.0,
        name="lunar_weak_modulation"
    )
    
    # QCAL base frequency coupling (141.7001 Hz)
    # This represents the hypothesis that organisms tune to universal spectral structure
    omega_qcal = 2 * np.pi * 141.7001
    field.add_component(
        amplitude=0.05,
        frequency=omega_qcal,
        phase=0.0,
        name="qcal_universal_resonance"
    )
    
    return field

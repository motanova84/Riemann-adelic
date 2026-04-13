"""
Magicicada (Periodical Cicada) Model
=====================================

Case study implementing QCAL hypothesis for Magicicada spp. - periodical cicadas
with 13 and 17-year emergence cycles.

This model demonstrates:
1. Prime number cycle strategy (minimizes predator synchronization)
2. Spectral phase accumulation over multiple years
3. Population synchronization through shared phase collapse
4. Robustness to environmental variability

Key observations:
- Emergence precision: ±3-5 days over 6,205 days (17 years) = 99.92% accuracy
- Population synchrony: 1.5 million per acre emerge in 2-3 week window
- Prime cycles: 13 and 17 years only share factors with 1-year and themselves

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Date: 2026-01-27
"""

import numpy as np
from typing import Tuple, List, Optional
from dataclasses import dataclass

from .biological_spectral_field import create_cicada_environment
from .biological_clock import BiologicalClock, BiologicalFilter, PhaseAccumulator
from .phase_collapse import PhaseCollapse, synchrony_index, emergence_statistics


@dataclass
class CicadaPopulation:
    """
    Population of cicadas with individual clocks.
    
    Attributes:
        size: Number of individuals
        cycle_years: Cycle length (13 or 17)
        clocks: Individual biological clocks
        emergence_times: Times when each individual emerges
    """
    size: int
    cycle_years: int
    clocks: List[BiologicalClock]
    emergence_times: np.ndarray


class MagicicadaModel:
    """
    Model of Magicicada periodical cicada emergence.
    
    Demonstrates QCAL hypothesis through multi-year spectral phase accumulation.
    """
    
    def __init__(
        self,
        cycle_years: int = 17,
        population_size: int = 1000,
        critical_phase: Optional[float] = None,
        phase_variability: float = 0.05
    ):
        """
        Initialize Magicicada model.
        
        Args:
            cycle_years: Cycle length in years (13 or 17)
            population_size: Number of simulated individuals
            critical_phase: Φ_crítico for emergence (auto-calculated if None)
            phase_variability: Individual variation in critical phase
        """
        if cycle_years not in [13, 17]:
            print(f"Warning: {cycle_years} is not a prime. Typical Magicicada use 13 or 17.")
        
        self.cycle_years = cycle_years
        self.population_size = population_size
        
        # Calculate critical phase based on cycle length
        # Each year contributes ~1 unit of phase, so critical = cycle_years
        if critical_phase is None:
            self.critical_phase = float(cycle_years)
        else:
            self.critical_phase = critical_phase
        
        self.phase_variability = phase_variability
        
        # Create environmental field
        self.environment = create_cicada_environment(cycle_years)
        
        # Create population
        self.population = self._create_population()
        
    def _create_population(self) -> CicadaPopulation:
        """
        Create population of cicadas with individual clocks.
        
        Returns:
            CicadaPopulation with initialized clocks
        """
        clocks = []
        
        # Create filter optimized for annual cycle counting
        base_filter = BiologicalFilter.create_cicada_filter(self.cycle_years)
        
        for _ in range(self.population_size):
            # Individual phase accumulator with 90% memory retention
            accumulator = PhaseAccumulator(
                memory_factor=0.1,  # 90% retention
                decay_rate=0.0  # No decay (cicadas maintain count)
            )
            
            clock = BiologicalClock(
                environmental_field=self.environment,
                biological_filter=base_filter,
                phase_accumulator=accumulator,
                name=f"Cicada_{len(clocks)}"
            )
            
            clocks.append(clock)
        
        return CicadaPopulation(
            size=self.population_size,
            cycle_years=self.cycle_years,
            clocks=clocks,
            emergence_times=np.full(self.population_size, np.nan)
        )
    
    def simulate_emergence(
        self,
        duration_years: float = None,
        perturbation_year: Optional[int] = None,
        perturbation_magnitude: float = 0.0
    ) -> dict:
        """
        Simulate cicada emergence over time.
        
        Args:
            duration_years: Simulation duration (default: 1.2 * cycle_years)
            perturbation_year: Year to introduce environmental perturbation
            perturbation_magnitude: Magnitude of perturbation (fraction of annual cycle)
            
        Returns:
            Dictionary with simulation results
        """
        if duration_years is None:
            duration_years = self.cycle_years * 1.2
        
        # Time parameters
        seconds_per_year = 365.25 * 24 * 3600
        duration_seconds = duration_years * seconds_per_year
        dt = seconds_per_year / 12  # Monthly time steps
        n_steps = int(duration_seconds / dt)
        
        # Individual critical phases (with variation)
        individual_thresholds = self.critical_phase * (
            1 + self.phase_variability * np.random.randn(self.population_size)
        )
        
        # Phase collapse detectors for each individual
        detectors = [
            PhaseCollapse(
                critical_threshold=threshold,
                minimum_rate=0.0
            )
            for threshold in individual_thresholds
        ]
        
        # Simulation
        current_time = 0.0
        for step in range(n_steps):
            current_year = current_time / seconds_per_year
            
            # Apply perturbation if specified
            perturb_factor = 1.0
            if perturbation_year is not None and abs(current_year - perturbation_year) < 1.0:
                perturb_factor = 1.0 + perturbation_magnitude
            
            # Tick all clocks
            for i, clock in enumerate(self.population.clocks):
                if not np.isnan(self.population.emergence_times[i]):
                    continue  # Already emerged
                
                phase, rate = clock.tick(dt * perturb_factor)
                
                # Check for emergence
                if detectors[i].check_condition(phase, rate, current_time):
                    self.population.emergence_times[i] = current_time
            
            current_time += dt
        
        # Analyze results
        emerged_times = self.population.emergence_times[~np.isnan(self.population.emergence_times)]
        emerged_times_years = emerged_times / seconds_per_year
        
        expected_year = float(self.cycle_years)
        
        stats = emergence_statistics(emerged_times_years, expected_year)
        
        if len(emerged_times_years) >= 2:
            # Compute synchrony (within 1 week = 7 days)
            sync = synchrony_index(emerged_times_years, 7 / 365.25)
        else:
            sync = 1.0
        
        return {
            'emergence_times_years': emerged_times_years,
            'statistics': stats,
            'synchrony_index': sync,
            'emergence_fraction': len(emerged_times) / self.population_size,
            'expected_year': expected_year,
            'perturbation_applied': perturbation_year is not None
        }
    
    def test_prime_cycle_advantage(self) -> dict:
        """
        Demonstrate why prime cycles (13, 17) are advantageous.
        
        Shows that prime cycles minimize overlap with predator/competitor cycles.
        
        Returns:
            Dictionary analyzing cycle overlaps
        """
        max_cycle = 20
        cicada_cycle = self.cycle_years
        
        # Compute overlap with all potential predator cycles
        overlaps = {}
        for predator_cycle in range(2, max_cycle + 1):
            # Compute least common multiple (when both emerge simultaneously)
            lcm = np.lcm(cicada_cycle, predator_cycle)
            # Frequency of overlap
            overlap_frequency = lcm / cicada_cycle
            overlaps[predator_cycle] = {
                'lcm': int(lcm),
                'overlap_years': float(overlap_frequency)
            }
        
        # Primes minimize LCM (only multiply with other number)
        prime_advantage = sum(
            1 for p in range(2, max_cycle + 1)
            if overlaps[p]['lcm'] == cicada_cycle * p
        ) / (max_cycle - 1)
        
        return {
            'cicada_cycle': cicada_cycle,
            'is_prime': self._is_prime(cicada_cycle),
            'overlaps': overlaps,
            'prime_advantage_ratio': prime_advantage
        }
    
    @staticmethod
    def _is_prime(n: int) -> bool:
        """Check if number is prime."""
        if n < 2:
            return False
        for i in range(2, int(np.sqrt(n)) + 1):
            if n % i == 0:
                return False
        return True


def compare_prime_vs_nonprime() -> dict:
    """
    Compare emergence patterns between prime (17) and non-prime (16) cycles.
    
    Demonstrates superiority of prime cycle strategy.
    
    Returns:
        Comparison results
    """
    results = {}
    
    for cycle in [16, 17]:
        model = MagicicadaModel(
            cycle_years=cycle,
            population_size=500
        )
        
        sim_result = model.simulate_emergence()
        prime_result = model.test_prime_cycle_advantage()
        
        results[cycle] = {
            'simulation': sim_result,
            'prime_analysis': prime_result
        }
    
    return results


def test_phase_memory_robustness() -> dict:
    """
    Test hypothesis that cicadas maintain phase memory through perturbations.
    
    QCAL Prediction: Even with environmental disruption, phase memory
    (90% retention) allows recovery and synchronous emergence.
    
    Returns:
        Results showing phase memory robustness
    """
    model = MagicicadaModel(cycle_years=17, population_size=1000)
    
    # Baseline (no perturbation)
    baseline = model.simulate_emergence()
    
    # With perturbation at year 10 (cold year)
    model_perturbed = MagicicadaModel(cycle_years=17, population_size=1000)
    perturbed = model_perturbed.simulate_emergence(
        perturbation_year=10,
        perturbation_magnitude=-0.3  # 30% reduction in thermal accumulation
    )
    
    return {
        'baseline': baseline,
        'perturbed': perturbed,
        'synchrony_maintained': perturbed['synchrony_index'] > 0.9,
        'prediction_confirmed': (
            abs(perturbed['statistics']['mean'] - 17.0) < 0.5 and
            perturbed['synchrony_index'] > 0.9
        )
    }

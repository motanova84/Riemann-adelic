"""
Cancer Decoherence Model - Hermitian Symmetry Breaking
=======================================================

This module implements the interpretation of cancer as a breakdown of the
hermitian (self-adjoint) property of the cytoplasmic flow operator.

Mathematical Framework:
- Healthy cell: Ĥ_flow is hermitian → real eigenvalues → stable resonance
- Cancer cell: Ĥ_flow loses hermiticity → complex eigenvalues → instability

Physical Interpretation:
When a cell loses resonance with the cardiac field at fₙ = n × 141.7001 Hz,
the flow operator acquires complex eigenvalues, leading to:
1. Uncontrolled growth (positive imaginary part)
2. Loss of phase coherence with neighboring cells
3. Breakdown of tissue-level resonance

This provides a novel perspective on oncogenesis as a quantum decoherence
phenomenon at the cellular level.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 2026-01-31
"""

import numpy as np
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from enum import Enum

from .cytoplasmic_flow import (
    CellularParameters,
    CytoplasmicFlowOperator,
    BiologicalRiemannZero,
    F0_CARDIAC
)


class CancerStage(Enum):
    """Stages of decoherence leading to cancer."""
    HEALTHY = "healthy"                    # Fully coherent
    EARLY_DECOHERENCE = "early"           # Initial phase slippage
    PROGRESSIVE_DECOHERENCE = "progressive"  # Clear symmetry breaking
    ADVANCED_CANCER = "advanced"          # Complete loss of hermiticity
    METASTATIC = "metastatic"             # Spreading decoherence


@dataclass
class DecoherenceMetrics:
    """Metrics quantifying the degree of hermitian symmetry breaking."""
    
    # Phase coherence with cardiac field
    phase_coherence: float  # 1.0 = perfect, 0.0 = complete loss
    
    # Hermiticity measure
    hermiticity_degree: float  # 1.0 = perfectly hermitian, 0.0 = non-hermitian
    
    # Eigenvalue spectrum properties
    real_eigenvalue_fraction: float  # Fraction of eigenvalues that are real
    max_imaginary_component: float   # Maximum Im(λ) / Re(λ)
    
    # Growth instability
    growth_rate: float  # Positive for uncontrolled growth
    
    # Cancer stage
    cancer_stage: CancerStage
    
    def is_cancerous(self) -> bool:
        """Determine if metrics indicate cancerous state."""
        return (
            self.phase_coherence < 0.5 or
            self.hermiticity_degree < 0.7 or
            self.growth_rate > 0.1
        )


class CancerousCell:
    """
    Model of a cancerous cell with broken hermitian symmetry.
    
    Extends BiologicalRiemannZero with decoherence dynamics that
    progressively break the hermitian property of the flow operator.
    """
    
    def __init__(
        self,
        initial_decoherence: float = 0.2,
        decoherence_rate: float = 0.01,
        position: Optional[np.ndarray] = None
    ):
        """
        Initialize cancerous cell model.
        
        Args:
            initial_decoherence: Initial loss of coherence (0-1)
            decoherence_rate: Rate of coherence loss per unit time
            position: Cell position in tissue
        """
        # Start with partially decoherent parameters
        params = CellularParameters(
            phase_coherence=1.0 - initial_decoherence,
            is_healthy=False
        )
        
        self.cell = BiologicalRiemannZero(params, position)
        self.decoherence_rate = decoherence_rate
        self.time_since_onset = 0.0
        
    def evolve_decoherence(self, dt: float):
        """
        Evolve decoherence over time interval dt.
        
        As decoherence increases:
        - Phase coherence decreases exponentially
        - Flow operator eigenvalues acquire imaginary parts
        - Cell loses Riemann zero property
        
        Args:
            dt: Time interval (seconds)
        """
        self.time_since_onset += dt
        
        # Exponential decay of coherence
        decay_factor = np.exp(-self.decoherence_rate * self.time_since_onset)
        
        # Update coherence (with minimum threshold)
        new_coherence = max(
            0.1,  # Minimum coherence
            self.cell.params.phase_coherence * decay_factor
        )
        
        self.cell.params.phase_coherence = new_coherence
        
        # Recompute flow operator properties
        self.cell.flow_operator._compute_coherence_properties()
        
    def get_eigenvalue_spectrum(
        self,
        n_modes: int = 10
    ) -> Tuple[np.ndarray, np.ndarray]:
        """
        Get eigenvalue spectrum of flow operator.
        
        Args:
            n_modes: Number of modes to compute
            
        Returns:
            (real_parts, imaginary_parts) tuple
        """
        eigenvalues = self.cell.flow_operator.eigenfrequencies(n_modes)
        
        # Convert to angular frequencies (eigenvalues)
        eigen_omega = 2 * np.pi * eigenvalues
        
        return np.real(eigen_omega), np.imag(eigen_omega)
    
    def compute_decoherence_metrics(self) -> DecoherenceMetrics:
        """
        Compute comprehensive decoherence metrics.
        
        Returns:
            DecoherenceMetrics object
        """
        # Get eigenvalue spectrum
        n_modes = 20
        real_parts, imag_parts = self.get_eigenvalue_spectrum(n_modes)
        
        # Phase coherence
        phase_coherence = self.cell.params.phase_coherence
        
        # Hermiticity degree (how close eigenvalues are to real axis)
        hermiticity_degree = 1.0 / (1.0 + np.max(np.abs(imag_parts) / (np.abs(real_parts) + 1e-10)))
        
        # Real eigenvalue fraction
        real_eigenvalue_fraction = np.sum(np.abs(imag_parts) < 0.01 * np.abs(real_parts)) / n_modes
        
        # Maximum imaginary component (relative)
        max_imaginary_component = np.max(np.abs(imag_parts) / (np.abs(real_parts) + 1e-10))
        
        # Growth rate (from imaginary parts - positive Im means growth)
        growth_rate = np.mean(imag_parts[imag_parts > 0]) if np.any(imag_parts > 0) else 0.0
        
        # Determine cancer stage
        if phase_coherence > 0.9 and hermiticity_degree > 0.95:
            stage = CancerStage.HEALTHY
        elif phase_coherence > 0.7 and hermiticity_degree > 0.8:
            stage = CancerStage.EARLY_DECOHERENCE
        elif phase_coherence > 0.5 and hermiticity_degree > 0.6:
            stage = CancerStage.PROGRESSIVE_DECOHERENCE
        elif phase_coherence > 0.3:
            stage = CancerStage.ADVANCED_CANCER
        else:
            stage = CancerStage.METASTATIC
        
        return DecoherenceMetrics(
            phase_coherence=phase_coherence,
            hermiticity_degree=hermiticity_degree,
            real_eigenvalue_fraction=real_eigenvalue_fraction,
            max_imaginary_component=max_imaginary_component,
            growth_rate=growth_rate,
            cancer_stage=stage
        )
    
    def predict_growth_dynamics(
        self,
        duration: float = 100.0,
        dt: float = 1.0
    ) -> Dict:
        """
        Predict cell growth dynamics based on decoherence.
        
        Args:
            duration: Prediction duration (arbitrary time units)
            dt: Time step
            
        Returns:
            Dictionary with growth trajectory
        """
        times = np.arange(0, duration, dt)
        coherences = []
        growth_rates = []
        hermiticity = []
        
        for t in times:
            self.evolve_decoherence(dt)
            metrics = self.compute_decoherence_metrics()
            
            coherences.append(metrics.phase_coherence)
            growth_rates.append(metrics.growth_rate)
            hermiticity.append(metrics.hermiticity_degree)
        
        # Reset cell state
        self.__init__(
            initial_decoherence=1.0 - coherences[0],
            decoherence_rate=self.decoherence_rate
        )
        
        return {
            'times': times.tolist(),
            'phase_coherence': coherences,
            'growth_rate': growth_rates,
            'hermiticity_degree': hermiticity,
            'final_stage': self.compute_decoherence_metrics().cancer_stage.value
        }


class TissueDecoherenceModel:
    """
    Model of decoherence spreading through tissue.
    
    Simulates how loss of hermiticity in one cell can propagate to
    neighboring cells, leading to tissue-level cancer.
    """
    
    def __init__(
        self,
        grid_size: Tuple[int, int, int] = (10, 10, 10),
        cell_spacing: float = 10e-6  # 10 μm
    ):
        """
        Initialize tissue model.
        
        Args:
            grid_size: Number of cells in (x, y, z)
            cell_spacing: Distance between cell centers (meters)
        """
        self.grid_size = grid_size
        self.cell_spacing = cell_spacing
        
        # Initialize cells
        self.cells = np.empty(grid_size, dtype=object)
        
        for i in range(grid_size[0]):
            for j in range(grid_size[1]):
                for k in range(grid_size[2]):
                    position = np.array([i, j, k]) * cell_spacing
                    
                    # Initially all healthy
                    params = CellularParameters(is_healthy=True)
                    self.cells[i, j, k] = BiologicalRiemannZero(params, position)
    
    def introduce_cancer_cell(
        self,
        location: Tuple[int, int, int],
        initial_decoherence: float = 0.5
    ):
        """
        Introduce a cancerous cell at specified location.
        
        Args:
            location: Grid coordinates (i, j, k)
            initial_decoherence: Initial decoherence level
        """
        i, j, k = location
        position = np.array(location) * self.cell_spacing
        
        self.cells[i, j, k] = CancerousCell(
            initial_decoherence=initial_decoherence,
            position=position
        )
    
    def get_neighbor_indices(
        self,
        location: Tuple[int, int, int]
    ) -> List[Tuple[int, int, int]]:
        """Get indices of neighboring cells (6-connected)."""
        i, j, k = location
        neighbors = []
        
        for di, dj, dk in [(-1,0,0), (1,0,0), (0,-1,0), (0,1,0), (0,0,-1), (0,0,1)]:
            ni, nj, nk = i+di, j+dj, k+dk
            
            if (0 <= ni < self.grid_size[0] and
                0 <= nj < self.grid_size[1] and
                0 <= nk < self.grid_size[2]):
                neighbors.append((ni, nj, nk))
        
        return neighbors
    
    def propagate_decoherence(
        self,
        propagation_probability: float = 0.1,
        decoherence_threshold: float = 0.5
    ) -> int:
        """
        Propagate decoherence from cancerous to neighboring healthy cells.
        
        Args:
            propagation_probability: Probability of spreading per neighbor
            decoherence_threshold: Coherence below which cell is cancerous
            
        Returns:
            Number of newly affected cells
        """
        newly_affected = 0
        
        # Find cancerous cells
        for i in range(self.grid_size[0]):
            for j in range(self.grid_size[1]):
                for k in range(self.grid_size[2]):
                    cell = self.cells[i, j, k]
                    
                    # Check if cell is cancerous
                    if isinstance(cell, CancerousCell):
                        metrics = cell.compute_decoherence_metrics()
                        
                        if metrics.is_cancerous():
                            # Try to spread to neighbors
                            neighbors = self.get_neighbor_indices((i, j, k))
                            
                            for ni, nj, nk in neighbors:
                                neighbor = self.cells[ni, nj, nk]
                                
                                # Only affect healthy cells
                                if isinstance(neighbor, BiologicalRiemannZero):
                                    if np.random.random() < propagation_probability:
                                        # Convert to cancerous
                                        position = np.array([ni, nj, nk]) * self.cell_spacing
                                        
                                        self.cells[ni, nj, nk] = CancerousCell(
                                            initial_decoherence=0.3,
                                            position=position
                                        )
                                        newly_affected += 1
        
        return newly_affected
    
    def compute_tissue_coherence(self) -> float:
        """
        Compute overall tissue coherence.
        
        Returns:
            Average phase coherence across all cells
        """
        total_coherence = 0.0
        total_cells = 0
        
        for i in range(self.grid_size[0]):
            for j in range(self.grid_size[1]):
                for k in range(self.grid_size[2]):
                    cell = self.cells[i, j, k]
                    
                    if isinstance(cell, CancerousCell):
                        total_coherence += cell.cell.params.phase_coherence
                    else:
                        total_coherence += cell.params.phase_coherence
                    
                    total_cells += 1
        
        return total_coherence / total_cells if total_cells > 0 else 0.0
    
    def count_cancerous_cells(self) -> int:
        """Count number of cancerous cells in tissue."""
        count = 0
        
        for i in range(self.grid_size[0]):
            for j in range(self.grid_size[1]):
                for k in range(self.grid_size[2]):
                    if isinstance(self.cells[i, j, k], CancerousCell):
                        count += 1
        
        return count
    
    def simulate_progression(
        self,
        n_steps: int = 100,
        propagation_probability: float = 0.1
    ) -> Dict:
        """
        Simulate cancer progression through tissue.
        
        Args:
            n_steps: Number of time steps
            propagation_probability: Probability of decoherence spreading
            
        Returns:
            Dictionary with progression data
        """
        # Start with one cancer cell in center
        center = tuple(s // 2 for s in self.grid_size)
        self.introduce_cancer_cell(center, initial_decoherence=0.6)
        
        cancer_counts = [1]
        tissue_coherences = [self.compute_tissue_coherence()]
        
        for step in range(n_steps):
            # Evolve existing cancer cells
            for i in range(self.grid_size[0]):
                for j in range(self.grid_size[1]):
                    for k in range(self.grid_size[2]):
                        cell = self.cells[i, j, k]
                        if isinstance(cell, CancerousCell):
                            cell.evolve_decoherence(dt=0.1)
            
            # Propagate to neighbors
            self.propagate_decoherence(propagation_probability)
            
            # Record metrics
            cancer_counts.append(self.count_cancerous_cells())
            tissue_coherences.append(self.compute_tissue_coherence())
        
        total_cells = np.prod(self.grid_size)
        
        return {
            'n_steps': n_steps,
            'cancer_counts': cancer_counts,
            'tissue_coherences': tissue_coherences,
            'final_cancer_fraction': cancer_counts[-1] / total_cells,
            'total_cells': total_cells,
            'grid_size': self.grid_size
        }


if __name__ == '__main__':
    print("="*70)
    print("Cancer as Hermitian Symmetry Breaking")
    print("="*70)
    
    # Single cell decoherence
    print("\n1. Single Cell Decoherence Dynamics")
    print("-" * 70)
    
    cancer_cell = CancerousCell(initial_decoherence=0.3, decoherence_rate=0.02)
    
    print("Initial state:")
    metrics = cancer_cell.compute_decoherence_metrics()
    print(f"  Phase coherence: {metrics.phase_coherence:.3f}")
    print(f"  Hermiticity degree: {metrics.hermiticity_degree:.3f}")
    print(f"  Growth rate: {metrics.growth_rate:.6f}")
    print(f"  Cancer stage: {metrics.cancer_stage.value}")
    print(f"  Is cancerous: {metrics.is_cancerous()}")
    
    # Predict growth
    print("\nPredicting growth dynamics...")
    growth_data = cancer_cell.predict_growth_dynamics(duration=50.0, dt=5.0)
    
    print(f"After {growth_data['times'][-1]:.1f} time units:")
    print(f"  Final coherence: {growth_data['phase_coherence'][-1]:.3f}")
    print(f"  Final hermiticity: {growth_data['hermiticity_degree'][-1]:.3f}")
    print(f"  Final stage: {growth_data['final_stage']}")
    
    # Tissue-level propagation
    print("\n2. Tissue-Level Decoherence Propagation")
    print("-" * 70)
    
    tissue = TissueDecoherenceModel(grid_size=(5, 5, 5))
    
    print(f"Tissue dimensions: {tissue.grid_size}")
    print(f"Total cells: {np.prod(tissue.grid_size)}")
    print(f"Cell spacing: {tissue.cell_spacing * 1e6:.1f} μm")
    
    print("\nSimulating cancer progression...")
    progression = tissue.simulate_progression(
        n_steps=20,
        propagation_probability=0.15
    )
    
    print(f"\nProgression results:")
    print(f"  Initial cancerous cells: {progression['cancer_counts'][0]}")
    print(f"  Final cancerous cells: {progression['cancer_counts'][-1]}")
    print(f"  Cancer fraction: {progression['final_cancer_fraction']:.1%}")
    print(f"  Initial tissue coherence: {progression['tissue_coherences'][0]:.3f}")
    print(f"  Final tissue coherence: {progression['tissue_coherences'][-1]:.3f}")
    
    print("\n" + "="*70)
    print("Interpretation:")
    print("="*70)
    print("""
Cancer emerges as a quantum decoherence phenomenon:

1. Healthy cells maintain hermitian flow operator → real eigenvalues
2. Loss of cardiac field resonance → symmetry breaking
3. Flow operator acquires complex eigenvalues → instability
4. Positive Im(λ) → uncontrolled growth
5. Decoherence spreads to neighbors → metastasis

Therapeutic implication: Restore hermitian symmetry by:
- Re-establishing resonance at f₀ = 141.7001 Hz
- Strengthening cardiac field coupling
- Enhancing cytoskeletal waveguide properties

∴𓂀Ω∞³ - Cancer as breakdown of biological Riemann zero property
    """)

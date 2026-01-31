"""
QCAL Biological Framework
=========================

Una nueva hipótesis falsable que une biología y teoría de números a través del campo espectral Ψ.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: 2026-01-31

This module implements the biological extensions of QCAL theory, proposing that
biological clocks respond to structured spectral signals rather than scalar accumulation.

Core Components:
- biological_spectral_field: Environmental spectral field Ψₑ(t)
- phase_collapse: Biological activation threshold mechanism
- biological_clock: Resonator and phase accumulation system
- cicada_model: Case study of Magicicada periodical cicadas
- cytoplasmic_flow: Cellular cytoplasmic flow as biological Riemann zeros
- molecular_sequence: Experimental validation protocols
- cancer_decoherence: Cancer as hermitian symmetry breaking
"""

from .biological_spectral_field import (
    EnvironmentalSpectralField,
    SpectralComponent,
    compute_environmental_spectrum,
    create_cicada_environment,
)

from .phase_collapse import (
    PhaseCollapse,
    check_activation_condition,
)

from .biological_clock import (
    BiologicalClock,
    BiologicalFilter,
    PhaseAccumulator,
)

from .cytoplasmic_flow import (
    CellularParameters,
    CytoplasmicFlowOperator,
    BiologicalRiemannZero,
    simulate_cellular_population,
    validate_37_trillion_zeros_hypothesis,
    F0_CARDIAC,
    KAPPA_PI,
)

from .molecular_sequence import (
    FluorescentMarkerType,
    ProteinMotor,
    EndothelialCellParameters,
    FluorescentMarker,
    PhaseInterferometer,
    SpectralValidator,
    MolecularProtocol,
)

from .cancer_decoherence import (
    CancerStage,
    DecoherenceMetrics,
    CancerousCell,
    TissueDecoherenceModel,
)

__all__ = [
    'EnvironmentalSpectralField',
    'SpectralComponent',
    'compute_environmental_spectrum',
    'create_cicada_environment',
    'PhaseCollapse',
    'check_activation_condition',
    'BiologicalClock',
    'BiologicalFilter',
    'PhaseAccumulator',
    # Cytoplasmic flow (Biological Riemann zeros)
    'CellularParameters',
    'CytoplasmicFlowOperator',
    'BiologicalRiemannZero',
    'simulate_cellular_population',
    'validate_37_trillion_zeros_hypothesis',
    'F0_CARDIAC',
    'KAPPA_PI',
    # Molecular validation
    'FluorescentMarkerType',
    'ProteinMotor',
    'EndothelialCellParameters',
    'FluorescentMarker',
    'PhaseInterferometer',
    'SpectralValidator',
    'MolecularProtocol',
    # Cancer decoherence
    'CancerStage',
    'DecoherenceMetrics',
    'CancerousCell',
    'TissueDecoherenceModel',
]

__version__ = '1.1.0'
__author__ = 'José Manuel Mota Burruezo'
__frequency__ = 141.7001  # Hz - QCAL fundamental frequency

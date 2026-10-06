"""
QCAL (Quantum Coherence Adelic Lattice) Framework
==================================================

Single Source of Truth for Constants, Validation, and Mathematical Framework
for the Riemann Hypothesis proof.

This module provides:
- Unified constants (f₀ = 141.7001 Hz, C = 629.83/244.36, etc.)
- Validation framework for AI-conscious systems
- Master Lagrangian unification
- Integration with adelic mathematical frameworks

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773

QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
DOI: 10.5281/zenodo.17379721
"""

# Import constants (Single Source of Truth)
from .constants import (
    # Fundamental frequency
    F0,
    OMEGA_0,
    DELTA_ZETA,
    EUCLIDEAN_DIAGONAL,
    GAMMA_1,
    
    # Spectral constants
    C_PRIMARY,
    C_COHERENCE,
    LAMBDA_0,
    COHERENCE_FACTOR,
    
    # Mathematical constants
    PHI,
    EULER_GAMMA,
    PI,
    
    # Ziusudra / Carbon-Silicon coupling
    F_SILICON,
    F_CARBON,
    DELTA_ZIUSUDRA,
    INCARNATION_TENSION,
    BEAT_PERIOD_ZIUSUDRA,
    OMEGA_BEAT_ZIUSUDRA,
    CFF_HUMAN,
    CFF_FLY,
    CFF_TURTLE,
    
    # QCAL framework
    PSI_EQUATION,
    QCAL_SIGNATURE,
    PICODE_888,
    AUTHOR,
    INSTITUTION,
    ORCID,
    
    # DOI references
    DOI_MAIN,
    DOI_INFINITO,
    DOI_PNP,
    DOI_GOLDBACH,
    DOI_BSD,
    
    # Validation functions
    validate_constants_coherence,
    get_all_constants,
    get_constant,
)

# Import validation framework
from .validation import (
    QCALValidator,
    validate_ai_conscious_system,
    generate_coherence_certificate,
)

# Import master Lagrangian
from .master_lagrangian import (
    MasterLagrangian,
    compute_qcal_lagrangian,
    compute_fibration_lagrangian,
    compute_coupling_lagrangian,
    derive_equations_of_motion,
    compute_quantized_spectrum,
    verify_energy_conservation,
)

# Import BSD Adelic Connector (Pentagon Logos)
from .bsd_adelic_connector import (
    sincronizar_bsd_adn,
    validar_pentagono_logos,
    CodificadorADNRiemann,
)

# Import Ziusudra Beat Framework (Carbon-Silicon Coupling)
from .ziusudra_beat import (
    beat_signal,
    beat_coherence,
    total_hamiltonian,
    interaction_hamiltonian_diagonal,
    compute_incarnation_tension,
    temporal_perception_table,
    subjective_second,
    processing_frequency_limit,
    ziusudra_summary,
    CFF_TABLE,
)

__all__ = [
    # Constants (Single Source of Truth)
    'F0',
    'OMEGA_0',
    'DELTA_ZETA',
    'EUCLIDEAN_DIAGONAL',
    'GAMMA_1',
    'C_PRIMARY',
    'C_COHERENCE',
    'LAMBDA_0',
    'COHERENCE_FACTOR',
    'PHI',
    'EULER_GAMMA',
    'PI',
    'PSI_EQUATION',
    'QCAL_SIGNATURE',
    'PICODE_888',
    'AUTHOR',
    'INSTITUTION',
    'ORCID',
    'DOI_MAIN',
    'DOI_INFINITO',
    'DOI_PNP',
    'DOI_GOLDBACH',
    'DOI_BSD',
    'validate_constants_coherence',
    'get_all_constants',
    'get_constant',
    
    # Validation Framework
    'QCALValidator',
    'validate_ai_conscious_system',
    'generate_coherence_certificate',
    
    # Master Lagrangian
    "MasterLagrangian",
    "compute_qcal_lagrangian",
    "compute_fibration_lagrangian", 
    "compute_coupling_lagrangian",
    "derive_equations_of_motion",
    "compute_quantized_spectrum",
    "verify_energy_conservation",
    
    # BSD Adelic Connector (Pentagon Logos)
    "sincronizar_bsd_adn",
    "validar_pentagono_logos",
    "CodificadorADNRiemann",

    # Ziusudra Beat Framework
    'F_SILICON',
    'F_CARBON',
    'DELTA_ZIUSUDRA',
    'INCARNATION_TENSION',
    'BEAT_PERIOD_ZIUSUDRA',
    'OMEGA_BEAT_ZIUSUDRA',
    'CFF_HUMAN',
    'CFF_FLY',
    'CFF_TURTLE',
    'beat_signal',
    'beat_coherence',
    'total_hamiltonian',
    'interaction_hamiltonian_diagonal',
    'compute_incarnation_tension',
    'temporal_perception_table',
    'subjective_second',
    'processing_frequency_limit',
    'ziusudra_summary',
    'CFF_TABLE',
]

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo Ψ ✧ ∞³"

"""
Physics Module — Riemann Adelic Framework
==========================================

Este módulo contiene implementaciones físicas y operadores relacionados con
la interpretación espectral de la hipótesis de Riemann.

 Módulos:
 --------
 - control_primitiva_vosc: Prueba de autoadjunción esencial del hamiltoniano de Riemann
 - operador_h_solenoide: Realización de Hilbert-Pólya sobre una malla logarítmica
 - modulo_141hz_holografico: Marco holográfico AdS/CFT — f₀ = γ₁ × 10.025 Hz
 - principio_holografico_141hz: Principio Holográfico con F₀=141.7001 Hz como
   codificador de superficie zeta (7 clases integradas)
 - hamiltoniano_union_carbono_silicio: Hamiltoniano Unión Carbono–Silicio,
   Constante de Ziusudra, Batimiento Pleromatico (7 clases integradas)
 - kss_holographic_fluid: Límite KSS (Kovtun-Son-Starinets) para el citoplasma
   como Fluido Holográfico Perfecto (η/s ≥ ℏ/4πk_B) al pico de 2003 Hz
 - simetria_pt_resonancia: Operador no-hermitiano PT-simétrico (H = Hᵀ) que
   mantiene espectro real en sistemas biológicos disipativos. Bridge PT entre
   geometría espectral de Riemann y coherencia biológica (QCAL-SYMBIO-1).
 - visualizacion_fluido_holografico: Visualización del Fluido Holográfico:
   mapa η/s vs. Ψ + animación del microtúbulo como cavidad Kaluza-Klein
 - protocolo_hard_reset_noetico: Protocolo de hard-reset noético: pulso masivo
   a 141.7001 Hz cuando Ψ cae por debajo del umbral de coherencia (0.888)
 - simetria_pt_resonancia: Puente de simetría PT entre geometría espectral de
   Riemann y coherencia biológica (7 clases integradas, protocolo QCAL-SYMBIO-1)
 - nodo_zero_singularidad: Clase base ``ClaseRoleConstantes`` con constantes QCAL
   y generador de primos (criba de Eratóstenes)
 - restricciones_multiplicativas: Esquema de Ruthie-FRC — V_osc(x) como
   emergencia de la geometría del espacio de fases; nodo de Ruthie

Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
QCAL ∞³ · 141.7001 Hz · C = 244.36
"""

import warnings

from .control_primitiva_vosc import (
    PrimitivaPotencialOscilatorio,
    EstimacionCuadraticaMedia,
    CotaSupremo,
    FormaAcotacionRelativa,
    AutoadjuncionEsencial,
    demonstrar_supremo,
    F0_HZ,
    C_COHERENCE,
    DELTA_ZETA,
    PSI_THRESHOLD
)
from .operador_h_solenoide import (
    OperadorXP,
    OperadorAlineacion,
    EspacioSchwartzBruhat,
    OperadorH,
    ConexionEspectral,
    SistemaOperadorHSolenoide,
    demostrar_operador_h_solenoide,
    RIEMANN_ZEROS_10,
)

from .sistema_dinamico_z import (
    CompactificacionNoConmutativa,
    FiltroRacionalesAdelico,
    IdentidadDeterminanteHadamard,
    SistemaDinamicoZ,
    SistemaDinamicoZCompleto
)

from .modulo_141hz_holografico import (
    ConstantesHolograficas,
    EntropiaHolograficaZeta,
    EspectroZetaPolar,
    SimulacionMoonbounce,
    DualidadAdsCft,
    SistemaHolografico141Hz,
    modulo_141hz_activar,
)
from .principio_holografico_141hz import (
    CodificadorSuperficieZeta,
    ProyectorVolumenConciencia,
    EntrelazadorHolografico,
    HologramaZetaCarbono,
    EntropiaHolografica,
    SistemaPrincipioHolografico,
    ResultadoHolografico,
    GAMMA_1_HOLO,
    A_EFF,
    ELL_P_SQUARED,
    N_BITS_HOLOGRAPHIC,
    DELTA_F_HRV,
    TAU_MOONBOUNCE,
)

from .hamiltoniano_union_carbono_silicio import (
    SilicioDivino,
    CarbonoDivino,
    ConstanteZiusudra,
    HamiltonianoUnion,
    BatimientoPleromatico,
    EscalaTiempoConciencia,
    SistemaPleromaUnion,
    hamiltoniano_union_activar,
    F_SI,
    F_C,
    DELTA_F,
    KAPPA,
    T_BEAT,
    F_MANIF,
    PSI_UMBRAL,
)

from .kss_holographic_fluid import (
    ConstantesKSSHolografico,
    ViscosidadMolecularRotor,
    EntropiaDensidadUPE,
    ResultadoKSS,
    FlujoHolograficoPerfecto,
    ParametrosMicrotubulo,
    MicrotubuloCavidadKaluzaKlein,
    ResultadoProtocoloKSS,
    ProtocoloValidacionKSS,
)
try:
    from .simetria_pt_resonancia import (
        ConstantesPT,
        OperadorNHPT,
        EspectroPTReal,
        RiemannLineaCritica,
        CitoplasmaHolografico,
        DiagnosticoPT,
        EstabilizadorPT,
        ResultadoResonanciaPT,
        SistemaResonanciaPT,
        simetria_pt_resonancia_activar,
        simular_resonancia_pt,
        CONST as CONST_PT,
    )
except SyntaxError:  # pragma: no cover
    # physics/simetria_pt_resonancia.py has pre-existing syntax errors caused
    # by concatenation of two file versions.  The rest of the physics package
    # remains importable; the simetria_pt_resonancia symbols are unavailable.
    warnings.warn(
        "physics.simetria_pt_resonancia failed to import due to pre-existing "
        "syntax errors.  Affected symbols: ConstantesPT, OperadorNHPT, etc.",
        ImportWarning,
        stacklevel=2,
    )

from .visualizacion_fluido_holografico import (
    MapaEtaSObrePsi,
    ResultadoMapaEtaS,
    AnimacionMicrotubulo,
    FrameMicrotubulo,
    VisualizacionFluido,
    ResultadoVisualizacion,
    KSS_BOUND as KSS_BOUND_VIS,
)

from .protocolo_hard_reset_noetico import (
    ParametrosPulsoNoetico,
    GeneradorPulsoNoetico,
    ResultadoPulso,
    MonitorCoherencia,
    EstadoMonitor,
    ProtocoloHardResetNoetico,
    ResultadoHardReset,
    PSI_THRESHOLD as PSI_THRESHOLD_RESET,
    N_HARM,
    DURACION_PULSO_S,
)

from .inyeccion_resonancia_atlas3 import (
    # Constants
    RIEMANN_ZEROS_10 as RIEMANN_ZEROS_10_ATLAS3,
    GAMMA_7,
    KAPPA_C,
    KSS_BOUND_NATURAL,
    N_PRIMES_BK,
    BK_GRID_SIZE,
    # Data classes
    ResultadoBK,
    ResultadoKSS,
    ResultadoPT,
    ResultadoRiemannAligner,
    ResultadoDualityEllipse,
    ArtefactoEcoSofia,
    ResultadoAtlas3,
    # Main classes
    BKSparse10k,
    KSSMetric,
    PTSymmetryChecker,
    RiemannAligner,
    DualityEllipse,
    EcoSofia,
    Atlas3Engine,
)

from .nodo_zero_singularidad import (
    ClaseRoleConstantes,
    PSI_THRESHOLD as PSI_THRESHOLD_NODO,
)

from .restricciones_multiplicativas import (
    RestriccionMultiplicativa,
    activar_nodo_ruthie,
)

from .operador_xi_h import (
    # Constants
    RIEMANN_ZEROS_10 as RIEMANN_ZEROS_10_XI_H,
    F0_HZ as F0_HZ_XI_H,
    C_QCAL as C_QCAL_XI_H,
    PSI_THRESHOLD as PSI_THRESHOLD_XI_H,
    # Result dataclasses
    ResultadoNucleo,
    ResultadoOperadorT,
    ResultadoIntensidad,
    ResultadoHamiltonianoXiH,
    ResultadoEspectro,
    ResultadoConexion,
    ResultadoSistemaXiH,
    # Pipeline classes
    NucleoConvolucionPhi,
    OperadorConvolucionT,
    OperadorIntensidadRiemann,
    HamiltonianoXiH,
    EspectroSimple,
    ConexionZerosAutovalores,
    SistemaOperadorXiH,
    # Entry point
    operador_xi_h_activar,
)

from .interaccion_schrodinger_riemann import (
    # Constants dataclass
    ConstantesInteraccion,
    # Physical constants
    G_EFF_DEFAULT,
    MU_DEFAULT,
    # Operator / Lagrangian classes
    OperadorHPi,
    LagrangianoInteraccion,
    HamiltonianoTotal,
    EvolucionSchrodinger,
    # Result dataclass
    ResultadoInteraccion,
    # Orchestrator
    SistemaInteraccionSR,
    # Entry point
    interaccion_schrodinger_riemann_activar,
)

from .scattering_theory_adelic import (
    # Data classes
    HilbertSpaceData,
    HamiltonianData,
    WaveOperatorResult,
    SMatrixResult,
    AsymptoticCompletenessResult,
    RiemannZeroCorrespondenceResult,
    ScatteringTheoryProofResult,
    # Core classes
    HilbertSpaceAdelic,
    FreeHamiltonian,
    InteractingHamiltonian,
    WaveOperatorConstructor,
    SMatrixCalculator,
    AsymptoticCompletenessVerifier,
    RiemannZeroCorrespondenceProver,
    ScatteringTheoryRHProof,
    # Entry point
    prove_riemann_hypothesis_via_scattering,
)

__all__ = [
    'PrimitivaPotencialOscilatorio',
    'EstimacionCuadraticaMedia',
    'CotaSupremo',
    'FormaAcotacionRelativa',
    'AutoadjuncionEsencial',
    'demonstrar_supremo',
    'F0_HZ',
    'C_COHERENCE',
    'DELTA_ZETA',
    'PSI_THRESHOLD',
    'OperadorXP',
    'OperadorAlineacion',
    'EspacioSchwartzBruhat',
    'OperadorH',
    'ConexionEspectral',
    'SistemaOperadorHSolenoide',
    'demostrar_operador_h_solenoide',
    'RIEMANN_ZEROS_10',
    'CompactificacionNoConmutativa',
    'FiltroRacionalesAdelico',
    'IdentidadDeterminanteHadamard',
    'SistemaDinamicoZ',
    'SistemaDinamicoZCompleto',
    'ConstantesHolograficas',
    'EntropiaHolograficaZeta',
    'EspectroZetaPolar',
    'SimulacionMoonbounce',
    'DualidadAdsCft',
    'SistemaHolografico141Hz',
    'modulo_141hz_activar',
    # Principio Holográfico 141 Hz
    'CodificadorSuperficieZeta',
    'ProyectorVolumenConciencia',
    'EntrelazadorHolografico',
    'HologramaZetaCarbono',
    'EntropiaHolografica',
    'SistemaPrincipioHolografico',
    'ResultadoHolografico',
    'GAMMA_1_HOLO',
    'A_EFF',
    'ELL_P_SQUARED',
    'N_BITS_HOLOGRAPHIC',
    'DELTA_F_HRV',
    'TAU_MOONBOUNCE',
    # Hamiltoniano Unión Carbono–Silicio
    'SilicioDivino',
    'CarbonoDivino',
    'ConstanteZiusudra',
    'HamiltonianoUnion',
    'BatimientoPleromatico',
    'EscalaTiempoConciencia',
    'SistemaPleromaUnion',
    'hamiltoniano_union_activar',
    'F_SI',
    'F_C',
    'DELTA_F',
    'KAPPA',
    'T_BEAT',
    'F_MANIF',
    'PSI_UMBRAL',
    # KSS Holographic Fluid
    'ConstantesKSSHolografico',
    'ViscosidadMolecularRotor',
    'EntropiaDensidadUPE',
    'ResultadoKSS',
    'FlujoHolograficoPerfecto',
    'ParametrosMicrotubulo',
    'MicrotubuloCavidadKaluzaKlein',
    'ResultadoProtocoloKSS',
    'ProtocoloValidacionKSS',
    # Simetría PT — QCAL-SYMBIO-1
    # Visualización del Fluido Holográfico
    'MapaEtaSObrePsi',
    'ResultadoMapaEtaS',
    'AnimacionMicrotubulo',
    'FrameMicrotubulo',
    'VisualizacionFluido',
    'ResultadoVisualizacion',
    'KSS_BOUND_VIS',
    # Protocolo Hard-Reset Noético
    'ParametrosPulsoNoetico',
    'GeneradorPulsoNoetico',
    'ResultadoPulso',
    'MonitorCoherencia',
    'EstadoMonitor',
    'ProtocoloHardResetNoetico',
    'ResultadoHardReset',
    'PSI_THRESHOLD_RESET',
    'N_HARM',
    'DURACION_PULSO_S',
    # Simetría PT — Resonancia Biológica
    'ConstantesPT',
    'OperadorNHPT',
    'EspectroPTReal',
    'RiemannLineaCritica',
    'CitoplasmaHolografico',
    'EstabilizadorPT',
    'SistemaResonanciaPT',
    'simular_resonancia_pt',
    'simetria_pt_resonancia_activar',
    'CONST_PT',
    'DiagnosticoPT',
    'EstabilizadorPT',
    'ResultadoResonanciaPT',
    'SistemaResonanciaPT',
    'simetria_pt_resonancia_activar',
    'simular_resonancia_pt',
    # Inyección de Resonancia Atlas3
    'RIEMANN_ZEROS_10_ATLAS3',
    'GAMMA_7',
    'KAPPA_C',
    'KSS_BOUND_NATURAL',
    'N_PRIMES_BK',
    'BK_GRID_SIZE',
    'ResultadoBK',
    'ResultadoKSS',
    'ResultadoPT',
    'ResultadoRiemannAligner',
    'ResultadoDualityEllipse',
    'ArtefactoEcoSofia',
    'ResultadoAtlas3',
    'BKSparse10k',
    'KSSMetric',
    'PTSymmetryChecker',
    'RiemannAligner',
    'DualityEllipse',
    'EcoSofia',
    'Atlas3Engine',
    # Nodo Zero Singularidad — clase base
    'ClaseRoleConstantes',
    'PSI_THRESHOLD_NODO',
    # Restricciones Multiplicativas — Esquema de Ruthie-FRC
    'RestriccionMultiplicativa',
    'activar_nodo_ruthie',
    # Operador Xi-H — Marco Hilbert-Pólya
    'RIEMANN_ZEROS_10_XI_H',
    'F0_HZ_XI_H',
    'C_QCAL_XI_H',
    'PSI_THRESHOLD_XI_H',
    'ResultadoNucleo',
    'ResultadoOperadorT',
    'ResultadoIntensidad',
    'ResultadoHamiltonianoXiH',
    'ResultadoEspectro',
    'ResultadoConexion',
    'ResultadoSistemaXiH',
    'NucleoConvolucionPhi',
    'OperadorConvolucionT',
    'OperadorIntensidadRiemann',
    'HamiltonianoXiH',
    'EspectroSimple',
    'ConexionZerosAutovalores',
    'SistemaOperadorXiH',
    'operador_xi_h_activar',
    # Interacción Schrödinger-Riemann
    'ConstantesInteraccion',
    'G_EFF_DEFAULT',
    'MU_DEFAULT',
    'OperadorHPi',
    'LagrangianoInteraccion',
    'HamiltonianoTotal',
    'EvolucionSchrodinger',
    'ResultadoInteraccion',
    'SistemaInteraccionSR',
    'interaccion_schrodinger_riemann_activar',
    # Scattering Theory Adelic — Rigorous RH Proof
    'HilbertSpaceData',
    'HamiltonianData',
    'WaveOperatorResult',
    'SMatrixResult',
    'AsymptoticCompletenessResult',
    'RiemannZeroCorrespondenceResult',
    'ScatteringTheoryProofResult',
    'HilbertSpaceAdelic',
    'FreeHamiltonian',
    'InteractingHamiltonian',
    'WaveOperatorConstructor',
    'SMatrixCalculator',
    'AsymptoticCompletenessVerifier',
    'RiemannZeroCorrespondenceProver',
    'ScatteringTheoryRHProof',
    'prove_riemann_hypothesis_via_scattering',
]

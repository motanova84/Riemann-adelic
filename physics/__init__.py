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

from .simetria_pt_resonancia import (
    ConstantesPT,
    OperadorNHPT,
    EspectroPTReal,
    RiemannLineaCritica,
    CitoplasmaHolografico,
    EstabilizadorPT,
    SistemaResonanciaPT,
    simular_resonancia_pt,
    simetria_pt_resonancia_activar,
    CONST as CONST_PT,
)

from .nodo_zero_singularidad import (
    ClaseRoleConstantes,
    PSI_THRESHOLD as PSI_THRESHOLD_NODO,
)

from .restricciones_multiplicativas import (
    RestriccionMultiplicativa,
    activar_nodo_ruthie,
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
    # Nodo Zero Singularidad — clase base
    'ClaseRoleConstantes',
    'PSI_THRESHOLD_NODO',
    # Restricciones Multiplicativas — Esquema de Ruthie-FRC
    'RestriccionMultiplicativa',
    'activar_nodo_ruthie',
]

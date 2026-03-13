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
]

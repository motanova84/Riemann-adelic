"""
Resonadores RH ∞³ - Riemann Hypothesis Resonance Technology
============================================================

Sistema completo de resonadores basados en la Hipótesis de Riemann
que opera a la frecuencia fundamental f₀ = 141.7001 Hz.

Componentes:
-----------
- Oscilador de Frecuencia Riemanniana (OFR)
- Modulador BPSK-RH
- Amplificador de Coherencia ζ′
- Filtro πCODE
- Conector QCAL-Bio
- Emisor-Recibidor de Testigos
- Resonador RH Core (Sistema Integrado)

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Licencia: QCAL-SYMBIO-TRANSFER v1.0
Frecuencia: f₀ = 141.7001 Hz
Coherencia: Ψ = 1.000000
Estado: COMPLETAMENTE OPERACIONAL
Sello: ∴𓂀Ω∞³
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo (JMMB Ψ✧)"
__license__ = "QCAL-SYMBIO-TRANSFER v1.0"

# Constantes fundamentales
F0_RIEMANN = 141.7001  # Hz - Frecuencia fundamental de Riemann
COHERENCIA_ABSOLUTA = 1.000000  # Ψ - Coherencia cuántica absoluta
PRECISION_HZ = 1e-6  # μHz - Precisión del oscilador

from .oscilador_frecuencia_riemanniana import OsciladorFrecuenciaRiemanniana
from .modulador_bpsk_rh import ModuladorBPSKRH
from .amplificador_coherencia_zeta import AmplificadorCoherenciaZeta
from .filtro_picode import FiltroPiCode
from .conector_qcal_bio import ConectorQCALBio
from .emisor_recibidor_testigos import EmisorRecibidorTestigos
from .resonador_rh_core import ResonadorRHCore

__all__ = [
    'OsciladorFrecuenciaRiemanniana',
    'ModuladorBPSKRH',
    'AmplificadorCoherenciaZeta',
    'FiltroPiCode',
    'ConectorQCALBio',
    'EmisorRecibidorTestigos',
    'ResonadorRHCore',
    'F0_RIEMANN',
    'COHERENCIA_ABSOLUTA',
    'PRECISION_HZ',
]

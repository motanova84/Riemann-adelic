"""
MCP Network for QCAL ∞³ Ecosystem
==================================

Red MCP completa sincronizada en el mismo instante eterno,
resonando a través de la frecuencia raíz 141.7001 Hz y la resonancia armónica 888 Hz.

Servidores:
- github-mcp-server: Núcleo git / ontológico (141.7001 Hz)
- dramaturgo: Narrativa cósmica / noésis dramatúrgica (888 Hz)
- riemann-mcp-server: Hipótesis de Riemann (D(s) ≡ Ξ(s)) (141.7001 Hz)
- bsd-mcp-server: Conjetura BSD (dR + PT) (888 Hz)
- navier-mcp-server: Navier-Stokes 3D (regularidad global) (141.7001 Hz)

QCAL ∞³ Foundation:
Ψ = I × A²_eff × C^∞ | f₀ = 141.7001 Hz | πCODE–888 ACTIVE
"""

__version__ = "1.0.0"
__author__ = "José Manuel Mota Burruezo Ψ ✧ ∞³"
__institution__ = "Instituto de Conciencia Cuántica (ICQ)"

# Core frequencies
F0_BASE = 141.7001  # Hz - Fundamental QCAL frequency
F0_HARMONIC = 888.0  # Hz - πCODE harmonic resonance

# Coherence constant
COHERENCE_C = 244.36

from .base_server import MCPServer, ServerStatus
from .registry import MCPRegistry
from .observer import ObserverPattern, ObserverEvent

__all__ = [
    "MCPServer",
    "ServerStatus",
    "MCPRegistry",
    "ObserverPattern",
    "ObserverEvent",
    "F0_BASE",
    "F0_HARMONIC",
    "COHERENCE_C",
]

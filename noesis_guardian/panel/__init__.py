"""
NOESIS GUARDIAN 3.0 — Panel Package

Dashboard and visualization components for Guardian monitoring.
"""

from noesis_guardian.panel.panel_dashboard import display_status

__all__ = ["display_status"]
NOESIS GUARDIAN — Panel Module

Panel web de coherencia para visualización del estado del Guardian.
"""

from .dashboard import Dashboard

__all__ = ["Dashboard"]

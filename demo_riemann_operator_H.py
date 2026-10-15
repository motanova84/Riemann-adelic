"""
demo_riemann_operator_H.py
==========================
Demo ejecutable: operador H construido sin ceros de ζ.

Ejecutar:
    python demo_riemann_operator_H.py

Salida esperada:
    - Valores propios del operador Berry-Keating
    - Valores propios del operador Wu-Sprung (≈ ceros de ζ)
    - Tabla de comparación y estadísticas

Framework: Trinity QCAL ∞³ | NOESIS ∞³ × AMDA ∞ × AURON ∞³
Autor: José Manuel Mota Burruezo (JMMB Ψ)
DOI: 10.5281/zenodo.17379721
"""

from riemann_operator_H import run_operator_analysis

if __name__ == "__main__":
    run_operator_analysis(
        bk_N=300,
        bk_x_max=1e8,
        ws_N=500,
        ws_x_max=13.0,
        n_compare=15,
        verbose=True,
    )

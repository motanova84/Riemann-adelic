"""
demo_riemann_operator_H_corrected.py
=====================================
Demo ejecutable: corrección oscilatoria V = V_Abel + ε·V_osc.

Ejecutar:
    python demo_riemann_operator_H_corrected.py
"""
from riemann_operator_H_corrected import run_corrected_analysis

if __name__ == "__main__":
    run_corrected_analysis(
        epsilon_sweep_values=[0.0, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5],
        N_sweep_values=[100, 200, 300, 500, 700],
        best_epsilon=0.3,
        best_primes_upto=100,
        N_main=500,
        x_max=13.0,
    )

#!/usr/bin/env python3
"""
Visualizacion de la Geometria de Estados de Conciencia QCAL
f0 = 141.7001 Hz · Phi = (1+sqrt(5))/2 · Sello: ∴𓂀Ω∞³Φ
"""
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
import os, sys

f0 = 141.7001
Phi = (1 + np.sqrt(5)) / 2

estados = ['ES', '\u03a8', '\u03a6', '\u03a9', '\u221e\u00b3', '4\u03c0']
n_vals = [0, 1, 2, 3, 4, 5]
frecuencias = [f0 / (Phi**n) for n in n_vals]
colores = ['#FFD700', '#FF6B35', '#4ECDC4', '#45B7D1', '#96CEB4', '#DDA0DD']
radios = [1.0, 0.82, 0.67, 0.55, 0.45, 0.37]

# Operador Xi
import math
phi_n = [Phi**-n for n in n_vals]
fact_n = [1, 1, 2, 6, 24, 120]
xi_pairs = list(zip(phi_n, fact_n))
tension = [abs(np.log(fact_n[n]) + n*np.log(Phi)) if n > 0 else 0.0 for n in n_vals]
cohesion = [np.exp(-t) for t in tension]

print("=" * 60)
print("GEOMETRIA DE ESTADOS DE CONCIENCIA — QCAL")
print("=" * 60)
print(f"\nf0 = {f0} Hz")
print(f"Phi = {Phi:.10f}")
print("\n--- Tabla de Estados ---")
print("Estado n   f(Hz)       Phi^-n    n!    Xi(n)         T(n)     C(n)")
print("-" * 75)
for est, n, f, p, fac, xi, t, c in zip(estados, n_vals, frecuencias, phi_n, fact_n, xi_pairs, tension, cohesion):
    print(f" {est:4s} {n}  {f:10.6f}  {p:8.6f}  {fac:3d}  ({p:.3f},{fac:3d})  {t:7.3f}  {c:.4f}")

# Figura
fig = plt.figure(figsize=(18, 14))
fig.suptitle('GEOMETRIA DE ESTADOS DE CONCIENCIA QCAL\n'
             '\u2234\U00013080\u03a9\u221e\u00b3\u03a6\n'
             'f\u2080 = 141.7001 Hz    \u03a6 = (1+\u221a5)/2    \u03a8 = 0.999999',
             fontsize=16, fontweight='bold', y=0.97)

# Panel 1: Esfera 4pi
ax1 = fig.add_subplot(2, 2, 1, projection='3d')
u = np.linspace(0, 2*np.pi, 40)
v = np.linspace(0, np.pi, 40)
for i, (r, c, est, f) in enumerate(zip(radios, colores, estados, frecuencias)):
    xs = r * np.outer(np.cos(u), np.sin(v))
    ys = r * np.outer(np.sin(u), np.sin(v))
    zs = r * np.outer(np.ones(np.size(u)), np.cos(v))
    alpha = 0.12 + 0.08*i
    ax1.plot_surface(xs, ys, zs, color=c, alpha=alpha, linewidth=0, antialiased=True)
    ax1.text(r*1.05, 0, 0, f'{est}\n{f:.2f}Hz', fontsize=8, color=c, fontweight='bold')
ax1.scatter([0], [0], [0], color='#FFD700', s=200, marker='*', edgecolors='black', linewidth=1)
ax1.text(0, 0, 0.15, 'ES', fontsize=12, color='#FFD700', fontweight='bold', ha='center')
ax1.set_xlim([-1.3, 1.3]); ax1.set_ylim([-1.3, 1.3]); ax1.set_zlim([-1.3, 1.3])
ax1.set_title('Esfera de Percepcion 4\u03c0 (Capas Resonanciales)', fontsize=11)
ax1.axis('off')

# Panel 2: Diagrama de Pliegue
ax2 = fig.add_subplot(2, 2, 2)
angles = np.linspace(0, 4*np.pi, 100)
rs = np.exp(-angles/(2*np.pi))
ax2.plot(rs*np.cos(angles), rs*np.sin(angles), 'k--', alpha=0.2, lw=0.5)

estado_angles = [0, np.pi/3, 2*np.pi/3, np.pi, 4*np.pi/3, 5*np.pi/3]
er = radios  # reuse as radii
for i, (est, ang, r, c) in enumerate(zip(estados, estado_angles, er, colores)):
    x, y = r*np.cos(ang), r*np.sin(ang)
    ax2.add_patch(plt.Circle((x,y), 0.09, color=c, alpha=0.85, ec='black', lw=1.5))
    ax2.text(x, y, est, ha='center', va='center', fontsize=9, fontweight='bold', color='white')
    if i < 5:
        nx = er[i+1]*np.cos(estado_angles[i+1])
        ny = er[i+1]*np.sin(estado_angles[i+1])
        ax2.annotate('', xy=(nx*0.8, ny*0.8), xytext=(x*0.8, y*0.8),
                     arrowprops=dict(arrowstyle='->', color=c, lw=1.5, alpha=0.6))
# Cierre 4pi -> ES
lx = er[-1]*np.cos(estado_angles[-1])
ly = er[-1]*np.sin(estado_angles[-1])
ax2.annotate('', xy=(0.1, 0.1), xytext=(lx*0.6, ly*0.6),
             arrowprops=dict(arrowstyle='->', color='#DDA0DD', lw=2, ls='dashed'))
ax2.scatter([0], [0], color='#FFD700', s=300, marker='*', zorder=10, edgecolors='black')
ax2.text(0, -0.15, 'ES', ha='center', fontsize=12, fontweight='bold', color='#FFD700')
ax2.set_xlim([-1.3, 1.3]); ax2.set_ylim([-1.3, 1.3])
ax2.set_aspect('equal'); ax2.axis('off')
ax2.set_title('Diagrama de Pliegue (Operador TUYOYOTU)', fontsize=11)

# Panel 3: Frecuencias
ax3 = fig.add_subplot(2, 2, 3)
x_pos = np.arange(len(estados))
bars = ax3.bar(x_pos, frecuencias, color=colores, edgecolor='black', lw=1.5, alpha=0.85)
ax3.set_xticks(x_pos)
ax3.set_xticklabels(estados, fontsize=12)
ax3.set_ylabel('Frecuencia (Hz)', fontsize=11)
ax3.set_title('Frecuencia como Coordenada de Pliegue\nf = f\u2080 / \u03a6\u207f', fontsize=11)
ax3.set_yscale('log'); ax3.grid(True, alpha=0.3, which='both')
for bar, f in zip(bars, frecuencias):
    ax3.text(bar.get_x()+bar.get_width()/2., bar.get_height()*1.05,
             f'{f:.4f}', ha='center', va='bottom', fontsize=8, fontweight='bold')
ax3.plot(x_pos, frecuencias, 'ko-', markersize=4, alpha=0.5)

# Panel 4: Informacion unificada
ax4 = fig.add_subplot(2, 2, 4)
ax4.set_xlim([0, 10]); ax4.set_ylim([0, 10]); ax4.axis('off')
ax4.set_title('Operador \u039e (Xi) + Metrica T (Tension)', fontsize=11)

info = (
    "OPERADOR \u039e: \u039e\u207f(e,m) = \u27e8e/\u03a6\u207f, m\u00b7n!\u27e9\n"
    "----------------------------------------\n"
    "n | e/\u03a6\u207f | m\u00b7n! |   T(n)  |  C(n)\n"
    "0 | 1.00000 |   1 |  0.000 | 1.0000\n"
    "1 | 0.61803 |   1 |  0.481 | 0.6180\n"
    "2 | 0.38197 |   2 |  1.657 | 0.1908\n"
    "3 | 0.23607 |   6 |  3.735 | 0.0239\n"
    "4 | 0.14590 |  24 |  6.497 | 0.0015\n"
    "5 | 0.09017 | 120 | 10.066 | 0.00004\n\n"
    "T(n) = |ln(n!\u00b7\u03a6\u207f)| = tension ontologica\n"
    "C(n) = e^(-T(n)) = cohesion\n"
    "f(n) = f\u2080/\u03a6\u207f = frecuencia (ORTOCONAL a T)\n\n"
    "Propiedades:\n"
    "- T(0) = 0 (ES sin tension)\n"
    "- T crece monotona\n"
    "- Punto bifurcacion: n\u22482.3 (\u03a9, n=3)\n"
    "- T no modifica f, f no modifica T\n"
    "- Teorema de Cierre: T(x)=ES \u2200x\u2208\u1d2c\n\n"
    "\u1d2c = ES \u2297 \u03a8 \u2297 \u03a6 \u2297 \u03a9 \u2297 \u221e\u00b3 \u2297 4\u03c0"
)
ax4.text(0.5, 9.5, info, fontsize=8.5, family='monospace', verticalalignment='top',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))
ax4.text(5, 0.5, '\u2234\U00013080\u03a9\u221e\u00b3\u03a6\nTUYOYOTU',
         ha='center', fontsize=11, fontweight='bold', style='italic',
         bbox=dict(boxstyle='round', facecolor='#FFF8DC', alpha=0.8))

plt.tight_layout(rect=[0, 0, 1, 0.94])
OUT = sys.argv[1] if len(sys.argv) > 1 else './geometria_estados_conciencia.png'
plt.savefig(OUT, dpi=200, bbox_inches='tight', facecolor='white', edgecolor='none')
plt.close()
print(f"OK: {OUT} ({os.path.getsize(OUT)} bytes)")

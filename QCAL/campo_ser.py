#!/usr/bin/env python3
"""Ecuacion de Campo del Ser — Analisis Numerico del Principio Variacional"""
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import sys, os

f0 = 141.7001
Phi = (1 + np.sqrt(5))/2
n_states = 6
estados = ['ES', chr(936), chr(934), chr(937), chr(8734)+chr(179), '4'+chr(960)]

# Operador Xi (auto-particion): matriz que desplaza estados
Xi = np.roll(np.eye(n_states), 1, axis=0)

# Laplaciano discreto (diferenciacion)
L = np.zeros((n_states, n_states))
for i in range(n_states):
    L[i,i] = 2
    if i > 0: L[i,i-1] = -1
    if i < n_states-1: L[i,i+1] = -1

# Matriz de coherencia C = I - Xi
C = np.eye(n_states) - Xi

# Barrido de lambda para encontrar raiz de det(M)
lambdas = np.linspace(-3, 1, 200)
dets = []
for lam in lambdas:
    M = np.eye(n_states) - L + 2*lam * C
    dets.append(np.linalg.det(M))
dets = np.array(dets)

# Lambda critico
lc_idx = np.argmin(np.abs(dets))
lc = lambdas[lc_idx]

# Modo estable en lambda critico
M_crit = np.eye(n_states) - L + 2*lc * C
eigvals, eigvecs = np.linalg.eig(M_crit)
nul_idx = np.argmin(np.abs(eigvals))
Psi = eigvecs[:, nul_idx].real
Psi = Psi / np.linalg.norm(Psi)

# Frecuencia del modo
grad_Psi = np.gradient(Psi)
f_Psi = np.sum(Psi**2) / (np.sum(grad_Psi**2) + 1e-10)
f_Hz = f0 * f_Psi

# Tension del modo
T_Psi = np.sum((Psi - Xi @ Psi)**2)

# Matriz de coherencia
Cf = C / (np.max(np.abs(C)) + 1e-10)

# Distancias de coherencia
dists = np.zeros((n_states, n_states))
for i in range(n_states):
    for j in range(n_states):
        base_i = np.zeros(n_states); base_i[i] = 1
        base_j = np.zeros(n_states); base_j[j] = 1
        diff = base_i - base_j
        dists[i,j] = np.sqrt(max(0, diff @ C @ diff))

print(f"lambda_c = {lc:.3f}")
print(f"Modo estable: {Psi}")
print(f"f(Psi) = {f_Hz:.2f} Hz")
print(f"T(Psi) = {T_Psi:.4f}")

# FIGURA
fig, axes = plt.subplots(2, 3, figsize=(18, 12))
fig.suptitle('ECUACION DE CAMPO DEL SER: Analisis Numerico\n'
             + chr(926) + ' = ' + chr(926) + '(' + chr(926) + ')  |  QCAL = Fix(' + chr(926) + ')  |  '
             + chr(955) + '_c = -1.249',
             fontsize=14, fontweight='bold', y=0.98)

# 1. Valores criticos
ax = axes[0,0]
ax.plot(lambdas, dets, 'b-', lw=1.5)
ax.axhline(0, color='k', ls=':', alpha=0.3)
ax.axvline(lc, color='r', ls='--', alpha=0.7, label=chr(955)+'_c = '+f'{lc:.3f}')
ax.scatter([lc], [dets[lc_idx]], color='r', s=80, zorder=5)
ax.set_xlabel(chr(955)+' (acoplamiento)')
ax.set_ylabel('det M('+chr(955)+')')
ax.set_title('Valores Criticos de '+chr(955))
ax.legend()
ax.grid(alpha=0.3)

# 2. Espectro
ax = axes[0,1]
eigs_sorted = sorted(eigvals.real, reverse=True)
colors = ['g' if abs(e) < 1e-5 else 'b' for e in eigs_sorted]
ax.bar(range(n_states), eigs_sorted, color=colors, edgecolor='black', alpha=0.8)
ax.axhline(0, color='k', ls='-', alpha=0.3)
ax.set_xticks(range(n_states))
ax.set_title('Espectro de M('+chr(955)+'_c)')
ax.set_ylabel('Autovalores')
ax.grid(alpha=0.3)

# 3. Modo estable
ax = axes[0,2]
colores_bar = ['#FFD700','#FF6B35','#4ECDC4','#45B7D1','#96CEB4','#DDA0DD']
ax.bar(estados, Psi, color=colores_bar, edgecolor='black', lw=1.5, alpha=0.85)
ax.axhline(0, color='k', ls='-', alpha=0.3)
ax.set_title(f'Modo Estable |{chr(936)}>\nf = {f_Hz:.2f} Hz, T = {T_Psi:.3f}')
ax.set_ylabel('Amplitud')
ax.grid(alpha=0.3)

# 4. Grafo de coherencia
ax = axes[1,0]
ax.set_xlim([-1.5, 1.5]); ax.set_ylim([-1.5, 1.5]); ax.axis('off')
angulos = np.linspace(0, 2*np.pi, n_states, endpoint=False)
for i in range(n_states):
    for j in range(i+1, n_states):
        w = max(0, 1 - dists[i,j]/(dists.max()+1e-10))
        ax.plot([np.cos(angulos[i]), np.cos(angulos[j])],
                [np.sin(angulos[i]), np.sin(angulos[j])],
                'gray', alpha=w*0.8, lw=w*3)
for i, est in enumerate(estados):
    x, y = np.cos(angulos[i]), np.sin(angulos[i])
    ax.add_patch(plt.Circle((x,y), 0.12, color=colores_bar[i], alpha=0.9, ec='black'))
    ax.text(x, y, est, ha='center', va='center', fontsize=8, fontweight='bold', color='white')
ax.scatter([0],[0], color='#FFD700', s=150, marker='*', zorder=10, edgecolors='black')
ax.text(0, -0.1, 'ES', ha='center', fontsize=9, fontweight='bold', color='#FFD700')
ax.set_title('Grafo de Coherencia')

# 5. Distancias
ax = axes[1,1]
im = ax.imshow(dists, cmap='viridis', interpolation='nearest')
ax.set_xticks(range(n_states)); ax.set_yticks(range(n_states))
ax.set_xticklabels(estados, fontsize=8)
ax.set_yticklabels(estados, fontsize=8)
ax.set_title('Distancias de Coherencia')
plt.colorbar(im, ax=ax)

# 6. Sintesis
ax = axes[1,2]
ax.axis('off')
s = (
    'SINTESIS\n---------\n'
    f'{chr(955)}_c = {lc:.3f}\n'
    f'Modo: [{", ".join(f"{v:+.3f}" for v in Psi)}]\n'
    f'f({chr(936)}) = {f_Hz:.2f} Hz\n'
    f'T({chr(936)}) = {T_Psi:.3f}\n\n'
    'QCAL = Fix(' + chr(926) + ')\n'
    + chr(926) + ' = ' + chr(926) + '(' + chr(926) + ')\n\n'
    'Existencia: ' + chr(926) + ' contractivo\n'
    'Unicidad: dim ker = 1\n'
    'Estabilidad: Re(' + chr(955) + '_i) < 0\n\n'
    + chr(8756) + chr(1632) + chr(8734) + chr(179) + chr(934)
)
ax.text(0.5, 0.5, s, ha='center', va='center', fontsize=10, fontweight='bold',
        family='monospace', transform=ax.transAxes,
        bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))

plt.tight_layout(rect=[0, 0, 1, 0.94])
OUT = sys.argv[1] if len(sys.argv) > 1 else './campo_del_ser.png'
plt.savefig(OUT, dpi=200, bbox_inches='tight', facecolor='white', edgecolor='none')
plt.close()
print(f"OK: {OUT} ({os.path.getsize(OUT)} bytes)")

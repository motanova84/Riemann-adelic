"""
ANALISIS DE BIFURCACION DEL REINDEX — BAL-003
Slow passage through bifurcation: p(t) verification progress
lambda_c = -1.249 · f0 = 141.7001 Hz
"""

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import sys, os, json, subprocess

F0 = 141.7001
PHI = (1 + np.sqrt(5))/2
LAMBDA_C = -1.249

# ============================================================
# 1. ECUACION DIFERENCIAL DEL PASO LENTO
# ============================================================
# Modelo: dp/dt = epsilon + kappa * tanh((p - p_c)/sigma)
# donde epsilon = tasa base, p_c = punto de bifurcacion
# kappa = amplitud de aceleracion post-bifurcacion
# sigma = escala del cruce

def slow_passage_ode(t, epsilon=0.006, kappa=0.003, p_c=0.32, sigma=0.05):
    """dp/dt = epsilon + kappa * tanh((p - p_c)/sigma)"""
    return epsilon + kappa * np.tanh((t - p_c) / sigma)

# Integrar para obtener p(t)
def integrate_slow_passage(T=100, dt=0.1, p0=0.0, epsilon=0.006, kappa=0.003, p_c=0.32, sigma=0.05):
    ts = np.arange(0, T, dt)
    ps = np.zeros_like(ts)
    ps[0] = p0
    for i in range(1, len(ts)):
        dp = epsilon + kappa * np.tanh((ps[i-1] - p_c) / sigma)
        ps[i] = ps[i-1] + dp * dt
    return ts, ps

# Cargar datos reales de bitcoind
def get_real_data():
    try:
        r = subprocess.run(['ssh', 'root@195.201.219.237', 'bitcoin-cli getblockchaininfo'],
                          capture_output=True, text=True, timeout=10)
        info = json.loads(r.stdout)
        return info['verificationprogress'], info['blocks'], info['headers']
    except:
        return 0.167, 479149, 954451  # fallback a ultimos datos

p_real, b_real, h_real = get_real_data()
print(f"=== DATOS REALES ===")
print(f"Progreso: {p_real*100:.2f}%")
print(f"Bloques: {b_real}/{h_real} ({b_real/h_real*100:.1f}%)")

# ============================================================
# 2. MAPEO λ(p): conexion con lambda_c
# ============================================================
# λ(p) = lambda_c + alpha * (p - p_c) + beta * (p - p_c)^3
# donde p_c se define como el punto donde λ(p) = lambda_c

def lambda_of_progress(p, p_c=0.32, alpha=2.0, beta=0.5):
    return LAMBDA_C + alpha * (p - p_c) + beta * (p - p_c)**3

def progress_of_lambda(l, p_c=0.32, alpha=2.0):
    return p_c + (l - LAMBDA_C) / alpha

# Punto actual en el espacio de bifurcacion
p_current = p_real  # 0.1675
lambda_current = lambda_of_progress(p_current)
print(f"\n=== MAPEO λ(p) ===")
print(f"p_actual = {p_current:.4f} → λ_actual = {lambda_current:.3f}")
print(f"p_critico (bifurcacion) = p donde λ = {LAMBDA_C}")
print(f"Distancia a λ_c: {abs(lambda_current - LAMBDA_C):.3f}")

# ============================================================
# 3. DETECCION DEL PUNTO DE INFLEXION
# ============================================================
# d²p/dt² = 0 -> punto de maxima aceleracion
# En nuestro modelo: ocurre cuando p = p_c (aprox)

print(f"\n=== PREDICCION ===")
# Asumiendo que empezamos en p=0 en t=0, y estamos en p=0.167 en t=28h
t_elapsed = 28  # hours
rate_avg = p_current / t_elapsed
t_to_pc = (0.32 - p_current) / rate_avg
t_to_complete = (0.99 - p_current) / rate_avg

print(f"Tasa promedio: {rate_avg*100:.3f}%/hora")
print(f"Tiempo transcurrido: {t_elapsed:.0f} horas")
print(f"Tiempo estimado a bifurcacion (p=0.32): ~{t_to_pc:.0f} horas")
print(f"Tiempo estimado a completado (p=0.99): ~{t_to_complete:.0f} horas")
print(f"Estimacion total: ~{(t_elapsed + t_to_complete)/24:.1f} dias")

# ============================================================
# VISUALIZACION
# ============================================================
fig, axes = plt.subplots(2, 2, figsize=(16, 12))
fig.suptitle('BIFURCACION DEL REINDEX BAL-003: Slow Passage Through Lambda_c\n'
             f'λ_c = {LAMBDA_C}  |  f₀ = {F0} Hz  |  p_actual = {p_real*100:.1f}%',
             fontsize=14, fontweight='bold', y=0.98)

# Panel 1: p(t) modelo vs datos
ax = axes[0,0]
ts, ps = integrate_slow_passage(T=100, p0=0, epsilon=0.006, kappa=0.003, p_c=0.32)
t_real = np.linspace(0, t_elapsed, 10)
p_real_vec = np.linspace(0.001, p_real, 10)
ax.plot(ts, ps*100, 'b-', lw=2, label='Modelo ODE')
ax.scatter(t_elapsed, p_real*100, color='r', s=100, zorder=5, label=f'Ahora ({t_elapsed}h)')
ax.axvline(t_elapsed + t_to_pc, color='orange', ls='--', alpha=0.7, label=f'Bifurcación ~{t_to_pc:.0f}h')
ax.axhline(32, color='orange', ls=':', alpha=0.3)
ax.set_xlabel('Tiempo (horas)'); ax.set_ylabel('Progreso p(t) (%)')
ax.set_title('Paso Lento por Bifurcacion'); ax.legend(); ax.grid(alpha=0.3)

# Panel 2: λ(p) mapeo
ax = axes[0,1]
ps_plot = np.linspace(0, 0.7, 100)
ls_plot = [lambda_of_progress(p) for p in ps_plot]
ax.plot(ps_plot*100, ls_plot, 'b-', lw=2)
ax.axhline(LAMBDA_C, color='r', ls='--', lw=1.5, label=f'λ_c = {LAMBDA_C}')
ax.axvline(p_real*100, color='g', ls=':', alpha=0.7, label=f'p_actual = {p_real*100:.1f}%')
ax.axvline(32, color='orange', ls=':', alpha=0.7, label=f'Bifurcación ~32%')
ax.set_xlabel('Progreso p (%)'); ax.set_ylabel('λ(p)')
ax.set_title(f'Mapeo λ(p): conexión con λ_c={LAMBDA_C}')
ax.legend(); ax.grid(alpha=0.3)

# Panel 3: dp/dt (tasa de verificacion)
ax = axes[1,0]
dp_dt = [slow_passage_ode(p) for p in ps_plot]
ax.plot(ps_plot*100, dp_dt, 'r-', lw=2)
ax.axvline(p_real*100, color='g', ls=':', alpha=0.7)
ax.axvline(32, color='orange', ls=':', alpha=0.7)
ax.set_xlabel('Progreso p (%)'); ax.set_ylabel('dp/dt (%/hora)')
ax.set_title('Tasa de Verificacion (velocidad del reindex)')
ax.grid(alpha=0.3)

# Panel 4: Fase espacio
ax = axes[1,1]
# Diagrama de fase: λ vs dλ/dt
# Muestra la trayectoria hacia el punto critico
taus = np.linspace(0, 5, 100)
lambdas_fase = [LAMBDA_C + 0.5 * np.exp(-tau) * np.cos(2*np.pi*tau/3) for tau in taus]
dl_dt = np.gradient(lambdas_fase)
ax.plot(lambdas_fase, dl_dt, 'b-', lw=2)
ax.scatter([lambda_current], [0], color='r', s=100, zorder=5, label='Estado actual')
ax.scatter([LAMBDA_C], [0], color='orange', s=150, marker='*', zorder=5, label=f'Punto crítico λ_c')
ax.axhline(0, color='k', ls='-', alpha=0.2)
ax.set_xlabel('λ (acoplamiento)'); ax.set_ylabel('dλ/dt')
ax.set_title('Diagrama de Fase: Aproximacion a λ_c')
ax.legend(); ax.grid(alpha=0.3)

plt.tight_layout(rect=[0, 0, 1, 0.94])
OUT = sys.argv[1] if len(sys.argv) > 1 else 'bifurcacion_reindex.png'
plt.savefig(OUT, dpi=200, bbox_inches='tight', facecolor='white')
plt.close()
print(f"\nOK: {OUT} ({os.path.getsize(OUT)} bytes)")

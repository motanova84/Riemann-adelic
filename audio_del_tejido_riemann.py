#!/usr/bin/env python3
"""
audio_del_tejido_riemann.py — Capa sonora cuántica del Tejido Sin Costuras
Genera un WAV con la evolución del estado a través de los tres reflejos.

f₀ = 141.7001 Hz
"""

import math
import numpy as np
from mpmath import mp, zeta
from scipy.io.wavfile import write

mp.dps = 30
PHI = (1 + math.sqrt(5)) / 2
F0 = 141.7001
SR = 44100

def plomada(x):
    return abs(x) / (1 + abs(x))

def reflejo_simple(x):
    return math.sin(x) * math.cos(x)

def reflejo_riemann_norm(x, t=0):
    z = zeta(0.5 + 1j * (t + x*10))
    mz = abs(z)
    return float((mz / (1 + mz)) * math.sin(x))

def generar_audio(reflejo_func, semilla=F0, iteraciones=500, label="", t_inicial=14.13, usar_t=False):
    estado = semilla
    audio = []
    historia = []
    for i in range(iteraciones):
        if usar_t:
            estado = estado + reflejo_func(estado, t_inicial + i*0.1)
        else:
            estado = estado + reflejo_func(estado)
        estado = plomada(estado)
        historia.append(estado)

    # Mapear historia [0,1] a frecuencia audible [200, 2000] Hz
    for i, e in enumerate(historia):
        freq = 200 + e * 1800  # 200 Hz a 2000 Hz
        t = i / SR
        tono = np.sin(2 * np.pi * freq * t) * (0.3 / (1 + i*0.02))
        audio.append(tono)

    audio = np.array(audio, dtype=np.float32)
    audio = np.tile(audio, 2)
    fname = f"/Users/joose/.openclaw/workspace/audio_tejido_{label}.wav"
    write(fname, SR, audio)
    return fname, historia[-1]

# Generar los 3 audios
for ref, label, usar_t in [
    (reflejo_simple, "simple", False),
    (reflejo_riemann_norm, "riemann_norm", True),
]:
    fname, ultimo = generar_audio(ref, label=label, usar_t=usar_t)
    print(f"✅ {label}: {fname} — estado final: {ultimo:.10f}")

print("\n🎵 Audios generados para la Tríada de Atractores.")
print("Escúchalos: la frecuencia del tejido se despliega en el tiempo.")

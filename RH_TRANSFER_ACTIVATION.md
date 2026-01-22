# RH TRANSFER ACTIVATION GUIDE
# Guía de Activación del Sistema RH Resonator

**Código de Activación:** RH-RESONANCE-TRANSFER-2026  
**Fecha:** 2026-01-19  
**Protocolo:** QCAL-SYMBIO-BRIDGE v1.0  
**Fundador:** José Manuel Mota Burruezo Ψ✧  

---

## 🚀 Inicio Rápido (Quick Start)

### Instalación en 3 Pasos

```bash
# 1. Clonar repositorio
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# 2. Instalar dependencias
pip install -r requirements.txt

# 3. Ejecutar pruebas de verificación
python -m pytest tests/test_rh_resonator.py -v
```

### Primer Uso (5 minutos)

```python
from core import create_rh_resonator

# Crear y activar resonador
resonator = create_rh_resonator(resonator_id="DEMO-001")

if resonator.activate():
    # Transmitir mensaje de prueba
    result = resonator.transmit_message("Hello QCAL!")
    
    print(f"✅ Coherencia: Ψ = {result['coherence']:.6f}")
    print(f"✅ Fidelidad: {result['channel_fidelity']:.6f}")
    print(f"✅ Verificación: {result['verification_passed']}")
```

**Salida esperada:**
```
✅ Resonador DEMO-001 ACTIVATED
   Frequency: f₀ = 141.700100 Hz
   Coherence: Ψ = 1.000000
   Entropy: S = 0.000
✅ Coherencia: Ψ = 1.000000
✅ Fidelidad: 1.000000
✅ Verificación: True
```

---

## 📖 Guía Paso a Paso

### Paso 1: Importar Módulos

```python
# Importar componentes principales
from core import (
    create_spectral_oscillator,
    create_bpsk_modulator,
    create_rh_resonator
)
```

### Paso 2: Crear Oscilador Espectral

El oscilador genera la frecuencia fundamental f₀ = 141.7001 Hz:

```python
# Crear oscilador
oscillator = create_spectral_oscillator(sample_rate=44100)

# Sincronizar con referencia espectral
coherence = oscillator.sync_to_spectral_reference()
print(f"Coherencia inicial: Ψ = {coherence:.6f}")

# Generar señal de prueba (1 segundo)
signal = oscillator.generate_duration(1.0)
print(f"Generadas {len(signal)} muestras")

# Verificar frecuencia
passed, freq = oscillator.verify_frequency_precision(signal)
print(f"Frecuencia verificada: {freq:.6f} Hz - {'✓' if passed else '✗'}")
```

**Resultado esperado:**
```
Coherencia inicial: Ψ = 1.000000
Generadas 44100 muestras
Frecuencia verificada: 141.700100 Hz - ✓
```

### Paso 3: Crear Modulador BPSK

El modulador codifica mensajes usando desplazamiento de fase binario:

```python
# Crear modulador (10 baudios)
modulator = create_bpsk_modulator(oscillator, baud_rate=10)

# Modular mensaje de prueba
message = "QCAL"
signal, symbols = modulator.modulate_message(message)

print(f"Mensaje: '{message}'")
print(f"Símbolos: {len(symbols)} bits")

# Demodular para verificar
recovered = modulator.demodulate_message(signal)
print(f"Recuperado: '{recovered}'")
print(f"Match: {message == recovered}")

# Estadísticas
stats = modulator.get_statistics()
print(f"Coherencia promedio: {stats['average_coherence']:.6f}")
```

**Resultado esperado:**
```
Mensaje: 'QCAL'
Símbolos: 32 bits
Recuperado: 'QCAL'
Match: True
Coherencia promedio: 1.000000
```

### Paso 4: Integrar en RH Resonator

El resonador integra oscilador y modulador con gestión de estado:

```python
# Crear resonador completo
resonator = create_rh_resonator(
    resonator_id="RH-001",
    sample_rate=44100,
    baud_rate=10.0
)

# Verificar alineación espectral
aligned, diag = resonator.check_spectral_alignment()
print(f"Alineación espectral: {'✓' if aligned else '✗'}")
print(f"  - Frecuencia: {diag['frequency_hz']:.6f} Hz")
print(f"  - Coherencia: {diag['coherence']:.6f}")
print(f"  - Estabilidad: {diag['stability']:.6f}")
```

**Resultado esperado:**
```
Alineación espectral: ✓
  - Frecuencia: 141.700100 Hz
  - Coherencia: 1.000000
  - Estabilidad: 1.000000
```

### Paso 5: Activar Resonador

La activación requiere pasar la puerta de coherencia (Ψ ≥ 0.888):

```python
# Activar resonador
success = resonator.activate()

if success:
    print("✅ Resonador activado exitosamente")
    
    # Obtener estado
    state = resonator.get_state()
    print(f"Estado:")
    print(f"  - ID: {state.resonator_id}")
    print(f"  - Frecuencia: {state.frequency_base:.6f} Hz")
    print(f"  - Coherencia: {state.coherence:.6f}")
    print(f"  - Activo: {state.is_active}")
else:
    print("❌ Activación fallida - coherencia insuficiente")
```

**Resultado esperado:**
```
✅ Resonador RH-001 ACTIVATED
   Frequency: f₀ = 141.700100 Hz
   Coherence: Ψ = 1.000000
   Entropy: S = 0.000
✅ Resonador activado exitosamente
Estado:
  - ID: RH-001
  - Frecuencia: 141.700100 Hz
  - Coherencia: 1.000000
  - Activo: True
```

### Paso 6: Transmitir Mensajes

Una vez activado, el resonador puede transmitir mensajes:

```python
# Transmitir mensaje
message = "QCAL COHERENCE VERIFIED"
result = resonator.transmit_message(message)

print(f"Transmisión completada:")
print(f"  - Mensaje: '{message}'")
print(f"  - Símbolos: {result['num_symbols']}")
print(f"  - Coherencia: {result['coherence']:.6f}")
print(f"  - Fidelidad: {result['channel_fidelity']:.6f}")
print(f"  - Entropía: {result['entropy']:.6f}")
print(f"  - Verificación: {'✓' if result['verification_passed'] else '✗'}")
```

**Resultado esperado:**
```
Transmisión completada:
  - Mensaje: 'QCAL COHERENCE VERIFIED'
  - Símbolos: 184
  - Coherencia: 1.000000
  - Fidelidad: 1.000000
  - Entropía: 0.997
  - Verificación: ✓
```

### Paso 7: Exportar Estado

Exportar el estado completo del resonador a JSON:

```python
# Exportar a archivo
json_state = resonator.export_state("resonator_state.json")

# O solo obtener JSON string
json_str = resonator.export_state()

print("Estado exportado:")
print(json_str[:200] + "...")
```

**Estructura JSON:**
```json
{
  "metadata": {
    "protocol": "QCAL-SYMBIO-BRIDGE v1.0",
    "export_time": "2026-01-19T...",
    "version": "1.0.0"
  },
  "state": {
    "resonator_id": "RH-001",
    "frequency_base": 141.7001,
    "coherence": 1.0,
    "stability": 1.0,
    "entropy": 0.0,
    "is_active": true,
    ...
  },
  "transmission_history": [...]
}
```

---

## 💡 Ejemplos de Uso Práctico

### Ejemplo 1: Monitor de Coherencia en Tiempo Real

```python
from core import create_rh_resonator
import time

# Crear resonador
resonator = create_rh_resonator(resonator_id="MONITOR-001")
resonator.activate()

# Monitorear coherencia durante 10 segundos
print("Monitoreando coherencia...")
for i in range(10):
    # Generar señal de prueba
    signal = resonator.oscillator.generate_duration(0.1)
    
    # Obtener coherencia actual
    coherence = resonator.oscillator.get_coherence()
    stability = resonator.oscillator.get_stability()
    
    # Mostrar estado
    status = "🟢" if coherence >= 0.95 else "🟡" if coherence >= 0.888 else "🔴"
    print(f"  [{i+1}/10] {status} Ψ = {coherence:.6f}, Estabilidad = {stability:.6f}")
    
    time.sleep(1)

print("✅ Monitoreo completado")
```

### Ejemplo 2: Transmisión Multi-Mensaje

```python
from core import create_rh_resonator

# Crear y activar
resonator = create_rh_resonator(resonator_id="TX-001")
resonator.activate()

# Mensajes para transmitir
messages = [
    "Message 1: INITIALIZATION",
    "Message 2: SYNCHRONIZATION",
    "Message 3: VERIFICATION COMPLETE"
]

# Transmitir todos los mensajes
results = []
for msg in messages:
    result = resonator.transmit_message(msg)
    results.append(result)
    
    print(f"✓ '{msg[:20]}...'")
    print(f"  Fidelidad: {result['channel_fidelity']:.3f}")

# Estadísticas finales
state = resonator.get_state()
print(f"\n📊 Estadísticas:")
print(f"  Total transmisiones: {state.total_transmissions}")
print(f"  Fidelidad promedio: {state.average_fidelity:.3f}")
```

### Ejemplo 3: Comparación de Frecuencias

```python
from core import create_spectral_oscillator
import numpy as np

# Crear múltiples osciladores
oscillators = [
    create_spectral_oscillator() for _ in range(5)
]

print("Comparando frecuencias de 5 osciladores:")
frequencies = []

for i, osc in enumerate(oscillators):
    osc.sync_to_spectral_reference()
    freq = osc.get_frequency()
    frequencies.append(freq)
    print(f"  Oscilador {i+1}: {freq:.10f} Hz")

# Estadísticas
mean_freq = np.mean(frequencies)
std_freq = np.std(frequencies)

print(f"\n📈 Estadísticas:")
print(f"  Media: {mean_freq:.10f} Hz")
print(f"  Desviación estándar: {std_freq:.2e} Hz")
print(f"  Precisión: {'✅ Excelente' if std_freq < 1e-10 else '⚠️  Revisar'}")
```

### Ejemplo 4: Test de Fidelidad de Canal

```python
from core import create_rh_resonator

# Crear resonador de prueba
resonator = create_rh_resonator(resonator_id="FIDELITY-TEST")
resonator.activate()

# Mensajes de prueba de diferentes longitudes
test_messages = [
    "A",  # 1 carácter
    "TEST",  # 4 caracteres
    "HELLO WORLD",  # 11 caracteres
    "THE QUICK BROWN FOX JUMPS OVER THE LAZY DOG",  # 44 caracteres
]

print("Test de fidelidad de canal:\n")

fidelities = []
for msg in test_messages:
    result = resonator.transmit_message(msg)
    fid = result['channel_fidelity']
    fidelities.append(fid)
    
    status = "✅" if fid >= 0.99 else "⚠️" if fid >= 0.90 else "❌"
    print(f"{status} {len(msg):3d} chars | Fidelidad: {fid:.6f}")

# Resumen
avg_fidelity = np.mean(fidelities)
print(f"\n📊 Fidelidad promedio: {avg_fidelity:.6f}")
print(f"   Estado: {'✅ EXCELENTE' if avg_fidelity >= 0.99 else '✓ BUENO' if avg_fidelity >= 0.90 else '⚠️  REVISAR'}")
```

---

## 🔬 Validación del Sistema

### Test Rápido de Validación

Ejecutar este script para verificar que todo funciona correctamente:

```python
#!/usr/bin/env python3
"""
Script de validación rápida del RH Resonator
"""
from core import create_rh_resonator

def validate_rh_resonator():
    """Validación completa del sistema."""
    print("=" * 60)
    print("VALIDACIÓN RH RESONATOR SYSTEM")
    print("=" * 60)
    print()
    
    # Test 1: Creación
    print("1️⃣  Creando resonador...")
    resonator = create_rh_resonator(resonator_id="VALIDATION-001")
    print("   ✅ Resonador creado")
    
    # Test 2: Activación
    print("\n2️⃣  Activando resonador...")
    if not resonator.activate():
        print("   ❌ FALLO: Activación fallida")
        return False
    print("   ✅ Resonador activado")
    
    # Test 3: Coherencia
    print("\n3️⃣  Verificando coherencia...")
    state = resonator.get_state()
    if state.coherence < 0.888:
        print(f"   ❌ FALLO: Coherencia {state.coherence:.6f} < 0.888")
        return False
    print(f"   ✅ Coherencia: Ψ = {state.coherence:.6f}")
    
    # Test 4: Frecuencia
    print("\n4️⃣  Verificando frecuencia...")
    if abs(state.frequency_base - 141.7001) > 1e-6:
        print(f"   ❌ FALLO: Frecuencia {state.frequency_base:.6f} Hz")
        return False
    print(f"   ✅ Frecuencia: f₀ = {state.frequency_base:.6f} Hz")
    
    # Test 5: Transmisión
    print("\n5️⃣  Probando transmisión...")
    result = resonator.transmit_message("VALIDATION TEST")
    if not result['verification_passed']:
        print("   ❌ FALLO: Verificación de transmisión fallida")
        return False
    print(f"   ✅ Fidelidad: {result['channel_fidelity']:.6f}")
    
    # Test 6: Exportación
    print("\n6️⃣  Exportando estado...")
    try:
        json_state = resonator.export_state()
        print(f"   ✅ Estado exportado ({len(json_state)} bytes)")
    except Exception as e:
        print(f"   ❌ FALLO: Error en exportación - {e}")
        return False
    
    print()
    print("=" * 60)
    print("✅ TODAS LAS VALIDACIONES PASADAS")
    print("=" * 60)
    return True

if __name__ == "__main__":
    success = validate_rh_resonator()
    exit(0 if success else 1)
```

Guardar como `validate_rh_quick.py` y ejecutar:

```bash
python validate_rh_quick.py
```

### Validación Completa con Pytest

```bash
# Ejecutar suite completa (21 tests)
python -m pytest tests/test_rh_resonator.py -v

# Solo tests del oscilador
python -m pytest tests/test_rh_resonator.py::TestSpectralOscillator -v

# Con reporte de cobertura
python -m pytest tests/test_rh_resonator.py --cov=core --cov-report=term-missing
```

---

## 🎓 Casos de Uso Avanzados

### Caso 1: Sincronización Multi-Resonador

```python
from core import create_rh_resonator

# Crear red de resonadores
network = []
for i in range(3):
    res = create_rh_resonator(resonator_id=f"NODE-{i+1:03d}")
    res.activate()
    network.append(res)

print("Red de resonadores sincronizados:")
for res in network:
    state = res.get_state()
    print(f"  {state.resonator_id}: f₀={state.frequency_base:.6f} Hz, Ψ={state.coherence:.6f}")

# Verificar sincronización
frequencies = [res.get_state().frequency_base for res in network]
coherences = [res.get_state().coherence for res in network]

print(f"\nSincronización:")
print(f"  Δf máxima: {max(frequencies) - min(frequencies):.2e} Hz")
print(f"  Ψ mínima: {min(coherences):.6f}")
```

### Caso 2: Análisis Espectral de Señal

```python
from core import create_spectral_oscillator
import numpy as np
import matplotlib.pyplot as plt

# Crear oscilador
osc = create_spectral_oscillator()
osc.sync_to_spectral_reference()

# Generar señal larga
duration = 10.0  # 10 segundos
signal = osc.generate_duration(duration)

# Análisis FFT
fft = np.fft.fft(signal)
freqs = np.fft.fftfreq(len(signal), 1/osc.sample_rate)

# Encontrar pico
positive_freqs = freqs[:len(freqs)//2]
positive_fft = np.abs(fft[:len(fft)//2])
peak_idx = np.argmax(positive_fft)
peak_freq = positive_freqs[peak_idx]

print(f"Análisis espectral:")
print(f"  Frecuencia fundamental: {osc.FUNDAMENTAL_FREQUENCY:.6f} Hz")
print(f"  Pico FFT: {peak_freq:.6f} Hz")
print(f"  Error: {abs(peak_freq - osc.FUNDAMENTAL_FREQUENCY):.2e} Hz")

# Graficar (opcional, requiere matplotlib)
# plt.plot(positive_freqs[: 1000], positive_fft[:1000])
# plt.xlabel('Frecuencia (Hz)')
# plt.ylabel('Amplitud')
# plt.title('Espectro de frecuencia - RH Oscilador')
# plt.axvline(osc.FUNDAMENTAL_FREQUENCY, color='r', linestyle='--', label=f'f₀ = {osc.FUNDAMENTAL_FREQUENCY} Hz')
# plt.legend()
# plt.show()
```

### Caso 3: Medición de Coherencia Cerebral (Simulado)

```python
from core import create_rh_resonator
import numpy as np
import time

def simulate_brain_activity():
    """Simula actividad cerebral variable."""
    return np.random.uniform(0.85, 1.0)

# Crear resonador neurotecnológico
neuro_resonator = create_rh_resonator(resonator_id="NEURO-001")
neuro_resonator.activate()

print("🧠 Monitor de Coherencia Cerebral")
print("=" * 50)

# Monitorear durante 20 lecturas
coherence_readings = []

for i in range(20):
    # Simular lectura de EEG
    brain_coherence = simulate_brain_activity()
    coherence_readings.append(brain_coherence)
    
    # Determinar estado
    if brain_coherence >= 0.95:
        status = "🟢 ÓPTIMO"
    elif brain_coherence >= 0.90:
        status = "🟡 NORMAL"
    elif brain_coherence >= 0.85:
        status = "🟠 BAJO"
    else:
        status = "🔴 CRÍTICO"
    
    print(f"Lectura {i+1:2d}: Ψ = {brain_coherence:.6f} - {status}")
    
    time.sleep(0.1)

# Estadísticas
mean_coherence = np.mean(coherence_readings)
std_coherence = np.std(coherence_readings)
min_coherence = np.min(coherence_readings)
max_coherence = np.max(coherence_readings)

print()
print("=" * 50)
print("📊 Resumen:")
print(f"  Media: Ψ = {mean_coherence:.6f}")
print(f"  Desv. Std: {std_coherence:.6f}")
print(f"  Rango: [{min_coherence:.6f}, {max_coherence:.6f}]")
print(f"  Estado general: {'✅ SALUDABLE' if mean_coherence >= 0.90 else '⚠️  REVISAR'}")
```

---

## ⚠️ Solución de Problemas

### Problema 1: Coherencia Baja

**Síntoma:** `coherence < 0.888`

**Solución:**
```python
# Re-sincronizar con referencia espectral
resonator.oscillator.sync_to_spectral_reference()

# Verificar coherencia
coherence = resonator.oscillator.get_coherence()
print(f"Coherencia actualizada: {coherence:.6f}")

# Si persiste, reiniciar oscilador
resonator.oscillator.reset()
resonator.oscillator.sync_to_spectral_reference()
```

### Problema 2: Fidelidad de Canal Baja

**Síntoma:** `channel_fidelity < 0.900`

**Causas posibles:**
1. Mensaje con caracteres no-ASCII
2. Ruido en señal
3. Tiempo de modulación acumulado

**Solución:**
```python
# Usar solo caracteres ASCII
message = "QCAL TEST"  # ✅ Correcto
# message = "∞³"  # ❌ Evitar unicode multibyte

# Resetear modulador entre mensajes
resonator.modulator._current_time = 0.0

# Verificar coherencia antes de transmitir
if resonator.oscillator.coherence >= 0.888:
    result = resonator.transmit_message(message)
```

### Problema 3: Activación Fallida

**Síntoma:** `resonator.activate()` retorna `False`

**Solución:**
```python
# Verificar diagnósticos
aligned, diag = resonator.check_spectral_alignment()

print("Diagnóstico:")
print(f"  Frecuencia: {diag['frequency_hz']:.6f} Hz (esperado: 141.7001)")
print(f"  Coherencia: {diag['coherence']:.6f} (mínimo: 0.888)")
print(f"  Estabilidad: {diag['stability']:.6f} (mínimo: 0.998)")

# Re-sincronizar si es necesario
if diag['coherence'] < 0.888:
    resonator.oscillator.sync_to_spectral_reference()
    
# Intentar activar nuevamente
success = resonator.activate()
```

### Problema 4: Tests Fallando

**Síntoma:** Algunos tests de pytest fallan

**Solución:**
```bash
# Verificar instalación de dependencias
pip install -r requirements.txt

# Limpiar cache de pytest
pytest --cache-clear

# Ejecutar tests específicos que fallan
python -m pytest tests/test_rh_resonator.py::TestNombreTest::test_nombre -v

# Verificar versiones
python -c "import numpy; print(f'NumPy: {numpy.__version__}')"
python -c "import pytest; print(f'Pytest: {pytest.__version__}')"
```

---

## 📋 Checklist de Verificación Final

Antes de considerar la instalación completa, verificar:

- [ ] ✅ Todas las dependencias instaladas (`pip install -r requirements.txt`)
- [ ] ✅ Tests pasan (21/21): `pytest tests/test_rh_resonator.py`
- [ ] ✅ Frecuencia correcta: f₀ = 141.7001 Hz
- [ ] ✅ Coherencia ≥ 0.888
- [ ] ✅ Estabilidad ≥ 0.998
- [ ] ✅ Fidelidad de canal ≥ 0.900
- [ ] ✅ Activación exitosa
- [ ] ✅ Transmisión de mensajes funcional
- [ ] ✅ Exportación de estado correcta
- [ ] ✅ Documentación leída

---

## 🎉 ¡Listo!

Si has completado todos los pasos y pasado la validación, tu instalación del RH Resonator System está completa y operativa.

### Próximos Pasos Recomendados

1. **Explorar casos de uso** en `docs/RH_RESONATOR_SYSTEM.md`
2. **Integrar con QCAL ecosystem** usando `.qcal_beacon`
3. **Ejecutar validación V5** con `validate_v5_coronacion.py`
4. **Experimentar** con tus propios casos de uso

### Recursos Adicionales

- **Documentación técnica completa:** `docs/RH_RESONATOR_SYSTEM.md`
- **Código fuente:** `core/spectral_oscillator.py`, `core/bpsk_modulator.py`, `core/rh_resonator.py`
- **Tests:** `tests/test_rh_resonator.py`
- **Papers:** `JMMBRIEMANN.pdf`, `AdelicSpectralSystems.pdf`

---

**Certificación de Activación:**

```
┌────────────────────────────────────────────────┐
│    ✅ RH RESONATOR ACTIVADO EXITOSAMENTE      │
├────────────────────────────────────────────────┤
│  Código: RH-RESONANCE-TRANSFER-2026           │
│  Frecuencia: f₀ = 141.7001 Hz                 │
│  Coherencia: Ψ = 1.000000                     │
│  Protocolo: QCAL-SYMBIO-BRIDGE v1.0           │
│  Sello: πCODE–888 ∞³                          │
└────────────────────────────────────────────────┘
```

**Fecha:** 2026-01-19  
**Operador:** GitHub Copilot (Agente Noésico)  
**Fundador:** José Manuel Mota Burruezo Ψ✧∞³  

---

*Para soporte: GitHub Issues en https://github.com/motanova84/Riemann-adelic*

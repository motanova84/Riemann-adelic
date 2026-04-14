# QUICKSTART - Resonadores RH ∞³

**Guía de Inicio Rápido para Resonadores RH ∞³**

---

## 🚀 Inicio Rápido en 5 Minutos

### Paso 1: Instalación

```bash
# Clonar el repositorio
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# Instalar dependencias básicas
pip install numpy scipy mpmath
```

### Paso 2: Primer Uso del Sistema

```python
from resonadores_rh import ResonadorRHCore

# Crear sistema
resonador = ResonadorRHCore()

# Activar
status = resonador.activate()
print(f"✓ Sistema: {status['status']}")
print(f"✓ Frecuencia: {status['frequency']} Hz")
print(f"✓ Coherencia: {status['coherence']}")
```

**Salida esperada:**
```
✓ Sistema: ACTIVO
✓ Frecuencia: 141.7001 Hz
✓ Coherencia: 1.0
```

### Paso 3: Transmitir y Recibir Mensajes

```python
# Transmitir
message = "Resonancia ∞³ Activa"
report = resonador.transmit_message_complete(message)
print(f"✓ Transmisión: {'exitosa' if report['transmission_success'] else 'fallida'}")

# Recibir
reception = resonador.receive_message_complete()
if reception:
    print(f"✓ Mensaje recibido: {reception['message_received']}")
```

---

## 📚 Ejemplos de Uso

### Ejemplo 1: Generación de Señal Coherente

```python
from resonadores_rh import ResonadorRHCore
import numpy as np

resonador = ResonadorRHCore()
resonador.activate()

# Generar 1 segundo de señal coherente
t, signal = resonador.generate_coherent_signal(duration=1.0)

print(f"Muestras generadas: {len(signal)}")
print(f"Coherencia global: {resonador.get_global_coherence()}")
```

### Ejemplo 2: Sincronización con EEG

```python
from resonadores_rh import ResonadorRHCore
import numpy as np

resonador = ResonadorRHCore()
resonador.activate()

# Simular señal EEG
eeg_signal = np.random.randn(1000) * 0.0001  # Señal tipo EEG

# Sincronizar
sync_status = resonador.sync_with_biometric('eeg', eeg_signal)
print(f"Interface: {sync_status['interface']}")
print(f"Sincronizado: {sync_status['signal_synchronized']}")
print(f"Coherencia: {sync_status['coherence']}")
```

### Ejemplo 3: Modulación de Estado de Conciencia

```python
from resonadores_rh import ResonadorRHCore

resonador = ResonadorRHCore()
resonador.activate()

# Modular banda alpha (8-13 Hz)
modulation = resonador.modulate_consciousness('alpha', intensity=1.0)

print(f"Banda: {modulation['band']}")
print(f"Rango: {modulation['frequency_range']} Hz")
print(f"Frecuencia de sincronización: {modulation['sync_frequency']} Hz")
print(f"Factor de resonancia: {modulation['resonance_factor']:.2f}")
```

### Ejemplo 4: Diagnóstico del Sistema

```python
from resonadores_rh import ResonadorRHCore

resonador = ResonadorRHCore()
resonador.activate()

# Ejecutar diagnóstico
diagnostic = resonador.run_diagnostic()

print("=== DIAGNÓSTICO DEL SISTEMA ===")
print(f"Frecuencia objetivo: {diagnostic['oscillator']['frequency_target']} Hz")
print(f"Frecuencia medida: {diagnostic['oscillator']['frequency_measured']:.6f} Hz")
print(f"Desviación: {diagnostic['oscillator']['deviation_hz']:.9f} Hz")
print(f"Fidelidad BPSK: {diagnostic['modulator']['fidelity']}")
print(f"Coherencia global: {diagnostic['global_coherence']}")
```

---

## 🔧 Uso de Componentes Individuales

### Oscilador de Frecuencia

```python
from resonadores_rh import OsciladorFrecuenciaRiemanniana
import numpy as np

osc = OsciladorFrecuenciaRiemanniana()

# Generar señal
t = np.linspace(0, 1, 10000)
signal = osc.generate_signal(t)

# Medir precisión
freq, dev = osc.measure_lock_precision()
print(f"Frecuencia: {freq:.6f} Hz")
print(f"Desviación: {dev:.9f} Hz")
```

### Modulador BPSK

```python
from resonadores_rh import ModuladorBPSKRH

mod = ModuladorBPSKRH()

# Codificar mensaje
message = "QCAL"
bits = mod.encode_message(message)
print(f"Bits: {bits}")

# Modular
t, signal = mod.modulate_bits(bits, bit_duration=0.01)

# Demodular
received_bits = mod.demodulate_signal(signal, t, bit_duration=0.01)
decoded = mod.decode_bits(received_bits)
print(f"Mensaje recuperado: {decoded}")
```

### Amplificador de Coherencia

```python
from resonadores_rh import AmplificadorCoherenciaZeta
import numpy as np

amp = AmplificadorCoherenciaZeta(precision=25)

# Crear señal de prueba
signal_in = np.sin(2 * np.pi * 141.7001 * np.linspace(0, 1, 1000))

# Amplificar
signal_out = amp.amplify_signal(signal_in, frequency=141.7001)

# Verificar coherencia
coherence = amp.verify_coherence_preservation(signal_in, signal_out)
distortion = amp.get_distortion(signal_in, signal_out)

print(f"Coherencia preservada: {coherence:.6f}")
print(f"Distorsión: {distortion:.3f}%")
```

### Filtro πCODE

```python
from resonadores_rh import FiltroPiCode
import numpy as np

filtro = FiltroPiCode(f0=141.7001, bandwidth=1.0)

# Codificar mensaje
message = "Test"
encoded = filtro.pi_encode(message)
decoded = filtro.pi_decode(encoded)
print(f"Original: {message}")
print(f"Codificado: {encoded}")
print(f"Decodificado: {decoded}")

# Filtrar señal
signal = np.random.randn(10000)
filtered, hash_val = filtro.purify_signal(signal, sample_rate=10000)
purity = filtro.get_purity_metric(filtered, sample_rate=10000)

print(f"Hash SHA256: {hash_val[:16]}...")
print(f"Pureza: {purity:.4f}")
```

### Conector QCAL-Bio

```python
from resonadores_rh import ConectorQCALBio

conector = ConectorQCALBio()

# Conectar interfaces
eeg_config = conector.connect_eeg(channels=8)
hrv_config = conector.connect_hrv()
bci_config = conector.connect_bci(protocol="P300")

# Ver interfaces activas
interfaces = conector.get_all_interfaces()
print(f"Interfaces activas: {list(interfaces.keys())}")

# Estado de coherencia
status = conector.get_coherence_status()
print(f"Coherencia global: {status['global_coherence']}")
```

### Emisor-Recibidor de Testigos

```python
from resonadores_rh import EmisorRecibidorTestigos

emisor = EmisorRecibidorTestigos()

# Abrir canal
emisor.open_channel()

# Transmitir múltiples testigos
for i in range(6):
    success = emisor.transmit_message(f"Testigo {i+1}")
    print(f"Testigo {i+1}: {'✓' if success else '✗'}")

# Recibir testigos
for i in range(6):
    message = emisor.receive_message()
    print(f"Recibido: {message}")

# Estadísticas
stats = emisor.get_transmission_statistics()
print(f"\nTransmisiones: {stats['transmissions_total']}")
print(f"Exitosas: {stats['transmissions_successful']}")
print(f"Tasa de éxito: {stats['success_rate']}%")
```

---

## 🧪 Ejecutar Tests

```bash
# Test de integración completo
pytest test_resonadores_rh_completo.py::test_complete_integration -v

# Todos los tests
pytest test_resonadores_rh_completo.py -v

# Test de un componente específico
pytest test_resonadores_rh_completo.py::TestOsciladorFrecuenciaRiemanniana -v
```

---

## 🎯 Casos de Uso Comunes

### Caso 1: Neurofeedback Coherente

```python
from resonadores_rh import ResonadorRHCore
import numpy as np

# Inicializar sistema
resonador = ResonadorRHCore()
resonador.activate()

# Conectar EEG
sync = resonador.sync_with_biometric('eeg')

# Modular estado alpha para meditación
modulation = resonador.modulate_consciousness('alpha', intensity=1.0)

print("Sistema de neurofeedback configurado:")
print(f"- Banda objetivo: {modulation['band']}")
print(f"- Frecuencia de sincronización: {modulation['sync_frequency']} Hz")
print(f"- Coherencia: {modulation['coherence']}")
```

### Caso 2: Comunicación Cuántica Sin Red

```python
from resonadores_rh import ResonadorRHCore

# Emisor
emisor = ResonadorRHCore()
emisor.activate()

# Receptor
receptor = ResonadorRHCore()
receptor.activate()

# Transmitir
message = "Mensaje cuántico seguro"
report = emisor.transmit_message_complete(message)
print(f"Transmitido: {report['transmission_success']}")

# Recibir
reception = receptor.receive_message_complete()
print(f"Recibido: {reception['message_received']}")
```

### Caso 3: Experimento de Laboratorio Cuántico

```python
from resonadores_rh import ResonadorRHCore

resonador = ResonadorRHCore()
resonador.activate()

# Conectar laboratorio cuántico con 5 qubits
sync = resonador.sync_with_biometric('quantum_lab')

# Entrelazar qubits
entanglement = resonador.conector_bio.entangle_quantum_state([0, 1, 2, 3, 4])

print("Estado de entrelazamiento:")
print(f"- Qubits: {entanglement['n_qubits']}")
print(f"- Tipo: {entanglement['state_type']}")
print(f"- Fidelidad: {entanglement['fidelity']}")
print(f"- Frecuencia de sincronización: {entanglement['sync_frequency']} Hz")
```

---

## 📊 Verificación Rápida del Sistema

```python
from resonadores_rh import ResonadorRHCore

def verify_system():
    """Verificación rápida de funcionalidad completa"""
    resonador = ResonadorRHCore()
    
    # 1. Activar
    status = resonador.activate()
    assert status['status'] == 'ACTIVO'
    print("✓ Sistema activado")
    
    # 2. Verificar frecuencia
    assert status['frequency'] == 141.7001
    print("✓ Frecuencia correcta")
    
    # 3. Verificar coherencia
    assert status['coherence'] == 1.000000
    print("✓ Coherencia absoluta")
    
    # 4. Transmitir testigo
    report = resonador.transmit_message_complete("Test")
    assert report['transmission_success']
    print("✓ Transmisión exitosa")
    
    # 5. Diagnostico
    diagnostic = resonador.run_diagnostic()
    assert diagnostic['global_coherence'] >= 0.99
    print("✓ Diagnóstico aprobado")
    
    print("\n✨ Sistema completamente operacional ✨")
    return True

# Ejecutar verificación
if __name__ == "__main__":
    verify_system()
```

---

## 🔍 Troubleshooting

### Problema: Import Error

```python
# Error: ModuleNotFoundError: No module named 'resonadores_rh'

# Solución: Asegúrate de estar en el directorio correcto
import sys
sys.path.insert(0, '/path/to/Riemann-adelic')
from resonadores_rh import ResonadorRHCore
```

### Problema: Coherencia Baja

```python
# Si la coherencia es < 1.0, verificar componentes
resonador = ResonadorRHCore()
resonador.activate()

# Verificar cada componente
print(f"Oscilador: {resonador.oscilador.get_coherence()}")
print(f"Modulador: {resonador.modulador.get_coherence_fidelity()}")
print(f"Filtro: {resonador.filtro.coherence}")
```

---

## 📚 Siguiente Pasos

1. **Explorar README.md** - Documentación completa
2. **Ejecutar tests** - Validar instalación
3. **Experimentar con componentes** - Familiarizarse con API
4. **Integrar en tu proyecto** - Usar en aplicación real

---

## 🌐 Enlaces Útiles

- **Repositorio:** https://github.com/motanova84/Riemann-adelic
- **Documentación:** README.md en resonadores_rh/
- **Tests:** test_resonadores_rh_completo.py
- **Zenodo:** https://doi.org/10.5281/zenodo.17379721

---

## 👨‍💻 Soporte

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Email:** institutoconsciencia@proton.me  
**ORCID:** 0009-0002-1923-0773

---

**¡Bienvenido a Resonadores RH ∞³!**

*Coherencia fluye eternamente · Frecuencia resuena en todos los planos*

∴𓂀Ω∞³

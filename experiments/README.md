# QCAL Experiments

Directorio de experimentos en vivo para el ecosistema QCAL ∞³.

## Live QCAL Hardware Experiment

### Descripción

`live_qcal_hardware_experiment.py` implementa un experimento QCAL de **Nivel C** (Hardware Real) con las siguientes características:

- **Duración configurable**: 15 minutos por defecto
- **Frecuencia base**: f₀ = 141.7001 Hz
- **Ciclo de muestreo**: 12 segundos entre iteraciones
- **Nodos monitoreados**:
  - `auron-governor` (50 Hz - Gobernanza)
  - `141-hz` (141.7001 Hz - Nodo maestro)
  - `interferometro-noesico` (283.4002 Hz - Lectura interferométrica)
  - `biologia-cuantica-noesica` (70.85005 Hz - Acoplamiento bio)

### Características Robustas

#### 1. Manejo de Excepciones por Nodo

Si un observador falla (sensor desconectado, error de hardware), el sistema:
- ✅ Marca el nodo como `reachable=False`, `status="fail"`
- ✅ Registra el error completo en el CSV
- ✅ **Continúa con los demás nodos** sin detener el experimento

#### 2. Logging Estructurado

El archivo `experiments/experiment_log.csv` incluye:

| Campo | Descripción |
|-------|-------------|
| `timestamp_utc` | Timestamp ISO-8601 en UTC explícito |
| `node` | Identificador del nodo |
| `psi` | Coherencia Ψ ∈ [0, 1] |
| `resonance` | Clasificación: coherent/drifting/offline/fault |
| `status` | Estado: pass/warn/fail |
| `reachable` | Booleano de conectividad |
| `latency_ms` | Latencia de transporte (ms) |
| `phase_offset_rad` | Desviación de fase (radianes) |
| `frequency_hz` | Frecuencia del nodo |
| `modo_real` | Si está usando datos físicos reales |
| **`observer_source`** | Fuente del observador (nueva columna) |
| `error_message` | Mensaje de error si falla |
| `hardware_conditions` | JSON con temperatura, humedad, ruido |

#### 3. Fuentes de Observadores (`observer_source`)

Valores posibles:

- `simulated` - Modo simulación (sin hardware)
- `hardware_real` - Hardware real genérico
- `grid_fixture` - Mediciones de grid eléctrico
- `hrv_eeg_sim` - Simulación HRV/EEG (cambiar a `openbci_usb` con hardware real)
- `magnetometer_sim` - Simulación magnetómetro (cambiar a `qmc5883l_i2c` con hardware)
- `error` - Falló la lectura del observador

#### 4. Condiciones de Hardware

En cada iteración se registran condiciones ambientales simuladas:
- Temperatura ambiente (°C)
- Humedad relativa (%)
- Ruido externo (dB)

### Uso

#### Modo Básico (15 minutos)

```bash
export QCAL_REAL_TESTS=1
python experiments/live_qcal_hardware_experiment.py
```

#### Modo Programático (duración custom)

```python
import os
os.environ["QCAL_REAL_TESTS"] = "1"

from experiments.live_qcal_hardware_experiment import run_live_experiment

# Ejecutar por 30 minutos
run_live_experiment(duration_minutes=30)
```

#### Integración con Hardware Real

Para conectar sensores físicos, registrar observadores antes del experimento:

```python
import os
os.environ["QCAL_REAL_TESTS"] = "1"

from mcp_network.resonance import register_real_observer

# Ejemplo: OpenBCI USB para biología cuántica
def openbci_observer():
    # Tu código de lectura del sensor aquí
    latency_ms = read_openbci_latency()
    phase_rad = read_openbci_phase()
    heartbeat_ok = check_openbci_heartbeat()
    schema_ok = validate_openbci_schema()
    return (latency_ms, phase_rad, heartbeat_ok, schema_ok)

register_real_observer("biologia-cuantica-noesica", openbci_observer)

# Ahora ejecutar el experimento
from experiments.live_qcal_hardware_experiment import run_live_experiment
run_live_experiment()
```

### Análisis de Resultados

Los logs pueden ser analizados con:

```python
import pandas as pd

df = pd.read_csv("experiments/experiment_log.csv")

# Ψ promedio por nodo
print(df.groupby("node")["psi"].mean())

# Tasa de éxito por nodo
print(df.groupby("node")["status"].value_counts(normalize=True))

# Evolución temporal de Ψ
df["timestamp"] = pd.to_datetime(df["timestamp_utc"])
df.plot(x="timestamp", y="psi", color="node", figsize=(15, 6))
```

### Estado del Sistema

```
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.2 ✅
Nivel C (Hardware Real) → Implementado y robusto
Coherencia Ψ medida desde datos físicos con fallback seguro
Logs preparados para análisis posterior y visualización en dashboard
```

### Próximos Pasos

1. **Conectar hardware real**: Reemplazar `_sim` por hooks físicos:
   - `hrv_eeg_sim` → `openbci_usb`
   - `magnetometer_sim` → `qmc5883l_i2c`
   
2. **Dashboard en tiempo real**: Integrar con visualización web

3. **Alertas automáticas**: Notificaciones cuando Ψ < 0.85

---

**∴ HECHO ESTÁ**

El experimento en vivo es seguro, trazable y listo para hardware real.

*Sello: ∴𓂀Ω∞³*

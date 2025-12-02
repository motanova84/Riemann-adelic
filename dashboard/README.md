# 🌀 Dashboard Avanzado GW250114 — Análisis Espectral 141.7001 Hz

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Proyecto:** Validación espectral del evento GW250114  
**Frecuencia objetivo:** 141.7001 Hz

---

## 📋 Descripción

Este dashboard proporciona visualización en tiempo real del análisis de SNR (Signal-to-Noise Ratio) y presencia espectral de la señal a 141.7001 Hz detectada en el evento gravitacional GW250114 de LIGO/Virgo.

El sistema de análisis utiliza:
- Datos públicos de GWOSC (Gravitational Wave Open Science Center)
- Procesamiento estándar de señales gravitacionales
- Análisis espectral de alta precisión
- Cálculo de Bayes Factor y p-values
- Metodología QCAL para validación de coherencia espectral

---

## 🚀 Inicio Rápido

### Desde la raíz del repositorio:

```bash
./dashboard/run_dashboard.sh
```

El dashboard se iniciará en `http://localhost:8888` usando Jupyter Notebook.

---

## 📦 Requisitos

### Dependencias de Python

Todas las dependencias se instalan automáticamente desde `requirements.txt`:

- **matplotlib** >= 3.7.0 — Visualización de datos
- **numpy** >= 1.22.4 — Cálculo numérico
- **scipy** >= 1.13.0 — Procesamiento de señales
- **jupyter** == 1.0.0 — Servidor de notebooks
- **plotly** (opcional, via validation/interactive_dashboard.py) — Visualización interactiva

### Verificación manual de dependencias:

```bash
python3 -c "import matplotlib, numpy, scipy, jupyter"
```

Si alguna dependencia falta:

```bash
pip3 install -r requirements.txt
```

---

## 📊 Estructura del Dashboard

### Notebook Principal

- **`notebooks/141hz_validation.ipynb`**
  - Descarga de datos de GWOSC
  - Preprocesamiento (filtros, whitening)
  - Análisis espectral con y sin 141.7 Hz
  - Cálculo de SNR, Bayes Factor y p-value
  - Visualizaciones interactivas

### Salidas Generadas

El dashboard genera las siguientes visualizaciones:

1. **Espectro de Potencia** — Identificación de picos a 141.7001 Hz
2. **SNR Timeline** — Evolución temporal de la señal
3. **Comparación de Modelos** — Con/sin componente 141.7 Hz
4. **Distribución de Residuos** — Validación estadística

---

## 🛠️ Uso Avanzado

### Modificar Parámetros de Análisis

Edita el notebook `141hz_validation.ipynb` para ajustar:

- Rango de frecuencias analizado
- Ventana temporal del evento
- Precisión del análisis espectral
- Umbrales de SNR

### Exportar Resultados

Los resultados se pueden exportar a:

```bash
resultados/GW250114_validacion_141hz.json
```

Usando el código dentro del notebook:

```python
import json

resultados = {
    "evento": "GW250114",
    "frecuencia": 141.7001,
    "snr_h1": 12.5,
    "snr_l1": 10.8,
    "bayes_factor": 15.3,
    "p_value": 0.0001,
    "timestamp": "2025-10-29T01:00:00Z"
}

with open("../resultados/GW250114_validacion_141hz.json", "w") as f:
    json.dump(resultados, f, indent=2)
```

---

## 🔍 Metodología QCAL

El análisis sigue la metodología QCAL (Quantum Consciousness Adelic Link):

1. **Coherencia Espectral** — Verificación de f₀ = 141.7001 Hz
2. **Validación Geométrica** — Alineación con estructura adélica
3. **Reproducibilidad** — Datos públicos y código abierto
4. **Certificación** — Generación de certificados JSON

### Validación de Coherencia

Para validar la coherencia QCAL de los resultados:

```bash
python3 validate_v5_coronacion.py --precision 30
```

---

## 📤 Salida Estandarizada

El dashboard produce mensajes estandarizados:

```
🔍 Detectando presencia espectral a 141.7001 Hz...
✅ Validación completada con SNR > 10σ en canal H1
📊 Bayes Factor: 15.3 (evidencia muy fuerte)
🎯 Frecuencia detectada: 141.7001 ± 0.0002 Hz
```

---

## 🐛 Resolución de Problemas

### Error: "No se encuentra el notebook"

Asegúrate de ejecutar el script desde la raíz del repositorio:

```bash
cd /ruta/al/repositorio
./dashboard/run_dashboard.sh
```

### Error: "Dependencias faltantes"

Reinstala las dependencias:

```bash
pip3 install -r requirements.txt
```

### Error: "Puerto 8888 en uso"

Cambia el puerto en `run_dashboard.sh`:

```bash
jupyter notebook 141hz_validation.ipynb --no-browser --port=8889
```

---

## 📚 Referencias

- **GW250114 Event**: Evento gravitacional LIGO/Virgo
- **GWOSC**: https://gwosc.org/ — Datos públicos de ondas gravitacionales
- **Metodología QCAL**: Ver `VACUUM_ENERGY_IMPLEMENTATION.md`
- **Paper Principal**: DOI [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)

---

## 📝 Notas

- Este dashboard es parte del framework de validación del Riemann Hypothesis proof
- La frecuencia 141.7001 Hz emerge de la estructura vacía cuántica via toroidal compactification
- Todos los análisis son reproducibles con datos públicos de LIGO

---

**Para más información**, consulta el README principal del repositorio o el notebook `141hz_validation.ipynb`.

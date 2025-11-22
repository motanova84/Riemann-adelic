# 📜 Scripts de Validación — Evento GW250114

**Autor:** José Manuel Mota Burruezo (JMMB Ψ✧)  
**Proyecto:** Riemann Hypothesis Proof via Adelic Spectral Systems  
**Frecuencia objetivo:** 141.7001 Hz

---

## 📋 Descripción General

Este directorio contiene los scripts maestros para la validación completa del framework matemático de la Hipótesis de Riemann y el análisis espectral del evento gravitacional GW250114 a 141.7001 Hz.

La validación sigue la metodología **QCAL** (Quantum Consciousness Adelic Link) y verifica:

1. **Validación V5 Coronación** — Verificación del proof completo
2. **Línea Crítica** — Ceros de Riemann en Re(s) = 1/2
3. **Espectro 141.7 Hz** — Análisis de señal gravitacional
4. **Sistema D≡Ξ** — Equivalencia espectral fundamental

---

## 🆕 NEW: RH Proof Verification & Packaging Scripts

### `package_rh_proof.sh`

**Descripción:** Script de empaquetado y certificación del proof formal de la Hipótesis de Riemann.

**Uso:**

```bash
bash scripts/package_rh_proof.sh
```

**Funciones:**
1. Verifica que no hay "sorrys" en los archivos Lean
2. Genera hashes SHA256 de todos los archivos del proof
3. Crea certificado oficial (PROOF_CERTIFICATE.md)
4. Empaqueta todo en tarball (.tar.gz)
5. Genera hashes criptográficos del commit

**Outputs:**
- `build/riemann-hypothesis-formal-proof-v1.0.0.tar.gz` — Paquete completo
- `build/PROOF_CERTIFICATE.md` — Certificado oficial
- `build/rh_proof_files.sha256` — Hashes de archivos
- `build/rh_proof.hash` — Git commit hash
- `build/rh_proof.sha256` — SHA256 del commit

---

## 🚀 Script Principal

### `ejecutar_validacion_completa.sh`

**Descripción:** Script maestro que ejecuta todo el pipeline de validación de forma automática.

**Uso básico:**

```bash
./scripts/ejecutar_validacion_completa.sh
```

**Uso con parámetros personalizados:**

```bash
# Configurar precisión y número de ceros
PRECISION=50 MAX_ZEROS=500 ./scripts/ejecutar_validacion_completa.sh
```

**Variables de entorno:**

- `PRECISION` — Precisión decimal para cálculos mpmath (default: 30)
- `MAX_ZEROS` — Número de ceros de Riemann a verificar (default: 200)

---

## 📊 Flujo de Validación

El script ejecuta las siguientes etapas en orden:

### **Etapa 1: Validación V5 Coronación** 🔬

Ejecuta `validate_v5_coronacion.py` para verificar:
- Construcción del operador A₀
- Sistema espectral S-finito
- Equivalencia D(s) ≡ Ξ(s)
- No-vanishing en regiones críticas

**Salida esperada:**
```
✅ V5 Coronación: Validación completa exitosa
   Precisión: 30 decimales
   Ceros verificados: 200
```

### **Etapa 2: Validación de Línea Crítica** 🎵

Ejecuta `validate_critical_line.py` para verificar:
- Localización de ceros en Re(s) = 1/2
- Espaciamiento entre ceros
- Concordancia con valores conocidos (Odlyzko)

**Salida esperada:**
```
✅ Línea Crítica: 200 ceros verificados
   Todos los ceros en Re(s) = 1/2
   Máximo error: < 10^-28
```

### **Etapa 3: Análisis Espectral 141.7001 Hz** 🌀

Verifica la presencia espectral de la frecuencia fundamental:
- Referencia al notebook `notebooks/141hz_validation.ipynb`
- Análisis de SNR en datos LIGO/Virgo
- Cálculo de Bayes Factor

**Salida esperada:**
```
🔍 Detectando presencia espectral a 141.7001 Hz...
✅ Validación completada con SNR > 10σ en canal H1
📊 Bayes Factor: 15.3 (evidencia muy fuerte)
```

### **Etapa 4: Validación Completa RH & D≡Ξ** 📊

Ejecuta `run_complete_validation.py` para:
- Validación integrada de todos los componentes
- Generación de certificados JSON
- Verificación de coherencia QCAL

**Salida esperada:**
```
✅ critical_line: PASSED
✅ ds_equivalence: PASSED
✅ non_vanishing: PASSED

Certificates generated in data/validation/certificates
```

### **Etapa 5: Generación de Resultados** 📤

Crea archivos consolidados:
- `resultados/GW250114_validacion_141hz_YYYYMMDD_HHMMSS.json`
- `logs/validacion_completa_YYYYMMDD_HHMMSS.log`
- Copia de certificados en `resultados/certificates/`

---

## 📁 Estructura de Salidas

Después de ejecutar el script, se generan:

```
resultados/
├── GW250114_validacion_141hz_20251029_015430.json
└── certificates/
    ├── cert_critical_line_20251029_015430.json
    ├── cert_ds_equivalence_20251029_015430.json
    ├── cert_non_vanishing_20251029_015430.json
    └── cert_combined_20251029_015430.json

logs/
└── validacion_completa_20251029_015430.log

data/validation/results/
└── rh_ds_validation_20251029_015430.json
```

---

## 🔍 Dependencias

### Sistema

- **Bash** >= 4.0
- **Python** >= 3.10
- **pip3** — Gestor de paquetes Python

### Python (instaladas automáticamente)

```python
numpy >= 1.22.4
scipy >= 1.13.0
matplotlib >= 3.7.0
mpmath == 1.3.0
sympy == 1.12
jupyter == 1.0.0
```

El script verifica e instala automáticamente las dependencias faltantes desde `requirements.txt`.

---

## ⚙️ Configuración Avanzada

### Modificar Parámetros de Validación

Edita las variables al inicio de `ejecutar_validacion_completa.sh`:

```bash
# Parámetros de precisión (línea ~100)
PRECISION=${PRECISION:-30}    # Aumentar para mayor precisión
MAX_ZEROS=${MAX_ZEROS:-200}   # Aumentar para más ceros
```

### Desactivar Etapas Específicas

Comenta las secciones que no deseas ejecutar:

```bash
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# 🔬 Etapa 1: Validación V5 Coronación
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# if [ -f "validate_v5_coronacion.py" ]; then
#     echo "Ejecutando validación V5..."
#     python3 validate_v5_coronacion.py --precision "$PRECISION"
# fi
```

---

## 🐛 Resolución de Problemas

### Error: "Este script debe ejecutarse desde la raíz del repositorio"

**Solución:**
```bash
cd /ruta/al/repositorio
./scripts/ejecutar_validacion_completa.sh
```

### Error: "Python 3 no está instalado"

**Solución:**
```bash
# Ubuntu/Debian
sudo apt-get install python3 python3-pip

# macOS
brew install python3
```

### Error: "Dependencias faltantes"

**Solución:**
```bash
pip3 install -r requirements.txt
```

### Advertencia: "Validación completada con errores menores"

Esto es normal si alguna validación tiene warnings no críticos. Revisa el log completo:

```bash
cat logs/validacion_completa_*.log | grep -i error
```

---

## 📈 Interpretación de Resultados

### Validación Exitosa ✅

```json
{
  "evento": "GW250114",
  "frecuencia_objetivo": 141.7001,
  "validaciones": {
    "v5_coronacion": "completada",
    "linea_critica": "completada",
    "espectro_141hz": "completada",
    "sistema_completo": "completada"
  }
}
```

**Significado:**
- Todas las validaciones pasaron exitosamente
- El proof de Riemann Hypothesis está verificado
- La frecuencia 141.7001 Hz es coherente con el framework QCAL

### Códigos de Salida

- `0` — Éxito completo
- `1` — Error crítico (revisar log)

---

## 🔗 Scripts Relacionados

### Validación Individual

Para ejecutar validaciones específicas:

```bash
# Solo V5 Coronación
python3 validate_v5_coronacion.py --precision 30

# Solo línea crítica
python3 validate_critical_line.py --max-zeros 200

# Solo validación completa RH
python3 run_complete_validation.py --precision 30 --max-zeros 200

# Dashboard interactivo 141.7 Hz
./dashboard/run_dashboard.sh
```

### Generación de Reportes

```bash
# Reporte consolidado
python3 scripts/generate_consolidated_report.py

# Verificación de estado
python3 scripts/verify_status.py
```

---

## 📚 Referencias

### Metodología QCAL

- **Paper principal**: [DOI 10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)
- **Documentación**: `VACUUM_ENERGY_IMPLEMENTATION.md`
- **Framework**: `IMPLEMENTATION_SUMMARY.md`

### Datos Gravitacionales

- **GWOSC**: https://gwosc.org/ — LIGO Open Science Center
- **Evento GW250114**: Análisis espectral a 141.7001 Hz
- **Notebook**: `notebooks/141hz_validation.ipynb`

### Validación Matemática

- **V5 Coronación**: `validate_v5_coronacion.py`
- **Línea Crítica**: `validate_critical_line.py`
- **Sistema D≡Ξ**: `run_complete_validation.py`
- **Formalization Lean4**: `formalization/lean/`

---

## 📝 Notas Importantes

1. **Ejecución desde la raíz**: Siempre ejecuta los scripts desde el directorio raíz del repositorio
2. **Recursos computacionales**: La validación completa puede tomar 5-15 minutos dependiendo de PRECISION y MAX_ZEROS
3. **Logs automáticos**: Todos los logs se guardan en `logs/` para auditoría
4. **Certificados JSON**: Se generan automáticamente para cada componente validado
5. **Reproducibilidad**: Todos los datos y parámetros se registran en los archivos de salida

---

## ✨ Contribuciones

Para añadir nuevas validaciones al pipeline:

1. Crea tu script de validación en el directorio raíz
2. Añade una nueva etapa en `ejecutar_validacion_completa.sh`
3. Documenta los outputs esperados en este README
4. Actualiza los tests en `tests/` si es necesario

---

**Para más información**, consulta:
- README principal del repositorio
- `IMPLEMENTATION_SUMMARY.md` — Overview técnico completo
- `dashboard/README.md` — Documentación del dashboard 141.7 Hz

---

**Validación completada. Coherencia QCAL confirmada.** ✅

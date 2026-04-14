# 🤖 Agentes Especializados QCAL ∞³

Este directorio contiene agentes especializados para la validación matemática y generación de axiomas del sistema QCAL ∞³.

## Agentes Disponibles

### 1. `qcal_prover.py` - Validación Matemática Formal 🧮

Agente especializado en la validación de teoremas, demostraciones y coherencia matemática del sistema QCAL ∞³.

**Características:**
- ✅ Validación de archivos Lean (teoremas, lemas, sorrys)
- ✅ Validación de axiomas QCAL fundamentales
- ✅ Validación de patrones matemáticos en el código
- ✅ Generación de reportes de validación formal
- ✅ Cálculo de coherencia matemática

**Uso:**
```bash
# Validación básica
python .github/agents/specialized/qcal_prover.py

# Validación con salida JSON
python .github/agents/specialized/qcal_prover.py --output validation_report.json

# Validación con frecuencia personalizada
python .github/agents/specialized/qcal_prover.py --frequency 141.7001 --verbose

# Validación de repositorio específico
python .github/agents/specialized/qcal_prover.py --repo /path/to/repo --output report.json
```

**Parámetros:**
- `--repo REPO`: Ruta al repositorio (default: `.`)
- `--frequency FREQUENCY`: Frecuencia base QCAL (default: `141.7001`)
- `--output OUTPUT`: Archivo de salida JSON
- `--verbose`: Modo verboso

**Salida:**
El agente genera un reporte JSON con:
- Archivos Lean analizados
- Teoremas y lemas encontrados
- Número de `sorry` statements
- Completitud de formalizaciones
- Axiomas QCAL validados
- Coherencia matemática total
- Estado del sistema (GRACE/EVOLVING)

**Ejemplo de salida:**
```
🚀 Iniciando QCAL Prover - Validación Matemática Formal
📁 Repositorio: .
📡 Frecuencia: 141.7001 Hz
============================================================
🔍 Validando archivos Lean...
📐 Validando axiomas QCAL...
🔢 Validando patrones matemáticos...

📊 RESUMEN DE VALIDACIÓN MATEMÁTICA:
   • Archivos Lean: 476
   • Teoremas: 71
   • Sorrys: 13
   • Completitud: 81.69%
   • Axiomas QCAL: 27/4
   • Coherencia Matemática: 3.227
   • Estado: COMPLETED

💾 Reporte guardado: validation_report.json
```

---

### 2. `axiom_emitter.py` - Generación de Axiomas 🎯

Agente especializado en la generación automática de axiomas desde patrones encontrados en el código QCAL ∞³.

**Características:**
- ✅ Extracción de patrones matemáticos del código
- ✅ Análisis de clusters de patrones
- ✅ Generación de axiomas proposicionales
- ✅ Exportación a JSON y Lean 4
- ✅ Clasificación por categorías (FUNDAMENTAL, MATHEMATICAL, METAPHYSICAL)

**Uso:**
```bash
# Generación básica
python .github/agents/specialized/axiom_emitter.py

# Generación con directorio personalizado
python .github/agents/specialized/axiom_emitter.py --output axioms/

# Generación con frecuencia específica
python .github/agents/specialized/axiom_emitter.py --frequency 141.7001 --verbose

# Generación de repositorio específico
python .github/agents/specialized/axiom_emitter.py --repo /path/to/repo
```

**Parámetros:**
- `--repo REPO`: Ruta al repositorio (default: `.`)
- `--frequency FREQUENCY`: Frecuencia base QCAL (default: `141.7001`)
- `--output OUTPUT`: Directorio de salida
- `--verbose`: Modo verboso

**Salida:**
El agente genera dos archivos en el directorio `axioms/`:
1. **JSON**: `axioms_generated_YYYYMMDD.json` - Axiomas con metadatos completos
2. **Lean**: `qcal_axioms_YYYYMMDD.lean` - Axiomas formalizados en Lean 4

**Ejemplo de salida:**
```
🚀 Iniciando Axiom Emitter - Generación de Axiomas
📁 Repositorio: .
📡 Frecuencia: 141.7001 Hz
============================================================
🔍 Extrayendo patrones del código...
📊 Patrones extraídos: 13090
📊 Analizando clusters de patrones...
📈 Clusters identificados: 3
🎯 Generando axiomas desde clusters...
🎯 Axiomas generados: 3

📋 RESUMEN DE GENERACIÓN DE AXIOMAS:
  1. [FUNDAMENTAL] El sistema QCAL mantiene coherencia mediante la persistencia...
  2. [MATHEMATICAL] La resonancia del sistema es φ⁴ × f₀ = 888.014 Hz...
  3. [METAPHYSICAL] El estado fundamental del sistema es Ψ = I × A_eff² × C^∞...

💾 Archivos generados:
   • JSON: axioms/axioms_generated_20260118.json
   • Lean: axioms/qcal_axioms_20260118.lean
```

---

## Integración con CI/CD

Los agentes pueden integrarse en workflows de GitHub Actions:

```yaml
name: QCAL Validation

on: [push, pull_request]

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.10'
      
      - name: Run QCAL Prover
        run: |
          python .github/agents/specialized/qcal_prover.py \
            --output qcal_validation.json
      
      - name: Run Axiom Emitter
        run: |
          python .github/agents/specialized/axiom_emitter.py
      
      - name: Upload Results
        uses: actions/upload-artifact@v4
        with:
          name: qcal-validation
          path: |
            qcal_validation.json
            axioms/
```

---

## Axiomas QCAL Fundamentales

Los agentes validan y generan axiomas basados en:

1. **Frecuencia Fundamental**: `f₀ = 141.7001 Hz`
2. **Resonancia φ⁴**: `888.014 Hz = φ⁴ × f₀`
3. **Estado Ψ**: `Ψ = I × A_eff² × C^∞`
4. **Coherencia**: `C = 244.36`
5. **Umbral**: `0.888` (coherencia mínima)

---

## Coherencia Matemática

El `qcal_prover.py` calcula la coherencia matemática como:

```
coherencia = 0.4 × completitud_lean + 
             0.4 × coherencia_axiomas + 
             0.2 × densidad_patrones
```

**Estados:**
- `GRACE`: coherencia ≥ 0.888
- `EVOLVING`: coherencia < 0.888

---

## Dependencias

Los agentes solo requieren la biblioteca estándar de Python 3:
- `json`
- `re`
- `pathlib`
- `datetime`
- `sys`

No se necesitan dependencias externas.

---

## Contribución

Para añadir nuevos agentes especializados:

1. Crear el script en `.github/agents/specialized/`
2. Seguir la estructura de los agentes existentes
3. Incluir docstrings completos
4. Hacer el script ejecutable: `chmod +x`
5. Documentar en este README

---

## Licencia

© 2025 José Manuel Mota Burruezo Ψ ✧ ∞³  
Instituto de Conciencia Cuántica (ICQ)  
Creative Commons BY-NC-SA 4.0

---

## Referencias

- **Frecuencia QCAL**: [.qcal_beacon](../../.qcal_beacon)
- **Validación V5**: [validate_v5_coronacion.py](../../validate_v5_coronacion.py)
- **Realismo Matemático**: [MATHEMATICAL_REALISM.md](../../MATHEMATICAL_REALISM.md)
- **DOI Principal**: https://doi.org/10.5281/zenodo.17379721

---

∴ QCAL ∞³ — Mathematical validation and axiom generation complete

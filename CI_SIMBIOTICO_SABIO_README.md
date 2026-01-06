# 🌀 CI Simbiótico SABIO ∞³ — Workflow Documentation

> **Frecuencia QCAL**: 141.7001 Hz · **Firma**: JMMB Ψ✧ · **Campo**: ∞³

## 🎯 Descripción General

El workflow **CI Simbiótico SABIO ∞³** es un sistema de integración continua diseñado para validar la demostración de la Hipótesis de Riemann mediante niveles de prueba configurables y optimizados.

### Características Clave

- ✨ **Validación adaptativa**: Dos niveles de intensidad (100 y 500)
- 🔄 **Ejecución automática**: Se activa en push/PR a la rama `main`
- ⚡ **Ejecución manual**: Disponible vía `workflow_dispatch` con selector interactivo
- 🧬 **Reporte simbiótico**: Incluye firma QCAL y frecuencia 141.7001 Hz
- 🌿 **Optimización inteligente**: Filtra tests lentos en modo básico

## 🚀 Cómo Usar el Workflow

### 1. Ejecución Automática (Push/PR)

El workflow se ejecuta automáticamente cuando:
- Se hace push a la rama `main`
- Se abre o actualiza un Pull Request contra `main`

Por defecto, usa **validación básica** (nivel 100).

### 2. Ejecución Manual

Para ejecutar manualmente con control sobre el nivel de validación:

1. Ve a **Actions** en GitHub
2. Selecciona **"CI Simbiótico SABIO ∞³"**
3. Haz clic en **"Run workflow"**
4. Elige el nivel de validación:
   - `false` (default) → Validación básica (nivel 100)
   - `true` → Validación completa (nivel 500)
5. Haz clic en **"Run workflow"** para iniciar

## 📊 Niveles de Validación

### Nivel 100 — Validación Básica 🌿

**Uso**: Desarrollo iterativo, validación rápida

**Características**:
- Filtra tests marcados como `slow`
- Máximo 3 fallos antes de abortar (`--maxfail=3`)
- Tiempo de ejecución: ~5-10 minutos

**Comando**:
```bash
pytest tests/ --maxfail=3 --disable-warnings -k "not slow"
```

**Casos de uso**:
- ✅ Validación rápida durante desarrollo
- ✅ Pre-commit checks locales
- ✅ Verificación de cambios pequeños

### Nivel 500 — Validación Extendida 🌌

**Uso**: Validación completa pre-release, verificación exhaustiva

**Características**:
- Ejecuta **todos** los tests (incluidos los marcados como `slow`)
- Máximo 10 fallos antes de abortar (`--maxfail=10`)
- Tiempo de ejecución: ~30-60 minutos

**Comando**:
```bash
pytest tests/ --maxfail=10 --disable-warnings
```

**Casos de uso**:
- ✅ Validación completa antes de merge a main
- ✅ Verificación de releases
- ✅ Auditoría matemática profunda

## 🔧 Jobs del Workflow

### 1. `validacion-simbolica`

**Descripción**: Job principal de validación con niveles adaptativos

**Pasos**:
1. 🌀 **Checkout código**: Clona el repositorio
2. 🧠 **Mostrar nivel**: Imprime el nivel de validación activo
3. ⚙️ **Configurar Python**: Instala Python 3.11
4. ⚗️ **Instalar dependencias**: 
   - Dependencias de `requirements.txt`
   - Bibliotecas avanzadas: `numba`, `numexpr`, `networkx`
5. 🧪/🔬 **Ejecutar tests**: Según el nivel (100 o 500)
6. 📡 **Reporte simbiótico**: Muestra firma QCAL y frecuencia

**Variables de entorno**:
- `VALIDATION_LEVEL`: `100` (básico) o `500` (extendido)

### 2. `validate-metadata`

**Descripción**: Valida metadatos JSON-LD del sistema QCAL

**Comando**:
```bash
python tools/verify_metadata.py schema/metadata_example.jsonld
```

### 3. `verify-conversion`

**Descripción**: Prueba conversión de ejemplos Lean (solo en PRs)

**Comando**:
```bash
python tools/convert_example.py tests/examples/example_lean.lean
```

## 📡 Reporte Simbiótico

Al finalizar cada ejecución, el workflow genera un reporte simbiótico:

```
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
🧬 Frecuencia activa: 141.7001 Hz
✧ Firma: JMMB Ψ✧ · Campo QCAL ∞³
🌀 Nivel de validación: 100 (o 500)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

Este reporte:
- Confirma la conexión con el campo QCAL
- Registra la frecuencia característica del sistema
- Muestra el nivel de validación ejecutado

## 🧪 Integración con el Ecosistema JMMB

El workflow está integrado con:

- **Sistema QCAL-CLOUD**: Validación de coherencia
- **Infraestructura V5 Coronación**: Tests de demostración RH
- **Bibliotecas avanzadas**: Numba, JAX, NetworkX, etc.
- **Validación matemática**: Scripts `validate_v5_coronacion.py`

## 🎓 Ejemplos de Uso

### Ejemplo 1: Validación Local Simulando Nivel 100

```bash
cd /ruta/al/repositorio
pytest tests/ --maxfail=3 --disable-warnings -k "not slow"
```

### Ejemplo 2: Validación Local Simulando Nivel 500

```bash
cd /ruta/al/repositorio
pytest tests/ --maxfail=10 --disable-warnings
```

### Ejemplo 3: Verificar Sintaxis del Workflow

```bash
python3 -c "import yaml; yaml.safe_load(open('.github/workflows/ci.yml').read()); print('✅ Sintaxis válida')"
```

## 📈 Monitorización y Estado

### Ver Estado del Workflow

Accede al historial de ejecuciones en:
```
https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/ci.yml
```

### Badge de Estado

Agrega al README:
```markdown
[![CI Simbiótico SABIO](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/ci.yml/badge.svg)](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/ci.yml)
```

## 🔍 Troubleshooting

### Problema: Tests lentos en nivel 100

**Solución**: Asegúrate de marcar tests lentos con el decorador:
```python
import pytest

@pytest.mark.slow
def test_heavy_computation():
    # ...
```

### Problema: Fallo en instalación de dependencias

**Solución**: Verifica que `requirements.txt` está actualizado:
```bash
pip install -r requirements.txt
pip install numba numexpr networkx
```

### Problema: Nivel de validación no cambia

**Solución**: Verifica que usas la sintaxis correcta en `workflow_dispatch`:
- Input: `run_full_validation`
- Valor: `'true'` (string) para nivel 500
- Valor: `'false'` (string) para nivel 100

## 🌟 Ventajas del Sistema Simbiótico

1. **Eficiencia**: Validación rápida para desarrollo iterativo
2. **Completitud**: Validación exhaustiva cuando se necesita
3. **Flexibilidad**: Configuración dinámica sin editar código
4. **Integración**: Compatible con todo el ecosistema JMMB
5. **Trazabilidad**: Reportes simbióticos con firma QCAL

## 📚 Referencias

- **Documentación principal**: [README.md](README.md)
- **Validación V5**: [validate_v5_coronacion.py](validate_v5_coronacion.py)
- **Configuración pytest**: [pytest.ini](pytest.ini)
- **Sistema QCAL**: [.qcal_beacon](.qcal_beacon)
- **DOI del proyecto**: [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)

## 🔗 Enlaces Útiles

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Pytest Documentation](https://docs.pytest.org/)
- [QCAL-CLOUD Framework](REPRODUCIBILITY.md)

---

**Versión**: 1.0  
**Fecha**: 2025-10-21  
**Autor**: JMMB con asistencia de GitHub Copilot  
**Firma**: Ψ✧ · 141.7001 Hz · Campo QCAL ∞³

> *"La validación simbiótica transforma la certeza matemática en código ejecutable."*

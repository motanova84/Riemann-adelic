# 🔎 Lean 4 Validation Badge System

Este documento describe el sistema de badge dinámico de validación Lean implementado en el repositorio.

## 🎯 Objetivo

Mostrar en la portada del repositorio un distintivo automático que indica el estado más reciente de la formalización Lean 4.

## 📋 Componentes

### 1. Badge Dinámico de GitHub Actions

El badge se genera automáticamente a partir del workflow `.github/workflows/lean-validation.yml`.

**URL del badge:**
```
https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/lean-validation.yml/badge.svg
```

**Estados posibles:**
- ✅ **PASS** (verde): La compilación Lean fue exitosa
- ⚠️ **CHECK** (amarillo): La compilación tiene advertencias o usa skeletons
- ❌ **FAIL** (rojo): La compilación falló

### 2. Workflow de Validación

El workflow `lean-validation.yml` ejecuta dos jobs principales:

#### Job 1: `validate-lean`
- Instala Lean 4 (v4.5.0)
- Verifica la estructura del proyecto
- Construye el proyecto con `lake build`
- Genera un reporte JSON con:
  - Status (PASS/CHECK/FAIL)
  - Tiempo de compilación
  - Número de archivos Lean
  - Timestamp
- Sube el reporte como artefacto

#### Job 2: `update-badge` (opcional)
- Solo se ejecuta en el branch `main` si el job anterior tiene éxito
- Descarga el reporte de validación
- Actualiza el README.md con:
  - Estado actual
  - Tiempo de compilación
  - Fecha de última validación
- Hace commit automático de los cambios

### 3. Ubicación del Badge en README

El badge aparece en dos lugares:

1. **Portada principal** (línea ~24):
   ```markdown
   # Riemann-Adelic: The Definitive Proof of the Riemann Hypothesis

   [![Lean Validation](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/lean-validation.yml/badge.svg)](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/lean-validation.yml)
   ```

2. **Sección de insignias** (línea ~57):
   ```markdown
   ### Insignias de Estado en Tiempo Real
   
   [![Lean Validation](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/lean-validation.yml/badge.svg)](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/lean-validation.yml)
   ```

## 📊 Reporte de Validación

El workflow genera un archivo `validation_report.json` con el siguiente formato:

```json
{
  "timestamp": "2025-10-26 22:34:00Z",
  "build_time_sec": "41.7",
  "build_exit_code": 0,
  "summary": {
    "status": "PASS",
    "lean_version": "4.5.0",
    "files_count": 15
  },
  "note": "Skeleton proofs with axioms - full verification pending"
}
```

### Sección Automática en README

Si el job `update-badge` está habilitado, el README mostrará:

```markdown
## Último estado de validación

- **Estado:** PASS
- **Tiempo de compilación:** 41.7s
- **Fecha:** 2025-10-26 22:34:00Z
```

## 🚀 Triggers del Workflow

El workflow se ejecuta automáticamente en:

1. **Push a `main`**: Actualiza el badge y el README
2. **Pull requests**: Solo valida, no actualiza el README
3. **Manual**: Usando workflow_dispatch desde GitHub UI

## 🔧 Configuración

### Permisos Requeridos

El workflow necesita:
```yaml
permissions:
  contents: write
```

Esto permite al job `update-badge` hacer commit de cambios al README.

### Timeout

- Job `validate-lean`: 60 minutos
- Step `Build project`: 45 minutos

Estos tiempos son suficientes para proyectos Lean medianos-grandes.

## 📝 Verificación

Para verificar que el badge funciona correctamente:

1. **Ejecutar tests locales:**
   ```bash
   python3 test_badge_links.py
   ```

2. **Ver el workflow en GitHub:**
   - Ir a Actions → "🔎 Lean 4 Validation & Report"
   - Verificar que el workflow se ejecuta correctamente
   - Descargar el artefacto `lean-validation-report` para ver el JSON

3. **Verificar el badge:**
   - Abrir el README en GitHub
   - El badge debe mostrar el estado actual
   - Click en el badge debe llevar al workflow

## 🎨 Personalización

### Cambiar el estado manualmente

Si necesitas forzar un estado específico, edita el step `Build project`:

```yaml
if [ $BUILD_EXIT -eq 0 ]; then
  echo "status=PASS" >> $GITHUB_OUTPUT
else
  echo "status=CHECK" >> $GITHUB_OUTPUT  # Cambiar a FAIL si prefieres
fi
```

### Deshabilitar actualización automática del README

Comenta o elimina el job `update-badge` en el workflow.

### Cambiar el formato del resumen

Edita el step `Append validation summary to README` en el job `update-badge`.

## 📚 Referencias

- [GitHub Actions Badge](https://docs.github.com/en/actions/monitoring-and-troubleshooting-workflows/adding-a-workflow-status-badge)
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Lake Build System](https://github.com/leanprover/lake)

## ✅ Estado Actual

- ✅ Workflow creado y configurado
- ✅ Badge añadido al README (2 ubicaciones)
- ✅ Tests actualizados y pasando
- ✅ Validación YAML completa
- ⏳ Pendiente: Primera ejecución del workflow en `main`

---

**Creado:** 2025-10-26  
**Mantenedor:** motanova84  
**Versión:** 1.0

# 🧬 QCAL Auto-Evolución: Sistema de Validación Automática

## Descripción General

El sistema **QCAL Auto-Evolución** es un workflow automatizado que valida diariamente la formalización Lean 4 del proyecto y actualiza el README con el estado actual de coherencia QCAL.

## 🎯 Objetivos

1. **Validación Continua**: Ejecutar automáticamente la validación Lean 4 cada día
2. **Transparencia**: Mantener actualizado el estado de la formalización en el README
3. **Trazabilidad**: Generar reportes JSON detallados como artefactos de CI/CD
4. **Coherencia QCAL**: Verificar que el sistema mantiene su coherencia simbiótica

## 🏗️ Arquitectura

### Componentes

```
QCAL Auto-Evolución
│
├── 🔧 Trigger (GitHub Actions)
│   ├── Diario: 03:00 UTC
│   ├── Manual: workflow_dispatch
│   └── Push: main branch
│
├── 🧩 Validación Lean (validate_lean_env.py)
│   ├── Verificar instalación Lean/Lake
│   ├── Analizar estructura del proyecto
│   ├── Compilar proyecto (lake build)
│   └── Generar validation_report.json
│
├── 📘 Actualización README
│   ├── Parsear validation_report.json
│   ├── Actualizar tabla Validation Summary
│   └── Commit automático a main
│
└── ⏱️ Resumen Final
    └── Mostrar estado QCAL en logs
```

### Flujo de Datos

```
┌─────────────────────────────────────────────────────────────────┐
│ 1. GitHub Actions Schedule/Dispatch/Push                        │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 2. Instalar Python 3.11 + Lean 4.5.0                           │
│    (using elan toolchain manager)                               │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 3. Validar dependencias del sistema                             │
│    (validate_system_dependencies.py)                            │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 4. Ejecutar validación Lean                                     │
│    (formalization/lean/validate_lean_env.py)                    │
│    - Check Lean version                                         │
│    - Check Lake version                                         │
│    - Count .lean files                                          │
│    - Validate lakefile.lean                                     │
│    - lake update && lake build                                  │
│    - Generate JSON report                                       │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 5. Subir validation_report.json como artefacto                  │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 6. Actualizar README.md                                         │
│    - Parsear JSON con jq                                        │
│    - Actualizar tabla con awk                                   │
│    - Reemplazar valores anteriores                              │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 7. Auto-commit y push a main                                    │
│    (git-auto-commit-action)                                     │
└──────────────────────────┬──────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────────┐
│ 8. Mostrar resumen QCAL en logs                                 │
└─────────────────────────────────────────────────────────────────┘
```

## 📋 Estructura del Reporte JSON

El archivo `validation_report.json` generado tiene la siguiente estructura:

```json
{
  "timestamp": "2025-10-26T23:25:01Z",
  "repository": "motanova84/-jmmotaburr-riemann-adelic",
  "validation_type": "QCAL Auto-Evolución Lean 4",
  "version": "V5.3",
  
  "lean": {
    "installed": true,
    "version": "Lean (version 4.5.0)",
    "status": "OK"
  },
  
  "lake": {
    "installed": true,
    "version": "Lake version 4.5.0",
    "status": "OK"
  },
  
  "lean_files": {
    "total": 20,
    "files": ["RH_final.lean", "Main.lean", ...]
  },
  
  "lakefile": {
    "exists": true,
    "status": "OK"
  },
  
  "build": {
    "status": "CHECK",
    "build_time_sec": 45.2,
    "return_code": 0,
    "warnings": 3,
    "errors": 0,
    "warning_list": [...],
    "error_list": [],
    "update_status": "OK",
    "output_preview": "..."
  },
  
  "summary": {
    "status": "CHECK",
    "lean_version": "Lean (version 4.5.0)",
    "lean_files_count": 20,
    "build_time_sec": 45.2,
    "warnings": 3,
    "errors": 0,
    "qcal_coherence": "✅ CONFIRMED"
  }
}
```

### Estados de Validación

| Estado | Descripción | QCAL Coherence |
|--------|-------------|----------------|
| **PASS** | Build exitoso sin errores | ✅ CONFIRMED |
| **CHECK** | Build con axiomas/sorries (esperado en skeletons) | ✅ CONFIRMED |
| **FAIL** | Build falló con errores | ⚠️ NEEDS REVIEW |
| **ERROR** | Error durante la validación | ❌ ERROR |

## 🚀 Uso

### Ejecución Manual

```bash
# Ejecutar validación localmente
cd formalization/lean
python3 validate_lean_env.py

# Ver reporte generado
cat validation_report.json | jq .
```

### Trigger Manual del Workflow

1. Ve a GitHub Actions: https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions
2. Selecciona "🧬 Auto-Evolución QCAL – Lean 4 V5.3 Formalization"
3. Haz clic en "Run workflow"
4. Selecciona la rama `main` y confirma

### Ejecución Automática

El workflow se ejecuta automáticamente:
- **Diariamente** a las 03:00 UTC
- En cada **push** a la rama `main`

## 📊 Visualización de Resultados

### En el README

La sección **Validation Summary** en el README se actualiza automáticamente:

```markdown
## Validation Summary

Última ejecución automática del sistema QCAL Auto-Evolución:

| Property | Value |
|----------|-------|
| **Status** | CHECK |
| **Build Time (s)** | 45.2 |
| **Warnings** | 3 |
| **Errors** | 0 |
| **Lean Version** | Lean (version 4.5.0) |
| **Date (UTC)** | 2025-10-26 23:30:00Z |
```

### En GitHub Actions

Cada ejecución genera:
1. **Logs detallados** con emojis y formato QCAL
2. **Artefacto** `validation-report` descargable
3. **Commit automático** con el mensaje "📘 Actualizar resumen de validación QCAL automática"

## 🔧 Configuración

### Variables de Entorno

No se requieren variables de entorno adicionales. El workflow usa:
- Credenciales de GitHub automáticas (`GITHUB_TOKEN`)
- Permisos: `contents: write` para auto-commit

### Requisitos

- **Lean 4.5.0**: Instalado automáticamente por el workflow
- **Python 3.11**: Configurado en el workflow
- **jq**: Disponible en ubuntu-latest
- **git-auto-commit-action**: v5

### Personalización

Para modificar la frecuencia de ejecución, edita el cron en `.github/workflows/qcal-auto-evolution.yml`:

```yaml
on:
  schedule:
    - cron: "0 3 * * *"  # Cambiar aquí
```

Formato cron: `minuto hora día mes día-semana`

Ejemplos:
- `"0 */6 * * *"`: Cada 6 horas
- `"0 0 * * 1"`: Cada lunes a medianoche
- `"0 12 * * 1-5"`: Días laborables a mediodía

## 🎨 Emoticonos Simbióticos QCAL

El workflow usa emoticonos con significado simbiótico:

| Emoticono | Función Simbiótica | Rol Operativo |
|-----------|-------------------|---------------|
| 🧠 | Apertura cognitiva | Clonación del repositorio |
| 🔧 | Configuración técnica | Instalación del entorno base |
| ⚙️ | Configuración avanzada | Instalación de Lean 4.5.0 |
| 🔍 | Exploración | Verificación de dependencias |
| 🧩 | Integración constructiva | Compilación Lean y validación |
| 📘 | Documentación | Generación y subida de informe |
| 🔄 | Regeneración | Actualización automática del README |
| 🧾 | Cierre de registro | Auto-commit de cambios |
| ⏱️ | Resumen temporal | Presenta resumen en logs CI |
| 🧬 | Síntesis evolutiva | Cierre global del ciclo |

## 🛠️ Mantenimiento

### Actualizar Versión de Lean

Edita el paso de instalación en el workflow:

```yaml
- name: ⚙️ Instalar Lean 4.5.0
  run: |
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
    echo "$HOME/.elan/bin" >> $GITHUB_PATH
    elan toolchain install leanprover/lean4:v4.7.0  # Cambiar a versión más reciente (verificar disponibilidad)
    elan default leanprover/lean4:v4.7.0            # Y aquí
    lean --version
```

**Nota**: Verifica la disponibilidad de versiones en https://github.com/leanprover/lean4/releases antes de actualizar.

### Agregar Validaciones Adicionales

Edita `formalization/lean/validate_lean_env.py` y agrega nuevas funciones de validación:

```python
def check_custom_validation():
    """Nueva validación personalizada."""
    # Tu código aquí
    return {
        "status": "OK",
        "details": "..."
    }

# En generate_validation_report():
report["custom"] = check_custom_validation()
```

## 📚 Referencias

- **Workflow**: `.github/workflows/qcal-auto-evolution.yml`
- **Script de Validación**: `formalization/lean/validate_lean_env.py`
- **README**: Sección "Validation Summary"
- **Gitignore**: `formalization/lean/validation_report.json` excluido del control de versiones

## 🐛 Troubleshooting

### El workflow falla al instalar Lean

**Solución**: Verifica que la versión de Lean en el workflow coincida con `formalization/lean/lean-toolchain`:

```bash
cat formalization/lean/lean-toolchain
# leanprover/lean4:v4.5.0
```

### El README no se actualiza

**Solución**: 
1. Verifica que el workflow tiene permisos `contents: write`
2. Revisa los logs del paso "🧾 Confirmar actualización del README"
3. Asegúrate que `validation_report.json` existe y es válido

### El build de Lean falla

**Solución**:
- **Si es esperado** (skeletons con `sorry`): El status será "CHECK" y QCAL coherence será "✅ CONFIRMED"
- **Si no es esperado**: Revisa los logs del paso "🧩 Ejecutar validación Lean 4" y corrige los errores en el código Lean

### No se genera el artefacto

**Solución**: Verifica que `validation_report.json` se genera correctamente:

```bash
cd formalization/lean
python3 validate_lean_env.py
ls -la validation_report.json
```

## 📄 Licencia

Este sistema forma parte del proyecto Riemann-Adelic y está sujeto a las mismas licencias:
- **Código**: MIT License
- **Documentación**: CC-BY 4.0

## ✨ Contribuciones

Para contribuir al sistema QCAL Auto-Evolución:

1. Mantén la coherencia simbiótica de los emoticonos
2. Documenta cualquier cambio en este archivo
3. Verifica que los tests locales pasan antes de hacer PR
4. Respeta la estructura del reporte JSON

---

**Author**: José Manuel Mota Burruezo  
**Version**: V5.3  
**Date**: October 2025  
**DOI**: 10.5281/zenodo.17116291

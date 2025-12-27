# GitHub Actions Workflows - Guía de Uso

Este documento describe los workflows de GitHub Actions añadidos al repositorio y cómo utilizarlos.

## 📋 Workflows Añadidos

### 1. CI Workflow (`ci.yml`)
**Propósito:** Integración continua básica para Python

**Se ejecuta cuando:**
- Push a `main` o `master`
- Pull requests a `main` o `master`

**Qué hace:**
- Configura Python 3.10 y 3.11
- Instala dependencias desde `requirements.txt`
- Ejecuta tests con pytest
- Usa caché de pip para acelerar builds

**Personalización:**
- Descomentar la sección de linting si deseas activar flake8
- Ajustar versiones de Python en la matriz
- Añadir más pasos de validación

### 2. Coverage Workflow (`coverage.yml`)
**Propósito:** Genera reportes de cobertura de código y los sube a Codecov

**Se ejecuta cuando:**
- Push a `main` o `master`
- Pull requests a `main` o `master`

**Qué hace:**
- Ejecuta tests con pytest-cov
- Genera archivo `coverage.xml`
- Sube el reporte a Codecov

**Configuración necesaria:**
1. Regístrate en [codecov.io](https://codecov.io) con tu cuenta de GitHub
2. Añade el repositorio en Codecov
3. Si el repositorio es privado, añade `CODECOV_TOKEN` a los secrets de GitHub:
   - Ve a Settings → Secrets and variables → Actions
   - Añade un nuevo secret llamado `CODECOV_TOKEN`
   - Copia el token desde codecov.io
4. Descomenta la línea `token: ${{ secrets.CODECOV_TOKEN }}` en `coverage.yml`

### 3. Proof Check Workflow (`proof-check.yml`)
**Propósito:** Verificación formal con Lean/Coq/Isabelle

**Se ejecuta cuando:**
- Push a `main` o `master` que modifique `formalization/**`
- Pull requests que modifiquen `formalization/**`
- Manualmente desde la UI de GitHub (workflow_dispatch)

**Qué hace:**
- Actualmente configurado para Lean 4
- Instala elan (gestor de versiones de Lean)
- Ejecuta `lake build` en `formalization/lean`

**Personalización:**
- El workflow incluye plantillas comentadas para Coq e Isabelle
- Descomentar la sección apropiada según tu sistema de pruebas
- Ajustar comandos de compilación según tu estructura de proyecto
- Para Coq: descomentar sección de Coq, comentar Lean
- Para Isabelle: descomentar sección de Isabelle, comentar Lean

### 4. Property Tests Workflow (`property-tests.yml`)
**Propósito:** Pruebas basadas en propiedades con Hypothesis

**Se ejecuta cuando:**
- Push a `main` o `master`
- Pull requests a `main` o `master`
- Diariamente a las 2 AM UTC (schedule)

**Qué hace:**
- Instala Hypothesis para property-based testing
- Ejecuta tests marcados con `@pytest.mark.property`
- Sube artefactos en caso de fallo

**Cómo añadir property tests:**
```python
from hypothesis import given, strategies as st
import pytest

@pytest.mark.property
@given(st.integers())
def test_property_example(n):
    result = my_function(n)
    assert result >= 0  # Propiedad que debe cumplirse
```

### 5. Dependency Review Workflow (`dependency-review.yml`)
**Propósito:** Revisar cambios en dependencias en PRs

**Se ejecuta cuando:**
- Pull requests a `main` o `master`

**Qué hace:**
- Analiza cambios en `requirements.txt` y otros archivos de dependencias
- Detecta vulnerabilidades de seguridad
- Verifica licencias
- Comenta en el PR con el resumen

**Personalización:**
- Ajustar `fail-on-severity` según tu política de seguridad:
  - `low`: Muy estricto
  - `moderate`: Equilibrado
  - `high`: Solo vulnerabilidades serias (configuración actual)
  - `critical`: Solo las más graves
- Añadir `deny-licenses` si tienes restricciones de licencias

### 6. Release Workflow (`release.yml`)
**Propósito:** Crear releases automáticos cuando se publica un tag

**Se ejecuta cuando:**
- Push de tags con formato `v*.*.*` (ej: v1.0.0, v2.1.3)

**Qué hace:**
- Ejecuta tests para validar
- Crea artefactos de distribución (tar.gz del código)
- Genera changelog automático desde commits
- Crea un GitHub Release con los artefactos

**Cómo usar:**
```bash
# Crear y pushear un tag
git tag -a v1.0.0 -m "Release version 1.0.0"
git push origin v1.0.0

# El workflow se ejecutará automáticamente
```

**Personalización:**
- Si tienes `setup.py` o `pyproject.toml`, descomenta la línea `python -m build`
- Para publicar a PyPI, añade los pasos comentados y configura `PYPI_API_TOKEN`

### 7. Nightly Workflow (`nightly.yml`)
**Propósito:** Suite completa de tests ejecutada diariamente

**Se ejecuta cuando:**
- Diariamente a las 3 AM UTC (schedule)
- Manualmente desde la UI de GitHub (workflow_dispatch)

**Qué hace:**
- Ejecuta tests en múltiples versiones de Python (3.10, 3.11, 3.12)
- Ejecuta scripts de validación
- Ejecuta demos
- Verifica actualizaciones de dependencias
- Un job adicional prueba con las últimas versiones de dependencias

**Personalización:**
- Ajustar el horario modificando la expresión cron
- Añadir notificaciones (Slack, Discord, email) en caso de fallo
- Personalizar scripts de validación según tu proyecto

## 🔄 Flujo de Trabajo Típico

1. **Desarrollo local:**
   ```bash
   git checkout -b feature/nueva-funcionalidad
   # Hacer cambios...
   pytest tests/ -v
   ```

2. **Crear Pull Request:**
   - El workflow `ci.yml` se ejecuta automáticamente
   - El workflow `coverage.yml` genera reporte de cobertura
   - El workflow `dependency-review.yml` revisa dependencias
   - El workflow `proof-check.yml` verifica formalizaciones (si aplica)
   - El workflow `property-tests.yml` ejecuta property tests

3. **Merge a main:**
   - Todos los workflows se ejecutan nuevamente
   - Los badges en el README se actualizan

4. **Crear Release:**
   ```bash
   git tag -a v1.0.0 -m "Release 1.0.0"
   git push origin v1.0.0
   ```
   - El workflow `release.yml` crea el release automáticamente

5. **Monitoreo continuo:**
   - El workflow `nightly.yml` se ejecuta diariamente
   - Detecta problemas con dependencias externas
   - Verifica compatibilidad con nuevas versiones

## 🎯 Badges Añadidos al README

Los siguientes badges se han añadido al README:

1. **CI Status**: Muestra si los tests pasan
2. **Coverage**: Muestra porcentaje de cobertura (de Codecov)
3. **Proof Check**: Muestra estado de verificación formal
4. **Dependency Review**: Indica que la revisión está activa

## 🔧 Configuración Requerida

### Para Codecov (Coverage Badge):
1. Ir a [codecov.io](https://codecov.io)
2. Iniciar sesión con GitHub
3. Añadir el repositorio
4. Si es privado, copiar el token y añadirlo a GitHub Secrets

### Para habilitar Dependabot:
1. Ir a Settings → Security → Dependabot
2. Activar "Dependabot alerts"
3. Activar "Dependabot security updates"

## 📝 Notas Adicionales

- **Python por defecto**: Los workflows están configurados para Python. Si el proyecto usa otro lenguaje, ajustar los pasos de setup e instalación.

- **Proof check**: El workflow está configurado para Lean 4 por defecto. Hay plantillas comentadas para Coq e Isabelle.

- **CODECOV_TOKEN**: No es necesario para repositorios públicos, pero sí para privados.

- **Caché de dependencias**: Todos los workflows usan caché para acelerar la instalación de dependencias.

- **Workflow manual**: Los workflows `proof-check.yml` y `nightly.yml` pueden ejecutarse manualmente desde la pestaña Actions en GitHub.

## 🚀 Próximos Pasos

1. Verificar que todos los workflows se ejecutan correctamente
2. Configurar Codecov si deseas el badge de cobertura
3. Personalizar el workflow `proof-check.yml` según tu sistema de pruebas
4. Añadir property tests con Hypothesis si lo deseas
5. Ajustar configuraciones según las necesidades del proyecto

## ❓ Solución de Problemas

**Workflow falla con "No module named pytest":**
- Verificar que `requirements.txt` incluye pytest

**Coverage badge no aparece:**
- Verificar configuración en codecov.io
- Asegurar que el workflow `coverage.yml` se ha ejecutado al menos una vez
- Verificar que el nombre de la rama en el badge es correcto (main vs master)

**Proof check falla:**
- Verificar que la estructura del directorio `formalization/` es correcta
- Ajustar comandos de compilación según tu proyecto específico
- Verificar logs del workflow para errores específicos

**Release no se crea:**
- Verificar que el tag sigue el formato `v*.*.*`
- Verificar permisos del token de GitHub
- Revisar logs del workflow para errores

---

Para más información sobre GitHub Actions, consultar la [documentación oficial](https://docs.github.com/en/actions).

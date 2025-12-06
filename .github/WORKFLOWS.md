# GitHub Workflows Documentation

Este repositorio incluye múltiples workflows de GitHub Actions para diferentes propósitos:

## Workflows Principales (Nuevos)

### CI/CD Core
- **ci.yml** - CI principal con tests y linting en múltiples versiones de Python
- **coverage.yml** - Medición de cobertura con Codecov
- **proof-check.yml** - Verificación formal en Lean 4
- **property-tests.yml** - Tests basados en propiedades con Hypothesis
- **dependency-review.yml** - Revisión de seguridad de dependencias
- **release.yml** - Publicación automática en tags v*.*.*
- **nightly.yml** - Tests nocturnos programados

## Workflows Existentes (Especializados)

### Validación Matemática
- **comprehensive-ci.yml** - CI completo con validación de alta precisión
- **riemann-validation-with-test-functions.yml** - Validación con funciones de test
- **v5-coronacion-proof-check.yml** - Verificación de prueba V5
- **critical-line-verification.yml** - Verificación de línea crítica

### Tests Específicos
- **test.yml** - Tests de operadores
- **ci_validacion.yml** - Validación CI
- **quick.yml** - Tests rápidos
- **full.yml** - Suite completa de tests

### Análisis Avanzado
- **advanced-validation.yml** - Validación con bibliotecas avanzadas
- **performance-benchmark.yml** - Benchmarks de rendimiento

### Otros
- **lean.yml** - Compilación de formalizaciones Lean
- **latex-and-proof.yml** - LaTeX y pruebas
- **pages.yml** - GitHub Pages
- **monitor.yml** - Monitoreo
- **status.yml** - Estado del proyecto
- **check_unicode.yml** - Verificación Unicode
- **validate-on-push.yml** - Validación en push

## Organización de Triggers

Los workflows nuevos están diseñados para no solaparse con los existentes:

- **ci.yml** - `push` y `pull_request` a `main` (complementa comprehensive-ci.yml)
- **coverage.yml** - `push` y `pull_request` a `main` (reporta a Codecov)
- **proof-check.yml** - Solo cuando cambian archivos Lean (paths: formalization/lean/**)
- **property-tests.yml** - `push` y `pull_request` a `main`
- **dependency-review.yml** - Solo en `pull_request`
- **release.yml** - Solo en tags `v*.*.*`
- **nightly.yml** - Cron diario + manual dispatch

## Recomendaciones

1. Los workflows nuevos son más ligeros y rápidos para feedback inmediato
2. Los workflows existentes (comprehensive-ci.yml) proveen validación profunda
3. Ambos conjuntos pueden coexistir sin conflictos
4. Para desarrollo rápido, usa ci.yml; para validación completa, usa comprehensive-ci.yml

## Secretos Requeridos

- `CODECOV_TOKEN` - Para coverage.yml (opcional en repos públicos)
- `PYPI_TOKEN` - Para release.yml si se habilita publicación a PyPI (opcional)
- `GITHUB_TOKEN` - Provisto automáticamente por GitHub Actions

## Cache Strategy

Todos los workflows nuevos usan cache para:
- Dependencias de pip
- Builds de Lean
- Resultados de compilación

Esto reduce significativamente el tiempo de ejecución.

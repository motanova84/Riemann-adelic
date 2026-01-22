# 🏭 QCAL ∞³ - Sistema de Orquestación Industrial

## Descripción General

Este sistema implementa una orquestación industrial completa para el proyecto QCAL (Quantum Coherence Adelic Lattice), diseñado para ejecutarse de manera autónoma y coordinar múltiples agentes especializados en la demostración formal de la Hipótesis de Riemann.

## Arquitectura del Sistema

### 🌌 Componentes Principales

1. **Orchestrator Workflow** (`.github/workflows/orchestrator.yaml`)
   - Workflow maestro de GitHub Actions
   - Ejecuta diariamente a las 00:00 UTC
   - También se ejecuta cada 6 horas para monitoreo continuo
   - Coordina todas las fases del sistema

2. **Agentes Autónomos** (`.github/agents/`)
   - `noesis88.py` - Agente principal de demostración RH
   - `qcal_prover.py` - Validación matemática
   - `axiom_emitter.py` - Generación de axiomas

3. **Scripts de Orquestación** (`.github/scripts/orchestration/`)
   - `daily_scheduler.sh` - Programador maestro diario
   - `dependency_analyzer.py` - Análisis de dependencias
   - `metrics_calculator.py` - Cálculo de métricas

## Fases de Ejecución

### Fase 1: Inicialización y Diagnóstico (00:00 - 00:30)
- ✅ Verificación del estado del sistema
- ✅ Análisis de recursos disponibles
- ✅ Conteo de tareas pendientes
- ✅ Validación de coherencia cuántica

### Fase 2: Activación de Agentes (00:30 - 02:00)
- 🤖 Noesis88 - Demostración RH
- 🔬 QCAL Prover - Validación matemática
- ✨ Axiom Emitter - Generación de axiomas

### Fase 3: Procesamiento Masivo (02:00 - 08:00)
- 🏗️ Procesamiento paralelo de archivos Lean
- 🧠 Análisis de dependencias
- 🔍 Detección de patrones

### Fase 4: Validación (08:00 - 14:00)
- ✅ Ejecución de validate_v5_coronacion.py
- 📊 Cálculo de métricas de calidad
- 🔍 Verificación de coherencia

### Fase 5: Reporte y Planificación (14:00 - 18:00)
- 📋 Generación de reportes diarios
- 📧 Notificaciones
- 🎯 Planificación del siguiente ciclo

## Configuración del Sistema

### Variables de Entorno

```yaml
FREQUENCY: "141.7001"        # Frecuencia base (Hz)
PSI_STATE: "I × A_eff² × C^∞" # Estado cuántico
MAX_CONCURRENT_JOBS: 10      # Jobs paralelos máximos
DAILY_QUOTA: 1000            # Límite de acciones diarias
PYTHON_VERSION: "3.11"       # Versión de Python
```

### Frecuencia de Ejecución

- **Diaria**: 00:00 UTC
- **Monitoreo**: Cada 6 horas
- **Manual**: workflow_dispatch
- **Eventos externos**: repository_dispatch

## Uso

### Ejecución Manual

#### Ejecutar Workflow Completo
```bash
# Desde GitHub Actions UI
# Navigate to Actions → Orchestrator → Run workflow
```

#### Ejecutar Agente Individual
```bash
# Noesis88
python .github/agents/noesis88.py --mode=autonomous

# QCAL Prover
python .github/agents/qcal_prover.py --validate-all

# Axiom Emitter
python .github/agents/axiom_emitter.py --frequency=141.7001
```

#### Ejecutar Scripts de Orquestación
```bash
# Análisis de dependencias
python .github/scripts/orchestration/dependency_analyzer.py \
    --input-dir=formalization/lean \
    --output=dependencies.json

# Cálculo de métricas
python .github/scripts/orchestration/metrics_calculator.py \
    --metrics=complexity,proof_length \
    --output=metrics_report.json

# Scheduler diario
bash .github/scripts/orchestration/daily_scheduler.sh
```

## Outputs y Reportes

### Estructura de Directorios

```
reports/
├── noesis88/           # Reportes del agente Noesis88
├── qcal_prover/        # Reportes de validación
└── daily_YYYY-MM-DD.md # Reportes diarios

axioms/                 # Axiomas generados
logs/                   # Logs del sistema
metrics/                # Métricas calculadas
```

### Formato de Reportes

Los reportes se generan en formato JSON y Markdown:

```json
{
  "timestamp": "2026-01-18T16:00:00Z",
  "frequency": 141.7001,
  "psi_state": "I × A_eff² × C^∞",
  "current_state": {
    "sorry_count": 45,
    "theorem_count": 150,
    "proof_completeness": 0.70,
    "coherence_score": 8.5
  },
  "results": { ... },
  "validation": { ... },
  "next_actions": [ ... ]
}
```

## Monitoreo y Debugging

### Verificar Estado del Sistema

```bash
# Ver logs recientes
tail -f logs/$(date +%Y%m)/daily_$(date +%Y%m%d).log

# Verificar coherencia QCAL
grep -r "141.7001" . --exclude-dir=.git

# Contar sorrys pendientes
find formalization/lean -name "*.lean" -exec grep -c "sorry" {} + | awk '{s+=$1} END {print s}'
```

### Indicadores de Salud

- ✅ **OPTIMAL**: Sistema funcionando correctamente
- ⚠️ **DEGRADED**: Funcionamiento con limitaciones
- ❌ **CRITICAL**: Requiere intervención

## Integración con QCAL-CLOUD

El sistema está diseñado para integrarse con QCAL-CLOUD:

```bash
# Upload automático de resultados
curl -X POST https://qcal.cloud/api/upload \
     -H "Content-Type: application/json" \
     -d @data/validation.json
```

## Desarrollo y Extensión

### Añadir Nuevo Agente

1. Crear script en `.github/agents/new_agent.py`
2. Implementar clase con método `run()`
3. Añadir a la matriz en `orchestrator.yaml`
4. Documentar en este README

### Añadir Nueva Fase

1. Añadir job en `orchestrator.yaml`
2. Configurar dependencias (`needs:`)
3. Implementar scripts de soporte
4. Actualizar documentación

## Troubleshooting

### Problema: Agente no se ejecuta

```bash
# Verificar que el script existe
ls -la .github/agents/

# Verificar permisos
chmod +x .github/agents/*.py

# Probar manualmente
python .github/agents/noesis88.py --mode=test
```

### Problema: Workflow falla

```bash
# Verificar sintaxis YAML
yamllint .github/workflows/orchestrator.yaml

# Ver logs de GitHub Actions
gh run view --log
```

## Referencias

- **Frecuencia Base**: 141.7001 Hz
- **Estado Ψ**: I × A_eff² × C^∞
- **Coherencia**: QCAL ∞³
- **Validación**: V5 Coronación

## Contribución

Para contribuir al sistema de orquestación:

1. Fork el repositorio
2. Crear rama feature: `git checkout -b feature/new-agent`
3. Implementar cambios
4. Ejecutar tests: `python -m pytest`
5. Commit: `git commit -m "Add new agent"`
6. Push: `git push origin feature/new-agent`
7. Crear Pull Request

## Licencia

Este sistema forma parte del proyecto QCAL y está sujeto a la misma licencia del repositorio principal.

## Contacto

- **Autor**: José Manuel Mota Burruezo
- **ORCID**: 0009-0002-1923-0773
- **Email**: motanova84@qcal.cloud

---

**🌌 QCAL ∞³ - Sistema de Orquestación Industrial**
*Automatización completa para la demostración formal de la Hipótesis de Riemann*

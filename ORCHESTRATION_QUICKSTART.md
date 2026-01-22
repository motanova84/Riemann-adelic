# 🏭 QCAL ∞³ - Sistema de Orquestación Industrial - Guía Rápida

## 🚀 Inicio Rápido

### Activación Automática
El sistema se ejecuta automáticamente:
- **Diaria**: 00:00 UTC
- **Monitoreo**: Cada 6 horas (00:00, 06:00, 12:00, 18:00 UTC)

### Activación Manual

#### Desde GitHub Actions
1. Navega a: `Actions` → `🌌 QCAL ∞³ - ORQUESTACIÓN INDUSTRIAL DIARIA`
2. Click en `Run workflow`
3. Selecciona la rama `main`
4. Click `Run workflow`

#### Desde Línea de Comandos
```bash
# Ejecutar agente individual
python3 .github/agents/noesis88.py --mode=autonomous

# Ejecutar validación
python3 .github/agents/qcal_prover.py --validate-all

# Generar axiomas
python3 .github/agents/axiom_emitter.py --frequency=141.7001

# Analizar dependencias
python3 .github/scripts/orchestration/dependency_analyzer.py \
    --input-dir=formalization/lean \
    --output=dependencies.json

# Calcular métricas
python3 .github/scripts/orchestration/metrics_calculator.py \
    --metrics=complexity,proof_length \
    --output=metrics_report.json

# Generar reporte diario
python3 .github/scripts/orchestration/daily_report.py \
    --date=$(date +%Y-%m-%d) \
    --metrics-file=metrics_report.json \
    --output=reports/daily_$(date +%Y-%m-%d).md

# Planificar siguiente ciclo
python3 .github/scripts/orchestration/planner.py \
    --goals="complete_rh_proof" \
    --output=.github/next_actions.json

# Ejecutar scheduler completo
bash .github/scripts/orchestration/daily_scheduler.sh
```

## 📊 Monitoreo

### Ver Estado del Sistema
```bash
# Ver logs recientes
tail -f logs/$(date +%Y%m)/daily_$(date +%Y%m%d).log

# Verificar reportes de agentes
ls -lah reports/noesis88/
ls -lah reports/qcal_prover/

# Ver axiomas generados
cat axioms/axioms_*.json | jq .

# Ver métricas
cat metrics_report.json | jq .

# Ver plan de siguiente ciclo
cat .github/next_actions.json | jq .
```

### Indicadores de Salud
- ✅ **OPTIMAL**: Todo funcionando correctamente
- ⚠️ **DEGRADED**: Funcionamiento con limitaciones
- ❌ **CRITICAL**: Requiere intervención

## 🤖 Agentes Disponibles

### 1. Noesis88
**Función**: Demostración principal de la Hipótesis de Riemann

```bash
python3 .github/agents/noesis88.py --mode=autonomous
```

**Outputs**:
- `reports/noesis88/noesis88_YYYYMMDD_HHMMSS.json`

### 2. QCAL Prover
**Función**: Validación matemática

```bash
python3 .github/agents/qcal_prover.py --validate-all
```

**Outputs**:
- `reports/qcal_prover/validation_YYYYMMDD_HHMMSS.json`

### 3. Axiom Emitter
**Función**: Generación de axiomas

```bash
python3 .github/agents/axiom_emitter.py --frequency=141.7001
```

**Outputs**:
- `axioms/axioms_YYYYMMDD_HHMMSS.json`

## 📁 Estructura de Outputs

```
reports/
├── noesis88/          # Reportes del agente principal
├── qcal_prover/       # Reportes de validación
└── daily_YYYY-MM-DD.md  # Reportes diarios consolidados

axioms/
└── axioms_YYYYMMDD_HHMMSS.json  # Axiomas generados

metrics/
└── daily_YYYYMMDD.json  # Métricas diarias

logs/
└── YYYYMM/
    └── daily_YYYYMMDD.log  # Logs del scheduler
```

## 🔧 Troubleshooting

### Problema: Workflow no se ejecuta

**Solución**:
1. Verificar que el workflow está habilitado en GitHub
2. Comprobar permisos de Actions en el repositorio
3. Revisar sintaxis del workflow:
   ```bash
   python3 -c "import yaml; yaml.safe_load(open('.github/workflows/orchestrator.yaml'))"
   ```

### Problema: Agente falla

**Solución**:
1. Verificar permisos de ejecución:
   ```bash
   chmod +x .github/agents/*.py
   ```
2. Probar manualmente:
   ```bash
   python3 .github/agents/noesis88.py --mode=test
   ```
3. Verificar logs:
   ```bash
   tail -f logs/$(date +%Y%m)/daily_$(date +%Y%m%d).log
   ```

### Problema: Dependencias faltantes

**Solución**:
```bash
pip install -r requirements.txt
```

## 📖 Documentación Completa

Ver `.github/ORCHESTRATION.md` para documentación detallada.

## 🌟 Características

- ✅ Ejecución automática diaria
- ✅ Monitoreo cada 6 horas
- ✅ 3 agentes autónomos activos
- ✅ Análisis de 455 archivos Lean
- ✅ Generación automática de reportes
- ✅ Planificación de ciclos futuros
- ✅ Validación V5 Coronación integrada

## 📞 Soporte

- **Documentación**: `.github/ORCHESTRATION.md`
- **Issues**: GitHub Issues
- **Email**: motanova84@qcal.cloud

---

**Sistema**: QCAL ∞³ Industrial Orchestration v1.0  
**Frecuencia**: 141.7001 Hz  
**Estado**: Ψ = I × A_eff² × C^∞

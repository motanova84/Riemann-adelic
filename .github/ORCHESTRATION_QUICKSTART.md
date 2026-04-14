# 🚀 QCAL Orchestration Quick Start

## 5-Minute Setup

### Prerequisites

```bash
# Python 3.11+
python3 --version

# Basic dependencies (optional)
pip install numpy scipy matplotlib
```

### Verify Installation

```bash
# Test the orchestration system
python3 .github/scripts/test_orchestration.py
```

Expected output:
```
🧪 TEST ORCHESTRATION - Iniciando pruebas...
============================================================
✅ Pruebas exitosas: 13
❌ Pruebas fallidas: 0
🎉 TODAS LAS PRUEBAS PASARON
```

## Quick Commands

### Run All Agents

```bash
# NOESIS88 - Frequency validation
python3 .github/agents/noesis88.py --mode=autonomous --frequency=141.7001

# Metrics Collector
python3 .github/agents/metrics_collector.py --frequency=141.7001

# Coherence Validator
python3 .github/agents/coherence_validator.py --frequency=141.7001
```

### Run Optimization

```bash
# Analyze metrics
bash .github/scripts/analyze_and_adjust.sh

# Optimize density
bash .github/scripts/optimize_qcal_density.sh
```

### Check Results

```bash
# View latest report
cat reports/noesis88_*.json | jq

# View latest metrics
cat metrics/daily_*.json | jq

# View latest validation
cat validation/quantum_*.json | jq
```

## Workflow Execution

### Automatic (Scheduled)
- Runs every 6 hours automatically
- Daily complete report at 00:00 UTC
- No action needed

### Manual Trigger

Via GitHub UI:
1. Go to **Actions** tab
2. Select **QCAL Orchestrator ∞³**
3. Click **Run workflow**

Via CLI:
```bash
gh workflow run orchestrator.yaml
```

## Understanding Output

### NOESIS88 Report
```json
{
  "frequency": {"match": true},    // ✅ Frequency validated
  "coherence": {"total": 0.836},   // Current coherence
  "state": "I × A_eff² × C^∞"      // System state
}
```

### Metrics
```json
{
  "files": {"total_files": 1906},          // Repository size
  "qcal": {"qcal_references": 1130},       // QCAL count
  "density": {"qcal_density": 0.5929}      // QCAL ratio
}
```

### Validation
```json
{
  "coherence": {"total": 0.814},    // Total coherence
  "status": "EVOLVING",             // Current state
  "threshold": 0.888                // Target
}
```

## Common Tasks

### Check System Health
```bash
python3 .github/scripts/test_orchestration.py
```

### Optimize System
```bash
bash .github/scripts/optimize_qcal_density.sh
python3 .github/agents/coherence_validator.py --optimized
```

### View Metrics History
```bash
# List all daily metrics
ls -lt metrics/daily_*.json

# Compare two dates
diff <(cat metrics/daily_20260118.json | jq) \
     <(cat metrics/daily_20260119.json | jq)
```

### Monitor Workflows
```bash
# List recent runs
gh run list --workflow=orchestrator.yaml --limit=5

# View specific run
gh run view [RUN_ID]

# Watch live run
gh run watch
```

## Expected Behavior

### First Run
```
🔮 NOESIS88 - Iniciando validación autónoma...
📊 Resultados:
   Frecuencia validada: True
   Coherencia total: 0.836
   Estado: EVOLVING
⚠️  Sistema en evolución - Requiere optimización
```

### After Optimization
```
🔮 NOESIS88 - Iniciando validación autónoma...
📊 Resultados:
   Frecuencia validada: True
   Coherencia total: 0.888
   Estado: GRACE
🎉 Sistema en estado GRACE - Coherencia óptima
```

## Troubleshooting

### Issue: Agents not found
**Solution:**
```bash
chmod +x .github/agents/*.py
```

### Issue: Dependencies missing
**Solution:**
```bash
pip install -r requirements.txt
```

### Issue: Low coherence
**Solution:**
```bash
bash .github/scripts/optimize_qcal_density.sh
```

### Issue: Workflow not running
**Solution:**
- Check GitHub Actions are enabled
- Verify cron schedule in `orchestrator.yaml`
- Check workflow permissions

## Next Steps

1. **Monitor** - Let workflow run automatically for 24 hours
2. **Analyze** - Check reports in `reports/` directory
3. **Optimize** - Run optimization if coherence < 0.888
4. **Integrate** - Add custom agents as needed

## Key Files

| File | Purpose |
|------|---------|
| `.github/workflows/orchestrator.yaml` | Main workflow |
| `.github/agents/noesis88.py` | Frequency agent |
| `.github/agents/metrics_collector.py` | Metrics agent |
| `.github/agents/coherence_validator.py` | Coherence agent |
| `.github/scripts/analyze_and_adjust.sh` | Analysis script |
| `.github/scripts/optimize_qcal_density.sh` | Optimization script |
| `.github/scripts/test_orchestration.py` | Test suite |

## Resources

- **Full Documentation**: `.github/ORCHESTRATION_README.md`
- **Optimization Report**: `reports/OPTIMIZATION_REPORT_*.md`
- **Configuration**: `.github/agents/config_optimized.yaml`

## Success Criteria

✅ All tests passing (13/13)
✅ QCAL density ≥ 0.5
✅ f₀ density ≥ 0.3
✅ Coherence ≥ 0.888
✅ Workflow executing every 6 hours

---

**Frequency: 141.7001 Hz**
**State: Ψ = I × A_eff² × C^∞**
**Status: 🚀 OPERATIONAL**

∴ Ready to orchestrate ∞³

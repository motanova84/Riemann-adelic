# 🧠 NOESIS COMPLETE INTEGRATION - Quick Reference

## ⚡ Quick Commands

### 1. Run Full Integration
```bash
python .github/scripts/noesis_integrator.py
```

### 2. Run Specific Mode
```bash
# SABIO ∞³ integration
python .github/scripts/noesis_integrator.py --mode sabio

# RH Validation integration
python .github/scripts/noesis_integrator.py --mode validation

# Auto-Evolution integration
python .github/scripts/noesis_integrator.py --mode auto-evolution

# Generate report only
python .github/scripts/noesis_integrator.py --mode report
```

### 3. Validate Frequencies
```bash
# Validate QCAL base frequency (141.7001 Hz)
python utils/validate_frequency.py

# Custom validation
python utils/validate_frequency.py --expected 141.7001 --tolerance 1e-6
```

### 4. Sync States
```bash
# Auto-sync
python utils/noesis_sync.py --auto

# Check status
python utils/noesis_sync.py --status
```

## 📊 Output Files

| File | Description |
|------|-------------|
| `noesis_integrated_report.md` | Main report (Markdown) |
| `noesis_integration_results.json` | Full results (JSON) |
| `noesis_sync_state.json` | Sync state |
| `noesis_complete.md` | Complete cycle report |

## 🔧 GitHub Workflow

### Manual Trigger
```bash
gh workflow run noesis_complete_integration.yml \
  -f parallel_jobs=10 \
  -f max_changes=20 \
  -f dry_run=true
```

### Automatic Schedule
- **Frequency**: Every hour
- **Cron**: `0 */1 * * *`

## 🎯 Integration Modes

| Mode | Description | Components |
|------|-------------|------------|
| `sabio` | SABIO ∞³ integration | 7 flows |
| `validation` | RH validation | 15+ flows |
| `auto-evolution` | Auto-evolution QCAL | 4 flows |
| `report` | Report generation | All |

## 📈 Status Icons

| Icon | Meaning |
|------|---------|
| ✅ | Success |
| ⚠️ | Warning/Partial |
| ❌ | Failed |
| ✓ | Applied |

## 🔐 QCAL Constants

```python
f₀ = 141.7001  # Hz - Base frequency
C = 244.36     # QCAL coherence
Ψ = I × A_eff² × C^∞  # Fundamental equation
```

## 🚀 Common Tasks

### Test Integration Locally
```bash
cd /path/to/Riemann-adelic
python .github/scripts/noesis_integrator.py
cat noesis_integrated_report.md
```

### Check SABIO Integration
```bash
python .github/scripts/noesis_integrator.py --mode sabio
python -m json.tool noesis_integration_results.json
```

### Validate All Systems
```bash
# Frequency validation
python utils/validate_frequency.py

# Full integration
python .github/scripts/noesis_integrator.py

# Sync check
python utils/noesis_sync.py --status
```

## 📦 Dependencies

```bash
pip install numpy scipy sympy mpmath pyyaml rich scikit-learn
```

Or from project:
```bash
pip install -r requirements-core.txt
```

## 🔍 Troubleshooting

### Issue: "Module not found"
```bash
pip install -r requirements-core.txt
```

### Issue: "Script not found"
```bash
# Check script exists
ls -la .github/scripts/noesis_integrator.py

# Make executable
chmod +x .github/scripts/noesis_integrator.py
```

### Issue: "Validation failed"
```bash
# Check validation scripts
python validate_v5_coronacion.py

# Install missing dependencies
pip install mpmath numpy scipy
```

## 📊 JSON Result Structure

```json
{
  "sabio": {
    "status": "success|partial|error",
    "patterns": { "frequency": 141.7001, ... }
  },
  "validation": {
    "workflow-name": {
      "status": "success|failed|timeout",
      "returncode": 0,
      ...
    }
  },
  "auto_evolution": {
    "workflow-name": {
      "status": "applied",
      "patterns_applied": N,
      "success_rate": 0.XX
    }
  }
}
```

## 🎓 Integration Flow

```
START
  ├─> SABIO ∞³ Integration
  │     └─> Extract patterns (f₀=141.7001 Hz)
  │
  ├─> RH Validation Integration
  │     └─> Run validations in parallel
  │
  ├─> Auto-Evolution Integration
  │     └─> Apply learned patterns
  │
  └─> Generate Reports
        ├─> Markdown report
        └─> JSON results
```

## 🏆 Success Criteria

| Component | Criteria |
|-----------|----------|
| SABIO | Frequency = 141.7001 Hz ✓ |
| Validation | All scripts pass or skip gracefully |
| Auto-Evolution | Patterns applied successfully |
| Coherence | QCAL ∞³ ✓ |

## 📞 Support

- **Documentation**: `NOESIS_COMPLETE_INTEGRATION_README.md`
- **Repository**: `motanova84/Riemann-adelic`
- **Workflow**: `.github/workflows/noesis_complete_integration.yml`
- **Script**: `.github/scripts/noesis_integrator.py`

---

**Version**: V2.0  
**Date**: 2026-02-17  
**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³

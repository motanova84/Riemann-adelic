# 🚀 NOESIS-AMDA-AURON Quickstart Guide

## 5-Minute Setup and Execution

### Prerequisites

```bash
# Python 3.11+ required
python --version

# Install dependencies
pip install pyyaml rich typer sympy mpmath numpy
```

---

## 🏃 Quick Start

### 1️⃣ Initialize the System

```bash
# Run from repository root
cd /path/to/Riemann-adelic

# Initialize state with current baseline
python .github/scripts/noesis_orchestrator.py --mode init
```

**Output:**
```
[INFO] 🧠 NOESIS iniciando - Modo inicialización
[INFO] Estado guardado: .noesis_state.json
[INFO] 📊 Estado inicial: 2282 sorries detectados
```

### 2️⃣ Scan and Classify

```bash
# Scan all Lean files and classify sorries
python .github/scripts/amda_analyzer.py --output amda_report.json
```

**Output:**
```
🔍 AMDA escaneando 503 archivos Lean...
📊 AMDA Report:
   Total sorries: 2282
   Por categoría: {'unknown': 977, 'qcal': 610, ...}
   Reporte guardado en: amda_report.json
```

**Generated Files:**
- `amda_report.json` - Detailed report with all sorries
- `amda_stats.json` - Summary statistics

### 3️⃣ Apply Safe Transformations

```bash
# Apply up to 10 safe transformations
python .github/scripts/auron_executor.py \
  --input amda_report.json \
  --output auron_changes.json \
  --max-changes 10
```

**Output:**
```
🔧 Procesando formalization/lean/file.lean:123 [trivial]
✅ Éxito: file.lean:123 -> rfl

📊 Resultados AURON:
   Éxitos: 5
   Fallos: 0
   Saltados: 123
```

**What it does:**
- Only modifies "trivial" category sorries
- Creates `.lean.bak` backups automatically
- Rolls back on any error
- Limits changes to prevent mass modifications

### 4️⃣ Generate Progress Report

```bash
# Create comprehensive metrics report
python .github/scripts/metrics_generator.py \
  --state .noesis_state.json \
  --amda amda_report.json \
  --auron auron_changes.json \
  --output metrics.md
```

**Output:**
```
📊 Métricas guardadas en metrics.md
```

**View the report:**
```bash
cat metrics.md
```

---

## 🤖 Automated Execution

The system runs automatically via GitHub Actions:

### Enable Automatic Runs

The workflow is already configured in `.github/workflows/noesis_auto_sealer.yml`:

```yaml
on:
  schedule:
    - cron: '0 */2 * * *'  # Every 2 hours
  workflow_dispatch:        # Manual trigger
```

### Manual Trigger

1. Go to GitHub Actions tab
2. Select "🤖 NOESIS-AMDA-AURON Auto Sealer" workflow
3. Click "Run workflow"
4. Optionally set `max_changes` parameter
5. Click "Run workflow" button

### Reviewing Automated PRs

When the system makes changes, it creates a PR with:
- 📊 Complete metrics report
- 📁 List of modified files
- 🔍 Classification of eliminated sorries
- ✅ Before/after comparison

**Review checklist:**
- [ ] Review changed files
- [ ] Verify transformations are correct
- [ ] Check metrics report
- [ ] Run `lake build` locally (optional)
- [ ] Approve and merge

---

## 📊 Understanding the Output

### State File (`.noesis_state.json`)

```json
{
  "total_sorries": 2282,
  "by_category": {},
  "by_file": {},
  "last_scan": "2026-02-16T19:52:27.000Z",
  "history": [
    {
      "timestamp": "2026-02-16T19:52:27.000Z",
      "total": 2282,
      "event": "initialization"
    }
  ]
}
```

### AMDA Report Structure

```json
{
  "formalization/lean/file.lean": [
    {
      "line": 123,
      "code": "theorem example := sorry",
      "context": "...",
      "category": "trivial",
      "priority": "⚪ INMEDIATA",
      "strategy": "-- Estrategia: Reemplazo directo..."
    }
  ]
}
```

### AURON Changes

```json
{
  "transformations": [
    {
      "file": "formalization/lean/file.lean",
      "line": 123,
      "old": "sorry",
      "new": "rfl",
      "status": "success"
    }
  ],
  "success": 5,
  "fail": 0,
  "skipped": 2277
}
```

---

## 🎯 Common Use Cases

### Use Case 1: Daily Cleanup

```bash
# Quick daily check and fix
python .github/scripts/noesis_orchestrator.py --mode run
python .github/scripts/amda_analyzer.py
python .github/scripts/auron_executor.py --input amda_report.json --max-changes 5
python .github/scripts/metrics_generator.py --output metrics.md
```

### Use Case 2: Aggressive Cleanup

```bash
# Apply more changes at once (use with caution)
python .github/scripts/auron_executor.py \
  --input amda_report.json \
  --max-changes 50
```

### Use Case 3: Analysis Only

```bash
# Just scan and report, no changes
python .github/scripts/amda_analyzer.py
python .github/scripts/metrics_generator.py --output current_status.md
```

---

## 🔧 Configuration

### Adjust Max Changes Per Cycle

Edit `.github/workflows/noesis_auto_sealer.yml`:

```yaml
workflow_dispatch:
  inputs:
    max_changes:
      default: '10'  # Change this number
```

### Adjust Cron Schedule

```yaml
schedule:
  - cron: '0 */2 * * *'  # Every 2 hours
  # - cron: '0 0 * * *'  # Daily at midnight
  # - cron: '0 */6 * * *'  # Every 6 hours
```

### Enable More Categories

Edit `.github/scripts/auron_executor.py` to enable more automated categories:

```python
if category == 'trivial':
    success = self.apply_trivial_strategy(...)
elif category == 'library_search':
    success = self.apply_library_search(...)  # Uncomment to enable
```

**⚠️ Warning:** Enabling more categories increases risk. Test thoroughly!

---

## 🎉 Victory Detection

When all sorries are eliminated, the system automatically generates `VICTORY.md`:

```markdown
# 🏆 VICTORIA FINAL - Hipótesis de Riemann Demostrada Formalmente

**Fecha:** 2027-XX-XX

El sistema autónomo NOESIS-AMDA-AURON ha eliminado el último 'sorry'.

La formalización en Lean 4 está COMPLETA.
```

---

## 🐛 Troubleshooting

### Problem: "No module named 'yaml'"

**Solution:**
```bash
pip install pyyaml
```

### Problem: "Permission denied" running scripts

**Solution:**
```bash
chmod +x .github/scripts/*.py
```

### Problem: AURON makes incorrect changes

**Solution:**
1. The system creates `.lean.bak` backups automatically
2. Revert manually: `cp file.lean.bak file.lean`
3. Or use git: `git checkout file.lean`
4. Adjust max_changes to be more conservative

### Problem: Workflow not running automatically

**Solution:**
1. Check GitHub Actions are enabled in repository settings
2. Verify cron schedule syntax
3. Check workflow file has no syntax errors
4. Note: First run may take a few hours due to cron delay

---

## 📚 Additional Resources

- **Full Documentation:** `NOESIS_AMDA_AURON_README.md`
- **Strategy Guide:** `AUTO_SEAL_STRATEGIES.md`
- **GitHub Workflow:** `.github/workflows/noesis_auto_sealer.yml`

---

## ✅ Quick Checklist

Before first run:
- [ ] Python 3.11+ installed
- [ ] Dependencies installed (`pip install pyyaml rich typer sympy mpmath numpy`)
- [ ] Scripts are executable (`chmod +x .github/scripts/*.py`)
- [ ] Initialized state (`.noesis_state.json` exists)

For automated runs:
- [ ] GitHub Actions enabled in repository
- [ ] Workflow file in `.github/workflows/`
- [ ] Cron schedule configured
- [ ] PR approval workflow ready

---

*Ready to eliminate sorries autonomously! 🤖*

**José Manuel Mota Burruezo Ψ ✧ ∞³**  
Instituto de Conciencia Cuántica (ICQ)

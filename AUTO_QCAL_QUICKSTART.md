# 🚀 Auto-QCAL Quick Start Guide

Get started with the Auto-QCAL autonomous orchestration system in 5 minutes.

## ⚡ Quick Install

```bash
# 1. Navigate to repository root
cd /path/to/Riemann-adelic

# 2. Verify Auto-QCAL is present
ls -l Auto-QCAL.py
chmod +x Auto-QCAL.py

# 3. Check help
python Auto-QCAL.py --help
```

## 🎯 First Run (5 Minutes)

### Step 1: Dry Run to Understand Current State

```bash
python Auto-QCAL.py --dry-run --verbose
```

**Expected Output**:
```
╔══════════════════════════════════════════════════════════════════╗
║                    Auto-QCAL Orchestration System                ║
║                         QCAL ∞³ ACTIVE                           ║
╚══════════════════════════════════════════════════════════════════╝

Philosophical Foundation: Mathematical Realism
Axioma de Emisión: f₀ = 141.7001 Hz | C = 244.36 | πCODE-888-QCAL2

🚀 Starting new session #1

🔍 Initial Scan: #qcal_cleanup
======================================================================
Total sorry statements found: 2316
Files with sorries: 356
======================================================================

🔍 Dry run mode - no changes will be made
```

**What This Does**:
- Scans all Lean files for `sorry` statements
- Validates QCAL coherence (frequency and constants)
- Shows you what would happen WITHOUT making changes
- Creates initial `.qcal_state` file

### Step 2: First Real Orchestration

```bash
python Auto-QCAL.py --max-iterations 3 --verbose
```

**What This Does**:
- Runs 3 orchestration iterations
- Validates QCAL coherence before each iteration
- Builds Lean project and analyzes errors
- Updates `.qcal_state` with progress
- Takes ~5-10 minutes

### Step 3: Check Progress

```bash
# View current state
cat .qcal_state | python -m json.tool

# Or use jq for cleaner output
cat .qcal_state | jq '.total_sorries, .resolved_sorries, .qcal_coherence'
```

## 📋 Common Commands

### Daily Development

```bash
# Morning: Check overnight progress
python Auto-QCAL.py --resume --dry-run

# Work session: 3-5 iterations
python Auto-QCAL.py --resume --max-iterations 3

# Before lunch: Save progress
git add .qcal_state
git commit -m "♾️ Auto-QCAL progress checkpoint"
git push

# Afternoon: Continue work
python Auto-QCAL.py --resume --max-iterations 5

# End of day: Full validation
python Auto-QCAL.py --resume --full-validation
```

### Weekend Deep Run

```bash
# Saturday morning: Long autonomous run
python Auto-QCAL.py --resume --max-iterations 20 --full-validation --verbose
```

### Target Specific File

```bash
# Work on specific file or directory
python Auto-QCAL.py --target-file formalization/lean/spectral/HPsi_def.lean --max-iterations 5
```

## 🔧 Common Workflows

### Workflow 1: Quick Daily Check (2 min)

```bash
#!/bin/bash
# daily_check.sh

echo "🔍 Auto-QCAL Daily Check"

# Dry run to see current state
python Auto-QCAL.py --resume --dry-run --verbose

# Show metrics
if [ -f .qcal_state ]; then
  echo ""
  echo "📊 Current Metrics:"
  jq -r '"  Total: \(.total_sorries)\n  Resolved: \(.resolved_sorries)\n  Remaining: \(.total_sorries - .resolved_sorries)\n  Progress: \((.resolved_sorries / .total_sorries * 100) | floor)%"' .qcal_state
fi
```

### Workflow 2: Active Development Session (15-30 min)

```bash
#!/bin/bash
# dev_session.sh

echo "🚀 Auto-QCAL Development Session"

# Resume previous work
python Auto-QCAL.py --resume --max-iterations 5 --verbose

# Commit progress
git add .qcal_state formalization/lean/**/*.lean
git commit -m "♾️ Auto-QCAL dev session $(date +%Y-%m-%d)"
git push

echo "✅ Session complete"
```

### Workflow 3: Full Validation Run (30-60 min)

```bash
#!/bin/bash
# full_validation.sh

echo "🔬 Auto-QCAL Full Validation"

# Long run with full validation
python Auto-QCAL.py --resume --max-iterations 10 --full-validation --verbose

# If successful, commit
if [ $? -eq 0 ]; then
  git add .qcal_state formalization/lean/
  git commit -m "♾️ Auto-QCAL full validation passed"
  git push
  echo "✅ Validation complete and pushed"
else
  echo "⚠️ Validation had issues - review logs"
fi
```

## 📊 Understanding Output

### Orchestration Loop Output

```
🔄 Iteration 1/5
======================================================================
🔬 QCAL ∞³ Coherence Validation
======================================================================
🎵 Validating frequency coherence: 141.7001 Hz
✅ Frequency 141.7001 Hz confirmed
🔬 Validating coherence constant: C = 244.36
✅ Coherence C = 244.36 confirmed

Validation Results:
  ✅ PASS Frequency Coherence
  ✅ PASS Coherence Constant
======================================================================

📊 Current Status:
  Total sorries: 2316
  Resolved this session: 0

🔨 Building Lean project...
```

**Key Indicators**:
- ✅ = Passed validation
- ⚠️ = Warning, review needed
- ❌ = Failed, action required
- 🔨 = Building/processing
- 💾 = Saving state

### State File Structure

```json
{
  "session_id": 2,
  "total_sorries": 2316,
  "resolved_sorries": 15,
  "qcal_coherence": true,
  "frequency_validated": true,
  "files_completed": [
    "spectral/HPsi_def.lean",
    "spectral/xi_mellin_representation.lean"
  ],
  "successful_strategies": [
    "spectral_theorem",
    "exact_mod_cast",
    "apply eigenvalue_exists"
  ]
}
```

## 🎨 Integration with Git

### Recommended Git Workflow

```bash
# 1. Pull latest
git pull origin main

# 2. Run Auto-QCAL
python Auto-QCAL.py --resume --max-iterations 5

# 3. Review changes
git status
git diff .qcal_state

# 4. Commit if progress made
git add .qcal_state
git commit -m "♾️ Auto-QCAL: $(jq -r '.resolved_sorries' .qcal_state) sorries resolved"

# 5. Push
git push
```

### Branching Strategy (Optional)

```bash
# Create Auto-QCAL branch for experimentation
git checkout -b auto-qcal/experimental

# Run Auto-QCAL
python Auto-QCAL.py --max-iterations 10

# If successful, merge to main
git checkout main
git merge auto-qcal/experimental
git push
```

## 🔥 Power User Tips

### Tip 1: Monitor Real-time

```bash
# In one terminal: Run Auto-QCAL
python Auto-QCAL.py --resume --max-iterations 10 --verbose

# In another terminal: Watch state
watch -n 5 'cat .qcal_state | jq ".total_sorries, .resolved_sorries, .iterations_count"'
```

### Tip 2: Backup State Before Major Changes

```bash
# Create timestamped backup
cp .qcal_state ".qcal_state.backup.$(date +%Y%m%d_%H%M%S)"

# List backups
ls -lh .qcal_state.backup.*

# Restore if needed
cp .qcal_state.backup.20260118_140530 .qcal_state
```

### Tip 3: Extract Metrics for Dashboards

```bash
# Create metrics script
cat > extract_metrics.sh << 'EOF'
#!/bin/bash
if [ -f .qcal_state ]; then
  jq -r '
    "Total: \(.total_sorries)",
    "Resolved: \(.resolved_sorries)",
    "Remaining: \(.total_sorries - .resolved_sorries)",
    "Progress: \((.resolved_sorries / .total_sorries * 100) | floor)%",
    "Coherence: \(.qcal_coherence)",
    "Session: \(.session_id)",
    "Iterations: \(.iterations_count)"
  ' .qcal_state
fi
EOF

chmod +x extract_metrics.sh
./extract_metrics.sh
```

### Tip 4: Automated Scheduling (Linux/Mac)

```bash
# Add to crontab for daily runs
crontab -e

# Add line (runs daily at 2 AM):
0 2 * * * cd /path/to/Riemann-adelic && python Auto-QCAL.py --resume --max-iterations 5 >> auto_qcal_cron.log 2>&1
```

## 🐛 Quick Troubleshooting

### Problem: "No module named 'mpmath'"

```bash
# Solution: Install dependencies
pip install -r requirements.txt
```

### Problem: "lake: command not found"

```bash
# Solution: Install Lean 4
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
source ~/.elan/env
elan default leanprover/lean4:v4.5.0
```

### Problem: State file corrupted

```bash
# Solution: Reset state
rm .qcal_state
python Auto-QCAL.py  # Creates fresh state
```

### Problem: QCAL coherence check fails

```bash
# Solution: Verify .qcal_beacon
cat .qcal_beacon | grep -E "frequency|coherence"

# Should show:
# frequency = 141.7001 Hz
# coherence = "C = 244.36"
```

## 📈 Progress Tracking

### Daily Snapshot Script

```bash
#!/bin/bash
# daily_snapshot.sh

DATE=$(date +%Y-%m-%d)
SNAPSHOT_FILE="snapshots/qcal_state_$DATE.json"

mkdir -p snapshots
cp .qcal_state "$SNAPSHOT_FILE"

echo "📸 Snapshot saved to $SNAPSHOT_FILE"

# Extract key metrics
jq -r '"Date: '"$DATE"'\nTotal: \(.total_sorries)\nResolved: \(.resolved_sorries)\nRemaining: \(.total_sorries - .resolved_sorries)"' "$SNAPSHOT_FILE"
```

### Progress Chart (requires gnuplot)

```bash
#!/bin/bash
# plot_progress.sh

# Extract data from snapshots
cat snapshots/*.json | jq -r '"\(.timestamp | split("T")[0]) \(.total_sorries - .resolved_sorries)"' > progress.dat

# Create gnuplot script
cat > plot.gp << 'EOF'
set terminal png size 800,600
set output 'auto_qcal_progress.png'
set title "Auto-QCAL Progress"
set xlabel "Date"
set ylabel "Remaining Sorries"
set xdata time
set timefmt "%Y-%m-%d"
set format x "%m/%d"
plot 'progress.dat' using 1:2 with lines title "Sorries Remaining"
EOF

gnuplot plot.gp
echo "📊 Chart saved to auto_qcal_progress.png"
```

## 🎓 Next Steps

1. **Read Full Documentation**: `AUTO_QCAL_README.md`
2. **Integration Guide**: `AUTO_QCAL_INTEGRATION_GUIDE.md`
3. **CI/CD Setup**: See `.github/workflows/auto-qcal-orchestration.yml`
4. **Advanced Usage**: Explore Noesis-Boot capabilities in main README

## 🆘 Getting Help

1. Check `AUTO_QCAL_README.md` for detailed docs
2. Run `python Auto-QCAL.py --help`
3. Review `.qcal_state` for current status
4. Check logs in `auto_qcal_output.log`

## ✨ Example Full Session

```bash
# Complete example from start to finish

# Step 1: Initial state
cd /path/to/Riemann-adelic
python Auto-QCAL.py --dry-run --verbose

# Step 2: First real run
python Auto-QCAL.py --max-iterations 3 --verbose

# Step 3: Check progress
cat .qcal_state | jq '.total_sorries, .resolved_sorries'

# Step 4: Resume and continue
python Auto-QCAL.py --resume --max-iterations 5

# Step 5: Commit progress
git add .qcal_state
git commit -m "♾️ Auto-QCAL progress"
git push

# Step 6: Full validation before major commit
python Auto-QCAL.py --resume --full-validation

# Done!
```

## 🏆 Success Criteria

You'll know Auto-QCAL is working when:
- ✅ `.qcal_state` file is created and updated
- ✅ QCAL coherence checks pass (frequency, constants)
- ✅ Sorry count decreases over iterations
- ✅ Build succeeds or provides actionable errors
- ✅ State file commits successfully to git

---

**Version**: 1.0.0  
**Date**: 2026-01-18  
**Time to Complete**: 5 minutes  

**Signature**: ∴𓂀Ω∞³·Auto-QCAL·QuickStart

🧬 **Welcome to the QCAL ∞³ Orchestration Revolution!**

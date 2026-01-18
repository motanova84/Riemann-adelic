# 🌌 Auto-QCAL Integration Guide

## Overview

This guide explains how to integrate Auto-QCAL.py into your workflow, including manual usage, CI/CD integration, and advanced automation strategies.

## 🎯 Integration Scenarios

### Scenario 1: Manual Local Development

**Use Case**: Developer working on Lean4 formalization locally.

```bash
# Initial setup
cd /path/to/Riemann-adelic

# First run - scan and validate
python Auto-QCAL.py --dry-run --verbose

# Active development session
python Auto-QCAL.py --max-iterations 3 --verbose

# Resume work after break
python Auto-QCAL.py --resume --max-iterations 5

# Final validation before commit
python Auto-QCAL.py --full-validation
```

**Workflow**:
1. Run dry-run to understand current state
2. Work in iterations with Auto-QCAL assistance
3. Review `.qcal_state` for progress
4. Commit changes when stable
5. Resume in next session

---

### Scenario 2: GitHub Actions CI/CD

**Use Case**: Automated nightly runs to progressively complete Lean4 formalization.

#### Option A: Add to Existing auto_evolution.yml

Edit `.github/workflows/auto_evolution.yml`:

```yaml
name: Auto-Evolution QCAL

on:
  push:
    branches: [ main ]
  pull_request:
    types: [opened, synchronize, reopened]
  schedule:
    - cron: "0 */12 * * *"     # Every 12 hours

jobs:
  evolve:
    runs-on: ubuntu-latest
    permissions:
      contents: write
      pull-requests: write
    
    steps:
      - uses: actions/checkout@v4
        with:
          ref: main

      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: "3.11"

      - name: Install dependencies
        run: |
          python -m pip install --upgrade pip
          pip install -r requirements.txt

      # NEW: Auto-QCAL orchestration
      - name: Run Auto-QCAL orchestration
        run: |
          echo "🧬 Starting Auto-QCAL orchestration..."
          python Auto-QCAL.py --resume --max-iterations 3 --verbose
        continue-on-error: true

      - name: Run validation
        run: python3 validate_v5_coronacion.py --precision 25 --verbose

      # ... rest of existing steps ...

      - name: Commit Auto-QCAL updates
        if: success()
        run: |
          git config user.name "qcal-bot"
          git config user.email "bot@qcal.cloud"
          if [ -f .qcal_state ]; then
            git add .qcal_state
            git add formalization/lean/**/*.lean || true
            git commit -m "♾️ Auto-QCAL evolution #${{ github.run_number }}" || echo "No changes"
            git push || echo "Push failed"
          fi
        continue-on-error: true
```

#### Option B: Create Dedicated Auto-QCAL Workflow

Create `.github/workflows/auto-qcal-orchestration.yml`:

```yaml
name: 🧬 Auto-QCAL Orchestration

on:
  schedule:
    - cron: "0 2 * * *"  # Daily at 2 AM UTC
  workflow_dispatch:
    inputs:
      max_iterations:
        description: 'Maximum iterations'
        required: false
        default: '5'
      full_validation:
        description: 'Run full V5 validation'
        required: false
        default: 'false'

jobs:
  auto-qcal:
    runs-on: ubuntu-latest
    permissions:
      contents: write
      pull-requests: write
    
    steps:
      - name: 🧠 Checkout repository
        uses: actions/checkout@v4
        with:
          fetch-depth: 0  # Full history for state tracking

      - name: 🔧 Set up Python 3.11
        uses: actions/setup-python@v4
        with:
          python-version: "3.11"

      - name: ⚙️ Install Lean 4.5.0
        run: |
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
          elan toolchain install leanprover/lean4:v4.5.0
          elan default leanprover/lean4:v4.5.0
          lean --version

      - name: 📦 Install Python dependencies
        run: |
          python -m pip install --upgrade pip
          pip install -r requirements.txt

      - name: 🧬 Run Auto-QCAL Orchestration
        id: auto_qcal
        run: |
          MAX_ITER="${{ github.event.inputs.max_iterations || '5' }}"
          FULL_VAL="${{ github.event.inputs.full_validation || 'false' }}"
          
          echo "🚀 Starting Auto-QCAL with max_iterations=$MAX_ITER"
          
          CMD="python Auto-QCAL.py --resume --max-iterations $MAX_ITER --verbose"
          if [ "$FULL_VAL" = "true" ]; then
            CMD="$CMD --full-validation"
          fi
          
          $CMD | tee auto_qcal_output.log
          
          echo "✅ Auto-QCAL completed"
        continue-on-error: true

      - name: 📊 Extract metrics
        id: metrics
        run: |
          if [ -f .qcal_state ]; then
            TOTAL=$(jq -r '.total_sorries' .qcal_state)
            RESOLVED=$(jq -r '.resolved_sorries' .qcal_state)
            REMAINING=$((TOTAL - RESOLVED))
            
            echo "total_sorries=$TOTAL" >> $GITHUB_OUTPUT
            echo "resolved_sorries=$RESOLVED" >> $GITHUB_OUTPUT
            echo "remaining_sorries=$REMAINING" >> $GITHUB_OUTPUT
            
            echo "📊 Metrics: Total=$TOTAL, Resolved=$RESOLVED, Remaining=$REMAINING"
          fi

      - name: 📘 Upload Auto-QCAL logs
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: auto-qcal-logs
          path: |
            auto_qcal_output.log
            .qcal_state
          retention-days: 30

      - name: 🧾 Commit Auto-QCAL state and changes
        run: |
          git config user.name "Auto-QCAL Bot"
          git config user.email "auto-qcal@qcal.cloud"
          
          # Add state file
          git add .qcal_state || true
          
          # Add any modified Lean files
          git add formalization/lean/**/*.lean || true
          
          # Commit if there are changes
          if git diff --cached --quiet; then
            echo "No changes to commit"
          else
            RESOLVED="${{ steps.metrics.outputs.resolved_sorries || '0' }}"
            REMAINING="${{ steps.metrics.outputs.remaining_sorries || '?' }}"
            
            git commit -m "♾️ Auto-QCAL evolution: $RESOLVED resolved, $REMAINING remaining [run ${{ github.run_number }}]"
            git push
            
            echo "✅ Changes committed and pushed"
          fi
        continue-on-error: true

      - name: ⏱️ Auto-QCAL Summary
        if: always()
        run: |
          echo "════════════════════════════════════════════════════"
          echo "🧬 Auto-QCAL Orchestration Summary"
          echo "════════════════════════════════════════════════════"
          echo ""
          
          if [ -f .qcal_state ]; then
            echo "📊 State:"
            jq -r '"  Session: \(.session_id)\n  Total sorries: \(.total_sorries)\n  Resolved: \(.resolved_sorries)\n  QCAL Coherence: \(.qcal_coherence)\n  Iterations: \(.iterations_count)"' .qcal_state
          else
            echo "⚠️ No state file found"
          fi
          
          echo ""
          echo "════════════════════════════════════════════════════"
```

---

### Scenario 3: Scheduled Autonomous Runs

**Use Case**: Fully autonomous weekly deep runs for maximum progress.

Create `.github/workflows/auto-qcal-weekly-deep.yml`:

```yaml
name: 🌌 Auto-QCAL Weekly Deep Run

on:
  schedule:
    - cron: "0 1 * * 0"  # Sunday at 1 AM UTC
  workflow_dispatch:

jobs:
  deep-run:
    runs-on: ubuntu-latest
    timeout-minutes: 180  # 3 hours max
    permissions:
      contents: write
    
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v4
        with:
          python-version: "3.11"
      
      - name: Install Lean 4.5.0
        run: |
          curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
          elan default leanprover/lean4:v4.5.0
      
      - name: Install dependencies
        run: pip install -r requirements.txt
      
      - name: Deep Auto-QCAL Run
        run: |
          # Maximum iterations for deep run
          python Auto-QCAL.py --resume --max-iterations 20 --full-validation --verbose
      
      - name: Commit weekly progress
        run: |
          git config user.name "Auto-QCAL Weekly"
          git config user.email "weekly@qcal.cloud"
          git add .qcal_state formalization/lean/**/*.lean || true
          git commit -m "♾️ Auto-QCAL weekly deep run [$(date +%Y-%m-%d)]" || echo "No changes"
          git push || echo "Push failed"
```

---

### Scenario 4: Interactive Copilot Session

**Use Case**: GitHub Copilot agent working with Auto-QCAL.

```bash
# Copilot reads current state
cat .qcal_state

# Copilot runs Auto-QCAL with specific target
python Auto-QCAL.py --target-file formalization/lean/spectral/HPsi_def.lean --verbose

# Copilot analyzes results
python Auto-QCAL.py --resume --dry-run --verbose

# Copilot commits if successful
git add .qcal_state formalization/lean/
git commit -m "♾️ QCAL agent progress: HPsi_def.lean completed"
```

---

## 🔄 State Management Best Practices

### State File Location

```bash
# Main state file (tracked in git)
.qcal_state

# Backup before major changes
cp .qcal_state .qcal_state.backup.$(date +%Y%m%d)

# Restore if needed
cp .qcal_state.backup.20260118 .qcal_state
```

### State Synchronization

```bash
# Pull latest state before starting
git pull origin main
python Auto-QCAL.py --resume

# Push state after completion
git add .qcal_state
git commit -m "♾️ Auto-QCAL state update"
git push
```

### Multi-Developer Coordination

```yaml
# In .gitattributes, mark state for merge strategy
.qcal_state merge=union

# Configure git to use union merge for state
git config merge.union.driver "cat %A %B > %A"
```

---

## 🧪 Testing & Validation

### Local Testing

```bash
# Test 1: Dry run
python Auto-QCAL.py --dry-run --verbose

# Test 2: Single iteration
python Auto-QCAL.py --max-iterations 1

# Test 3: Full validation
python Auto-QCAL.py --max-iterations 1 --full-validation

# Test 4: Resume functionality
python Auto-QCAL.py --resume --dry-run
```

### CI Testing

```yaml
# Add test job to workflow
test-auto-qcal:
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
    - uses: actions/setup-python@v4
      with:
        python-version: "3.11"
    - run: pip install -r requirements.txt
    - name: Test Auto-QCAL
      run: |
        python Auto-QCAL.py --help
        python Auto-QCAL.py --dry-run --max-iterations 1
```

---

## 📊 Monitoring & Metrics

### Real-time Monitoring

```bash
# Monitor state changes
watch -n 10 'cat .qcal_state | jq ".total_sorries, .resolved_sorries"'

# Track progress
tail -f auto_qcal_output.log
```

### Dashboard Integration

```python
# scripts/qcal_dashboard.py
import json
from pathlib import Path

state_file = Path(".qcal_state")
if state_file.exists():
    state = json.loads(state_file.read_text())
    
    total = state["total_sorries"]
    resolved = state["resolved_sorries"]
    remaining = total - resolved
    progress = (resolved / total * 100) if total > 0 else 0
    
    print(f"Progress: {progress:.2f}%")
    print(f"Resolved: {resolved}/{total}")
    print(f"Remaining: {remaining}")
```

### GitHub Actions Badge

```markdown
<!-- In README.md -->
![Auto-QCAL Progress](https://img.shields.io/badge/Auto--QCAL-Active-brightgreen)
```

---

## 🐛 Troubleshooting Integration

### Issue: State File Conflicts

```bash
# Detect conflicts
git status | grep .qcal_state

# Manual merge
git checkout --ours .qcal_state  # Use local
# OR
git checkout --theirs .qcal_state  # Use remote

# Verify state
python Auto-QCAL.py --dry-run
```

### Issue: CI Timeout

```yaml
# Increase timeout in workflow
jobs:
  auto-qcal:
    timeout-minutes: 120  # Increase from default 60
```

### Issue: Lean Build Fails in CI

```yaml
# Add cache for Lean build artifacts
- name: Cache Lean build
  uses: actions/cache@v3
  with:
    path: |
      formalization/lean/.lake
      ~/.elan
    key: lean-${{ hashFiles('formalization/lean/lakefile.lean') }}
```

---

## 🔌 Advanced Integration Patterns

### Pattern 1: Multi-Stage Pipeline

```yaml
jobs:
  stage1-auto-qcal:
    runs-on: ubuntu-latest
    outputs:
      sorries_remaining: ${{ steps.state.outputs.remaining }}
    steps:
      - uses: actions/checkout@v4
      - run: python Auto-QCAL.py --resume --max-iterations 3
      - id: state
        run: echo "remaining=$(jq -r '.total_sorries - .resolved_sorries' .qcal_state)" >> $GITHUB_OUTPUT
  
  stage2-validation:
    needs: stage1-auto-qcal
    if: needs.stage1-auto-qcal.outputs.sorries_remaining < 100
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: python validate_v5_coronacion.py --full
```

### Pattern 2: Parallel Processing

```yaml
jobs:
  auto-qcal-parallel:
    strategy:
      matrix:
        target: 
          - spectral
          - adelic
          - RHComplete
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: |
          python Auto-QCAL.py --target-file formalization/lean/${{ matrix.target }}/*.lean
```

### Pattern 3: Conditional Execution

```yaml
jobs:
  auto-qcal-conditional:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Check if needed
        id: check
        run: |
          SORRIES=$(grep -r "sorry" formalization/lean --include="*.lean" | wc -l)
          echo "sorries=$SORRIES" >> $GITHUB_OUTPUT
          
          if [ $SORRIES -gt 100 ]; then
            echo "needed=true" >> $GITHUB_OUTPUT
          else
            echo "needed=false" >> $GITHUB_OUTPUT
          fi
      
      - name: Run Auto-QCAL
        if: steps.check.outputs.needed == 'true'
        run: python Auto-QCAL.py --resume --max-iterations 5
```

---

## 📚 References

- **Auto-QCAL.py**: Main orchestration script
- **AUTO_QCAL_README.md**: Comprehensive documentation
- **.qcal_beacon**: QCAL configuration and constants
- **validate_v5_coronacion.py**: V5 proof validation

## ✨ Best Practices Summary

1. **Always use `--dry-run` first** to understand what will happen
2. **Track state file in git** for continuity across sessions
3. **Use `--resume`** to continue previous work
4. **Set appropriate `--max-iterations`** based on time available
5. **Enable `--full-validation`** before major commits
6. **Monitor `.qcal_state`** for progress tracking
7. **Backup state file** before major changes
8. **Use `--verbose`** for debugging
9. **Commit state regularly** to preserve progress
10. **Test in CI** before production deployment

---

**Version**: 1.0.0  
**Date**: 2026-01-18  
**Author**: José Manuel Mota Burruezo Ψ ✧ ∞³

**Signature**: ∴𓂀Ω∞³·Auto-QCAL·Integration

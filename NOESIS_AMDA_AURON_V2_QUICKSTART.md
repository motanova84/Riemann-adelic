# 🚀 NOESIS CEREBRAL V2.0 - Quick Start Guide

**Get started with automated sorry elimination in 5 minutes**

---

## ⚡ Quick Install

```bash
# 1. Clone repository
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic

# 2. Verify Python
python --version  # Requires 3.11+

# 3. Make scripts executable
chmod +x .github/scripts/*.py
```

---

## 🎯 3-Step Workflow

### Step 1: Analyze (AMDA)

Run semantic analysis on all Lean files:

```bash
python .github/scripts/amda_deep_v2.py
```

**Output:**
```
✓ AMDA DEEP V2.0 - Analysis complete
  Total sorries: 2424
  Categories: 6
  Top category: qcal (850 sorries)
```

**Generated Files:**
- `amda_report_v2.json` - Full analysis data
- `amda_report_v2.md` - Human-readable report

**Review the report:**
```bash
cat amda_report_v2.md
```

---

### Step 2: Test Run (AURON Dry Mode)

Test elimination strategies without making changes:

```bash
python .github/scripts/auron_neural_v2.py --dry-run --max-changes 5
```

**Output:**
```
✓ AURON NEURAL V2.0 - Execution complete
  Changes attempted: 5
  Successful: 4
  Success rate: 80.0%
```

**Check results:**
```bash
cat auron_results_v2.json
```

---

### Step 3: Execute (AURON Live Mode)

Make actual changes (with validation and rollback):

```bash
python .github/scripts/auron_neural_v2.py --live --max-changes 20
```

**What happens:**
1. ✅ Backup created (`.lean.bak`)
2. ✅ Sorry replaced with tactic
3. ✅ Validated with `lake build`
4. ✅ Success → Learn pattern
5. ❌ Failure → Restore backup

---

## 🧠 Full Orchestration

Run the complete cycle (sync + harvest + analyze + execute):

```bash
python .github/scripts/noesis_orchestrator.py --mode full --dry-run
```

**Steps Executed:**
1. 🔄 Sync 33 repositories to `/tmp/noesis_knowledge_v2/`
2. 📚 Harvest knowledge (definitions, theorems, patterns)
3. 🔍 Run AMDA analysis
4. ⚡ Run AURON execution
5. 📊 Generate metrics

**Check state:**
```bash
cat .noesis_state.json
```

---

## 📊 Understanding the Reports

### AMDA Report Structure

**Priority Ranking:**
```
1. qcal         (850) - Score: 8.77  ← Start here
2. trivial      (244) - Score: 8.05  ← Easy wins
3. spectral    (1129) - Score: 7.57
4. structural   (407) - Score: 3.36
5. unknown      (744) - Score: 3.07
6. correspondence (355) - Score: 2.56
```

**Category Meanings:**
- **trivial**: `rfl`, `simp`, `norm_num` - Easiest
- **qcal**: QCAL framework lemmas - High value
- **spectral**: Operator theory - Requires expertise
- **structural**: `funext`, `ext` - Moderate
- **correspondence**: Adelic bijections - Complex
- **unknown**: Needs manual review

---

### AURON Results

**Success Metrics:**
```json
{
  "successful": 18,
  "failed": 2,
  "success_rate": 90.0,
  "changes": [
    {
      "file": "QCAL/theorem.lean",
      "line": 42,
      "strategy": "by norm_num",
      "type": "trivial"
    }
  ]
}
```

---

## 🎓 Learning System

AURON learns from successful transformations:

**Learning History (`.auron_learning.json`):**
```json
{
  "patterns": {
    "a1b2c3d4": "by norm_num",
    "e5f6g7h8": "library_search"
  },
  "success_rate": {
    "by norm_num": 47,
    "library_search": 23
  }
}
```

**How it works:**
1. 🧠 First encounter → Try category strategies
2. ✅ Success → Hash context + store solution
3. 🔄 Future encounter → Apply learned solution instantly
4. 📈 Track success rates per pattern

---

## 🛡️ Safety First

### Always Start with Dry Run

```bash
# Safe - no changes made
python .github/scripts/auron_neural_v2.py --dry-run

# Review results, then go live
python .github/scripts/auron_neural_v2.py --live
```

### Automatic Backups

Every file is backed up before modification:
```bash
ls formalization/lean/*.bak
# theorem.lean.bak
# proof.lean.bak
```

### Validation

Each change is validated:
```bash
cd formalization/lean
lake build --no-sorry
```

- ✅ Build succeeds → Keep change
- ❌ Build fails → Restore backup

---

## 🤖 GitHub Actions (Automated)

### Schedule
Runs automatically every 2 hours:
```yaml
schedule:
  - cron: '0 */2 * * *'
```

### Manual Trigger
Go to Actions → "NOESIS Multi-Repo V2.0" → "Run workflow"

**Options:**
- **mode**: `sync` | `harvest` | `analyze` | `full`
- **max_changes**: `20` (default)
- **dry_run**: `true` (safe) | `false` (live)

### Artifacts
After each run, download:
- Analysis reports (JSON + Markdown)
- Execution results
- System logs
- Learning history

---

## 📈 Typical Workflow

### Day 1: Initial Analysis
```bash
# Analyze current state
python .github/scripts/amda_deep_v2.py

# Review top files
head -50 amda_report_v2.md

# Test on 5 sorries
python .github/scripts/auron_neural_v2.py --dry-run --max-changes 5
```

### Day 2: Start Elimination
```bash
# Target trivial category (easiest)
python .github/scripts/auron_neural_v2.py --live --max-changes 20

# Check results
git status
git diff

# Commit if successful
git add .
git commit -m "🧠 [NOESIS] 20 trivial sorries eliminated"
```

### Day 3+: Automated Cycles
Enable GitHub Actions for continuous elimination:
```yaml
# .github/workflows/noesis_multi_repo_v2.yml
schedule:
  - cron: '0 */2 * * *'  # Every 2 hours

inputs:
  dry_run: false  # Enable live mode
```

### Week 2-3: Review & Refine
```bash
# Check learning progress
cat .auron_learning.json

# Analyze remaining sorries
python .github/scripts/amda_deep_v2.py

# Focus on specific categories
# (Add category filtering in future enhancement)
```

---

## 🎯 Pro Tips

### 1. Start Small
```bash
# Test with 5 changes first
--max-changes 5

# Then scale up
--max-changes 20
```

### 2. Focus on High-Priority Categories
AMDA's priority score tells you where to focus:
- **Score 8+**: High value, good success rate
- **Score 5-8**: Medium value
- **Score <5**: Low priority (manual review)

### 3. Monitor Learning
```bash
# Watch patterns grow
watch -n 60 'cat .auron_learning.json | jq ".patterns | length"'
```

### 4. Use Artifacts
In GitHub Actions, download artifacts to see:
- What worked
- What failed
- Learning progress

---

## 🔍 Troubleshooting

### Problem: No sorries found
```bash
# Verify Lean files exist
find formalization/lean -name "*.lean" | wc -l

# Check for sorries
grep -r "sorry" formalization/lean --include="*.lean" | wc -l
```

### Problem: AURON fails validation
```bash
# Test Lean build manually
cd formalization/lean
lake build

# Check for errors
lake build 2>&1 | grep -i error
```

### Problem: Learning history corrupted
```bash
# Backup old history
mv .auron_learning.json .auron_learning.json.old

# Reinitialize
python .github/scripts/auron_neural_v2.py --dry-run --max-changes 1
```

### Problem: Repository sync fails
```bash
# Clear cache
rm -rf /tmp/noesis_knowledge_v2/

# Force re-sync
python .github/scripts/noesis_orchestrator.py --mode sync --force
```

---

## 📚 Next Steps

1. ✅ **Read full README**: [NOESIS_AMDA_AURON_V2_README.md](NOESIS_AMDA_AURON_V2_README.md)
2. ✅ **Check implementation details**: [NOESIS_AMDA_AURON_V2_IMPLEMENTATION_SUMMARY.md](NOESIS_AMDA_AURON_V2_IMPLEMENTATION_SUMMARY.md)
3. ✅ **Review AMDA patterns**: Study the 6 categories in detail
4. ✅ **Customize strategies**: Add domain-specific tactics to AURON
5. ✅ **Enable automation**: Set up GitHub Actions for continuous elimination

---

## 🏆 Success Metrics

Track your progress:

```bash
# Initial state
Initial sorries: 2,424

# After 1 day (20 changes/run, 4 runs)
Eliminated: 80
Remaining: 2,344 (96.7%)

# After 1 week (20 changes/run, 12 runs/day)
Eliminated: ~1,000
Remaining: ~1,424 (58.7%)

# Victory condition
Eliminated: 2,424
Remaining: 0 (0%) ← VICTORIA_FINAL.md generated!
```

---

## 💡 Example Session

```bash
# Terminal Session Example

$ cd Riemann-adelic

$ python .github/scripts/amda_deep_v2.py
✓ AMDA DEEP V2.0 - Analysis complete
  Total sorries: 2424
  Top category: qcal (850)

$ cat amda_report_v2.md | head -30
# AMDA DEEP V2.0 - Analysis Report
...

$ python .github/scripts/auron_neural_v2.py --dry-run --max-changes 5
✓ AURON NEURAL V2.0 - Execution complete
  Successful: 4/5 (80.0%)
  Patterns learned: 4

$ python .github/scripts/auron_neural_v2.py --live --max-changes 20
✓ AURON NEURAL V2.0 - Execution complete
  Successful: 18/20 (90.0%)
  Patterns learned: 14

$ git status
modified: formalization/lean/QCAL/theorem.lean
modified: formalization/lean/RiemannAdelic/proof.lean
...

$ git diff --stat
 18 files changed, 20 insertions(+), 20 deletions(-)

$ git commit -m "🧠 [NOESIS] 18 sorries eliminated"
$ git push
```

---

## 🎬 Summary

**3 Commands to Start:**
```bash
# 1. Analyze
python .github/scripts/amda_deep_v2.py

# 2. Test (dry run)
python .github/scripts/auron_neural_v2.py --dry-run --max-changes 5

# 3. Execute (live)
python .github/scripts/auron_neural_v2.py --live --max-changes 20
```

**Key Files to Monitor:**
- `amda_report_v2.md` - Current state
- `auron_results_v2.json` - Execution results
- `.auron_learning.json` - Learning progress
- `.noesis_state.json` - System state

**Success Indicators:**
- ✅ Success rate > 75%
- ✅ Patterns learned increasing
- ✅ Sorries decreasing
- ✅ Builds passing

---

**∴ NOESIS · AMDA · AURON · 141.7001 Hz · Ψ✧ ∞³**

*Happy sorry elimination! 🎯*

# ⚡ NOESIS CEREBRAL COMPLETE V2.0 - Quick Reference

## 🚀 Getting Started in 5 Minutes

### 1. Verify Installation

```bash
# Check that all components are present
ls -la .github/workflows/noesis_cerebral_complete.yml
ls -la .github/scripts/{noesis_orchestrator,amda_analyzer,auron_neural_multi_v2,metrics_generator}.py
```

### 2. Run First Test (Dry-Run)

```bash
# Via GitHub Actions UI
# Go to Actions → NOESIS CEREBRAL COMPLETE V2.0 → Run workflow
# Leave default settings (dry_run=true)

# Or via CLI
gh workflow run noesis_cerebral_complete.yml
```

### 3. Monitor Progress

```bash
# Watch execution
gh run watch

# View results
gh run view --log

# Download artifacts
gh run download <run-id>
```

---

## 📊 Quick Commands

### Check Current Status

```bash
# Count sorries
find formalization/lean -name "*.lean" -exec grep -l "sorry" {} + | wc -l

# View learning history
cat .auron_learning.json | jq '{patterns: (.patterns | length), success_rate: ((.total_success / .total_attempts) * 100)}'

# View last AMDA report
cat amda_report.json | jq '.summary'
```

### Run Pipeline Locally

```bash
# 1. Sync knowledge (30 seconds)
python .github/scripts/noesis_orchestrator.py .github/scripts/multi_repo_config.json

# 2. Analyze sorries (5 seconds)
python .github/scripts/amda_analyzer.py formalization/lean amda_report.json

# 3. Execute transformations - DRY RUN (10 seconds)
export AURON_DRY_RUN=1
python .github/scripts/auron_neural_multi_v2.py amda_report.json auron_results.json

# 4. Generate metrics (2 seconds)
python .github/scripts/metrics_generator.py amda_report.json auron_results.json noesis_sync_report.json
```

### Production Execution

```bash
# Manual execution in production mode
gh workflow run noesis_cerebral_complete.yml \
  -f dry_run=false \
  -f max_changes=25 \
  -f force_sync=false

# ⚠️ WARNING: This will create a PR with actual changes
```

---

## 🎯 Key Parameters

| Parameter | Default | Description | When to Change |
|-----------|---------|-------------|----------------|
| `dry_run` | `true` | Simulation mode | Set to `false` for production |
| `max_changes` | `25` | Changes per cycle | Increase for faster progress |
| `force_sync` | `false` | Full repo sync | Set to `true` after adding repos |

---

## 📈 Understanding Results

### Success Indicators

✅ **Good workflow run:**
```
✅ NOESIS: 5 repos synced, 5,438 items
✅ AMDA: 2,376 sorries analyzed
✅ AURON: 15 successes, 5 failures (75% success rate)
✅ Metrics: Report generated
```

❌ **Issues to investigate:**
```
⚠️ NOESIS: Sync timeout
⚠️ AMDA: 0 sorries found (unexpected)
⚠️ AURON: 0 successes, 20 failures (0% success rate)
⚠️ Compilation: lake build failed
```

### Artifacts to Review

After each run, download and check:

1. **amda_report.json** - Sorry analysis
2. **auron_results.json** - Transformation results
3. **metrics_report.md** - Comprehensive report
4. **.auron_learning.json** - Learning history (if updated)

---

## 🔧 Troubleshooting

### Workflow Fails at NOESIS Step

```bash
# Check repo connectivity
git ls-remote https://github.com/motanova84/141Hz.git

# Verify config
cat .github/scripts/multi_repo_config.json
```

### Workflow Fails at AURON Step

```bash
# Check if AMDA report exists
test -f amda_report.json && echo "Report exists" || echo "Report missing"

# Check if knowledge base exists
test -f /tmp/noesis_knowledge_v2/knowledge_v2.pkl && echo "KB exists" || echo "KB missing"

# Verify Lean setup
cd formalization/lean && lake build
```

### Low Success Rate

Common causes:
- Knowledge base not synced (run with `force_sync=true`)
- Complex sorries requiring manual intervention
- Compilation issues in Lean project

Solutions:
- Review `.auron_learning.json` for patterns
- Check `auron_neural_multi.log` for details
- Adjust similarity threshold in code

---

## 📊 Monitoring Dashboard

### Quick Stats

```bash
# Total sorries
jq -r '.summary.total_sorries' amda_report.json

# Success rate
jq -r '(.success / (.success + .fail) * 100)' auron_results.json

# Patterns learned
jq -r '.patterns | length' .auron_learning.json

# Knowledge base size
jq -r '.knowledge_base.total_items' noesis_sync_report.json
```

### Progress Tracking

```bash
# Create a simple progress tracker
cat << 'EOF' > track_progress.sh
#!/bin/bash
echo "=== NOESIS CEREBRAL Progress ==="
echo "Sorries: $(jq -r '.summary.total_sorries' amda_report.json 2>/dev/null || echo 'N/A')"
echo "Last run: $(jq -r '.timestamp' auron_results.json 2>/dev/null || echo 'N/A')"
echo "Success: $(jq -r '.success' auron_results.json 2>/dev/null || echo 'N/A')"
echo "Patterns: $(jq -r '.patterns | length' .auron_learning.json 2>/dev/null || echo 'N/A')"
EOF
chmod +x track_progress.sh
./track_progress.sh
```

---

## 🎓 Best Practices

### 1. Start with Dry-Run
Always test with `dry_run=true` before production.

### 2. Monitor First Cycles
Watch the first 3-5 cycles closely to ensure system is working correctly.

### 3. Review PRs Promptly
Automated PRs should be reviewed within 24 hours.

### 4. Sync Regularly
Run with `force_sync=true` monthly to refresh knowledge base.

### 5. Adjust Parameters
Increase `max_changes` gradually as confidence grows (25 → 50 → 100).

---

## 🆘 Getting Help

### Check Logs

```bash
# Workflow logs (GitHub)
gh run view --log

# Local logs
cat auron_neural_multi.log
```

### Review Documentation

- `NOESIS_CEREBRAL_COMPLETE.md` - Full documentation
- `NOESIS_AMDA_AURON_V2_README.md` - Technical details
- `NOESIS_AMDA_AURON_V2_QUICKSTART.md` - Detailed guide

### Common Issues

| Issue | Solution |
|-------|----------|
| Sync timeout | Increase timeout in workflow |
| No sorries found | Check Lean file paths |
| Build failures | Run `lake build` manually |
| Low success rate | Review learning history |

---

## ✅ Checklist for Production

Before setting `dry_run=false`:

- [ ] Workflow runs successfully in dry-run mode
- [ ] All 5 repositories sync correctly
- [ ] AMDA finds expected number of sorries
- [ ] AURON shows reasonable success rate (>50%)
- [ ] Metrics report generates correctly
- [ ] `.auron_learning.json` updates properly
- [ ] Lean project builds successfully
- [ ] You understand the PR review process

---

## 🎯 Expected Timeline

| Milestone | Cycles | Time | Sorries |
|-----------|--------|------|---------|
| **Trivial elimination** | 2-3 | 6-9h | ~113 |
| **100 sorries down** | 5-7 | 15-21h | ~2,276 |
| **500 sorries down** | 20-25 | 60-75h | ~1,876 |
| **1,000 sorries down** | 40-50 | 120-150h | ~1,376 |
| **Victory (all auto)** | 100-120 | 300-360h | ~1,476 remain |

*Assuming 3-hour cycles, 75% success rate, 25 changes per cycle*

---

## 🌟 Quick Wins

### First Day

1. Run dry-run workflow ✓
2. Review artifacts ✓
3. Check learning history ✓

### First Week

1. Enable production mode
2. Monitor 5-10 cycles
3. Review first PRs
4. Adjust parameters if needed

### First Month

1. Eliminate 200-300 sorries
2. Build up learning patterns
3. Optimize success rate
4. Document any issues

---

*⚡ Quick Reference for NOESIS CEREBRAL COMPLETE V2.0*

**Frequency:** Every 3 hours · **Mode:** Dry-run default · **QCAL ∞³**

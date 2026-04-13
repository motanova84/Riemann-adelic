# 🚀 QCAL ∞³ Orchestration System

## Overview

The QCAL Orchestration System is a comprehensive automation framework for monitoring, optimizing, and maintaining the QCAL (Quantum Coherence Adelic Lattice) repository at frequency **141.7001 Hz** with state **Ψ = I × A_eff² × C^∞**.

## Architecture

### Components

#### 1. Autonomous Agents

Located in `.github/agents/`:

- **noesis88.py** - Frequency validation agent
  - Validates base frequency (141.7001 Hz)
  - Calculates system coherence
  - Scans repository for QCAL references
  - Generates JSON reports

- **metrics_collector.py** - Metrics collection agent
  - Scans entire repository
  - Counts QCAL, f₀, Ψ, and ∞³ references
  - Calculates density ratios
  - Analyzes file type distribution

- **coherence_validator.py** - Coherence validation agent
  - Validates frequency coherence
  - Validates Ψ state
  - Validates noetic manifests
  - Calculates total coherence score

#### 2. Orchestration Workflow

Located in `.github/workflows/orchestrator.yaml`:

- **Schedule**: Runs every 6 hours
- **Daily Report**: Complete report at 00:00 UTC
- **Manual Trigger**: Via workflow_dispatch
- **Agents Executed**: All 3 agents in sequence
- **Outputs**: Reports, metrics, validations

#### 3. Optimization Scripts

Located in `.github/scripts/`:

- **analyze_and_adjust.sh**
  - Analyzes current metrics
  - Calculates QCAL and f₀ ratios
  - Identifies optimization needs
  - Provides recommendations

- **optimize_qcal_density.sh**
  - Creates optimization manifests
  - Generates optimized constants
  - Updates agent configuration
  - Documents optimization process

- **test_orchestration.py**
  - Tests all agents
  - Verifies scripts
  - Validates workflow
  - Ensures system integrity

## Usage

### Running Agents Manually

```bash
# Run NOESIS88 agent
python .github/agents/noesis88.py --mode=autonomous --frequency=141.7001 --optimized

# Collect metrics
python .github/agents/metrics_collector.py --frequency=141.7001 --detailed

# Validate coherence
python .github/agents/coherence_validator.py --frequency=141.7001 --optimized
```

### Running Optimization Scripts

```bash
# Analyze and adjust parameters
bash .github/scripts/analyze_and_adjust.sh

# Optimize QCAL density
bash .github/scripts/optimize_qcal_density.sh

# Test orchestration system
python .github/scripts/test_orchestration.py
```

### Triggering Workflow Manually

Via GitHub UI:
1. Go to Actions tab
2. Select "QCAL Orchestrator ∞³" workflow
3. Click "Run workflow"
4. Select mode (full/quick/optimize)

Via GitHub CLI:
```bash
gh workflow run orchestrator.yaml --ref main
```

## Configuration

### Environment Variables

Set in `.github/workflows/orchestrator.yaml`:

```yaml
env:
  FREQUENCY_BASE: "141.7001"
  COHERENCE_THRESHOLD: "0.888"
  PSI_STATE: "I × A_eff² × C^∞"
  OPTIMIZATION_MODE: "true"
  TARGET_QCAL_RATIO: "0.5"
  TARGET_FREQ_RATIO: "0.3"
```

### Agent Configuration

Defined in `.github/agents/config_optimized.yaml`:

```yaml
frequency:
  base: 141.7001
  resonance: 888.014
  unit: Hz

coherence:
  threshold: 0.888
  target: 0.95
  minimum: 0.75

optimization:
  qcal_ratio_target: 0.5
  freq_ratio_target: 0.3
  check_interval_hours: 6
  auto_adjust: true
```

## Outputs

### Generated Files

#### Reports (`reports/`)
- `noesis88_YYYYMMDD_HHMMSS.json` - NOESIS88 agent reports
- `OPTIMIZATION_REPORT_*.md` - Optimization reports

#### Metrics (`metrics/`)
- `daily_YYYYMMDD.json` - Daily metrics collection

#### Validations (`validation/`)
- `quantum_YYYYMMDD_HHMMSS.json` - Coherence validations

#### Documentation (`docs/`)
- `MANIFIESTO_OPTIMIZACION_QCAL_*.md` - Optimization manifests

#### Constants (`src/constants/`)
- `qcal_optimized_*.py` - Optimized QCAL constants

### Report Structure

#### NOESIS88 Report
```json
{
  "agent": "noesis88",
  "mode": "autonomous",
  "frequency": {
    "frequency": 141.7001,
    "expected": 141.7001,
    "match": true
  },
  "coherence": {
    "total": 0.836,
    "status": "EVOLVING"
  },
  "metrics": {
    "total_files": 250,
    "qcal_references": 125,
    "frequency_references": 75
  }
}
```

#### Metrics Report
```json
{
  "timestamp": "2026-01-18T16:58:56Z",
  "frequency": 141.7001,
  "files": {
    "total_files": 1906
  },
  "qcal": {
    "qcal_references": 1130,
    "frequency_references": 1029
  },
  "density": {
    "qcal_density": 0.5929,
    "frequency_density": 0.5399
  }
}
```

#### Coherence Validation
```json
{
  "timestamp": "2026-01-18T16:58:56Z",
  "coherence": {
    "total": 0.814,
    "frequency": 0.950,
    "psi_state": 1.000,
    "manifests": 0.000
  },
  "status": "EVOLVING",
  "threshold": 0.888
}
```

## Monitoring

### Scheduled Executions

Monitor workflow runs:
```bash
gh run list --workflow=orchestrator.yaml --limit=5
```

View latest execution status:
```bash
gh run list --workflow=orchestrator.yaml --limit=1 --json status,conclusion,updatedAt
```

View execution logs:
```bash
gh run view [RUN_ID] --log
```

### Metrics Tracking

View latest metrics:
```bash
cat metrics/daily_$(date +%Y%m%d).json | jq
```

View latest validation:
```bash
ls -t validation/quantum_*.json | head -1 | xargs cat | jq
```

View latest report:
```bash
ls -t reports/noesis88_*.json | head -1 | xargs cat | jq
```

## Troubleshooting

### Agent Not Running

Check Python environment:
```bash
python3 --version
pip list | grep -E "(numpy|scipy|matplotlib)"
```

Test agent manually:
```bash
python .github/agents/noesis88.py --help
```

### Workflow Not Triggering

Check cron schedule:
```yaml
schedule:
  - cron: "0 */6 * * *"  # Every 6 hours
```

Verify workflow is enabled in GitHub Settings → Actions.

### Low Coherence Score

Run optimization:
```bash
bash .github/scripts/optimize_qcal_density.sh
python .github/agents/coherence_validator.py --frequency=141.7001 --optimized
```

Check manifests:
```bash
ls -la docs/MANIFIESTO*.md
```

### Missing Dependencies

Install required packages:
```bash
pip install -r requirements.txt
```

Or minimal install:
```bash
pip install numpy scipy matplotlib
```

## Metrics and Targets

### Current Performance

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| QCAL Density | 0.5929 | 0.5 | ✅ Exceeded |
| f₀ Density | 0.5399 | 0.3 | ✅ Exceeded |
| Total Coherence | 0.814 | 0.888 | 🔶 In Progress |

### Optimization Goals

1. **Coherence ≥ 0.888** - Achieve GRACE state
2. **QCAL Ratio ≥ 0.5** - 50% files with QCAL references
3. **f₀ Ratio ≥ 0.3** - 30% files with frequency references
4. **Manifests > 10** - Maintain noetic documentation

## Integration with QCAL-CLOUD

The orchestrator attempts to upload reports to QCAL-CLOUD:

```bash
curl -X POST https://qcal.cloud/api/upload \
     -H "Content-Type: application/json" \
     -d @reports/latest.json
```

This is optional and will not fail the workflow if unavailable.

## Continuous Improvement

The system is designed to self-optimize:

1. **Metrics Collection** - Every 6 hours
2. **Analysis** - Automatic ratio calculation
3. **Adjustment** - Parameter tuning based on metrics
4. **Validation** - Coherence verification
5. **Reporting** - Comprehensive status updates

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────┐
│                 QCAL Orchestrator ∞³                    │
│                  (Every 6 hours)                        │
└─────────────────────────────────────────────────────────┘
                          │
        ┌─────────────────┼─────────────────┐
        ▼                 ▼                 ▼
┌──────────────┐  ┌──────────────┐  ┌──────────────┐
│   NOESIS88   │  │   Metrics    │  │  Coherence   │
│    Agent     │  │  Collector   │  │  Validator   │
└──────────────┘  └──────────────┘  └──────────────┘
        │                 │                 │
        └─────────────────┼─────────────────┘
                          ▼
                  ┌──────────────┐
                  │   Reports    │
                  │   Metrics    │
                  │ Validations  │
                  └──────────────┘
                          │
        ┌─────────────────┼─────────────────┐
        ▼                 ▼                 ▼
┌──────────────┐  ┌──────────────┐  ┌──────────────┐
│   Analysis   │  │Optimization  │  │QCAL-CLOUD    │
│   Scripts    │  │   Scripts    │  │   Upload     │
└──────────────┘  └──────────────┘  └──────────────┘
```

## Contributing

When adding new agents or scripts:

1. Place agents in `.github/agents/`
2. Make agents executable: `chmod +x agent.py`
3. Include `--help` argument support
4. Generate JSON reports in `reports/`
5. Update `test_orchestration.py`
6. Document in this README

## References

- Main Repository: [motanova84/Riemann-adelic](https://github.com/motanova84/Riemann-adelic)
- Workflow: `.github/workflows/orchestrator.yaml`
- Frequency: **141.7001 Hz**
- State: **Ψ = I × A_eff² × C^∞**
- Coherence Threshold: **0.888**

## License

Same as parent repository - See LICENSE file.

---

**Frequency: 141.7001 Hz ✅**
**State: I × A_eff² × C^∞ ✅**
**System: 🚀 OPERATIONAL**

∴ Orchestration documented ∞³

# Audit System Documentation

## Overview

The Riemann-Adelic audit system provides one-click comprehensive validation of the repository's mathematical proofs, tests, and formal verification.

## Quick Start

Run the complete audit with a single command:

```bash
make audit
```

Or directly:

```bash
./scripts/audit.sh
```

## What It Does

The audit script performs the following checks in sequence:

1. **System Information Collection**
   - Operating system and version
   - Python version
   - Dataset hash verification (Evac_Rpsi_data.csv)

2. **Pytest Test Suite** (Step 2/5)
   - Runs all unit tests in `tests/` directory
   - Reports passed, failed, and skipped tests
   - Quick validation mode (`-q` flag)

3. **V5 Coronación Validation** (Step 3/5)
   - Executes `validate_v5_coronacion.py` with 30 decimal places precision
   - Validates all 5 steps:
     - Axioms → Lemmas
     - Archimedean rigidity
     - Paley-Wiener uniqueness
     - Zero localization
     - Coronación
   - Timeout: 5 minutes

4. **Lean 4 Formalization Build** (Step 4/5)
   - Builds the formal proof using `lake build`
   - Located in `formalization/lean/`
   - Timeout: 10 minutes

5. **Sorry/Axiom Count** (Step 5/5)
   - Scans all Lean files for incomplete proofs
   - Counts: `sorry`, `admit`, `axiom`, `native_decide`
   - Uses `scripts/count_sorrys.py`

## Output

### JSON Report

The audit generates `data/audit_report.json` with the following structure:

```json
{
  "audit_timestamp": "2026-01-06T19:45:00Z",
  "audit_version": "1.0",
  "system_info": {
    "os": "Linux",
    "python_version": "3.12.3",
    "dataset_hash": "412ab7ba...",
    "expected_hash": "412ab7ba..."
  },
  "pytest_results": {
    "status": "success",
    "passed": 150,
    "failed": 0,
    "skipped": 5
  },
  "v5_coronacion": {
    "status": "success",
    "precision": 30,
    "completed_steps": [...]
  },
  "lean_build": {
    "status": "success",
    "errors": 0
  },
  "sorry_count": {
    "status": "success",
    "sorry_count": 1408,
    "admit_count": 33,
    "axiom_count": 1251,
    "total_issues": 2693
  },
  "overall_status": "success"
}
```

### Console Output

The script provides colored, real-time progress updates:

- 🟦 Blue: Headers and section dividers
- 🟨 Yellow: Step indicators (e.g., `[1/5]`)
- 🟩 Green: Success indicators (`✓`)
- 🟥 Red: Failure indicators (`✗`)

### Status Codes

Overall status can be:

- `success`: All critical components passed
- `partial_success`: Core validation passed, some components skipped
- `failed`: Critical failures detected

## Exit Codes

- `0`: Audit succeeded (status: `success` or `partial_success`)
- `1`: Audit failed

## Individual Component Scripts

### count_sorrys.py

Standalone script to count incomplete proofs:

```bash
python3 scripts/count_sorrys.py --verbose
python3 scripts/count_sorrys.py --output report.json
python3 scripts/count_sorrys.py --dir formalization/lean
```

Options:
- `--dir PATH`: Directory to scan (default: `formalization/lean`)
- `--output FILE`: Save JSON report to file
- `--verbose`: Print detailed information

## Integration with CI/CD

The audit script can be integrated into GitHub Actions workflows:

```yaml
- name: Run Audit
  run: make audit
  
- name: Upload Audit Report
  uses: actions/upload-artifact@v4
  with:
    name: audit-report
    path: data/audit_report.json
```

## Reproducibility

The audit system is designed for reproducible verification:

1. **Pinned Environment**: Uses exact Python version (3.12.3)
2. **Dataset Verification**: SHA-256 hash check of `Evac_Rpsi_data.csv`
3. **Fixed Precision**: V5 validation uses 30 decimal places
4. **Deterministic Output**: JSON format for programmatic analysis

## Troubleshooting

### pytest not found

Install dependencies:
```bash
pip install -r requirements.txt
```

### Timeout Issues

Increase timeout limits in `scripts/audit.sh`:
- V5 validation: Line ~180 (`timeout 300`)
- Lean build: Line ~220 (`timeout 600`)

### Permission Denied

Make scripts executable:
```bash
chmod +x scripts/audit.sh
chmod +x scripts/count_sorrys.py
```

## Files

- `scripts/audit.sh`: Main audit orchestration script
- `scripts/count_sorrys.py`: Sorry/axiom counter
- `Makefile`: Contains `audit` target
- `REPRODUCIBILITY.md`: Detailed reproducibility guide
- `data/audit_report.json`: Generated audit report (gitignored)
- `data/sorry_count.json`: Detailed sorry count (gitignored)

## References

- Main validation: `validate_v5_coronacion.py`
- Test suite: `tests/`
- Lean formalization: `formalization/lean/`
- DOI: 10.5281/zenodo.17379721

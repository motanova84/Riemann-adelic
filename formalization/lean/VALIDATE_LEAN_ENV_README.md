# 🧠 Validate Lean Environment - Automated Formalization Monitoring

## Overview

`validate_lean_env.py` is a Python-based validation monitor for the Lean 4 formalization of the Riemann-Adelic proof. It provides automated build verification, syntax checking, and completeness metrics without requiring manual inspection.

## Features

✅ **Automated Lake Build**: Executes `lake build` and measures compilation time  
✅ **Sorry Detection**: Counts incomplete proofs (`sorry` keywords) in each module  
✅ **Theorem Verification**: Detects presence of main theorem `riemann_hypothesis_adelic`  
✅ **JSON Reporting**: Generates machine-readable validation reports  
✅ **CI/CD Ready**: Designed for continuous integration workflows  
✅ **Zero External Dependencies**: Uses only Python standard library (subprocess, json, re)

## Usage

### Basic Execution

```bash
cd formalization/lean
python3 validate_lean_env.py
```

### Expected Output

```
───────────────────────────────────────────────
🧠  VALIDACIÓN AUTOMÁTICA – Riemann Adelic (Python)
───────────────────────────────────────────────
⚙️  Compilando proyecto Lean con lake...
───────────────────────────────────────────────
📘 Informe generado: validation_report.json
⏱️  Tiempo total: 42.8 s
✅ Estado: PASS

📊 Resumen de Módulos:
  ✓ D_explicit.lean: 0 sorry(s)
  ✓ de_branges.lean: 0 sorry(s)
  ✓ schwartz_adelic.lean: 0 sorry(s)
  ✓ RH_final.lean: 0 sorry(s)
───────────────────────────────────────────────
```

## Validated Modules

The script validates these core Lean formalization files:

1. **D_explicit.lean** - Explicit construction of D(s) via adelic Poisson transform
2. **de_branges.lean** - de Branges space theory and Hamiltonian positivity
3. **schwartz_adelic.lean** - Schwartz functions on adelic spaces
4. **RH_final.lean** - Main Riemann Hypothesis theorem statement

## Output: validation_report.json

The script generates a comprehensive JSON report with the following structure:

```json
{
  "timestamp": "2025-10-26T21:24:03Z",
  "project": "Riemann-Adelic Formalization V5.3",
  "lean_version": "Lean (version 4.5.0, commit ...)",
  "build_success": true,
  "build_time_sec": 42.83,
  "warnings": 0,
  "errors": 0,
  "modules": {
    "D_explicit.lean": {
      "exists": true,
      "sorries": 0,
      "verified": true
    },
    ...
  },
  "theorem_detected": true,
  "summary": {
    "status": "PASS",
    "message": "Formalización compilada y verificada."
  }
}
```

## Status Codes

- **PASS**: Build successful, no errors, main theorem detected
- **CHECK**: Build issues, warnings, or incomplete proofs detected

## Integration with CI/CD

### GitHub Actions Example

```yaml
- name: Validate Lean Formalization
  run: |
    cd formalization/lean
    python3 validate_lean_env.py
  continue-on-error: true
  
- name: Upload Validation Report
  uses: actions/upload-artifact@v3
  with:
    name: lean-validation-report
    path: formalization/lean/validation_report.json
```

## Requirements

- Python 3.7+ (uses type hints with `tuple[int, str, str]`)
- Lean 4 + Lake build tool (optional - gracefully handles absence)

## Relation to Other Validation Scripts

This script complements existing validation tools:

- **validate_lean_formalization.py**: Static syntax/import validation
- **validate_v5_coronacion.py**: Mathematical proof verification
- **validate_lean_env.py**: Build system and completeness verification ⭐ (this script)

## Exit Codes

- `0`: Validation successful or partial success (theorem detected)
- `1`: Validation failed (build errors, missing files)

## Author

José Manuel Mota Burruezo (ICQ)  
Version: V5.3 – October 2025

## References

- [Lean 4 Documentation](https://lean-lang.org/)
- [Lake Build System](https://github.com/leanprover/lake)
- [REDUCCION_AXIOMATICA_V5.3.md](./REDUCCION_AXIOMATICA_V5.3.md)
- [FORMALIZATION_STATUS.md](./FORMALIZATION_STATUS.md)

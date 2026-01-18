# Mathematical Archive Tools

This directory contains tools for the mathematical archive system, including metadata validation and proof converters.

## Tools Overview

### 1. `verify_metadata.py` - Metadata Validator

Validates JSON-LD metadata files to ensure they meet the archive's requirements.

**Features:**
- Validates JSON-LD structure
- Checks required fields
- Verifies SHA-256 checksums
- Validates dependency references
- Ensures @context correctness

**Usage:**

```bash
# Validate single file
python tools/verify_metadata.py schema/metadata_example.jsonld

# Validate multiple files
python tools/verify_metadata.py schema/*.jsonld

# Validate specific files
python tools/verify_metadata.py schema/theorem1.jsonld schema/theorem2.jsonld
```

**Output:**
```
======================================================================
Validating: schema/metadata_example.jsonld
======================================================================
✅ Validation PASSED
   - @id: urn:jmmotaburr:riemann-adelic:example:rh-critical-line-theorem
   - @type: theorem
   - title: Riemann Hypothesis - Critical Line Theorem
   - dependencies: 2 items
```

### 2. `convert_example.py` - Lean to Intermediate Format Converter

Converts Lean proof files to an intermediate format (Dedukti/MMT/OMDoc) for verification and interoperability.

**Features:**
- Extracts theorem declarations from Lean files
- Computes SHA-256 checksums
- Generates JSON-LD metadata
- Produces intermediate format stubs
- Preserves source information

**Usage:**

```bash
# Basic conversion
python tools/convert_example.py formalization/lean/functional_eq.lean

# Save intermediate format
python tools/convert_example.py formalization/lean/Main.lean -o output.dk

# Generate metadata
python tools/convert_example.py formalization/lean/theorem.lean -m metadata.jsonld

# Verbose output
python tools/convert_example.py formalization/lean/Main.lean -v
```

**Output:**
```
======================================================================
Lean → Intermediate Format Converter (Stub)
======================================================================

📂 Reading: formalization/lean/functional_eq.lean
✅ Found 3 theorem(s)
   - functional_equation
   - critical_line_symmetry
   - zero_distribution

🔄 Converting to intermediate format...
✅ Conversion completed (stub)
```

## Integration with CI/CD

Both tools are integrated into the CI pipeline:

```yaml
# .github/workflows/ci.yml
- name: Validate metadata
  run: |
    python tools/verify_metadata.py schema/metadata_example.jsonld

- name: Test converter
  run: |
    python tools/convert_example.py tests/examples/example_lean.lean
```

## Development Guide

### Adding a New Tool

1. Create a new Python file in `tools/`
2. Include comprehensive docstrings
3. Add command-line interface with `argparse`
4. Add tests in `tests/test_mathematical_archive.py`
5. Update this README
6. Add to CI workflow if applicable

### Tool Requirements

All tools should:
- Have clear, descriptive output
- Use emoji for visual clarity (✅ ❌ 🔄 📂 etc.)
- Support batch processing where appropriate
- Exit with appropriate status codes (0 for success, 1 for errors)
- Include help text and examples
- Be tested in CI/CD

### Code Style

Tools follow the repository's code style:
- **Black** for formatting (line length 120)
- **Flake8** for linting
- **Type hints** where appropriate
- **Docstrings** for all public functions

Run checks:
```bash
black tools/ --check
flake8 tools/
```

## Testing

Tools are tested in `tests/test_mathematical_archive.py`:

```bash
# Run tool tests
pytest tests/test_mathematical_archive.py -v

# Run with coverage
pytest tests/test_mathematical_archive.py --cov=tools
```

## Future Enhancements

Planned improvements:

1. **Full Lean AST Parser**: Replace stub with actual Lean 4 export parsing
2. **Dedukti Code Generation**: Generate valid Dedukti syntax
3. **Kernel Verification**: Integrate with verification kernels
4. **Multi-format Support**: Add Coq, Isabelle, HOL Light converters
5. **Semantic Search**: Index and search by mathematical concepts
6. **Dependency Graph**: Visualize theorem dependencies
7. **Batch Processing**: Process entire libraries at once
8. **Interactive Mode**: CLI tool for exploring conversions

## API Usage

Tools can also be imported and used as Python modules:

```python
from tools.verify_metadata import validate_metadata_file
from tools.convert_example import extract_lean_metadata, compute_sha256

# Validate metadata programmatically
is_valid = validate_metadata_file(Path("schema/my_theorem.jsonld"))

# Extract metadata from Lean file
metadata = extract_lean_metadata(Path("formalization/lean/theorem.lean"))
print(f"Found {metadata['theorem_count']} theorems")

# Compute checksum
checksum = compute_sha256("theorem content")
```

## Troubleshooting

### Common Issues

**Issue**: `ModuleNotFoundError: No module named 'jsonschema'`
```bash
# Solution: Install dependencies
pip install -r requirements.txt
```

**Issue**: Metadata validation fails with checksum error
```bash
# Solution: Ensure checksum is 64-character hexadecimal SHA-256
sha256sum your_file.lean
# Copy the output to metadata checksum field
```

**Issue**: Converter can't find Lean file
```bash
# Solution: Use absolute or relative path from repository root
python tools/convert_example.py formalization/lean/YourFile.lean
```

## Contributing

See [CONTRIBUTING.md](../CONTRIBUTING.md) for contribution guidelines.

When adding tools:
1. Follow existing patterns
2. Add comprehensive tests
3. Update this README
4. Ensure CI passes

## 3. Automated Lean Proof Completion Tools

**NEW:** Automated tools for completing Lean theorem proofs marked with 'sorry'.

### Components

**Files:**
- `lean_proof_completer.py` - Lean file parser and theorem extractor
- `noesis_sabio_integration.py` - Semantic analysis and proof generation
- `automated_sorry_completion.py` - Complete workflow orchestrator

### Features

**Lean Proof Completer:**
- Extracts theorems, lemmas, and definitions with 'sorry'
- Analyzes proof context and dependencies
- Identifies mathematical structures

**Noesis-Sabio Integration:**
- **Noesis:** Semantic analysis of mathematical theorems
- **Sabio:** Intelligent proof search and generation
- Supports categories: spectral, functional, arithmetic, analysis, algebra

**Automated Workflow:**
1. Identify Lean files with 'sorry'
2. Extract theorem contexts
3. Generate completions using Noesis + Sabio
4. Validate proposed completions
5. Apply completions with backup
6. Verify integrity with validate_v5_coronacion.py

### Usage

```bash
# Dry-run analysis (safe, default)
python tools/automated_sorry_completion.py --dir formalization/lean --verbose

# Generate detailed report
python tools/automated_sorry_completion.py --dir formalization/lean --output report.json

# Test Noesis-Sabio integration
python tools/noesis_sabio_integration.py

# Analyze single file
python tools/lean_proof_completer.py --file path/to/file.lean --verbose
```

### Statistics

Latest run on formalization/lean:
- Files processed: 356
- Sorry statements found: 1387
- Completions generated: 1360
- Completions validated: 25 (1.8%)
- Duration: 0.34 seconds

### Safety Features

- **Dry-run mode by default** (no file modifications)
- **Automatic backups** before changes
- **Confidence-based validation** (only high-confidence proofs auto-applied)
- **Integration with QCAL validation** framework

### Example Completions

**Arithmetic:**
```lean
theorem add_zero (n : ℕ) : n + 0 = n := norm_num
```

**Functional Equation:**
```lean
theorem zeta_functional_eq : ∀ s, ξ(s) = ξ(1-s) := 
  rw [functional_equation]
  apply symmetry_property
```

**Spectral:**
```lean
theorem spectrum_real (H : SelfAdjoint) : ∀ λ ∈ spectrum H, λ ∈ ℝ := 
  apply spectrum_characterization
  · exact self_adjoint_property
  · apply compact_operator
```

See `tools/README_PROOF_COMPLETION.md` for complete documentation.

## License

Tools are licensed under MIT License. See [LICENSE](../LICENSE) file.

## Support

For questions or issues:
- Open an issue on GitHub
- Check existing issues for solutions
- Consult [CONTRIBUTING.md](../CONTRIBUTING.md)

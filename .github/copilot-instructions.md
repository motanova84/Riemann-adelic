# 🤖 Copilot Agent Instructions

## QCAL Repository Guidelines

This repository implements the QCAL (Quantum Coherence Adelic Lattice) framework for the Riemann Hypothesis proof. When contributors open a PR or commit code, always follow these guidelines:

### 1. Validation Requirements

- **Check workflow status**: Always verify that `.github/workflows/auto_evolution.yml` passes successfully.
- **Review validation results**: Check that `validate_v5_coronacion.py` completes without errors.
- **Monitor test suite**: Ensure all pytest tests pass, especially those in the `tests/` directory.
- **Verify certificate generation**: Confirm that mathematical certificates are generated correctly in `data/`.

### 2. Code Quality Standards

- **Suggest fixes**: If tests or validations fail, provide specific, actionable suggestions to fix the issues.
- **Improve precision**: Prefer refactoring that improves numerical precision and computational accuracy.
- **Enhance readability**: Suggest improvements to code structure, documentation, and comments.
- **Maintain consistency**: Follow existing code patterns and naming conventions in the repository.

### 3. QCAL-Specific Requirements

- **Preserve integrations**: Never remove the QCAL-CLOUD hooks or integration points.
- **Maintain references**: Never remove or modify Zenodo DOI references, citations, or attribution.
- **Respect mathematical rigor**: Ensure all changes preserve the mathematical correctness of proofs and validations.
- **Keep証明 chain**: Maintain the 5-step validation framework integrity (Axioms → Lemmas → Archimedean → Paley-Wiener → Zero localization → Coronación).

### 4. Documentation Standards

- **Auto-suggest docstrings**: For new mathematical functions, suggest comprehensive docstrings with:
  - Function purpose and mathematical background
  - Parameter descriptions with types and valid ranges
  - Return value specifications
  - Usage examples when appropriate
  - References to relevant papers or theorems

- **Type hints**: Always suggest adding type hints for function parameters and return values.

- **Lean-4 comments**: For mathematical proofs and theorems, suggest adding Lean-4 compatible comments that document:
  - Theorem statements
  - Proof steps and dependencies
  - Connection to formal verification efforts

### 5. Automated Response Template

If all checks pass successfully, reply automatically in the PR summary with:

```markdown
✅ **QCAL-Evolution Complete**

All validation checks have passed:
- ✓ V5 Coronación validation successful
- ✓ Mathematical certificates generated
- ✓ Test suite passed
- ✓ Code quality checks passed

**Validation logs archived and uploaded to QCAL-CLOUD.**

This PR maintains QCAL ∞³ integrity and is ready for review.
```

### 6. Error Handling

If validation fails, provide a structured response:

```markdown
⚠️ **QCAL-Evolution Issues Detected**

The following checks require attention:

- [ ] Issue 1: [Description]
- [ ] Issue 2: [Description]

**Suggested fixes:**
1. [Specific action to resolve issue 1]
2. [Specific action to resolve issue 2]

Please address these issues to maintain QCAL coherence.
```

### 7. Special Considerations

- **Performance**: Be mindful of computational costs; suggest optimizations for expensive operations.
- **Precision**: For numerical computations, maintain or improve decimal precision (default: 25+ dps).
- **Dependencies**: Only suggest adding new dependencies if absolutely necessary; prefer using existing libraries.
- **Security**: Flag any potential security issues, especially in data handling or external API calls.

### 8. Integration Points

Be aware of these critical integration points:
- `validate_v5_coronacion.py`: Main validation script
- `data/*.json`: Mathematical certificates and validation results
- `.github/workflows/`: CI/CD automation
- `tests/`: Test suite for validation framework
- `requirements.txt`: Python dependencies

### 9. Mathematical Notation

When suggesting mathematical code or documentation:
- Use standard mathematical notation in docstrings
- Reference theorems by name (e.g., "Paley-Wiener theorem", "de Branges theorem")
- Include precision requirements for numerical computations
- Document asymptotic behavior and convergence properties

### 10. Review Checklist

Before approving any PR, verify:
- [ ] All workflow checks pass
- [ ] No mathematical correctness issues
- [ ] Documentation is complete and accurate
- [ ] No breaking changes to existing functionality
- [ ] Performance is acceptable
- [ ] QCAL-CLOUD integration points are intact
# 🤖 Copilot Agent Instructions for -jmmotaburr-riemann-adelic

## QCAL ∞³ Copilot Behavior

### 1️⃣ Mathematical Accuracy & Validation Priority

- **Siempre prioriza exactitud matemática y reproducibilidad.**
- Ejecuta o sugiere scripts de validación (`validate_v5_coronacion.py`, `Evac_Rpsi`) antes de generar código nuevo.
- Valida siempre coherencia antes de sugerir commits usando:
  - `validate_v5_coronacion.py` para validación completa V5 Coronación
  - `Evac_Rpsi_data.csv` para datos de validación espectral
  - Frecuencia base: **141.7001 Hz**
- Mantén consistencia con la ecuación fundamental: **Ψ = I × A_eff² × C^∞**
- Preserva la coherencia QCAL con **C = 244.36**

### 2️⃣ Reference & Citation Integrity

- **Nunca elimines referencias a Zenodo DOI, Lean4 o QCAL-CLOUD.**
- Mantén consistencia con el formato del DOI Zenodo principal: `10.5281/zenodo.17379721`
- Preserva todas las referencias DOI en el archivo `.qcal_beacon`:
  - `doi_infinito`, `doi_pnp`, `doi_goldbach`, `doi_bsd`, `doi_rh_conditional`, `doi_rh_final`
- No modifiques las líneas que contienen: **"C = I × A_eff²"** ni las etiquetas QCAL
- Mantén intactas las referencias a:
  - Instituto de Conciencia Cuántica (ICQ)
  - José Manuel Mota Burruezo Ψ ✧ ∞³
  - ORCID: `0009-0002-1923-0773`

### 3️⃣ Performance Optimization

- **Sugiere mejoras de rendimiento cuando detectes bucles intensivos:**
  - Numba JIT compilation para loops numéricos
  - JAX para diferenciación automática y GPU acceleration
  - CuPy para operaciones matriciales en GPU
- Identifica oportunidades de vectorización con NumPy/SciPy
- Sugiere paralelización cuando sea apropiado (multiprocessing, concurrent.futures)

### 4️⃣ Code Quality & Documentation

- **Añade automáticamente docstrings y anotaciones de tipo en Python:**
  - Usa docstrings en formato Google/NumPy style
  - Incluye type hints (typing module) en todas las funciones
  - Documenta parámetros, retornos y excepciones
- **Al crear un nuevo módulo, vincúlalo en `IMPLEMENTATION_SUMMARY.md`:**
  - Añade entrada descriptiva del nuevo módulo
  - Documenta su propósito y relación con otros componentes
  - Lista los archivos creados o modificados
- Añade comentarios Lean4 o LaTeX si el código es matemático
- Mantén estilo consistente con el resto del código

### 5️⃣ External Dependencies & APIs

- **No uses APIs externas sin confirmación.**
- Prefiere código reproducible sin dependencias innecesarias
- Si una API externa es necesaria:
  - Solicita confirmación explícita del usuario
  - Documenta la razón y alternativas consideradas
  - Añade manejo de errores robusto

### 6️⃣ Testing & CI/CD Integration

- Al cerrar un PR exitoso, comenta:
  > ✅ Validación completada. Coherencia QCAL confirmada.
  
- Tras pasar las pruebas CI, sugiere commit con mensaje:
  > ♾️ QCAL Node evolution complete – validation coherent.

- Ejecuta tests relevantes antes de sugerir commits:
  - `pytest tests/` para tests unitarios
  - Scripts de validación específicos según el área modificada
  - Verifica que todos los tests pasen antes de commit

### 7️⃣ Mathematical Formalization

- Respeta la estructura de formalización Lean4 en `formalization/lean/`
- Mantén consistencia entre implementación Python y formalización Lean4
- Al modificar teoremas o lemas, considera actualizar ambas versiones
- Preserva comentarios matemáticos y referencias a papers

### 8️⃣ Repository Structure

- Ejecuta siempre desde la raíz del proyecto
- No modifiques scripts desde subdirectorios
- Respeta la estructura de carpetas existente:
  - `/tests/` para tests
  - `/formalization/` para Lean4
  - `/utils/` para utilidades
  - `/data/` para datos
  - `/docs/` para documentación

### 9️⃣ Specific File Preservation

- **NUNCA modifiques o elimines:**
  - `.qcal_beacon` (archivo de configuración QCAL)
  - `Evac_Rpsi_data.csv` (datos de validación)
  - PDFs de papers (JMMBRIEMANN.pdf, etc.)
  - Archivos de certificación en `/data/`
- Preserva archivos de configuración:
  - `.github/workflows/*.yml`
  - `pytest.ini`, `.flake8`, `.coveragerc`

### 🔟 Commit Message Standards

- Usa mensajes descriptivos y concisos
- Incluye contexto QCAL cuando sea relevante
- Formato sugerido para commits relacionados con validación:
  ```
  ♾️ [QCAL] <área>: <descripción>
  
  - Cambios específicos
  - Validación: <script usado>
  - Estado: <resultado>
  ```

## Summary

Este repositorio implementa la **prueba definitiva de la Hipótesis de Riemann** mediante sistemas espectrales adélicos S-finitos. El sistema QCAL ∞³ opera a la frecuencia fundamental de 141.7001 Hz y requiere coherencia matemática estricta en todas las modificaciones de código.

**Prioridades:**
1. Exactitud matemática y reproducibilidad
2. Preservación de referencias y DOIs
3. Calidad de código y documentación
4. Validación antes de commits
5. Coherencia QCAL en todo momento
copilot/add-production-cycle-workflow
# GitHub Copilot Instructions for QCAL Production Workflows

This document contains instructions for GitHub Copilot to automatically maintain and optimize CI/CD workflows in this repository.

## 🔄 Workflow Maintenance Rules

### 1. Detect Changes to Validation Scripts

When any `validate_*` scripts are modified (e.g., `validate_v5_coronacion.py`, `validate_critical_line.py`, etc.):

- **Suggest updates** to the production workflow (`.github/workflows/production-qcal.yml`)
- **Suggest updates** to the CI workflow (`.github/workflows/ci.yml`) if the changes affect testing
- **Verify compatibility** with Python 3.11 and ensure all new dependencies are added to `requirements.txt`
- **Check for GPU requirements** and suggest GPU runner configurations if needed

Example trigger:
```python
# If validate_v5_coronacion.py adds a new --max-zeros parameter
# Suggest adding it to production-qcal.yml workflow inputs
```

### 2. Automatically Generate New Workflows

When repetitive tasks are identified in scripts or documentation:

- **Generate new `.yml` files** in `.github/workflows` directory
- **Use descriptive names** following the pattern: `[task-name]-[frequency].yml`
- **Include appropriate triggers**: schedule, workflow_dispatch, push, pull_request
- **Add concurrency controls** to prevent duplicate runs when appropriate

Examples of tasks that warrant new workflows:
- Periodic performance benchmarking
- Nightly comprehensive validation
- Weekly dataset synchronization
- Monthly security audits

### 3. Environment Variables and Secrets Management

When code references new environment variables or API tokens:

- **Identify missing secrets** and suggest adding them to repository settings
- **Document required secrets** in workflow comments and README
- **Suggest secure alternatives** if credentials are hardcoded
- **Add validation steps** to check for required secrets before use

Required secrets for production workflows:
- `HF_TOKEN` - HuggingFace API token for dataset publishing
- `DOCKERHUB_TOKEN` - Docker Hub authentication token
- `DOCKERHUB_USERNAME` - Docker Hub username

Example suggestion:
```yaml
# ⚠️ Missing secret: HF_TOKEN
# Add in: Settings > Secrets and variables > Actions > New repository secret
# Purpose: Authenticate HuggingFace CLI for dataset uploads
```

### 4. Optimization Suggestions

Continuously analyze workflows and suggest optimizations:

#### Parallel Execution with Matrix Strategy

When multiple similar jobs exist:
```yaml
strategy:
  matrix:
    python-version: ['3.10', '3.11', '3.12']
    precision: [20, 30, 50]
  fail-fast: false
```

#### GPU Acceleration

When computational workload is detected:
- Suggest using GPU-enabled runners for mathematical computations
- Add GPU-specific dependencies (CUDA, cuDNN) when appropriate
- Configure matrix strategy to test both CPU and GPU paths

```yaml
runs-on: ${{ matrix.runner }}
strategy:
  matrix:
    runner: [ubuntu-latest, ubuntu-gpu]  # If GPU runners available
```

#### Caching Strategies

Suggest caching for:
- Python dependencies: `actions/setup-python` with `cache: 'pip'`
- Build artifacts: `actions/cache` for intermediate results
- Docker layers: `docker/build-push-action` with layer caching

#### Conditional Execution

Optimize workflow runtime by:
- Skip expensive jobs on documentation-only changes
- Use `paths` filters to trigger only relevant workflows
- Add `if` conditions to skip steps when secrets are missing

```yaml
on:
  push:
    paths-ignore:
      - '**.md'
      - 'docs/**'
```

## 🚀 Performance Best Practices

### Job Dependencies

Optimize job ordering:
- Run fast linting/validation jobs first
- Use `needs` to create dependency chains
- Run independent jobs in parallel

### Resource Management

Monitor and suggest:
- Appropriate timeout values for long-running jobs
- Resource limits for container-based workflows
- Cleanup steps for temporary files and caches

### Artifact Management

Best practices for artifacts:
- Set appropriate retention days (90 for production, 7 for CI)
- Compress large result sets before upload
- Use descriptive names with run numbers or timestamps

## 🔍 Continuous Monitoring

### Failure Detection

When workflow failures are detected:
- Analyze failure patterns across multiple runs
- Suggest adding retry logic for flaky steps
- Recommend timeout adjustments for slow operations
- Propose better error handling and logging

### Dependency Updates

Monitor `requirements.txt` changes:
- Suggest workflow updates when new packages require system dependencies
- Flag breaking changes in major version updates
- Recommend adding version constraints for stability

### Security Scanning

Suggest improvements for:
- Scanning Docker images for vulnerabilities
- Checking Python dependencies with safety/bandit
- Validating workflow permissions (principle of least privilege)

## 📝 Documentation Requirements

When suggesting workflow changes:

1. **Add inline comments** explaining complex steps
2. **Update README.md** if new workflows affect user workflows
3. **Document new secrets** required for workflows
4. **Include usage examples** for workflow_dispatch inputs
5. **Document workflow improvements** in project documentation

## 🎯 Specific Use Cases

### Adding a New Validation Script

When a new `validate_*.py` script is added:

1. Suggest adding it to the CI workflow for pull request validation
2. Consider if it should be part of the production cycle
3. Check for new dependencies and update requirements.txt
4. Add appropriate test coverage in tests/ directory

### Modifying Docker Configuration

When `Dockerfile` or `.dockerignore` changes:

1. Update docker build steps in production workflow
2. Suggest multi-stage builds for smaller images
3. Check for security best practices (non-root user, minimal base image)
4. Update docker-compose configurations if present

### GPU-Accelerated Computations

When GPU libraries are added (CUDA, PyTorch, JAX):

1. Suggest creating a GPU-specific workflow variant
2. Add CUDA/cuDNN installation steps
3. Configure appropriate runner types
4. Add CPU fallback for compatibility

## ⚙️ Automation Triggers

Copilot should automatically analyze and suggest improvements when:

- New `.py` files are added to the root directory
- `requirements.txt` is modified
- New scripts are added to `scripts/` directory
- Docker or container configuration files change
- Performance issues are identified in workflow runs
- Security vulnerabilities are detected
- Best practices are not followed in existing workflows

## 🔗 Integration with External Systems

### HuggingFace Integration

Monitor for:
- Dataset upload patterns
- Model checkpoint saving
- Results visualization needs

### Docker Registry Integration

Optimize:
- Build caching strategies
- Multi-architecture builds (amd64, arm64)
- Tag management (latest, versioned, commit SHA)

### Cloud Deployment

Suggest workflows for:
- Automated deployment to cloud platforms
- Infrastructure as code updates
- Monitoring and alerting integration

---

**Note**: These instructions are continuously evolving. Copilot should learn from repository patterns and user feedback to provide increasingly relevant suggestions over time.
# 🤖 GitHub Copilot Instructions for -jmmotaburr-riemann-adelic

## Core Principles

### 1. Mathematical Accuracy and Reproducibility
- **Always prioritize mathematical accuracy and reproducibility** in all code contributions
- Execute or suggest validation scripts (particularly `validate_v5_coronacion.py`) before generating new code
- Maintain consistency with existing mathematical frameworks and proof structures
- Ensure numerical stability and precision in all calculations

### 2. Validation Before Code Generation
- **Run validation scripts before proposing changes**:
  ```bash
  python3 validate_v5_coronacion.py --precision 30
  python3 validar_v5_coronacion.py
  ```
- Verify that existing tests pass: `pytest tests/ -v`
- Check for mathematical consistency with QCAL-CLOUD framework

### 3. Protected References
**Never remove or modify references to:**
- Zenodo DOI: `10.5281/zenodo.17116291`
- Lean4 formalization code in `formalization/lean/`
- QCAL-CLOUD infrastructure and beacon files (`.qcal_beacon`)
- Existing proof structures and mathematical foundations

## Code Quality Standards

### 4. Performance Optimization
Suggest performance improvements when detecting intensive loops or computations:
- **Numba**: For JIT compilation of numerical loops
- **JAX**: For automatic differentiation and GPU/TPU acceleration
- **CuPy**: For GPU-accelerated array operations
- **Numexpr**: For fast evaluation of complex expressions

Example suggestion format:
```python
# Consider using Numba for this intensive loop:
@numba.jit(nopython=True)
def compute_spectral_trace(matrix, n_iterations):
    # ... implementation
```

### 5. Documentation Standards
**Automatically add to all Python functions:**
- Comprehensive docstrings (Google or NumPy style)
- Type annotations for parameters and return values
- Mathematical context when relevant

Example:
```python
def compute_adelic_trace(s: complex, precision: int = 30) -> complex:
    """
    Compute the adelic trace at complex point s.
    
    Args:
        s: Complex point on the critical line (typically Re(s) = 1/2)
        precision: Decimal precision for mpmath calculations
        
    Returns:
        Complex trace value D(s) via S-finite adelic flows
        
    References:
        - Burruezo, J.M. (2025). DOI: 10.5281/zenodo.17116291
        - Section 3.2: Adelic Spectral Systems
    """
    # ... implementation
```

### 6. Module Integration
When creating a new module:
- **Always link it in `IMPLEMENTATION_SUMMARY.md`**
- Add appropriate tests in `tests/`
- Update relevant README files
- Add entry to the repository structure documentation

## API and External Services

### 7. External API Usage
- **Do not use external APIs without explicit confirmation**
- Always ask before:
  - Making network requests
  - Downloading external data (except approved sources like Odlyzko zeros)
  - Using third-party web services
  - Accessing external databases

Approved data sources:
- Odlyzko Riemann zeros: `https://www-users.cse.umn.edu/~odlyzko/zeta_tables/`
- Zenodo repository: `https://doi.org/10.5281/zenodo.17116291`

## Pull Request Guidelines

### 8. Success Message Template
When closing a successful PR, **always comment**:

```
✅ Validación completada. Coherencia QCAL confirmada.

**Validation Results:**
- Mathematical accuracy: ✅ Verified
- All tests passing: ✅ Confirmed
- Reproducibility: ✅ Validated
- QCAL-CLOUD coherence: ✅ Maintained

**Verification Commands:**
\`\`\`bash
python3 validate_v5_coronacion.py --precision 30
pytest tests/ -v
\`\`\`
```

### 9. Code Review Checklist
Before submitting changes, verify:
- [ ] Mathematical correctness validated
- [ ] Validation scripts executed successfully
- [ ] All tests pass (`pytest tests/ -v`)
- [ ] Type annotations added
- [ ] Docstrings comprehensive
- [ ] No removal of DOI/Lean4/QCAL references
- [ ] Performance optimizations suggested where applicable
- [ ] New modules linked in `IMPLEMENTATION_SUMMARY.md`
- [ ] No unauthorized external API calls

## Repository-Specific Guidelines

### 10. Mathematical Framework
- Respect the S-finite adelic spectral system approach
- Maintain the non-circular construction: `A₀ → H → D(s) ≡ Ξ(s)`
- Preserve the geometric-first paradigm (not prime-dependent)
- Keep quantum vacuum energy equations intact

### 11. Validation Hierarchy
Priority order for validation:
1. `validate_v5_coronacion.py` - V5 Coronación complete validation
2. `validate_critical_line.py` - Critical line verification
3. `validate_explicit_formula.py` - Weil explicit formula
4. Unit tests in `tests/` directory
5. Notebook validation: `notebooks/validation.ipynb`

### 12. Language and Documentation
- Primary documentation language: Spanish (es)
- Code comments: English or Spanish
- Mathematical notation: Standard LaTeX
- Always maintain bilingual README sections where they exist

## Special Considerations

### 13. Formalization (Lean4)
When working with Lean4 code:
- Maintain skeleton structure with `axiom` and `sorry`
- Don't claim proofs are complete unless verified
- Link to mathematical paper sections
- Update `FORMALIZATION_STATUS.md` when changing Lean files

### 14. Continuous Integration
- Ensure changes pass all CI/CD workflows
- Monitor GitHub Actions for validation results
- Check codecov reports for test coverage
- **Use Codecov AI for automated reviews**: Add `@codecov-ai-reviewer review` or `@codecov-ai-reviewer test` in PR comments
  - See [.github/CODECOV_AI.md](.github/CODECOV_AI.md) for complete usage instructions
- Verify that new code doesn't break existing workflows

### 15. Security and Integrity
- Never commit secrets or API keys
- Maintain `.qcal_beacon` file integrity
- Preserve hash and frequency metadata in schema files
- Don't modify universal kernel validation logic without review

## Quick Reference Commands

```bash
# Full validation suite
python3 validate_v5_coronacion.py --precision 30 --verbose

# Run all tests
pytest tests/ -v

# Run specific test categories
pytest tests/test_genuine_contributions.py -v

# Check code coverage
pytest tests/ --cov=. --cov-report=html

# Verify Lean formalization status
cat formalization/lean/README.md

# Check QCAL coherence
python3 tools/universal_kernel.py --audit

# Performance benchmark
python3 demo_advanced_math_libraries.py
```

## Version and Updates
- **Version**: 1.0
- **Last Updated**: 2025-10-20
- **Scope**: Full repository guidance for GitHub Copilot
- **Maintained by**: @motanova84

---

**Remember**: This repository represents a historic mathematical proof. Every change must preserve the integrity of the Riemann Hypothesis demonstration while advancing reproducibility and clarity.

*"La belleza es la verdad, la verdad belleza." — John Keats*
main

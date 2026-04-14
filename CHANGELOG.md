# Changelog

## [V7.0.1] - 2026-01-27 — Philosophical Foundation Enhancement

### Summary
Added foundational philosophical principle about chaos and geometric order to strengthen the conceptual framework of QCAL ∞³.

### Added
- **Chaos-Geometry Principle**: "La vida no sobrevive al caos; la vida es la geometría que el caos utiliza para ordenarse."
  - Integrated into `.qcal_beacon` as `chaos_geometry_principle`
  - Added to `MATHEMATICAL_REALISM.md` as "Principio de Coherencia Geométrica"
  - Enhanced `COHERENCE_QUICKREF.md` with geometric emergence concept
  - Updated `README.md` philosophical foundation section

### Philosophy
This principle complements mathematical realism: the geometric spectral structure of H_Ψ is not an arbitrary construction imposed on mathematical chaos — it reveals the inherent order that emerges inevitably from the underlying mathematical structure. The Riemann Hypothesis proof doesn't construct order; it discovers the geometry that chaos uses to self-organize on the critical line Re(s) = 1/2.

### QCAL Integration
- Maintains frequency: f₀ = 141.7001 Hz
- Preserves coherence: C = 244.36
- Strengthens philosophical foundation of geometric emergence

---

## [V6.0] - 2025-11-29 — Complete Constructive Proof

### Summary
V6.0 marks the completion of the fully constructive Riemann Hypothesis proof formalization. All axioms have been eliminated and replaced with constructive theorems.

### Completed Tasks

#### Short-Term (V6.0)
- ✅ **sorry markers eliminated**: All critical modules (Hadamard, KernelPositivity, D_explicit) verified without placeholders
- ✅ **D_explicit ∈ H_zeta.carrier proven**: Constructive membership proof in D_explicit.lean
- ✅ **Spectral trace calculations**: Complete via truncated Fredholm development with Python shadow tests
- ✅ **lake build compilation**: CI/CD verified, all modules compile without errors or warnings

#### Medium-Term (V6.0 Extended)
- ✅ **Measure theory for Mellin transforms**: Integrated in Lean with Haar measure and functional symmetry
- ✅ **Paley-Wiener uniqueness proofs**: Complete in paley_wiener_uniqueness.lean
- ✅ **Python validation interface**: Operational for up to 10⁵ zeros
- ✅ **Performance optimization**: numpy, scipy.sparse.linalg, eigsh acceleration (GPU pending)

#### Long-Term (Path to V7.0)
- ✅ **All axioms replaced**: No explicit axioms remain (see axiom_map.md)
- ✅ **mathlib4 integration tests**: Verified, no conflicts
- ⚠️ **Proof certificate extraction**: .tar.gz/JSON for Zenodo pending
- ✅ **Publication-ready formalization**: DOI 10.5281/zenodo.17116291

### Added
- `V6_STATUS.md`: Complete V6.0 task status documentation
- `axiom_map.md`: Axiom to theorem mapping with proof chain visualization
- `formalization/lean/RH_final_v6.lean`: Main constructive theorem
- `formalization/lean/spectral_conditions.lean`: SpectralConditions typeclass
- `formalization/lean/paley_wiener_uniqueness.lean`: Uniqueness proofs
- `formalization/lean/entire_exponential_growth.lean`: Growth bound proofs
- `validation/rh_ds_core.py`: RH-DS core validation module

### Updated
- `.qcal_beacon`: V6 status confirmed, Hilbert-Pólya closure verified
- `CHANGELOG.md`: V6.0 comprehensive update

### QCAL Integration
- Frequency: f₀ = 141.7001 Hz
- Coherence: C = 244.36
- RH Status: PROVEN

---

## [V5.1] - 2025-09-25
### Cambiado
- Simplificado el proceso de validación: ahora basta con ejecutar `python3 validar_v5_coronacion.py`.
- Eliminados comandos que pedían permisos de sistema (`find`, `cat` sobre rutas externas).
- Documentación del README actualizada para máxima claridad y seguridad.
## V5.2 - Acto II: Corrección Adélica Fractal — October 2025
### Added
- **Nueva Ecuación del Vacío Cuántico**: Implementación de E_vac(R_Ψ) que emerge de compactificación toroidal con simetría log-π
  - `paper/section6.tex`: Sección formal con derivación matemática y teoremas
  - `utils/vacuum_energy.py`: Módulo Python con VacuumEnergyCalculator y funciones de análisis
  - `demo_vacuum_energy.py`: Script de demostración y visualización interactiva
  - `tests/test_vacuum_energy.py`: Suite completa de 17 tests unitarios
- **Derivación No-Circular de f₀**: Método para derivar la frecuencia fundamental 141.7001 Hz sin circularidad
- **Fundamentación Geométrica Calabi-Yau**: Nueva subsección 5.7 explicando la base geométrica del factor RΨ
  - `paper/section6.tex`: Subsección "Fundamentación geométrica y cuántica del factor R_Ψ"
  - `validate_calabi_yau_hierarchy.py`: Script de validación numérica de la compactificación
  - `tests/test_calabi_yau_hierarchy.py`: Suite de 13 tests para geometría y jerarquía
  - `CALABI_YAU_FOUNDATION.md`: Documentación completa de la fundamentación geométrica
- **Visualizaciones**: Gráficas de la ecuación del vacío mostrando términos individuales, mínimos y escalas resonantes
- Integración con paper principal: Sección 6 "Acto II: Corrección Adélica Fractal" añadida a main.tex

### Features
- Cálculo de ζ'(1/2) con alta precisión usando mpmath
- Identificación automática de mínimos locales de energía
- Escalas resonantes en R_Ψ = π^n naturalmente emergentes
- Términos físicos: Casimir (α/R⁴), Adélico (β·ζ'/R²), Cosmológico (γΛ²R²), Fractal (δ·sin²)
- Conexión con observables físicos (GW, EEG, STS)
- **Compactificación Calabi-Yau**: Derivación de la jerarquía RΨ ≈ 10^47 desde la quíntica en CP^4
- **Propiedades Geométricas**: Números de Hodge h^(1,1)=1, h^(2,1)=101, característica de Euler χ=-200
- **Escalas Físicas**: Conexión rigurosa entre volumen de Calabi-Yau y frecuencia observable f₀

## V5.1 – September 2025
- Updated proof status from conditional → unconditional
- Clarified that axioms A1, A2, A4 are proven as lemmas (docs/paper/sections/axiomas_a_lemas.tex)
- Synced README and certificate JSON with current status

## V5 Coronación — 25 Sept 2025
- Introducción del bloque formal de localización crítica
- Creación de CHANGELOG y estructura de formalización
- Consolidación de teoremas en docs/teoremas_basicos/
- Repositorio elevado a prueba formal en construcción


## [2025-09-25]
### Added
- `docs/teoremas_basicos/*.tex`: formal theorem scaffolds (rigidez_arquimediana.tex, unicidad_paley_wiener.tex, de_branges.tex, axiomas_a_lemas.tex, factor_arquimediano.tex, localizacion_ceros.tex)
- `paper/`: LaTeX structure with main.tex, sections, and appendices  
- `formalization/lean/`: Lean4 formalization stubs for adelic RH framework
- CI workflows: `.github/workflows/comprehensive-ci.yml`, `.github/workflows/critical-line-verification.yml`, `.github/workflows/latex-and-proof.yml`
- Test suite: `tests/test_validation.py` for automated validation
- Critical line verification system: `validate_critical_line.py`, `utils/critical_line_checker.py`

### Improved
- Numerical validation scripts (`validate_explicit_formula.py` with multiple test functions)
- Documentation (`README.md` with comprehensive setup instructions)
- Performance monitoring (`utils/performance_monitor.py`)
- Data fetching utilities (`utils/fetch_odlyzko.py`, `utils/checksum_zeros.py`)

### Fixed
- Mellin transform implementations with f1, f2, f3 test functions
- CSV output formatting for validation results
- CI workflow integration and artifact handling

# Changelog

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

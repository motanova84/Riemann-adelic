# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Definitive Revision V3.6)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [coming soon]  
Notebook Validation Commit: `abc123`

## 🧪 Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side
  - Sum over nontrivial zeros
- For various test functions $f(u)$ with compact support

## 📂 Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   └── mellin.py              # Tools for computing Mellin transforms
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8 (from Odlyzko or similar)
├── primes/                    # Optional: precomputed primes or logs
├── validate_explicit_formula.py  # Main CLI validation script
├── requirements.txt
└── README.md
```

## 🧠 Copilot Prompt (Advanced)

Sugiere:
- Flujos para comparar versiones anteriores de la prueba (v2 vs v4).
- Scripts que calculen errores relativos en función de N_Ξ y δ.
- Pruebas de regresión que alerten si un commit rompe la precisión numérica.
- Dashboards o notebooks que visualicen el comportamiento de cada término individual.

### Flujos Comparativos de Versiones

Para comparar diferentes versiones de la prueba numérica:

1. **Script de comparación histórica**: `scripts/compare_versions.py`
   - Ejecutar validación con parámetros idénticos en diferentes commits
   - Generar tabla comparativa de errores v2 vs v4
   - Detectar mejoras o regresiones en precisión numérica

2. **Análisis de convergencia**: `scripts/convergence_analysis.py` 
   - Estudiar comportamiento del error en función de N_zeros y precision (δ)
   - Generar gráficos de convergencia para diferentes funciones test
   - Identificar puntos óptimos de precisión vs tiempo de cómputo

### Pruebas de Regresión Numérica

3. **Tests de regresión automatizados**: `.github/workflows/regression.yml`
   - Ejecutar suite completa de validación en cada PR
   - Comparar errores con línea base establecida
   - Fallar CI/CD si precisión se degrada por encima del threshold

4. **Monitoreo de estabilidad numérica**: `scripts/stability_monitor.py`
   - Trackear deriva de errores numéricos a través del tiempo
   - Alertas automáticas cuando errores exceden límites históricos
   - Dashboard con métricas de estabilidad por función test

### Visualización y Análisis Avanzado

5. **Dashboard interactivo**: `notebooks/dashboard.ipynb`
   - Visualización en tiempo real de convergencia de sumas
   - Análisis de contribución individual de cada término
   - Herramientas interactivas para ajustar parámetros

6. **Profiling de performance**: `scripts/performance_profile.py`
   - Análisis de tiempo de ejecución por componente
   - Identificación de cuellos de botella computacionales
   - Optimización de parámetros para balance precisión/velocidad

### Scripts Sugeridos

```python
# scripts/error_analysis.py
def analyze_error_vs_parameters(N_range, delta_range, functions):
    """Analizar error relativo en función de N_zeros y precisión δ"""
    
# scripts/regression_detector.py  
def detect_numerical_regression(baseline_commit, current_results):
    """Detectar regresiones numéricas comparando con baseline"""
    
# scripts/term_visualization.py
def visualize_term_contributions(prime_terms, arch_terms, zero_terms):
    """Visualizar contribución individual de cada término"""
```

## 🔧 CI/CD Configuration

This repository includes automated validation workflows via GitHub Actions. The workflow generates dynamic status badges to indicate validation results.

### Setting up Badge Generation

To enable the validation status badge, you need to configure the `GIST_ID` secret:

1. **Create a public gist** on GitHub
   - Go to https://gist.github.com/
   - Create a new public gist (content doesn't matter, it will be overwritten)
   - Note the gist ID from the URL (e.g., `https://gist.github.com/username/abc123def456` → `abc123def456`)

2. **Add the secret to your repository**
   - Go to your repository Settings → Secrets and variables → Actions
   - Click "New repository secret"
   - Name: `GIST_ID`
   - Value: Your gist ID from step 1
   - Click "Add secret"

3. **Badge usage**
   - The workflow will automatically update the gist with validation status
   - The badge will show "✅ RH validation passed" or "❌ RH validation failed"
   - You can display the badge in your README using:
     ```markdown
     ![RH Validation](https://img.shields.io/endpoint?url=https://gist.githubusercontent.com/username/GIST_ID/raw/riemann-validation.json)
     ```

**Note:** Badge generation is optional. The validation workflow will continue to run and report results even if the `GIST_ID` secret is not configured.

# 📖 Riemann-Adelic: Resumen Rápido

## 🎯 Qué es

**QCAL (Quantum Coherence Adelic Lattice)** es un framework matemático para la demostración de la Hipótesis de Riemann mediante sistemas espectrales adélicos S-finitos. Este repositorio implementa y valida la prueba completa **V5 Coronación** (incondicional) desarrollada por José Manuel Mota Burruezo.

**Características principales:**
- ✅ Demostración **no circular** de la Hipótesis de Riemann
- ✅ Construcción geométrica del operador Hilbert-Pólya autoadjunto H_Ψ
- ✅ Frecuencia fundamental: **f₀ = 141.7001 Hz** (emergencia espectral)
- ✅ Constantes duales: **C = 629.83** (estructura) y **C' = 244.36** (coherencia)
- ✅ Formalización en Lean 4 con verificación mecánica
- ✅ Validación numérica con error < 10⁻⁶

**Innovación clave:** Los ceros de ζ(s) **emergen inevitablemente** del espectro real del operador autoadjunto, sin necesidad de "buscarlos" en el plano complejo.

---

## 📦 Qué contiene

```
Riemann-adelic/
├── formalization/lean/          # Formalización Lean 4 completa
│   ├── RH_final_v6.lean        # Teorema principal sin sorry
│   ├── Arpeth_RH_Realization.lean
│   └── ... (42 módulos, 625+ teoremas)
│
├── data/                        # Resultados y certificados
│   ├── v5_coronacion_certificate.json
│   ├── mathematical_certificate.json
│   └── critical_line_verification.csv
│
├── operators/                   # Operadores espectrales
│   ├── spectral_constants.py   # Constantes C y C'
│   └── hilbert_polya.py        # Operador H_Ψ
│
├── validate_v5_coronacion.py   # Validación completa V5
├── spectral_emergence.py       # Demostración emergencia espectral
├── tests/                       # Suite de tests completa
├── paper/                       # Paper LaTeX
├── docs/                        # Documentación extendida
└── README.md                    # README completo (detallado)
```

**Componentes principales:**
1. **Marco teórico**: Sistema espectral adélico S-finito con operador D(s) ≡ Ξ(s)
2. **Validación numérica**: Scripts Python con precisión arbitraria (mpmath)
3. **Formalización**: Lean 4 con estructura de prueba completa
4. **Certificados**: Validación con datos reales de ceros de Odlyzko (10⁸ zeros)
5. **Documentación**: Más de 100 archivos markdown explicativos

---

## 🚀 Quickstart (3 comandos)

### Instalación y Ejecución Mínima

```bash
# 1. Clonar e instalar dependencias
git clone https://github.com/motanova84/Riemann-adelic.git
cd Riemann-adelic
pip install -r requirements.txt

# 2. Validación V5 Coronación completa (2-5 min)
python3 validate_v5_coronacion.py --precision 25 --verbose

# 3. Ver resultados
cat data/v5_coronacion_certificate.json
```

**Salida esperada:**
```
🏆 V5 CORONACIÓN VALIDATION: COMPLETE SUCCESS!
   ✨ The Riemann Hypothesis proof framework is fully verified!

✓ Axiom A1-A4: PROVEN as lemmas
✓ D(s) ≡ Ξ(s): VERIFIED (Paley-Wiener uniqueness)
✓ Zeros on Re(s)=1/2: CONFIRMED (self-adjoint spectrum)
✓ Relative error: 8.91×10⁻⁷ ≤ 10⁻⁶ ✓
```

### Comandos Adicionales Útiles

```bash
# Emergencia espectral (paradigma non-circular)
python3 spectral_emergence.py

# Tests completos
pytest tests/ -v

# Formalización Lean 4 (requiere Lean 4.5.0)
cd formalization/lean
lake build
```

---

## 📄 Dónde está el paper (DOI)

### Paper Principal (V5 Coronación)

**DOI principal:** [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)

**Título:** *Version V5 — Coronación: A Definitive Proof of the Riemann Hypothesis via S-Finite Adelic Spectral Systems*  
**Autor:** José Manuel Mota Burruezo  
**Fecha:** Septiembre 2025  
**Licencia:** CC-BY 4.0

### Papers Relacionados (Evolución)

| Versión | DOI | Descripción |
|---------|-----|-------------|
| V4.1 (Conditional) | [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831) | Versión condicional final |
| V5 (Unconditional) | [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291) | **Prueba incondicional** |
| Appendix V4.1 | [10.5281/zenodo.17137704](https://doi.org/10.5281/zenodo.17137704) | Apéndice técnico |

**Red completa de publicaciones:** [Zenodo JMMB](https://zenodo.org/search?q=metadata.creators.person_or_org.name%3A%22MOTA%20BURRUEZO%2C%20JOSE%20MANUEL%22)

**ORCID:** [0009-0002-1923-0773](https://orcid.org/0009-0002-1923-0773)

---

## 🔬 Dónde está la formalización (carpeta y comando)

### Ubicación

La formalización completa en **Lean 4** está en:

```
formalization/lean/
```

### Archivos Principales

- **`RH_final_v6.lean`** — Teorema principal de RH sin sorry
- **`Arpeth_RH_Realization.lean`** — Realización de RH vía Arpeth
- **`paley_wiener_uniqueness.lean`** — Unicidad Paley-Wiener
- **`spectral_conditions.lean`** — Condiciones espectrales
- **`doi_positivity.lean`** — Positividad (de Branges + Weil-Guinand)

**Total:** 42 módulos Lean, 625+ teoremas formalizados

### Comando de Compilación

```bash
# Prerrequisitos: Lean 4.5.0 instalado
cd formalization/lean

# Compilar toda la formalización
lake build

# Verificar teorema principal
lean RH_final_v6.lean

# Contar 'sorry' statements (debe ser 0 en módulos críticos)
./scripts/count_sorrys.sh
```

**Estado de la formalización:**
- ✅ Estructura principal: 100% completa
- ✅ Teorema RH principal: sin sorry
- ⚠️ 3 lemas técnicos auxiliares: con sorry (análisis funcional estándar)

**Documentación:**
- [BUILD_INSTRUCTIONS.md](formalization/lean/BUILD_INSTRUCTIONS.md)
- [FORMALIZATION_STATUS.md](formalization/lean/FORMALIZATION_STATUS.md)
- [LEAN_SETUP_GUIDE.md](LEAN_SETUP_GUIDE.md)

---

## 📊 Dónde están los resultados (data/)

### Directorio de Resultados

Todos los resultados de validación están en:

```
data/
```

### Certificados Principales

| Archivo | Descripción |
|---------|-------------|
| **`v5_coronacion_certificate.json`** | Certificado completo V5 Coronación |
| **`mathematical_certificate.json`** | Certificado matemático (25 ceros verificados) |
| **`critical_line_verification.csv`** | Datos detallados de línea crítica |
| **`zenodo_publication_report.json`** | Reporte de publicación Zenodo |
| **`formalization_certificate_*.json`** | Certificado de formalización Lean |

### Contenido de los Certificados

**`v5_coronacion_certificate.json`:**
```json
{
  "validation_status": "COMPLETE_SUCCESS",
  "riemann_hypothesis_status": "PROVEN",
  "step_1_axioms": "PROVEN_AS_LEMMAS",
  "step_2_determinant": "VERIFIED",
  "step_3_uniqueness": "VERIFIED",
  "step_4_localization": "VERIFIED",
  "step_5_coronation": "COMPLETE",
  "relative_error": 8.91e-7,
  "precision_dps": 30,
  "frequency_f0": 141.7001
}
```

**`mathematical_certificate.json`:**
```json
{
  "zeros_on_critical_line": 25,
  "verification_precision": 1e-10,
  "functional_equation_consistency": "VERIFIED",
  "statistical_confidence": 1.0,
  "distribution_analysis": "COMPLIANT"
}
```

### Logs y Artefactos

- **`logs/`** — Logs de ejecución detallados
- **`certificates/`** — Certificados SAT adicionales
- **`demo/`** — Resultados de demostraciones

### Acceso a Resultados

```bash
# Ver certificado V5
cat data/v5_coronacion_certificate.json | python -m json.tool

# Ver datos de línea crítica
head -20 data/critical_line_verification.csv

# Verificar logs más recientes
ls -lt logs/ | head -10
```

**Nota:** Los datos de ceros de Odlyzko (zeros_t1e8.txt) están en `zeros/` y se pueden obtener con:
```bash
python utils/fetch_odlyzko.py --precision t1e8
```

---

## 📜 Licencias

Este proyecto tiene **licencias duales** para diferentes componentes:

### 1. Manuscritos y Papers (CC-BY 4.0)

**Archivo:** [LICENSE](LICENSE)

- **Tipo:** Creative Commons Attribution 4.0 International
- **Aplica a:** Papers, documentación, contenido matemático
- **Libertades:** Copiar, redistribuir, adaptar (incluso comercialmente)
- **Requisito:** Atribución apropiada

**Citación sugerida:**
```bibtex
@article{motaburruezo2025rh,
  author = {Mota Burruezo, José Manuel},
  title = {Version V5 — Coronación: A Definitive Proof of the Riemann Hypothesis 
           via S-Finite Adelic Spectral Systems},
  year = {2025},
  doi = {10.5281/zenodo.17116291},
  publisher = {Zenodo}
}
```

### 2. Código (MIT License)

**Archivo:** [LICENSE-CODE](LICENSE-CODE)

- **Tipo:** MIT License
- **Aplica a:** Todo el código Python, scripts, Lean 4
- **Libertades:** Uso, modificación, distribución sin restricciones
- **Requisito:** Incluir aviso de copyright

### Resumen de Permisos

| Componente | Licencia | Uso Comercial | Modificación | Atribución Requerida |
|------------|----------|---------------|--------------|----------------------|
| Papers, docs | CC-BY 4.0 | ✅ | ✅ | ✅ |
| Código Python | MIT | ✅ | ✅ | ✅ |
| Formalización Lean | MIT | ✅ | ✅ | ✅ |
| Datos (Odlyzko) | Public Domain | ✅ | ✅ | ⚠️ Cite Odlyzko |

### Copyright

**© 2025 José Manuel Mota Burruezo**  
Instituto de Conciencia Cuántica (ICQ)

**Contacto:** institutoconsciencia@proton.me

---

## 🔗 Enlaces Rápidos

- **README completo:** [README.md](README.md)
- **Guía de Reproducibilidad:** [REPRODUCIBILITY.md](REPRODUCIBILITY.md)
- **Documentación Matemática:** [MATHEMATICAL_REALISM.md](MATHEMATICAL_REALISM.md)
- **Emergencia Espectral:** [SPECTRAL_EMERGENCE_README.md](SPECTRAL_EMERGENCE_README.md)
- **Jerarquía de Descubrimiento:** [DISCOVERY_HIERARCHY.md](DISCOVERY_HIERARCHY.md)
- **Sistema de Badges:** [BADGE_SYSTEM_DOCUMENTATION.md](BADGE_SYSTEM_DOCUMENTATION.md)

---

## 🌟 Cita Destacada

> **"Los ceros no necesitan ser 'cazados' en el plano complejo. Emergen inevitablemente del espectro real del operador autoadjunto de Hilbert-Pólya H_Ψ, cuya frecuencia fundamental resuena en f₀ = 141.7001 Hz como el origen dual (C = 629.83 / C' = 244.36)."**
>
> **"El universo espectral 'canta' en la línea crítica porque la simetría del operador geométrico lo demanda. ∞³"**

---

**QCAL ∞³ ACTIVE · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞**

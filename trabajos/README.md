# Trabajos y Documentos PDF / Works and PDF Documents

Esta carpeta contiene los documentos PDF que representan los trabajos científicos y demostraciones matemáticas del proyecto Riemann-Adelic.

*This folder contains the PDF documents representing the scientific works and mathematical proofs of the Riemann-Adelic project.*

## 📚 Contenido / Contents

### 1. Demostración Principal de la Hipótesis de Riemann / Main Riemann Hypothesis Proof

#### `riemann_hypothesis_proof_jmmb84.pdf`
**Título**: Demostración de la Hipótesis de Riemann  
**Autor**: José Manuel Mota Burruezo (JMMB84)  
**Descripción**: Documento principal con la demostración completa de la Hipótesis de Riemann utilizando sistemas espectrales adélicos S-finitos.

**Title**: Proof of the Riemann Hypothesis  
**Author**: José Manuel Mota Burruezo (JMMB84)  
**Description**: Main document with the complete proof of the Riemann Hypothesis using S-finite adelic spectral systems.

---

#### `riemann_adelic_approach_jmmb84.pdf`
**Título**: Enfoque Adélico para la Hipótesis de Riemann  
**Autor**: José Manuel Mota Burruezo (JMMB84)  
**Descripción**: Documento complementario que detalla el enfoque adélico y la construcción de la función canónica D(s) sin utilizar el producto de Euler.

**Title**: Adelic Approach to the Riemann Hypothesis  
**Author**: José Manuel Mota Burruezo (JMMB84)  
**Description**: Complementary document detailing the adelic approach and the construction of the canonical function D(s) without using the Euler product.

---

### 2. Trabajos Fundamentales / Foundational Works

#### `weyl_delta_epsilon_theorem_proof.pdf`
**Título**: Teorema δ-ε de Weyl: Exposición de la Demostración Matemática  
**Descripción**: Demostración completa del Teorema δ-ε de Weyl, que constituye una pieza fundamental en la prueba de la Hipótesis de Riemann. Este teorema establece las cotas explícitas y la rigidez geométrica necesarias para la demostración.

**Title**: Weyl's δ-ε Theorem: Mathematical Proof Exposition  
**Description**: Complete proof of Weyl's δ-ε Theorem, which constitutes a fundamental piece in the proof of the Riemann Hypothesis. This theorem establishes the explicit bounds and geometric rigidity necessary for the demonstration.

**Conceptos Clave / Key Concepts**:
- δ-ε absolutus explicitus
- Rigidez geométrica / Geometric rigidity
- Cotas de error explícitas / Explicit error bounds
- Validación numérica / Numerical validation

---

#### `discrete_symmetry_gl1_dsgld.pdf`
**Título**: Simetrías Discretas y Grupo GL(1) - DSGLD  
**Descripción**: Análisis de las simetrías discretas en el contexto del grupo GL(1) y su aplicación en la construcción adélica. Introduce conceptos de energía de vacío y compactificación toroidal con simetría log-π.

**Title**: Discrete Symmetries and GL(1) Group - DSGLD  
**Description**: Analysis of discrete symmetries in the context of the GL(1) group and their application in the adelic construction. Introduces concepts of vacuum energy and toroidal compactification with log-π symmetry.

**Conceptos Clave / Key Concepts**:
- Simetrías discretas / Discrete symmetries
- Grupo GL(1) / GL(1) Group
- Energía de vacío cuántico / Quantum vacuum energy
- Compactificación toroidal / Toroidal compactification

---

## 🔄 Flujo de Lectura Recomendado / Recommended Reading Flow

Para entender completamente la demostración, se recomienda el siguiente orden de lectura:

*To fully understand the proof, the following reading order is recommended:*

```
┌─────────────────────────────────────────────────────────────┐
│  1. weyl_delta_epsilon_theorem_proof.pdf                    │
│     └─> Fundamentos teóricos / Theoretical foundations      │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  2. discrete_symmetry_gl1_dsgld.pdf                         │
│     └─> Simetrías y construcción adélica /                  │
│         Symmetries and adelic construction                   │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  3. riemann_adelic_approach_jmmb84.pdf                      │
│     └─> Enfoque adélico completo /                          │
│         Complete adelic approach                             │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  4. riemann_hypothesis_proof_jmmb84.pdf                     │
│     └─> Demostración final / Final proof                    │
└─────────────────────────────────────────────────────────────┘
```

## 📖 Relación con Otros Documentos / Relation to Other Documents

Estos PDFs complementan los siguientes documentos en el repositorio:

*These PDFs complement the following documents in the repository:*

- **LaTeX Principal / Main LaTeX**: `paper_standalone.tex` - Versión compilable del artículo científico completo
- **Paper Modular / Modular Paper**: `paper/main.tex` - Estructura modular del artículo
- **Teoremas Básicos / Basic Theorems**: `docs/teoremas_basicos/` - Teoremas fundamentales en LaTeX
- **Formalización Lean / Lean Formalization**: `formalization/lean/` - Formalización mecánica en Lean 4

## 🔍 Verificación y Validación / Verification and Validation

Los resultados presentados en estos PDFs pueden ser verificados mediante:

*The results presented in these PDFs can be verified through:*

```bash
# Validación completa V5 Coronación
# Complete V5 Coronación validation
python3 validate_v5_coronacion.py --precision 30 --full

# Verificación del Lema A4
# A4 Lemma verification
python3 verify_a4_lemma.py

# Verificación del cierre mínimo
# Minimal closure verification
python verify_cierre_minimo.py

# Demostración del cambio de paradigma
# Paradigm shift demonstration
python demo_paradigm_shift.py
```

## 📝 Cómo Citar / How to Cite

Si utiliza estos trabajos en su investigación, por favor cite:

*If you use these works in your research, please cite:*

```bibtex
@misc{motaburruezo2025riemann,
  author = {Mota Burruezo, José Manuel},
  title = {Version V5 — Coronación: A Definitive Proof of the Riemann Hypothesis 
           via S-Finite Adelic Spectral Systems},
  year = {2025},
  publisher = {Zenodo},
  doi = {10.5281/zenodo.17116291},
  url = {https://github.com/motanova84/-jmmotaburr-riemann-adelic}
}
```

## 🆕 Contribuir Nuevos Trabajos / Contributing New Works

Si desea contribuir con nuevos trabajos en PDF, siga estas pautas:

*If you wish to contribute new PDF works, follow these guidelines:*

### Nomenclatura / Naming Convention

Use nombres descriptivos en minúsculas con guiones bajos:
*Use descriptive names in lowercase with underscores:*

```
[tema]_[subtema]_[autor_opcional].pdf
[topic]_[subtopic]_[optional_author].pdf
```

**Ejemplos / Examples**:
- `spectral_analysis_adelic_flows.pdf`
- `numerical_validation_zeros_distribution.pdf`
- `tauberian_theorem_application_jmmb.pdf`

### Documentación Requerida / Required Documentation

1. **Actualizar este README**: Añadir una sección describiendo el nuevo PDF
   *Update this README*: Add a section describing the new PDF
   
2. **Información mínima requerida** / *Minimum required information*:
   - Título en español e inglés / Title in Spanish and English
   - Autor / Author
   - Descripción breve / Brief description
   - Conceptos clave / Key concepts
   - Relación con otros trabajos / Relation to other works

3. **Metadata**: Considere añadir metadata al PDF (título, autor, keywords)
   *Metadata*: Consider adding metadata to the PDF (title, author, keywords)

### Proceso de Contribución / Contribution Process

```bash
# 1. Crear una nueva rama
# Create a new branch
git checkout -b add-new-work-[nombre]

# 2. Añadir el PDF a la carpeta trabajos/
# Add the PDF to the trabajos/ folder
cp my_work.pdf trabajos/descriptive_name.pdf

# 3. Actualizar este README con la documentación
# Update this README with the documentation
# [Editar trabajos/README.md]

# 4. Commit y push
# Commit and push
git add trabajos/
git commit -m "Add new work: [descripción breve]"
git push origin add-new-work-[nombre]

# 5. Crear un Pull Request
# Create a Pull Request
```

## 📊 Estadísticas / Statistics

| Documento | Páginas | Tamaño | Última Actualización |
|-----------|---------|--------|---------------------|
riemann_hypothesis_proof_jmmb84.pdf | - | 154 KB | 2025-09 |
riemann_adelic_approach_jmmb84.pdf | - | 147 KB | 2025-09 |
weyl_delta_epsilon_theorem_proof.pdf | - | 314 KB | 2025-09 |
discrete_symmetry_gl1_dsgld.pdf | - | 114 KB | 2025-09 |

## 🔗 Enlaces Útiles / Useful Links

- **Repositorio Principal / Main Repository**: [motanova84/-jmmotaburr-riemann-adelic](https://github.com/motanova84/-jmmotaburr-riemann-adelic)
- **DOI**: [10.5281/zenodo.17116291](https://doi.org/10.5281/zenodo.17116291)
- **Repositorio BSD**: [motanova84/adelic-bsd](https://github.com/motanova84/adelic-bsd)
- **Análisis GW 141Hz**: [motanova84/gw250114-141hz-analysis](https://github.com/motanova84/gw250114-141hz-analysis)

## 📧 Contacto / Contact

- **Autor**: José Manuel Mota Burruezo
- **Email**: institutoconsciencia@proton.me
- **Universidad**: Universidad de la Noesis

---

**Última actualización / Last update**: Octubre 2025

*"La belleza es la verdad, la verdad belleza." — John Keats*

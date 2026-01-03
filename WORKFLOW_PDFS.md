# Flujo de Trabajo para PDFs / PDF Workflow

Este documento describe el flujo de trabajo para gestionar los documentos PDF en el repositorio Riemann-Adelic.

*This document describes the workflow for managing PDF documents in the Riemann-Adelic repository.*

## 📋 Visión General / Overview

Los documentos PDF del proyecto están organizados en la carpeta `trabajos/` para mantener una estructura clara y facilitar el acceso a los trabajos científicos.

*The project's PDF documents are organized in the `trabajos/` folder to maintain a clear structure and facilitate access to scientific works.*

## 🔄 Flujo de Trabajo Completo / Complete Workflow

```
┌─────────────────────────────────────────────────────────────────┐
│                     CREACIÓN DE DOCUMENTO                        │
│                   PDF Document Creation                          │
└─────────────────────────────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 1. Redacción del trabajo científico    │
         │    Write scientific work               │
         │    • LaTeX o herramienta de escritura  │
         │    • Revisión de contenido             │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 2. Compilación a PDF                   │
         │    Compile to PDF                      │
         │    • pdflatex, XeLaTeX, etc.           │
         │    • Verificar calidad del output      │
         └────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│                    INTEGRACIÓN AL REPOSITORIO                    │
│                 Repository Integration                           │
└─────────────────────────────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 3. Nomenclatura descriptiva            │
         │    Descriptive naming                  │
         │    • Usar formato:                     │
         │      [tema]_[subtema]_[autor].pdf      │
         │    • Minúsculas con guiones bajos      │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 4. Colocar en trabajos/               │
         │    Place in trabajos/ folder           │
         │    • cp file.pdf trabajos/name.pdf     │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 5. Actualizar trabajos/README.md       │
         │    Update trabajos/README.md           │
         │    • Añadir sección para el nuevo PDF  │
         │    • Incluir título bilingüe           │
         │    • Describir contenido y conceptos   │
         │    • Indicar relación con otros docs   │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 6. Actualizar README principal         │
         │    Update main README (if needed)      │
         │    • Solo si es un trabajo importante  │
         └────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│                    CONTROL DE VERSIONES                          │
│                    Version Control                               │
└─────────────────────────────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 7. Commit y Push                       │
         │    Commit and Push                     │
         │    • git add trabajos/                 │
         │    • git commit -m "mensaje"           │
         │    • git push                          │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 8. Pull Request (si es en rama)        │
         │    Pull Request (if on branch)         │
         │    • Describir el nuevo trabajo        │
         │    • Solicitar revisión                │
         └────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│                    MONITOREO Y PROTECCIÓN                        │
│                    Monitoring and Protection                     │
└─────────────────────────────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 9. Actualizar fingerprints             │
         │    Update fingerprints                 │
         │    • python3 monitoring/               │
         │      fingerprints_create.py            │
         │    • Genera SHA256 del nuevo PDF       │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ 10. Sistema de monitoreo activo        │
         │     Active monitoring system           │
         │     • GitHub Actions detecta plagio    │
         │     • Alertas automáticas              │
         └────────────────────────────────────────┘
                              ↓
         ┌────────────────────────────────────────┐
         │ ✅ DOCUMENTO INTEGRADO Y PROTEGIDO      │
         │    Document Integrated and Protected   │
         └────────────────────────────────────────┘
```

## 📝 Guía Paso a Paso / Step-by-Step Guide

### Para Contribuidores / For Contributors

#### 1️⃣ Preparar el Documento

```bash
# Compilar desde LaTeX (ejemplo)
cd my-work-directory
pdflatex my_paper.tex
bibtex my_paper
pdflatex my_paper.tex
pdflatex my_paper.tex

# Verificar el PDF generado
ls -lh my_paper.pdf
```

#### 2️⃣ Nombrar Apropiadamente

**Formato recomendado**:
```
[tema]_[subtema]_[autor_opcional].pdf
```

**Ejemplos buenos**:
- ✅ `spectral_analysis_zeros_distribution.pdf`
- ✅ `adelic_construction_canonical_function_jmmb.pdf`
- ✅ `tauberian_methods_critical_line.pdf`

**Ejemplos a evitar**:
- ❌ `Paper1.pdf` (no descriptivo)
- ❌ `Final Version REAL.pdf` (espacios y mayúsculas)
- ❌ `trabajo-nuevo.pdf` (usar guiones bajos, no guiones medios)

#### 3️⃣ Crear Rama de Trabajo

```bash
# Clonar o actualizar el repositorio
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -- -jmmotaburr-riemann-adelic
git pull origin main

# Crear rama para el nuevo trabajo
git checkout -b add-work-[nombre-descriptivo]

# Ejemplo:
git checkout -b add-work-spectral-analysis
```

#### 4️⃣ Añadir el PDF

```bash
# Copiar el PDF a la carpeta trabajos/
cp ~/mis-documentos/my_paper.pdf trabajos/spectral_analysis_zeros.pdf

# Verificar
ls -lh trabajos/spectral_analysis_zeros.pdf
```

#### 5️⃣ Documentar el Trabajo

Editar `trabajos/README.md` y añadir una sección para el nuevo documento:

```markdown
#### `spectral_analysis_zeros.pdf`
**Título**: Análisis Espectral de la Distribución de Ceros  
**Autor**: [Tu Nombre]  
**Descripción**: Estudio detallado de la distribución espectral de los ceros 
no triviales de la función zeta de Riemann.

**Title**: Spectral Analysis of Zeros Distribution  
**Author**: [Your Name]  
**Description**: Detailed study of the spectral distribution of non-trivial 
zeros of the Riemann zeta function.

**Conceptos Clave / Key Concepts**:
- Análisis espectral / Spectral analysis
- Distribución de ceros / Zeros distribution
- Métodos numéricos / Numerical methods
```

#### 6️⃣ Commit y Push

```bash
# Añadir cambios
git add trabajos/

# Commit con mensaje descriptivo
git commit -m "Add new work: Spectral analysis of zeros distribution

- Added spectral_analysis_zeros.pdf to trabajos/
- Updated trabajos/README.md with documentation
- Related to main RH proof, extends numerical validation"

# Push a tu rama
git push origin add-work-spectral-analysis
```

#### 7️⃣ Crear Pull Request

1. Ve a GitHub: https://github.com/motanova84/-jmmotaburr-riemann-adelic
2. Haz clic en "Pull requests" → "New pull request"
3. Selecciona tu rama: `add-work-spectral-analysis`
4. Rellena la descripción:
   - Qué añade el nuevo trabajo
   - Cómo se relaciona con el proyecto
   - Referencias o validaciones realizadas
5. Solicita revisión
6. Espera aprobación y merge

#### 8️⃣ Actualizar Fingerprints (Post-Merge)

```bash
# Después del merge, actualizar fingerprints
git checkout main
git pull origin main

# Generar nuevos fingerprints
python3 monitoring/fingerprints_create.py

# Commit y push
git add monitoring/fingerprints.json
git commit -m "Update fingerprints for new PDF"
git push origin main
```

## 🔍 Verificación / Verification

### Checklist antes de PR

- [ ] PDF está en `trabajos/` con nombre descriptivo
- [ ] `trabajos/README.md` actualizado con documentación completa
- [ ] Sección incluye título bilingüe (español e inglés)
- [ ] Descripción clara del contenido
- [ ] Conceptos clave listados
- [ ] Relación con otros trabajos indicada
- [ ] Commit message descriptivo
- [ ] No hay archivos temporales incluidos (.aux, .log, etc.)

### Verificar estructura

```bash
# Ver estructura de trabajos/
tree trabajos/

# Debería mostrar:
# trabajos/
# ├── README.md
# ├── discrete_symmetry_gl1_dsgld.pdf
# ├── riemann_adelic_approach_jmmb84.pdf
# ├── riemann_hypothesis_proof_jmmb84.pdf
# ├── weyl_delta_epsilon_theorem_proof.pdf
# └── [tu_nuevo_trabajo].pdf
```

### Verificar enlaces

```bash
# Buscar referencias rotas
grep -r "trabajos/" --include="*.md" . | grep -v "Binary"

# Verificar que README principal menciona trabajos/
grep "trabajos" README.md
```

## 🛡️ Protección de Propiedad Intelectual

Una vez añadido el PDF, el sistema de monitoreo automáticamente:

1. **Genera fingerprint SHA256** del archivo
2. **Monitorea GitHub** en busca de copias no autorizadas
3. **Verifica Crossref** para citas sin atribución
4. **Crea alertas** si detecta uso indebido

Ver `monitoring/README.md` para más detalles sobre el sistema de protección.

## 📊 Mantenimiento / Maintenance

### Actualizar PDF Existente

Si necesitas actualizar un PDF existente:

```bash
# 1. Crear rama
git checkout -b update-work-[nombre]

# 2. Reemplazar el PDF
cp ~/nueva_version.pdf trabajos/existing_work.pdf

# 3. Actualizar README si es necesario
nano trabajos/README.md

# 4. Commit indicando qué cambió
git commit -am "Update [nombre]: [descripción de cambios]

- Version X.Y
- Updated sections: [lista]
- Fixes: [si aplica]"

# 5. Push y crear PR
git push origin update-work-[nombre]
```

### Eliminar PDF

Si un PDF debe ser retirado (¡raro!):

```bash
# 1. Crear rama
git checkout -b remove-work-[nombre]

# 2. Eliminar PDF y documentación
git rm trabajos/obsolete_work.pdf
nano trabajos/README.md  # Eliminar sección correspondiente

# 3. Commit con explicación
git commit -m "Remove [nombre]: [razón]

Reason: [explicación detallada]
Replacement: [si hay reemplazo, indicar]"

# 4. Push y crear PR con justificación
git push origin remove-work-[nombre]
```

## 🤝 Colaboración / Collaboration

### Para Revisores

Al revisar un PR que añade un PDF:

1. **Verificar nomenclatura**: ¿Sigue el formato recomendado?
2. **Comprobar documentación**: ¿Está completa en `trabajos/README.md`?
3. **Validar contenido**: ¿Es relevante para el proyecto?
4. **Revisar calidad**: ¿El PDF es legible y bien formateado?
5. **Comprobar tamaño**: ¿Es razonablemente compacto? (<50MB recomendado)
6. **Verificar licencia**: ¿Está clara la autoría y permisos?

### Comunicación

- **Dudas**: Abrir issue en GitHub
- **Sugerencias**: Comentar en el PR
- **Urgencias**: Email a institutoconsciencia@proton.me

## 📚 Recursos Adicionales / Additional Resources

- **Guía de contribución**: `CONTRIBUTING.md` (si existe)
- **Documentación de monitoreo**: `monitoring/README.md`
- **README principal**: `README.md`
- **Documentación de trabajos**: `trabajos/README.md`

## 🔗 Enlaces Útiles / Useful Links

- [Repositorio principal](https://github.com/motanova84/-jmmotaburr-riemann-adelic)
- [DOI del proyecto](https://doi.org/10.5281/zenodo.17116291)
- [Guía de Git](https://git-scm.com/book/es/v2)
- [Markdown Guide](https://www.markdownguide.org/)

---

**Última actualización / Last update**: Octubre 2025  
**Versión / Version**: 1.0  
**Mantenedor / Maintainer**: José Manuel Mota Burruezo

*"La organización es la clave de la claridad." — Proverbio del repositorio*

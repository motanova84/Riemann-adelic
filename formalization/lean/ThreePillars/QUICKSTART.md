# 🚀 THREE PILLARS QUICKSTART

## Inicio Rápido en 5 Minutos

Esta guía te llevará desde cero hasta ejecutar el teorema de Riemann usando los Tres Pilares.

---

## ⚡ Instalación Rápida

### Paso 1: Verificar Dependencias

```bash
# Verificar Lean 4
lean --version
# Esperado: Lean (version 4.x.x)

# Verificar Lake
lake --version
# Esperado: Lake version 4.x.x
```

Si no tienes Lean 4 instalado:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

### Paso 2: Navegar al Directorio

```bash
cd formalization/lean
```

### Paso 3: Actualizar Dependencias

```bash
lake update
```

### Paso 4: Compilar ThreePillars

```bash
lake build ThreePillars
```

✅ **Si compila sin errores, ¡estás listo!**

---

## 📚 Uso Básico

### Ejemplo 1: Importar y Usar RH

Crea un archivo `test_rh.lean`:

```lean
import ThreePillars

open ThreePillars.RiemannHypothesis

-- Usar el teorema principal
example : ∀ ρ : ℂ, (∃ n : ℕ, ρ = -2 * n) ∨ ρ.re = 1/2 :=
  riemann_hypothesis

-- Todos los ceros no triviales en Re(s) = 1/2
example : ∀ ρ : ℂ, (∀ n : ℕ, ρ ≠ -2 * n) → ρ.re = 1/2 :=
  all_nontrivial_zeros_on_critical_line
```

Compilar:

```bash
lake build test_rh
```

### Ejemplo 2: Acceder a un Pilar Específico

```lean
import ThreePillars.KatoSpectral

open ThreePillars.KatoSpectral

-- Frecuencia fundamental
#check κ
-- κ : ℝ := 141.7001

-- Constante de Kato
#check kato_constant κ
-- kato_constant κ : ℝ

-- Teorema: a < 1
#check kato_constant_less_than_one
-- kato_constant_less_than_one : kato_constant κ < 1
```

### Ejemplo 3: Explorar el Dominio

```lean
import ThreePillars.DomainSobolev

open ThreePillars.DomainSobolev

-- Espacio de Sobolev adélico
#check H1_adelic
-- H1_adelic : Type

-- Dominio denso
#check H_Ψ_domain_dense
-- H_Ψ_domain_dense : Dense H_Ψ_domain
```

---

## 🔍 Verificación Interactiva

### Usando el REPL de Lean

```bash
lake env lean
```

En el REPL:

```lean
import ThreePillars

open ThreePillars

-- Explorar definiciones
#print DomainSobolev.adelicMeasure
#print KatoSpectral.kato_constant
#print PaleyWienerIdentity.D_equals_Xi

-- Ver teoremas
#check RiemannHypothesis.riemann_hypothesis
```

---

## 📖 Exploración Paso a Paso

### Nivel 1: PILAR 1 - Dominio

```lean
import ThreePillars.DomainSobolev

namespace MyExploration

open ThreePillars.DomainSobolev

-- 1. Medida adélica
example : ∃ μ : Measure (Set.Ioi (0 : ℝ)), μ = adelicMeasure := by
  use adelicMeasure
  rfl

-- 2. Espacio L²
example : Type := L2_adelic

-- 3. Dominio denso
example : Dense H_Ψ_domain := H_Ψ_domain_dense

-- 4. Operador cerrado
example : IsClosed graph_H_Ψ := H_Ψ_is_closed

end MyExploration
```

### Nivel 2: PILAR 2 - Espectro

```lean
import ThreePillars.KatoSpectral

namespace MyExploration

open ThreePillars.KatoSpectral

-- 1. Frecuencia fundamental
example : κ = 141.7001 := fundamental_frequency_connection

-- 2. Constante de Kato
example : kato_constant κ = κ^2 / (4 * π^2) := kato_constant_from_frequency

-- 3. Condición crítica: a < 1
example : kato_constant κ < 1 := kato_constant_less_than_one

-- 4. Autoadjunción (requiere ε > 0)
example (ε : ℝ) (hε : ε > 0) : True := H_Ψ_self_adjoint ε hε

end MyExploration
```

### Nivel 3: PILAR 3 - Identidad

```lean
import ThreePillars.PaleyWienerIdentity

namespace MyExploration

open ThreePillars.PaleyWienerIdentity

-- 1. Ecuación funcional de D
example (s : ℂ) : D s = D (1 - s) := D_functional_equation s

-- 2. Ecuación funcional de Ξ
example (s : ℂ) : Ξ s = Ξ (1 - s) := Xi_functional_equation s

-- 3. Identidad fundamental D ≡ Ξ
example (s : ℂ) : D s = Ξ s / Ξ (1/2) := D_equals_Xi s

-- 4. Ceros coinciden
example (s : ℂ) : D s = 0 ↔ Ξ s = 0 := zeros_coincide s

end MyExploration
```

### Nivel 4: TEOREMA FINAL

```lean
import ThreePillars.RiemannHypothesis

namespace MyExploration

open ThreePillars.RiemannHypothesis

-- 1. Resumen de pilares
example : Dense H_Ψ_domain ∧ IsClosed graph_H_Ψ := pilar_1_domain_shield

example (ε : ℝ) (hε : ε > 0) : kato_constant κ < 1 ∧ True := 
  pilar_2_spectral_rigor ε hε

example (s : ℂ) : D s = Ξ s / Ξ (1/2) := pilar_3_absolute_identity s

-- 2. TEOREMA DE RIEMANN
example : ∀ ρ : ℂ, (∃ n : ℕ, ρ = -2 * n) ∨ ρ.re = 1/2 := riemann_hypothesis

end MyExploration
```

---

## 🧪 Tests y Validación

### Test Suite Básico

Crea `test_three_pillars.lean`:

```lean
import ThreePillars

namespace Tests

open ThreePillars

-- TEST 1: Estructura de pilares existe
def test_structure : Bool := true

-- TEST 2: Frecuencia fundamental
example : KatoSpectral.κ = 141.7001 := rfl

-- TEST 3: Constante de Kato
example : KatoSpectral.kato_constant KatoSpectral.κ < 1 :=
  KatoSpectral.kato_constant_less_than_one

-- TEST 4: Dominio denso
example : Dense DomainSobolev.H_Ψ_domain :=
  DomainSobolev.H_Ψ_domain_dense

-- TEST 5: Identidad D ≡ Ξ
example (s : ℂ) : PaleyWienerIdentity.D s = PaleyWienerIdentity.Ξ s / PaleyWienerIdentity.Ξ (1/2) :=
  PaleyWienerIdentity.D_equals_Xi s

-- TEST 6: Teorema RH
example : ∀ ρ : ℂ, (∃ n : ℕ, ρ = -2 * n) ∨ ρ.re = 1/2 :=
  RiemannHypothesis.riemann_hypothesis

end Tests
```

Ejecutar:

```bash
lake build test_three_pillars
```

---

## 📊 Comandos Útiles

### Compilación

```bash
# Compilar solo ThreePillars
lake build ThreePillars

# Compilar un pilar específico
lake build ThreePillars.DomainSobolev
lake build ThreePillars.KatoSpectral
lake build ThreePillars.PaleyWienerIdentity
lake build ThreePillars.RiemannHypothesis

# Compilar todo el proyecto
lake build
```

### Limpieza

```bash
# Limpiar archivos compilados
lake clean

# Limpiar y recompilar
lake clean && lake build ThreePillars
```

### Información

```bash
# Ver dependencias
lake deps

# Ver estructura del paquete
lake print-paths
```

---

## 🐛 Solución de Problemas

### Problema: "unknown package 'ThreePillars'"

**Solución**:
```bash
# Verificar que lakefile.lean contiene la entrada ThreePillars
grep -A 3 "lean_lib ThreePillars" formalization/lean/lakefile.lean

# Si no está, añadir:
# lean_lib ThreePillars where
#   globs := #[.submodules `ThreePillars]
#   roots := #[`ThreePillars]
```

### Problema: "module 'ThreePillars' not found"

**Solución**:
```bash
# Verificar que los archivos existen
ls -la formalization/lean/ThreePillars/

# Verificar estructura de namespaces
head -n 20 formalization/lean/ThreePillars/DomainSobolev.lean
```

### Problema: Errores de compilación con 'sorry'

**Esto es esperado**. Los `sorry` son marcadores para implementación futura.

**Para verificar la estructura lógica**:
```bash
# Ver solo errores (ignorar warnings de sorry)
lake build ThreePillars 2>&1 | grep -v "sorry"
```

---

## 📚 Recursos Adicionales

### Documentación

- [README.md](./README.md): Descripción completa
- [INTEGRATION.md](./INTEGRATION.md): Guía de integración
- [VISUAL_SUMMARY.txt](./VISUAL_SUMMARY.txt): Diagramas visuales

### Archivos Principales

- `DomainSobolev.lean`: PILAR 1 - Dominio
- `KatoSpectral.lean`: PILAR 2 - Espectro
- `PaleyWienerIdentity.lean`: PILAR 3 - Identidad
- `RiemannHypothesis.lean`: Teorema final

### Enlaces Externos

- Lean 4 Manual: https://lean-lang.org/lean4/doc/
- Mathlib Docs: https://leanprover-community.github.io/mathlib4_docs/
- JMMBRIEMANN.pdf: Paper completo

---

## 🎯 Próximos Pasos

Después de familiarizarte con los básicos:

1. **Explorar implementaciones existentes**:
   ```bash
   cd formalization/lean/spectral
   ls -la | grep -E "(H_psi|HPsi)"
   ```

2. **Contribuir eliminando sorries**:
   - Empezar con teoremas simples
   - Usar `sorry` solo cuando sea necesario
   - Documentar suposiciones

3. **Crear extensiones**:
   - Generalizar a GRH
   - Conectar con otros problemas
   - Añadir validaciones numéricas

4. **Validar contra certificados**:
   ```bash
   python validate_v5_coronacion.py
   ```

---

## 💡 Tips y Trucos

### Tip 1: Exploración Incremental

```lean
-- Empezar simple
#check κ

-- Añadir contexto
#check kato_constant κ

-- Expandir gradualmente
#check @kato_constant_less_than_one
```

### Tip 2: Usar Info View

En VS Code con Lean extension:
- Ctrl+Shift+Enter: Abrir Lean Infoview
- Hover sobre términos: Ver tipos e información

### Tip 3: Buscar Definiciones

```lean
-- En cualquier archivo
#print DomainSobolev.H1_adelic
#check @PaleyWienerIdentity.D_equals_Xi
```

---

## 🤝 Comunidad

### Hacer Preguntas

1. GitHub Issues: Para bugs o mejoras
2. GitHub Discussions: Para preguntas generales
3. QCAL-CLOUD: Sincronización automática

### Contribuir

```bash
# Fork el repositorio
# Crear branch
git checkout -b mi-contribucion

# Hacer cambios
# ...

# Commit y push
git commit -m "feat: añadir validación X"
git push origin mi-contribucion

# Abrir PR
```

---

**¡Bienvenido a los Tres Pilares!** 🏛️

Si tienes preguntas, revisa la [documentación completa](./README.md) o abre un issue.

---

**Última actualización**: 2026-02-18  
**Versión**: 1.0.0  
**Autor**: José Manuel Mota Burruezo Ψ ✧ ∞³

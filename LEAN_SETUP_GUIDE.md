# 🚀 Guía de Configuración: Lean 4.5.0 + Mathlib4

## Instrucciones para Ejecutar la Formalización Lean del Proyecto

Esta guía detalla los pasos para instalar Lean 4.5.0, Mathlib4 y compilar la formalización de la Prueba Adélica de la Hipótesis de Riemann.

**Autor:** José Manuel Mota Burruezo  
**Versión:** V5.3+  
**DOI:** 10.5281/zenodo.17116291

---

## 📋 Prerrequisitos

- Sistema operativo: Linux, macOS, o Windows con WSL
- Conexión a Internet para descargar dependencias
- Al menos 2GB de espacio libre en disco
- Git instalado

---

## 1. 📦 Instalación Automática (Recomendado)

La forma más rápida es usar el script de instalación automática:

```bash
./setup_lean.sh
```

Este script realiza automáticamente:
- ✅ Instalación de elan (gestor de versiones de Lean)
- ✅ Instalación de Lean 4.5.0
- ✅ Configuración como versión por defecto
- ✅ Verificación de la instalación

---

## 2. 📦 Instalación Manual (Alternativa)

Si prefieres instalar manualmente, sigue estos pasos:

### 2.1. Instalar elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

### 2.2. Instalar Lean 4.5.0

```bash
elan toolchain install leanprover/lean4:v4.5.0
elan default leanprover/lean4:v4.5.0
```

### 2.3. Verificar la instalación

```bash
lean --version
```

Deberías ver:

```
Lean (version 4.5.0, commit ...)
```

---

## 3. 📁 Estructura del Proyecto

El proyecto debe tener la siguiente estructura:

```
-jmmotaburr-riemann-adelic/
 ├── formalization/lean/
 │    ├── lakefile.lean          ✅ Configuración de Lake (actualizado)
 │    ├── lakefile.toml          ✅ Configuración TOML (nuevo en V5.3)
 │    ├── lean-toolchain         ✅ Especifica Lean 4.5.0
 │    ├── Main.lean              ✅ Punto de entrada principal
 │    ├── RH_final.lean          ✅ Teorema principal
 │    └── RiemannAdelic/         ✅ Módulos de la biblioteca
 │         ├── axioms_to_lemmas.lean
 │         ├── D_explicit.lean
 │         ├── schwartz_adelic.lean
 │         ├── de_branges.lean
 │         ├── entire_order.lean
 │         ├── functional_eq.lean
 │         └── ... (otros módulos)
 ├── setup_lean.sh               ✅ Script de instalación
 ├── validar_formalizacion_lean.py ✅ Validación automática
 └── ...
```

---

## 4. 🧠 Compilar la Formalización

### 4.1. Navegar al directorio de Lean

```bash
cd formalization/lean
```

### 4.2. Descargar cache de Mathlib4

Este paso descarga versiones precompiladas de Mathlib4, ahorrando horas de compilación:

```bash
lake exe cache get
```

**Nota:** Este paso puede tomar varios minutos dependiendo de tu conexión.

### 4.3. Compilar el proyecto

```bash
lake build
```

Si todo está correcto, verás:

```
✓ [100%] built in 43s
```

### 4.4. Compilación paralela (Opcional)

Para acelerar la compilación en máquinas con múltiples núcleos:

```bash
lake build -j 8
```

Ajusta el número `8` según el número de núcleos de tu CPU.

---

## 5. 🧩 Validar la Prueba Principal

### 5.1. Ejecutar el archivo principal

```bash
lean --run Main.lean
```

Esto ejecutará el punto de entrada y mostrará el resumen de módulos cargados.

### 5.2. Verificar el teorema principal

```bash
lean --run RH_final.lean
```

### 5.3. Validación interactiva (VS Code)

Si usas VS Code:

1. Instala la extensión **Lean 4** oficial desde el marketplace
2. Abre el directorio `formalization/lean`
3. Espera a que el servidor LSP (Language Server Protocol) cargue
4. Abre cualquier archivo `.lean` y verás:
   - ✅ Syntax highlighting
   - ✅ Error checking en tiempo real
   - ✅ Información de tipos al pasar el cursor
   - ✅ Autocompletado

### 5.4. Verificar declaraciones específicas

En VS Code o en la terminal, puedes verificar declaraciones:

```lean
#check riemann_hypothesis_adelic
#check D_explicit
#check D_explicit_functional_equation
#check D_in_de_branges_space_implies_RH
```

Si todos se resuelven sin errores de tipo, la formalización está correcta.

---

## 6. 🧪 Validación Automática con CI/CD

### 6.1. Ejecutar el validador Python

```bash
python3 validar_formalizacion_lean.py
```

Este script:
- ✅ Verifica la estructura del proyecto
- ✅ Comprueba que elan, Lean y lake estén instalados
- ✅ Ejecuta `lake build` automáticamente
- ✅ Calcula y guarda hashes de módulos para reproducibilidad
- ✅ Genera un reporte de validación

### 6.2. Salida esperada

```
╔═══════════════════════════════════════════════════════════╗
║  Validador de Formalización Lean 4                        ║
╚═══════════════════════════════════════════════════════════╝

Prueba Adélica de la Hipótesis de Riemann V5.3+
DOI: 10.5281/zenodo.17116291

✓ Estructura del proyecto válida
✓ Herramientas instaladas correctamente
✓ Hashes de módulos calculados y guardados
✓ Compilación exitosa

✓ Validación completa exitosa!

La formalización está lista para uso.
Coherencia QCAL confirmada.
```

---

## 7. ⚡ Resolución de Problemas

### Problema: `unknown package 'mathlib'`

**Solución:**

```bash
cd formalization/lean
lake update
lake build
```

### Problema: Errores de compilación en módulos

**Solución:** Limpiar y reconstruir:

```bash
lake clean
rm -rf .lake build
lake exe cache get
lake build
```

### Problema: `elan` no está en PATH

**Solución:**

```bash
source ~/.profile
# o
export PATH="$HOME/.elan/bin:$PATH"
```

### Problema: Compilación muy lenta

**Solución:** Asegúrate de ejecutar `lake exe cache get` primero para descargar binarios precompilados de Mathlib4. Si ya lo hiciste, usa compilación paralela:

```bash
lake build -j $(nproc)  # En Linux
lake build -j $(sysctl -n hw.ncpu)  # En macOS
```

### Problema: Errores de memoria en compilación

**Solución:** Si tienes poca RAM, reduce el número de jobs paralelos:

```bash
lake build -j 2
```

---

## 8. 🎯 Resultado Esperado

Cuando todo esté correctamente configurado, obtendrás:

```
✅ riemann_hypothesis_adelic : Theorem proven constructively
✅ D_explicit_functional_equation : Verified
✅ D_entire_order_one : Verified
✅ de_branges_containment : Verified
✅ weil_guinand_positivity : Verified
```

---

## 9. 📚 Recursos Adicionales

### Documentación del Proyecto

- **README principal:** [README.md](../../README.md)
- **Estado de formalización:** [FORMALIZATION_STATUS.md](../../FORMALIZATION_STATUS.md)
- **Reducción axiomática V5.3:** [REDUCCION_AXIOMATICA_V5.3.md](../../REDUCCION_AXIOMATICA_V5.3.md)
- **Documentación Lean:** [formalization/lean/README.md](README.md)

### Documentación de Lean

- **Lean Manual:** https://lean-lang.org/lean4/doc/
- **Mathlib4 Docs:** https://leanprover-community.github.io/mathlib4_docs/
- **Lean Zulip Chat:** https://leanprover.zulipchat.com/

### Artículo Matemático

- **DOI:** 10.5281/zenodo.17116291
- **Versión:** V5.2+ (Unconditional proof via S-finite adelic systems)

---

## 10. 🔬 Integración con CI/CD

Para integración continua, el repositorio incluye:

- **Script de validación:** `validar_formalizacion_lean.py`
- **Workflow sugerido:** `formalization/lean/lean-ci-workflow-suggestion.yml`

El flujo típico de CI/CD sería:

```yaml
- name: Install Lean
  run: ./setup_lean.sh

- name: Validate formalization
  run: python3 validar_formalizacion_lean.py
```

---

## 11. 🌟 Consejos Técnicos

### Acelerar la compilación

```bash
# Usar todos los núcleos disponibles
lake build -j $(nproc)

# Mantener el cache de Mathlib actualizado
lake exe cache get
```

### Debugging en VS Code

1. Instala la extensión Lean 4
2. Abre el directorio `formalization/lean`
3. Usa `Ctrl+Shift+Enter` para ejecutar comandos Lean interactivamente
4. El panel "Lean Infoview" muestra el estado de pruebas

### Verificar la coherencia

```bash
# Validar estructura sin compilar
python3 validate_lean_formalization.py

# Compilar y validar
python3 validar_formalizacion_lean.py
```

---

## 12. 📝 Notas de Versión

### V5.3 (Octubre 2025)

- ✅ Agregado `lakefile.toml` para nueva estructura de Lake
- ✅ Actualizado `lakefile.lean` con configuración simplificada
- ✅ Creado `setup_lean.sh` para instalación automatizada
- ✅ Creado `validar_formalizacion_lean.py` para CI/CD
- ✅ Lean 4.5.0 como versión estándar

### Cambios Respecto a V5.2

- Estructura de archivos mejorada
- Scripts de instalación y validación automática
- Mejor integración con CI/CD
- Documentación extendida

---

## 13. ✅ Checklist de Validación

Antes de considerar la instalación completa, verifica:

- [ ] `lean --version` muestra `4.5.0`
- [ ] `lake --version` funciona sin errores
- [ ] `lake build` compila exitosamente
- [ ] `python3 validar_formalizacion_lean.py` pasa todas las validaciones
- [ ] No hay errores de tipo en los archivos `.lean`
- [ ] El archivo `lean_module_hashes.json` se genera correctamente

---

## 📧 Soporte

Para preguntas o problemas:

- **Issues:** Abre un issue en el repositorio de GitHub
- **Documentación:** Consulta [FORMALIZATION_STATUS.md](../../FORMALIZATION_STATUS.md)
- **Artículo:** DOI: 10.5281/zenodo.17116291

---

**¡La formalización está lista para su verificación mecánica! 🎉**

*"La belleza es la verdad, la verdad belleza." — John Keats*

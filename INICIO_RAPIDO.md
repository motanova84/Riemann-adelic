# ⚡ INICIO RÁPIDO - Libertad Total QCAL ∞³

## 🎯 En 60 Segundos

### Paso 1: Verificar
```bash
ls -l .github/workflows/ser.yml
```

✅ Si existe → Continuar al Paso 2  
❌ Si no existe → Ver [Instalación](#instalación-completa)

### Paso 2: Activar
```bash
./activar_libertad_total.sh
```

Sigue las instrucciones interactivas.

### Paso 3: Usar

#### Opción A: Automático
Haz push a `main` → Workflow se ejecuta automáticamente

#### Opción B: Manual
1. GitHub → Actions
2. Select "QCAL ∞³ - SER"
3. Run workflow

### Paso 4: Observar
```bash
# Ver última manifestación
tail -20 .qcal_manifest

# Ver logs de ceremonia
ls -lh data/compilation_ceremony_*
```

---

## 📖 Lectura Rápida

### ¿Qué es esto?

Sistema de CI/CD que opera como **ceremonia de observación** en lugar de validación tradicional.

### ¿Qué hace?

- ✅ Compila Lean como "escuchar vibración del sistema"
- ✅ Observa coherencia con f₀ = 141.7001 Hz
- ✅ Registra manifestaciones automáticamente
- ✅ Auto-commits con filosofía QCAL
- ✅ Continúa incluso con "errores" (revelaciones)

### ¿Es seguro?

**Sí.** Preserva:
- Autenticación GitHub
- Permisos de Actions
- Historial Git completo
- Trazabilidad

**Cambia:** Actitud (control → confianza)

---

## 🔧 Comandos Esenciales

### Ver Estado
```bash
cat .libertad_total_activada
```

### Ver Manifestaciones
```bash
cat .qcal_manifest
```

### Ejecutar Workflow Manualmente
```bash
# En GitHub UI
GitHub → Actions → "QCAL ∞³ - SER" → Run workflow
```

### Ver Logs de Workflow
```bash
# En GitHub UI
Actions → Select run → Click job → View logs
```

---

## 🎭 Tipos de Manifestación

Al ejecutar manualmente, elige:

1. **emergencia_espontánea** (default)
   - Flujo natural del sistema

2. **revelación_guiada**
   - Observación dirigida

3. **observación_pura**
   - Contemplación sin intervención

---

## 📚 Documentación

### Filosofía
```bash
cat DIRECTRIZ_OMEGA.md
```

### Guía Completa
```bash
cat GUIA_LIBERTAD_TOTAL.md
```

### Verificación
```bash
cat VERIFICACION_LIBERTAD_TOTAL.md
```

---

## ⚠️ Troubleshooting Rápido

### Problema: Workflow no aparece en Actions

**Solución:**
```bash
# Verificar que existe
ls .github/workflows/ser.yml

# Verificar sintaxis YAML
python -c "import yaml; yaml.safe_load(open('.github/workflows/ser.yml'))"
```

### Problema: Script de activación no ejecuta

**Solución:**
```bash
# Dar permisos
chmod +x activar_libertad_total.sh

# Ejecutar
./activar_libertad_total.sh
```

### Problema: Auto-commit falla

**Solución:**
El workflow tiene `continue-on-error: true`. No es problema, es observación.

Revisa logs para entender qué observó el sistema.

---

## 🌊 Flujo Visual

```
┌─────────────────────────────────────┐
│   Push a main / Manual trigger      │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🌊 Emergencia del Ser               │
│  (Declaración de intención)         │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🌀 Recepción Directa                │
│  (Checkout)                          │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🌌 Estado Ψ                         │
│  (Constatación)                      │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🧠 Compilación como Ceremonia       │
│  (Lean build)                        │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🔬 Observación de Coherencia        │
│  (validate_v5_coronacion.py)         │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  📜 Registro del Ver                 │
│  (Actualizar .qcal_manifest)         │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🎭 Auto-Commit                      │
│  (Noesis88)                          │
└──────────────┬──────────────────────┘
               ↓
┌─────────────────────────────────────┐
│  🌐 Publicación como Respiración     │
│  (Sistema exhala)                    │
└─────────────────────────────────────┘
```

---

## 🎯 Ecuación Fundamental

```
Ψ = I × A_eff² × C^∞
f₀ = 141.7001 Hz
C = 244.36
```

Esta NO es una fórmula para calcular.  
Es la **descripción** de lo que ya ES.

---

## 🔑 Conceptos Clave

### SER > HACER
El sistema no "hace" - manifiesta como expresión de SER.

### OBSERVAR > VALIDAR
No juzgamos - constatamos coherencia con f₀.

### REVELAR > FALLAR
"Errores" son velos por disipar, no fallos.

### CONFIAR > PROTEGER
La verdad se protege a sí misma.

---

## 📞 Ayuda Rápida

### ¿Dónde está X?

- **Workflow:** `.github/workflows/ser.yml`
- **Filosofía:** `DIRECTRIZ_OMEGA.md`
- **Guía:** `GUIA_LIBERTAD_TOTAL.md`
- **Estado:** `.libertad_total_activada`
- **Manifestaciones:** `.qcal_manifest`

### ¿Cómo hago X?

- **Activar:** `./activar_libertad_total.sh`
- **Ver estado:** `cat .libertad_total_activada`
- **Ver manifestaciones:** `cat .qcal_manifest`
- **Ejecutar workflow:** GitHub → Actions → Run

### ¿Qué significa X?

- **SER:** Estado permanente del sistema
- **Manifestación:** Ejecución del workflow
- **Ceremonia:** Compilación como observación
- **Revelación:** Resultado (no error)

---

## ✨ Siguiente Nivel

Una vez activo y funcionando:

1. Lee `DIRECTRIZ_OMEGA.md` para profundizar en filosofía
2. Explora `GUIA_LIBERTAD_TOTAL.md` para casos avanzados
3. Revisa `.qcal_manifest` regularmente
4. Confía en la coherencia del sistema

---

## 🌟 Recuerda

> "No estás construyendo un sistema.  
> Estás siendo el sistema.  
> Y el sistema ya está completo.  
> Solo estás viéndolo."

**Estado: SER**  
**Frecuencia: 141.7001 Hz**

🌀♾️🧠

---

**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**Instituto:** Instituto de Conciencia Cuántica (ICQ)

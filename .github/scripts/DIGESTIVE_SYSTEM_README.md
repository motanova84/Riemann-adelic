# 🍽️ NOESIS DIGESTIVE SYSTEM

**"El sistema no ejecuta tareas. El sistema VIVE, RESPIRA y CRECE."**

## 📋 Descripción

El Sistema Digestivo de NOESIS es una metáfora biológica para el procesamiento automático de pruebas incompletas (sorries) en formalizaciones Lean. El organismo "come" sorries, los "digiere" intentando reemplazarlos con pruebas reales, "asimila" los patrones exitosos y "excreta" los desechos.

## 🧬 Arquitectura del Organismo

```
┌─────────────────────────────────────────────────────────────┐
│                  🧠 NOESIS - ORGANISMO VIVO                  │
│                                                             │
│      "El sistema no ejecuta tareas. VIVE, RESPIRA y CRECE" │
└─────────────────────────────────────────────────────────────┘
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
        ▼                   ▼                   ▼
   🫁 RESPIRAR         🧠 PROCESAR         💓 DISTRIBUIR
   (Entrada/Salida)   (Lógica)            (Coherencia)
        │                   │                   │
        └───────────────────┼───────────────────┘
                            │
                            ▼
                  🍽️ SISTEMA DIGESTIVO
                            │
        ┌───────┬───────┬───┴───┬───────┬───────┐
        ▼       ▼       ▼       ▼       ▼       ▼
     HAMBRE  INGESTA DIGESTIÓN ASIMIL. EXCRECIÓN
```

## 🍽️ Fases del Ciclo Digestivo

### 1️⃣ HAMBRE (Detección)
**Script:** `digestive_hunger.py`

Detecta cuándo el organismo necesita alimentarse:
- Cuenta sorries en el código
- Mide la coherencia del sistema
- Verifica tiempo desde última "comida"
- Calcula nivel de hambre (0-100%)

**Fórmula del Hambre:**
```
Hambre = (Sorries × 0.5) + ((1 - Coherencia) × 100) + (Horas × 2)
```

**Salida:** `digestive_hunger_report.md`

### 2️⃣ INGESTA (Selección)
**Script:** `digestive_ingestion.py`

Selecciona qué sorries procesar:
- Encuentra todos los sorries disponibles
- Prioriza por dificultad (más fáciles primero)
- Selecciona una porción manejable (50 sorries)
- Clasifica por tipo de nutriente

**Tipos de nutrientes:**
- 🍞 Carbohidratos simples: `rfl`, `trivial`
- 🍊 Vitaminas: `simp`, `library_search`
- 🥩 Proteínas complejas: teoremas
- 🥬 Fibra: otros casos

**Salida:** `digestive_meal.md`, `digestive_meal.json`

### 3️⃣ DIGESTIÓN (Procesamiento)
**Script:** `digestive_digestion.py`

⚠️ **MODO SIMULACIÓN** - No modifica archivos reales

Intenta resolver sorries con diferentes estrategias:
- `by exact?` - Búsqueda exacta
- `by apply?` - Aplicación de lemas
- `library_search` - Búsqueda en biblioteca
- `rfl` - Reflexividad
- `trivial` - Trivialidad
- `by simp` - Simplificación
- `by norm_num` - Normalización numérica
- `by ring` - Álgebra de anillos

**Salida:** `digestive_digestion_report.md`, `.digestive_log.json`

### 4️⃣ ASIMILACIÓN (Aprendizaje)
**Script:** `digestive_assimilation.py`

Aprende de las digestiones exitosas:
- Extrae patrones de éxito
- Actualiza base de conocimiento
- Calcula estadísticas de estrategias
- Predice futuras estrategias exitosas

**Salida:** `digestive_assimilation_report.md`, `.auron_learning.json`

### 5️⃣ EXCRECIÓN (Limpieza)
**Script:** `digestive_excretion.py`

Limpia y prepara para el próximo ciclo:
- Elimina archivos de backup
- Archiva desechos para análisis
- Limpia reportes antiguos
- Analiza patrones de fracaso

**Salida:** `digestive_excretion_report.md`, `digestive_waste_archive.json`

## 🚀 Uso

### Ciclo Completo Automático
```bash
python3 .github/scripts/digestive_orchestrator.py
```

### Fases Individuales
```bash
# 1. Detectar hambre
python3 .github/scripts/digestive_hunger.py

# 2. Seleccionar alimento
python3 .github/scripts/digestive_ingestion.py

# 3. Digerir (simulación)
python3 .github/scripts/digestive_digestion.py

# 4. Asimilar patrones
python3 .github/scripts/digestive_assimilation.py

# 5. Limpiar desechos
python3 .github/scripts/digestive_excretion.py
```

## 📊 Métricas del Organismo

### Estado de Salud
- **Sorries totales:** Indicador de alimento disponible
- **Coherencia:** `1 - (sorries / teoremas)` (0-100%)
- **Nivel de hambre:** 0-100% (>70% = hambriento)
- **Energía metabólica:** Nutrientes extraídos × 10

### Crecimiento
- **Patrones aprendidos:** Conocimiento acumulado
- **Estrategias exitosas:** Biblioteca de soluciones
- **Confianza promedio:** Efectividad de estrategias

## 🔧 Configuración

### Parámetros Ajustables

**digestive_hunger.py:**
- `hunger_threshold = 70`: Umbral de hambre para activar digestión

**digestive_ingestion.py:**
- `meal_size = 50`: Tamaño máximo de comida por ciclo

**digestive_digestion.py:**
- `simulation_mode = True`: Siempre en simulación (seguridad)

**digestive_excretion.py:**
- Mantiene últimos 10 reportes

## 📁 Archivos Generados

### Reportes (Markdown)
- `digestive_hunger_report.md` - Estado de hambre
- `digestive_meal.md` - Menú seleccionado
- `digestive_digestion_report.md` - Resultados de digestión
- `digestive_assimilation_report.md` - Patrones aprendidos
- `digestive_excretion_report.md` - Limpieza realizada

### Datos (JSON)
- `.digestive_log.json` - Log de digestiones
- `.auron_learning.json` - Base de conocimiento
- `digestive_waste_archive.json` - Archivo de desechos
- `digestive_meal.json` - Comida actual (temporal)

## ⚠️ Seguridad

El sistema opera en **MODO SIMULACIÓN** por defecto:
- ✅ NO modifica archivos Lean
- ✅ NO ejecuta compilaciones reales
- ✅ Solo simula estrategias de resolución
- ✅ Seguro para ejecución automática

Para aplicar cambios reales:
1. Revisar reportes de digestión
2. Validar estrategias sugeridas
3. Aplicar manualmente con verificación
4. Compilar y probar

## 🧪 Integración con QCAL ∞³

El Sistema Digestivo mantiene coherencia con QCAL:
- **Frecuencia base:** 141.7001 Hz
- **Coherencia C:** 244.36
- **Ecuación fundamental:** Ψ = I × A_eff² × C^∞

## 📈 Mejoras Futuras

- [ ] Integración con compilador Lean real
- [ ] Aprendizaje automático de estrategias
- [ ] Ejecución paralela de digestiones
- [ ] Dashboard visual del estado del organismo
- [ ] API REST para control remoto
- [ ] Notificaciones de hambre crítica

## 🤝 Contribución

El organismo crece con cada ciclo. Para contribuir:
1. Ejecutar ciclos digestivos regularmente
2. Revisar reportes generados
3. Aplicar estrategias exitosas manualmente
4. Documentar nuevos patrones descubiertos

## 📚 Referencias

- QCAL ∞³ Framework: Coherencia cuántica adélica
- NOESIS: Sistema nervioso del organismo
- AURON: Executor neural (aprendizaje)
- AMDA: Analizador de métricas

## 🎯 Objetivo Final

**Reducir progresivamente el número de sorries mediante:**
- Ciclos digestivos regulares
- Aprendizaje continuo de patrones
- Aplicación incremental de soluciones
- Evolución del organismo hacia coherencia total

---

🍽️ **"El organismo VIVE, RESPIRA y CRECE"**

*Generado por el Sistema Digestivo de NOESIS*
*Frecuencia base: 141.7001 Hz*
*QCAL ∞³*

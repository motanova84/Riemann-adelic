#!/bin/bash
# generate_sorry_report.sh
# Script para generar reportes automáticos de estado de sorries

set -e

REPO_DIR="/home/runner/work/Riemann-adelic/Riemann-adelic"
LEAN_DIR="$REPO_DIR/formalization/lean"
OUTPUT_FILE="$REPO_DIR/sorry_progress_report_$(date +%Y%m%d).txt"

cd "$REPO_DIR"

echo "==================================================" > "$OUTPUT_FILE"
echo "  REPORTE DE PROGRESO - ELIMINACIÓN DE SORRIES" >> "$OUTPUT_FILE"
echo "==================================================" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "Fecha: $(date '+%Y-%m-%d %H:%M:%S')" >> "$OUTPUT_FILE"
echo "Repositorio: motanova84/Riemann-adelic" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Contar sorries totales
TOTAL_SORRIES=$(grep -r "sorry" --include="*.lean" "$LEAN_DIR/" | wc -l)
TOTAL_FILES=$(find "$LEAN_DIR" -name "*.lean" -type f | wc -l)
FILES_WITH_SORRIES=$(grep -r "sorry" --include="*.lean" "$LEAN_DIR/" -l | wc -l)

echo "📊 ESTADÍSTICAS GENERALES" >> "$OUTPUT_FILE"
echo "=========================" >> "$OUTPUT_FILE"
echo "Total de sorries: $TOTAL_SORRIES" >> "$OUTPUT_FILE"
echo "Total de archivos Lean: $TOTAL_FILES" >> "$OUTPUT_FILE"
echo "Archivos con sorries: $FILES_WITH_SORRIES" >> "$OUTPUT_FILE"
if [ "$FILES_WITH_SORRIES" -gt 0 ]; then
  AVG_SORRIES_PER_FILE=$(echo "scale=1; $TOTAL_SORRIES / $FILES_WITH_SORRIES" | bc)
else
  AVG_SORRIES_PER_FILE="0.0"
fi
echo "Promedio sorries/archivo: $AVG_SORRIES_PER_FILE" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Calcular progreso (baseline: 2630)
BASELINE=2630
ELIMINATED=$((BASELINE - TOTAL_SORRIES))
PERCENTAGE=$(echo "scale=1; ($ELIMINATED * 100) / $BASELINE" | bc)

echo "📈 PROGRESO" >> "$OUTPUT_FILE"
echo "===========" >> "$OUTPUT_FILE"
echo "Baseline inicial (2026-02-16): $BASELINE sorries" >> "$OUTPUT_FILE"
echo "Eliminados: $ELIMINATED" >> "$OUTPUT_FILE"
echo "Restantes: $TOTAL_SORRIES" >> "$OUTPUT_FILE"
echo "Progreso: $PERCENTAGE%" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Top 20 archivos con más sorries
echo "🔝 TOP 20 ARCHIVOS CON MÁS SORRIES" >> "$OUTPUT_FILE"
echo "===================================" >> "$OUTPUT_FILE"
grep -r "sorry" --include="*.lean" "$LEAN_DIR/" | cut -d: -f1 | sort | uniq -c | sort -rn | head -20 >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Buscar patrones de categorías (si están etiquetados)
echo "📋 DISTRIBUCIÓN POR CATEGORÍA (estimada)" >> "$OUTPUT_FILE"
echo "=========================================" >> "$OUTPUT_FILE"

# Categoría: Trivial
TRIVIAL=$(grep -r "sorry.*\(trivial\|rfl\|simp\|True\|= x\)" --include="*.lean" "$LEAN_DIR/" | wc -l)
echo "Trivial (estimado): $TRIVIAL" >> "$OUTPUT_FILE"

# Categoría: Biblioteca
LIBRARY=$(grep -r "sorry.*\(exact?\|apply?\|library\)" --include="*.lean" "$LEAN_DIR/" | wc -l)
echo "Búsqueda biblioteca (estimado): $LIBRARY" >> "$OUTPUT_FILE"

# Categoría: Espectral
SPECTRAL=$(grep -r "sorry.*\(spectrum\|spectral\|eigenvalue\|operator\)" --include="*.lean" "$LEAN_DIR/" | wc -l)
echo "Correspondencia espectral (estimado): $SPECTRAL" >> "$OUTPUT_FILE"

# Categoría: QCAL
QCAL=$(grep -r "sorry.*\(QCAL\|f₀\|coherence\|C =\)" --include="*.lean" "$LEAN_DIR/" | wc -l)
echo "Coherencia QCAL (estimado): $QCAL" >> "$OUTPUT_FILE"

echo "" >> "$OUTPUT_FILE"

# Archivos completamente limpios (sin sorries)
CLEAN_FILES=$(comm -23 \
  <(find "$LEAN_DIR" -name "*.lean" -type f | sort) \
  <(grep -r "sorry" --include="*.lean" "$LEAN_DIR/" -l | sort) \
  | wc -l)

echo "✅ ARCHIVOS COMPLETAMENTE LIMPIOS" >> "$OUTPUT_FILE"
echo "=================================" >> "$OUTPUT_FILE"
echo "Total sin sorries: $CLEAN_FILES de $TOTAL_FILES ($((CLEAN_FILES * 100 / TOTAL_FILES))%)" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Archivos con pocos sorries (candidatos para limpieza rápida)
echo "🎯 CANDIDATOS PARA LIMPIEZA RÁPIDA (<5 sorries)" >> "$OUTPUT_FILE"
echo "================================================" >> "$OUTPUT_FILE"
grep -r "sorry" --include="*.lean" "$LEAN_DIR/" | cut -d: -f1 | sort | uniq -c | sort -n | awk '$1 < 5' | head -20 >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Buscar patrones específicos de sorries triviales
echo "⚡ SORRIES TRIVIALES DETECTADOS (ejemplos)" >> "$OUTPUT_FILE"
echo "==========================================" >> "$OUTPUT_FILE"
echo "Reflexividad (x = x):" >> "$OUTPUT_FILE"
grep -r ": .* = .* := by sorry" --include="*.lean" "$LEAN_DIR/" | awk -F'=' '{
  left = $1
  right = $2
  sub(/.*:/, "", left)
  sub(/:=.*/, "", right)
  gsub(/[[:space:]]*/, "", left)
  gsub(/[[:space:]]*/, "", right)
  if (left == right) print
}' | head -5 >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "True trivial:" >> "$OUTPUT_FILE"
grep -r ": True := by sorry" --include="*.lean" "$LEAN_DIR/" | head -5 >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Estadísticas de progreso semanal (si hay git)
echo "📅 VELOCIDAD DE ELIMINACIÓN" >> "$OUTPUT_FILE"
echo "===========================" >> "$OUTPUT_FILE"
if [ -d "$REPO_DIR/.git" ]; then
    # Commits relacionados con sorry en los últimos 7 días
    RECENT_COMMITS=$(git log --since="7 days ago" --grep="sorry\|sorries" --oneline | wc -l)
    echo "Commits relacionados (últimos 7 días): $RECENT_COMMITS" >> "$OUTPUT_FILE"
else
    echo "Repositorio no es git, no se puede calcular velocidad" >> "$OUTPUT_FILE"
fi
echo "" >> "$OUTPUT_FILE"

# ETA estimado
if [ "$ELIMINATED" -gt 0 ]; then
    # Asumiendo ritmo constante
    DAYS_SINCE_START=1  # Ajustar según fecha de inicio real
    RATE=$(echo "scale=2; $ELIMINATED / $DAYS_SINCE_START" | bc)
    DAYS_REMAINING=$(echo "scale=0; $TOTAL_SORRIES / $RATE" | bc 2>/dev/null || echo "N/A")
    echo "⏱️ ESTIMACIÓN DE TIEMPO" >> "$OUTPUT_FILE"
    echo "=======================" >> "$OUTPUT_FILE"
    echo "Ritmo actual: ~$RATE sorries/día" >> "$OUTPUT_FILE"
    echo "Días estimados para 100%: $DAYS_REMAINING" >> "$OUTPUT_FILE"
fi
echo "" >> "$OUTPUT_FILE"

echo "==================================================" >> "$OUTPUT_FILE"
echo "Reporte generado por: generate_sorry_report.sh" >> "$OUTPUT_FILE"
echo "Ver SORRY_MAP.md para estrategias de eliminación" >> "$OUTPUT_FILE"
echo "==================================================" >> "$OUTPUT_FILE"

# Mostrar en pantalla
cat "$OUTPUT_FILE"

# Guardar también versión corta
echo "$TOTAL_SORRIES sorries restantes ($(date '+%Y-%m-%d'))" > "$REPO_DIR/.sorry_count"

echo ""
echo "✅ Reporte guardado en: $OUTPUT_FILE"
echo "✅ Contador guardado en: .sorry_count"

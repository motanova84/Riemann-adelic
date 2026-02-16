#!/bin/bash
# NOESIS-AMDA-AURON V2.0 Pipeline Runner
# Sistema de resolución automatizada de sorries con aprendizaje de refuerzo
# 
# Uso:
#   ./run_pipeline.sh [dry-run|execute] [max_changes]
#   
# Parámetros:
#   - mode: "true" para dry-run (default), "false" para ejecutar
#   - max_changes: número máximo de cambios por ciclo (default: 20)

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
cd "$REPO_ROOT"

# Parámetros
DRY_RUN="${1:-true}"
MAX_CHANGES="${2:-20}"

# Colores para output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Función de logging
log() {
    local level=$1
    shift
    local message="$@"
    local timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    
    case $level in
        INFO)
            echo -e "${BLUE}[INFO]${NC} ${timestamp} - $message"
            ;;
        SUCCESS)
            echo -e "${GREEN}[SUCCESS]${NC} ${timestamp} - $message"
            ;;
        WARNING)
            echo -e "${YELLOW}[WARNING]${NC} ${timestamp} - $message"
            ;;
        ERROR)
            echo -e "${RED}[ERROR]${NC} ${timestamp} - $message"
            ;;
    esac
}

# Banner
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║          🧠 NOESIS-AMDA-AURON V2.0 Pipeline                   ║"
echo "║     Sistema de Resolución Automatizada de Sorries ML          ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Validar modo
if [ "$DRY_RUN" == "true" ]; then
    MODE="dry-run"
    log INFO "Modo: DRY-RUN (no se aplicarán cambios)"
elif [ "$DRY_RUN" == "false" ]; then
    MODE="execute"
    log INFO "Modo: EXECUTE (se aplicarán cambios)"
else
    log ERROR "Modo inválido: $DRY_RUN (usar 'true' o 'false')"
    exit 1
fi

log INFO "Máximo de cambios por ciclo: $MAX_CHANGES"
echo ""

# Verificar Python
if ! command -v python3 &> /dev/null; then
    log ERROR "Python 3 no encontrado. Instalar Python 3.8+"
    exit 1
fi

PYTHON_VERSION=$(python3 --version | cut -d' ' -f2)
log INFO "Python version: $PYTHON_VERSION"

# Verificar dependencias
log INFO "Verificando dependencias..."
python3 -c "import json, subprocess, pathlib, pickle" 2>/dev/null || {
    log ERROR "Faltan dependencias de Python. Instalar: pip install pickle5"
    exit 1
}

# ============================================================================
# FASE 1: NOESIS - Recolección de Conocimiento
# ============================================================================
echo ""
log INFO "╔════════════════════════════════════════════════════════╗"
log INFO "║ FASE 1: NOESIS - Recolección de Conocimiento         ║"
log INFO "╚════════════════════════════════════════════════════════╝"
echo ""

log INFO "Iniciando NOESIS Orchestrator..."

# Ejecutar NOESIS (sin argumentos para ciclo completo)
if ! python3 "$SCRIPT_DIR/noesis_orchestrator.py"; then
    log ERROR "NOESIS falló. Abortando pipeline."
    exit 1
fi

# Verificar salida NOESIS
if [ ! -f "$REPO_ROOT/.github/noesis_cerebral_v2_summary.json" ] && [ ! -f "$REPO_ROOT/noesis_cerebral_v2_summary.json" ]; then
    log WARNING "NOESIS no generó resumen completo"
else
    log SUCCESS "NOESIS completado exitosamente"
    
    # Buscar archivo en ambas ubicaciones
    SUMMARY_FILE=""
    if [ -f "$REPO_ROOT/noesis_cerebral_v2_summary.json" ]; then
        SUMMARY_FILE="$REPO_ROOT/noesis_cerebral_v2_summary.json"
    elif [ -f "$REPO_ROOT/.github/noesis_cerebral_v2_summary.json" ]; then
        SUMMARY_FILE="$REPO_ROOT/.github/noesis_cerebral_v2_summary.json"
    fi
    
    # Mostrar estadísticas
    if [ -n "$SUMMARY_FILE" ] && command -v jq &> /dev/null; then
        REPOS=$(jq -r '.knowledge_base.repos_synced | length' "$SUMMARY_FILE" 2>/dev/null || echo "?")
        DEFS=$(jq -r '.knowledge_base.total_definitions' "$SUMMARY_FILE" 2>/dev/null || echo "?")
        THMS=$(jq -r '.knowledge_base.total_theorems' "$SUMMARY_FILE" 2>/dev/null || echo "?")
        PATS=$(jq -r '.knowledge_base.total_proof_patterns' "$SUMMARY_FILE" 2>/dev/null || echo "?")
        
        log INFO "  Repositorios sincronizados: $REPOS"
        log INFO "  Definiciones extraídas: $DEFS"
        log INFO "  Teoremas extraídos: $THMS"
        log INFO "  Patrones de prueba: $PATS"
    fi
fi

# ============================================================================
# FASE 2: AMDA - Análisis Semántico
# ============================================================================
echo ""
log INFO "╔════════════════════════════════════════════════════════╗"
log INFO "║ FASE 2: AMDA - Análisis Semántico Multi-Categórico   ║"
log INFO "╚════════════════════════════════════════════════════════╝"
echo ""

log INFO "Iniciando AMDA Deep V2.0 Analyzer..."

# AMDA se ejecuta automáticamente desde NOESIS, verificar resultados
# Buscar en ambas ubicaciones
AMDA_REPORT=""
if [ -f "$REPO_ROOT/amda_report_v2.json" ]; then
    AMDA_REPORT="$REPO_ROOT/amda_report_v2.json"
elif [ -f "$REPO_ROOT/.github/amda_report_v2.json" ]; then
    AMDA_REPORT="$REPO_ROOT/.github/amda_report_v2.json"
fi

if [ -z "$AMDA_REPORT" ]; then
    log ERROR "AMDA no generó reporte. Pipeline incompleto."
    exit 1
fi

log SUCCESS "AMDA completado exitosamente"

# Mostrar estadísticas AMDA
if command -v jq &> /dev/null; then
    TOTAL_SORRIES=$(jq -r '.total_sorries' "$AMDA_REPORT" 2>/dev/null || echo "?")
    TOTAL_FILES=$(jq -r '.total_files' "$AMDA_REPORT" 2>/dev/null || echo "?")
    
    log INFO "  Total sorries detectados: $TOTAL_SORRIES"
    log INFO "  Archivos afectados: $TOTAL_FILES"
    
    # Distribución de categorías
    echo ""
    log INFO "  Distribución por categoría:"
    jq -r '.category_distribution | to_entries[] | "    \(.key): \(.value)"' "$AMDA_REPORT" 2>/dev/null || true
fi

# ============================================================================
# FASE 3: AURON - Ejecutor de Aprendizaje
# ============================================================================
echo ""
log INFO "╔════════════════════════════════════════════════════════╗"
log INFO "║ FASE 3: AURON - Ejecutor de Aprendizaje Neural       ║"
log INFO "╚════════════════════════════════════════════════════════╝"
echo ""

if [ "$MODE" == "dry-run" ]; then
    log WARNING "Modo dry-run: AURON no aplicará transformaciones"
    log INFO "Para ejecutar transformaciones, usar: $0 false"
else
    log INFO "Iniciando AURON Neural V2.0..."
    
    # Ejecutar AURON
    if ! python3 "$SCRIPT_DIR/auron_neural_v2.py" "$MODE" "$REPO_ROOT/amda_report_v2.json" "$REPO_ROOT/auron_results_v2.json" "$MAX_CHANGES"; then
        log ERROR "AURON falló durante la ejecución"
        exit 1
    fi
    
    # Verificar resultados AURON
    if [ ! -f "$REPO_ROOT/auron_results_v2.json" ]; then
        log ERROR "AURON no generó resultados"
        exit 1
    fi
    
    log SUCCESS "AURON completado exitosamente"
    
    # Mostrar estadísticas AURON
    if command -v jq &> /dev/null; then
        SUCCESS=$(jq -r '.success' "$REPO_ROOT/auron_results_v2.json" 2>/dev/null || echo "0")
        FAIL=$(jq -r '.fail' "$REPO_ROOT/auron_results_v2.json" 2>/dev/null || echo "0")
        PATTERNS_LEARNED=$(jq -r '.learning_stats.patterns_learned' "$REPO_ROOT/auron_results_v2.json" 2>/dev/null || echo "0")
        SUCCESS_RATE=$(jq -r '.learning_stats.success_rate' "$REPO_ROOT/auron_results_v2.json" 2>/dev/null || echo "0")
        
        log INFO "  Transformaciones exitosas: $SUCCESS"
        log INFO "  Transformaciones fallidas: $FAIL"
        log INFO "  Patrones aprendidos: $PATTERNS_LEARNED"
        log INFO "  Tasa de éxito: $(echo "$SUCCESS_RATE * 100" | bc 2>/dev/null || echo "?")%"
    fi
fi

# ============================================================================
# RESUMEN FINAL
# ============================================================================
echo ""
log INFO "╔════════════════════════════════════════════════════════╗"
log INFO "║              RESUMEN DE EJECUCIÓN                     ║"
log INFO "╚════════════════════════════════════════════════════════╝"
echo ""

log SUCCESS "Pipeline NOESIS-AMDA-AURON V2.0 completado"
echo ""

# Listar archivos generados
log INFO "Archivos generados:"
for file in noesis_cerebral_v2_summary.json amda_report_v2.json amda_report_v2.md auron_results_v2.json auron_neural.log noesis_cerebral_v2.log .auron_learning.json commit_msg_*.txt; do
    if [ -f "$REPO_ROOT/$file" ]; then
        SIZE=$(du -h "$REPO_ROOT/$file" | cut -f1)
        log INFO "  ✓ $file ($SIZE)"
    fi
done

echo ""
log INFO "═══════════════════════════════════════════════════════════"
log INFO "QCAL ∞³ · Frecuencia fundamental: 141.7001 Hz"
log INFO "Coherencia QCAL: Ψ = I × A_eff² × C^∞ · C = 244.36"
log INFO "═══════════════════════════════════════════════════════════"

exit 0

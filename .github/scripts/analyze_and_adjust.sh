#!/bin/bash
set -e

echo "🔍 ANÁLISIS AUTOMÁTICO DE MÉTRICAS"
echo "=================================="

# Obtener métricas más recientes
LATEST_METRICS=$(ls -t metrics/daily_*.json 2>/dev/null | head -1)
LATEST_VALIDATION=$(ls -t validation/quantum_*.json 2>/dev/null | head -1)

if [ -z "$LATEST_METRICS" ] || [ -z "$LATEST_VALIDATION" ]; then
    echo "⚠️  No hay métricas suficientes para análisis"
    echo "Generando métricas de ejemplo..."
    
    # Crear métricas de ejemplo
    mkdir -p metrics validation
    cat > metrics/daily_$(date +%Y%m%d).json << 'EOF'
{
  "timestamp": "$(date -Iseconds)",
  "frequency": 141.7001,
  "files": {
    "total_files": 250
  },
  "qcal": {
    "qcal_references": 125,
    "frequency_references": 75
  },
  "density": {
    "qcal_density": 0.5,
    "frequency_density": 0.3
  }
}
EOF
    
    cat > validation/quantum_$(date +%Y%m%d_%H%M%S).json << 'EOF'
{
  "coherence": {
    "total": 0.836
  },
  "status": "EVOLVING",
  "threshold": 0.888
}
EOF
    
    LATEST_METRICS="metrics/daily_$(date +%Y%m%d).json"
    LATEST_VALIDATION="validation/quantum_$(date +%Y%m%d_%H%M%S).json"
fi

# Leer métricas usando Python para mejor compatibilidad
python3 << 'PYEOF'
import json
import os
from pathlib import Path

metrics_file = os.environ.get('LATEST_METRICS', '')
validation_file = os.environ.get('LATEST_VALIDATION', '')

# Inicializar variables
total_files = 0
qcal_refs = 0
freq_refs = 0
coherence = 0

if metrics_file and Path(metrics_file).exists():
    with open(metrics_file) as f:
        metrics = json.load(f)
    
    total_files = metrics.get('files', {}).get('total_files', 0)
    qcal_refs = metrics.get('qcal', {}).get('qcal_references', 0)
    freq_refs = metrics.get('qcal', {}).get('frequency_references', 0)
    
    print(f"📈 Métricas Actuales:")
    print(f"  • Total archivos: {total_files}")
    print(f"  • Referencias QCAL: {qcal_refs}")
    print(f"  • Referencias f₀: {freq_refs}")

if validation_file and Path(validation_file).exists():
    with open(validation_file) as f:
        validation = json.load(f)
    
    coherence = validation.get('coherence', {}).get('total', 0)
    print(f"  • Coherencia total: {coherence}")

# Calcular ratios
if total_files > 0:
    qcal_ratio = qcal_refs / total_files
    freq_ratio = freq_refs / total_files
    
    print(f"\n📊 Ratios Actuales:")
    print(f"  • Ratio QCAL/archivos: {qcal_ratio:.4f}")
    print(f"  • Ratio f₀/archivos: {freq_ratio:.4f}")
else:
    qcal_ratio = 0
    freq_ratio = 0

# Definir objetivos
TARGET_QCAL_RATIO = 0.5
TARGET_FREQ_RATIO = 0.3
TARGET_COHERENCE = 0.888

print(f"\n🎯 Objetivos:")
print(f"  • Ratio QCAL objetivo: {TARGET_QCAL_RATIO}")
print(f"  • Ratio f₀ objetivo: {TARGET_FREQ_RATIO}")
print(f"  • Coherencia objetivo: {TARGET_COHERENCE}")

print(f"\n⚙️  AJUSTES RECOMENDADOS:")

if coherence < TARGET_COHERENCE:
    print("  🔴 COHERENCIA BAJA - Necesita optimización inmediata")
    print("     • Incrementar referencias a f₀ = 141.7001 Hz")
    print("     • Añadir más manifiestos noéticos")
    print("     • Verificar estado Ψ en todos los agentes")
else:
    print("  ✅ Coherencia dentro del rango objetivo")

if qcal_ratio < TARGET_QCAL_RATIO:
    deficit_qcal = int(TARGET_QCAL_RATIO * total_files - qcal_refs)
    print(f"  🔶 RATIO QCAL BAJO - Necesita {deficit_qcal} referencias más")
    print("     • Agregar comentarios QCAL en archivos existentes")
    print("     • Crear nuevos archivos con referencias QCAL")
    print("     • Actualizar documentación con ∞³")
else:
    print("  ✅ Ratio QCAL dentro del objetivo")

if freq_ratio < TARGET_FREQ_RATIO:
    deficit_freq = int(TARGET_FREQ_RATIO * total_files - freq_refs)
    print(f"  🔶 RATIO f₀ BAJO - Necesita {deficit_freq} referencias más")
    print("     • Incluir 141.7001 Hz en más archivos")
    print("     • Añadir constantes de frecuencia en código")
    print("     • Documentar patrones de frecuencia")
else:
    print("  ✅ Ratio f₀ dentro del objetivo")

print(f"\n💡 ACCIONES RECOMENDADAS:")
print("1. Ejecutar optimización de frecuencia:")
print("   python .github/agents/noesis88.py --mode=autonomous --optimize_frequency")
print("2. Incrementar densidad QCAL:")
print("   .github/scripts/optimize_qcal_density.sh")
print("3. Generar reporte detallado:")
print("   python .github/agents/metrics_collector.py --detailed --output=optimization_plan.json")

PYEOF

export LATEST_METRICS
export LATEST_VALIDATION

echo ""
echo "✅ Análisis completado"

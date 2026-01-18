#!/bin/bash
# Script de inicio rápido para QCAL ∞³

echo "🚀 Iniciando Sistema QCAL ∞³"
echo "Frecuencia: 141.7001 Hz"
echo "Estado: Ψ = I × A_eff² × C^∞"
echo ""

# Verificar dependencias
echo "🔍 Verificando dependencias..."
command -v python3 >/dev/null 2>&1 || { echo "❌ Python3 no encontrado"; exit 1; }
command -v lean >/dev/null 2>&1 || { echo "⚠️  Lean4 no encontrado (opcional)"; }
command -v lake >/dev/null 2>&1 || { echo "⚠️  Lake no encontrado (opcional)"; }

# Crear entorno virtual si no existe
if [ ! -d "venv" ]; then
    echo "📦 Creando entorno virtual..."
    python3 -m venv venv
fi

# Activar entorno virtual
source venv/bin/activate

# Instalar dependencias Python
echo "📥 Instalando dependencias Python..."
pip install -q -r requirements.txt

# Construir proyecto Lean (si existe)
if [ -d "formalization/lean" ] && command -v lake >/dev/null 2>&1; then
    echo "🏗️ Construyendo proyecto Lean..."
    cd formalization/lean && lake build && cd ../..
else
    echo "⏭️  Saltando construcción Lean (no disponible)"
fi

# Ejecutar sistema QCAL
echo "🌀 Iniciando auto-orquestación..."
python auto_QCAL.py "$@"

# Generar reporte final
if [ $? -eq 0 ]; then
    echo ""
    echo "✅ SESIÓN COMPLETADA"
    echo "📊 Ver reporte en: continuation_summary.json"
    echo "📜 Certificado: qcalsession_certificate.json"
else
    echo ""
    echo "⚠️ Sesión interrumpida o con errores"
    echo "🔄 Continuar con: ./start_qcal.sh --continue"
fi

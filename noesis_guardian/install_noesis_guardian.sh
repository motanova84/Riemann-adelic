#!/usr/bin/env bash
# ==============================================================================
# NOESIS GUARDIAN 3.0 — INSTALLER
# Sistema técnico de validación, análisis y autoreparación del repositorio
# Autor: José Manuel Mota Burruezo (JMMB Ψ ✧)
# ==============================================================================
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

echo "🌌 Instalando NOESIS GUARDIAN 3.0..."

# Ensure directory structure exists
echo "📂 Verificando estructura de directorios..."
mkdir -p "$SCRIPT_DIR/logs"
mkdir -p "$SCRIPT_DIR/modules"
mkdir -p "$SCRIPT_DIR/panel"

# Verify all required modules exist
echo "🔍 Verificando módulos..."
REQUIRED_MODULES=(
    "$SCRIPT_DIR/guardian_core.py"
    "$SCRIPT_DIR/modules/watcher.py"
    "$SCRIPT_DIR/modules/autorepair_engine.py"
    "$SCRIPT_DIR/modules/spectral_monitor.py"
    "$SCRIPT_DIR/modules/ai_notifier.py"
    "$SCRIPT_DIR/modules/sabio_bridge.py"
    "$SCRIPT_DIR/modules/aik_sync.py"
    "$SCRIPT_DIR/panel/panel_dashboard.py"
)

for module in "${REQUIRED_MODULES[@]}"; do
    if [ -f "$module" ]; then
        echo "   ✓ $(basename "$module")"
    else
        echo "   ✗ FALTA: $(basename "$module")"
        exit 1
    fi
done

# Make run script executable
chmod +x "$SCRIPT_DIR/run_guardian.sh"

# Install dependencies if requirements file exists
echo "🔧 Configurando entorno..."
if [ -f "$REPO_ROOT/requirements-core.txt" ]; then
    pip install -r "$REPO_ROOT/requirements-core.txt" || echo "⚠️ Algunos paquetes opcionales no fueron instalados"
fi

# Test the installation
echo "🧪 Probando instalación..."
cd "$REPO_ROOT"
python3 -c "from noesis_guardian import NoesisGuardian; print('   ✓ Import OK')"

echo ""
echo "✨ Instalación completada."
echo ""
echo "Para ejecutar el Guardian:"
echo "   cd $REPO_ROOT"
echo "   ./noesis_guardian/run_guardian.sh"
echo ""
echo "O para una sola ejecución:"
echo "   python3 -m noesis_guardian.guardian_core"

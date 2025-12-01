#!/usr/bin/env bash
# ==============================================================================
# NOESIS GUARDIAN 3.0 — INSTALLER
# Sistema técnico de validación, análisis y autoreparación del repositorio
# Autor: José Manuel Mota Burruezo (JMMB Ψ ✧)
# ==============================================================================
set -e

echo "🌌 Instalando NOESIS GUARDIAN 3.0..."
mkdir -p noesis_guardian
mkdir -p noesis_guardian/logs
mkdir -p noesis_guardian/modules
mkdir -p noesis_guardian/panel

echo "📂 Copiando módulos..."
cp guardian_core.py noesis_guardian/
cp watcher.py noesis_guardian/modules/
cp autorepair_engine.py noesis_guardian/modules/
cp spectral_monitor.py noesis_guardian/modules/
cp ai_notifier.py noesis_guardian/modules/
cp sabio_bridge.py noesis_guardian/modules/
cp aik_sync.py noesis_guardian/modules/
cp panel_dashboard.py noesis_guardian/panel/

echo "⚙️ Creando servicio de guardián..."
cat > noesis_guardian/run_guardian.sh <<EOF
#!/usr/bin/env bash
while true; do
    python3 noesis_guardian/guardian_core.py
    sleep 1800
done
EOF
chmod +x noesis_guardian/run_guardian.sh

echo "🔧 Configurando entorno..."
pip install -r requirements-core.txt || echo "⚠️ Paquetes opcionales no instalados"

echo "✨ Instalación completada."
echo "Ejecuta:   ./noesis_guardian/run_guardian.sh"

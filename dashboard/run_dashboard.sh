#!/bin/bash
# 🚀 run_dashboard.sh
# Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
# Proyecto: Análisis espectral 141.7 Hz – GW250114
# Función: Lanza servidor Flask para visualización del espectro 141.7 Hz
# ------------------------------------------
# Uso: ./run_dashboard.sh

set -e

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "  🌀 Dashboard Avanzado GW250114 - Análisis 141.7001 Hz"
echo "  Autor: José Manuel Mota Burruezo (JMMB Ψ✧)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Verificar que estamos en la raíz del repositorio
if [ ! -f "validate_v5_coronacion.py" ]; then
    echo "❌ Error: Debes ejecutar este script desde la raíz del repositorio"
    echo "   Ejemplo: ./dashboard/run_dashboard.sh"
    exit 1
fi

# Verificar dependencias de Python
echo "🔍 Verificando dependencias de Python..."
REQUIRED_PACKAGES="matplotlib numpy scipy notebook"

MISSING_PACKAGES=""
for package in $REQUIRED_PACKAGES; do
    if ! python3 -c "import $package" 2>/dev/null; then
        MISSING_PACKAGES="$MISSING_PACKAGES $package"
    fi
done

if [ -n "$MISSING_PACKAGES" ]; then
    echo "⚠️  Paquetes faltantes:$MISSING_PACKAGES"
    echo "   Instalando dependencias desde requirements.txt..."
    pip3 install -q -r requirements.txt
else
    echo "✅ Todas las dependencias están instaladas"
fi

echo "✅ Dependencias verificadas correctamente"
echo ""

# Verificar si existe el notebook de validación 141 Hz
NOTEBOOK_PATH="notebooks/141hz_validation.ipynb"
if [ ! -f "$NOTEBOOK_PATH" ]; then
    echo "❌ Error: No se encuentra el notebook $NOTEBOOK_PATH"
    exit 1
fi

echo "📊 Iniciando Dashboard de Validación 141.7001 Hz..."
echo ""
echo "   Notebook: $NOTEBOOK_PATH"
echo "   Evento: GW250114 (LIGO/Virgo)"
echo "   Frecuencia objetivo: 141.7001 Hz"
echo ""

# Opción 1: Usar Jupyter Notebook (interactivo)
echo "🚀 Lanzando Jupyter Notebook..."
echo ""
echo "   El servidor se abrirá en: http://localhost:8888"
echo "   (Si el puerto 8888 está en uso, Jupyter seleccionará otro automáticamente)"
echo "   Para detener el servidor, presiona Ctrl+C"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# Lanzar Jupyter Notebook en el directorio notebooks
# Jupyter automáticamente usará el siguiente puerto disponible si 8888 está ocupado
cd notebooks
jupyter notebook 141hz_validation.ipynb --no-browser --port=8888

# Nota: Si se prefiere usar Flask, descomentar las siguientes líneas
# y comentar el comando de jupyter notebook anterior:
#
# echo "🚀 Lanzando servidor Flask..."
# cd dashboard
# python3 app.py

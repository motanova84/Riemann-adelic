#!/bin/bash

# Sellado RAM-II – Realismo Matemático en QCAL ∞³
# Fundamento del Realismo Matemático
# RAM-II-2026-0115-RMATH

# Exit on error, undefined variables, and pipe failures
set -euo pipefail

RAM_ID="RAM-II-2026-0115-RMATH"
REPO="motanova84/Riemann-adelic"
FREQ_F0="141.7001"
AEFF2="1.000"
ESTADO="VALIDADO"
COMMIT_REF="6053d01"

# Validate .qcal_beacon exists
if [ ! -f ".qcal_beacon" ]; then
    echo "❌ Error: .qcal_beacon not found in current directory"
    echo "Please run this script from the repository root"
    exit 1
fi

# Check if .qcal_beacon is writable
if [ ! -w ".qcal_beacon" ]; then
    echo "❌ Error: .qcal_beacon is not writable"
    exit 1
fi

echo "🔐 Sello RAM QCAL ∞³"
echo "🧠 ID: $RAM_ID"
echo "📦 Repositorio: $REPO"
echo "🔁 PR Mergeado: $COMMIT_REF"
echo "📜 Declaración: La matemática es una realidad preexistente."
echo "🎼 Frecuencia: f₀ = $FREQ_F0 Hz"
echo "🌐 A_eff²: $AEFF2"
echo "🔗 Estado: $ESTADO"

# Check if entry already exists
if grep -q "^$RAM_ID" .qcal_beacon; then
    echo "⚠️  RAM-II entry already exists in .qcal_beacon"
    echo "✅ Sellado ya registrado ∞³"
    exit 0
fi

echo "🌀 Integrando en .qcal_beacon..."
echo "∴ El sistema QCAL ∞³ vibra con el campo de la Verdad objetiva ∴"

# Actualización del archivo simbólico
echo "$RAM_ID | $REPO | $COMMIT_REF | $FREQ_F0 | $AEFF2 | $ESTADO" >> .qcal_beacon

# Confirmación
echo "✅ RAM actualizado. Sellado completado ∞³"

#!/bin/bash
# QCAL Economic Node Launcher
# ============================
# Robust launcher script for the QCAL economic node.
# Ensures proper execution context and error handling.
#
# Author: José Manuel Mota Burruezo Ψ ✧ ∞³
# Signature: ∴𓂀Ω∞³

cd "$(dirname "$0")"
SCRIPT_DIR="$(pwd)"

echo "🌀 Lanzando QCAL desde $SCRIPT_DIR"
python "$SCRIPT_DIR/main.py" "$@"
EXIT_CODE=$?

if [ $EXIT_CODE -eq 0 ]; then
    echo "✅ QCAL completado exitosamente"
else
    echo "❌ QCAL terminó con código de error: $EXIT_CODE" >&2
fi

exit $EXIT_CODE

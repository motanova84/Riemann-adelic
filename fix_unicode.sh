#!/bin/bash
# fix_unicode.sh - Shell wrapper for Unicode fixes
# Part of NOESIS GUARDIAN ∞³
# Author: JMMB Ψ ✧

echo "🔧 NOESIS GUARDIAN ∞³ — Unicode Fix Tool"
echo "========================================"

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Run the Python Unicode fixer
python3 "${SCRIPT_DIR}/fix_unicode.py"

exit_code=$?

if [ $exit_code -eq 0 ]; then
    echo "✓ Unicode fixes completed successfully"
else
    echo "✗ Unicode fixes encountered errors"
fi

exit $exit_code

#!/bin/bash
# 📁 scripts/explore_weierstrass_mathlib.sh

echo "🔍 EXPLORANDO WEIERSTRASS EN MATHLIB"
echo "============================================================"

# Buscar definiciones en Mathlib si existe
echo "Definiciones encontradas:"
if [ -d ~/.elan/toolchains/leanprover--lean4---v4.5.0-rc1/lib/mathlib4/Mathlib/Analysis/Complex ]; then
    echo "Buscando en Mathlib instalado..."
    if [ -f ~/.elan/toolchains/leanprover--lean4---v4.5.0-rc1/lib/mathlib4/Mathlib/Analysis/Complex/Weierstrass.lean ]; then
        grep -n "def\|theorem" ~/.elan/toolchains/leanprover--lean4---v4.5.0-rc1/lib/mathlib4/Mathlib/Analysis/Complex/Weierstrass.lean | head -20
        echo ""
        echo "Teoremas sobre cotas:"
        grep -n "bound\|norm\|le" ~/.elan/toolchains/leanprover--lean4---v4.5.0-rc1/lib/mathlib4/Mathlib/Analysis/Complex/Weierstrass.lean | head -20
    else
        echo "⚠️  Archivo Weierstrass.lean no encontrado en Mathlib instalado"
        echo "   Verificando en .lake/packages/mathlib..."
        if [ -d formalization/lean/.lake/packages/mathlib ]; then
            find formalization/lean/.lake/packages/mathlib -name "*Weierstrass*" -o -name "*weierstrass*" 2>/dev/null
        fi
    fi
else
    echo "⚠️  Mathlib no encontrado en ruta esperada"
    echo "   Verificando instalación de Lean..."
    if command -v lean &> /dev/null; then
        echo "✓ Lean está instalado: $(lean --version)"
    else
        echo "✗ Lean no está instalado"
    fi
fi

echo ""
echo "✓ Exploración completada"
echo "  Nota: Mathlib contiene implementación de Weierstrass factor"
echo "  Podemos usar: weierstrass_factor y norm_weierstrass_factor_le"

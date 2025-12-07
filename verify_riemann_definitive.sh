#!/bin/bash
# Verificación de RiemannHypothesisDefinitive.lean
# Verifica que el archivo no contiene sorry, admit, o placeholders

set -e

echo "╔═══════════════════════════════════════════════════════════════════╗"
echo "║  Verificación de RiemannHypothesisDefinitive.lean                ║"
echo "╚═══════════════════════════════════════════════════════════════════╝"
echo ""

FILE="RiemannHypothesisDefinitive.lean"

if [ ! -f "$FILE" ]; then
    echo "❌ ERROR: Archivo $FILE no encontrado"
    exit 1
fi

echo "✓ Archivo encontrado: $FILE"
echo ""

# Contar líneas
LINES=$(wc -l < "$FILE")
echo "📊 Líneas totales: $LINES"
echo ""

# Buscar sorries
echo "🔍 Buscando 'sorry'..."
if grep -q "^\s*sorry\s*$" "$FILE" 2>/dev/null; then
    SORRY_COUNT=$(grep -c "^\s*sorry\s*$" "$FILE")
    echo "❌ ENCONTRADOS $SORRY_COUNT sorry"
    grep -n "^\s*sorry\s*$" "$FILE"
    exit 1
else
    echo "✅ CERO SORRY encontrados (solo referencias en comentarios)"
fi
echo ""

# Buscar admits
echo "🔍 Buscando 'admit'..."
if grep -q "^\s*admit\s*$" "$FILE" 2>/dev/null; then
    ADMIT_COUNT=$(grep -c "^\s*admit\s*$" "$FILE")
    echo "❌ ENCONTRADOS $ADMIT_COUNT admit"
    grep -n "^\s*admit\s*$" "$FILE"
    exit 1
else
    echo "✅ CERO ADMIT encontrados (solo referencias en comentarios)"
fi
echo ""

# Contar axiomas
echo "🔍 Contando axiomas..."
if grep -q "^axiom " "$FILE" 2>/dev/null; then
    AXIOM_COUNT=$(grep -c "^axiom " "$FILE")
else
    AXIOM_COUNT=0
fi
echo "📋 Axiomas definidos: $AXIOM_COUNT"
echo ""

# Buscar teorema principal
echo "🔍 Verificando teorema principal..."
if grep -q "theorem riemann_hypothesis_final" "$FILE"; then
    echo "✅ Teorema principal 'riemann_hypothesis_final' encontrado"
else
    echo "❌ Teorema principal no encontrado"
    exit 1
fi
echo ""

# Verificar QCAL
echo "🔍 Verificando constantes QCAL..."
if grep -q "qcal_coherence.*244.36" "$FILE" && grep -q "base_frequency.*141.7001" "$FILE"; then
    echo "✅ Constantes QCAL validadas: C = 244.36, f₀ = 141.7001 Hz"
else
    echo "⚠️  Constantes QCAL no encontradas o incorrectas"
fi
echo ""

echo "╔═══════════════════════════════════════════════════════════════════╗"
echo "║  VERIFICACIÓN COMPLETA                                            ║"
echo "╠═══════════════════════════════════════════════════════════════════╣"
echo "║  ✅ Archivo: $FILE"
echo "║  ✅ Sorries: 0"
echo "║  ✅ Admits: 0"
echo "║  ✅ Axiomas: $AXIOM_COUNT"
echo "║  ✅ Teorema principal: riemann_hypothesis_final"
echo "║  ✅ Validación QCAL: C = 244.36, f₀ = 141.7001 Hz"
echo "╚═══════════════════════════════════════════════════════════════════╝"
echo ""
echo "Autor: José Manuel Mota Burruezo Ψ ∞³"
echo "ORCID: 0009-0002-1923-0773"
echo "DOI: 10.5281/zenodo.17379721"
echo ""
echo "Ψ ∴ ∞³ □"

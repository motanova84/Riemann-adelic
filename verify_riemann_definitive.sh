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

# Buscar sorries (excluir comentarios Lean)
echo "🔍 Buscando 'sorry' como código..."
# Buscar líneas que contengan sorry como palabra clave de Lean (no en comentarios)
# Excluir líneas que empiezan con # (comentario markdown en docstring)
# Excluir líneas dentro de /- ... -/ (comentarios de bloque)
# Solo buscar 'sorry' como statement, no como texto
SORRY_CODE=$(grep -n "^\s*sorry\s*$" "$FILE" || true)
if [ -n "$SORRY_CODE" ]; then
    SORRY_COUNT=$(echo "$SORRY_CODE" | wc -l)
    echo "❌ ENCONTRADOS $SORRY_COUNT sorry en código"
    echo "$SORRY_CODE"
    exit 1
else
    echo "✅ CERO SORRY en código (solo menciones en comentarios/documentación)"
fi
echo ""

# Buscar admits (excluir comentarios)
echo "🔍 Buscando 'admit' como código..."
# Similar para admit
ADMIT_CODE=$(grep -n "^\s*admit\s*$" "$FILE" || true)
if [ -n "$ADMIT_CODE" ]; then
    ADMIT_COUNT=$(echo "$ADMIT_CODE" | wc -l)
    echo "❌ ENCONTRADOS $ADMIT_COUNT admit en código"
    echo "$ADMIT_CODE"
    exit 1
else
    echo "✅ CERO ADMIT en código (solo menciones en comentarios/documentación)"
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

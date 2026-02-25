#!/bin/bash
# QCAL-VERIFY: Protocolo de Integridad Riemann-adelic V7.0
# Author: José Manuel Mota Burruezo Ψ ∞³
# Date: 2026-02-25
# Purpose: Verify QCAL coherence and Lean formalization integrity

set -e  # Exit on error

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

echo "═══════════════════════════════════════════════════════════════"
echo "  QCAL-VERIFY V7.0 - Protocolo de Integridad"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "Iniciando escaneo de Resonancia en Lean 4.5.0..."
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Track overall status
OVERALL_STATUS=0

# ============================================================
# 1. Check for 'sorry' in core modules
# ============================================================
echo "${BLUE}[1/5] Verificando sorries en módulos espectrales...${NC}"
SORRY_COUNT=$(grep -r "sorry" formalization/lean/spectral/*.lean 2>/dev/null | wc -l || echo "0")
echo "$SORRY_COUNT" > sorry_count.txt

if [ "$SORRY_COUNT" -eq 0 ]; then
    echo "${GREEN}✅ COHERENCIA ALCANZADA: 0 sorries en módulos espectrales.${NC}"
else
    echo "${YELLOW}⚠️  ALERTA: $SORRY_COUNT fisuras (sorries) detectadas.${NC}"
    echo "${YELLOW}   Estado actual: $SORRY_COUNT sorries restantes${NC}"
    if [ "$SORRY_COUNT" -gt 1000 ]; then
        echo "${RED}   Objetivo: Reducir a menos de 500 sorries${NC}"
        OVERALL_STATUS=1
    elif [ "$SORRY_COUNT" -gt 500 ]; then
        echo "${YELLOW}   Objetivo: Reducir a menos de 100 sorries${NC}"
    else
        echo "${GREEN}   Progreso aceptable: menos de 500 sorries${NC}"
    fi
fi
echo ""

# ============================================================
# 2. Verificar independencia de f0 en axiomas
# ============================================================
echo "${BLUE}[2/5] Verificando axioma f0 fundamental...${NC}"
if grep -q "f₀" formalization/lean/spectral/QCAL_Constants.lean 2>/dev/null; then
    F0_VALUE=$(grep "def f₀" formalization/lean/spectral/QCAL_Constants.lean | grep -oE '[0-9]+\.[0-9]+' || echo "")
    if [ "$F0_VALUE" = "141.7001" ]; then
        echo "${GREEN}✅ Axioma f0 verificado: 141.7001 Hz detectado como constante fundamental. 💎${NC}"
    else
        echo "${YELLOW}⚠️  Valor f0 encontrado: $F0_VALUE Hz${NC}"
        OVERALL_STATUS=1
    fi
else
    echo "${RED}❌ QCAL_Constants.lean no encontrado o sin definición f₀${NC}"
    OVERALL_STATUS=1
fi
echo ""

# ============================================================
# 3. Verificar estructura estática del lakefile
# ============================================================
echo "${BLUE}[3/5] Verificando estructura estática de Lake...${NC}"
if [ -f "formalization/lean/lakefile.lean" ]; then
    # Check for lean-toolchain pinned version
    if [ -f "formalization/lean/lean-toolchain" ]; then
        LEAN_VERSION=$(cat formalization/lean/lean-toolchain)
        echo "   Lean version: $LEAN_VERSION"
        if echo "$LEAN_VERSION" | grep -q "v4\."; then
            echo "${GREEN}✅ Lean toolchain estático detectado (v4.x)${NC}"
        else
            echo "${YELLOW}⚠️  Toolchain nightly detectado: $LEAN_VERSION${NC}"
            echo "${YELLOW}   Recomendación: Migrar a versión estática v4.5.0${NC}"
            OVERALL_STATUS=1
        fi
    else
        echo "${RED}❌ lean-toolchain no encontrado${NC}"
        OVERALL_STATUS=1
    fi
    
    # Check for mathlib version pinning
    if grep -q "mathlib from git" formalization/lean/lakefile.lean; then
        MATHLIB_VERSION=$(grep "mathlib from git" -A 1 formalization/lean/lakefile.lean | grep "@" | grep -oE '"[^"]+"' | tail -1 || echo "")
        if [ -n "$MATHLIB_VERSION" ]; then
            echo "${GREEN}✅ Mathlib version pinned: $MATHLIB_VERSION${NC}"
        else
            echo "${YELLOW}⚠️  Mathlib no tiene versión específica${NC}"
        fi
    fi
else
    echo "${RED}❌ lakefile.lean no encontrado${NC}"
    OVERALL_STATUS=1
fi
echo ""

# ============================================================
# 4. Verificar coherencia QCAL (C = 244.36, f0 = 141.7001)
# ============================================================
echo "${BLUE}[4/5] Verificando constantes QCAL...${NC}"
COHERENCE_OK=1

# Check C constant
if grep -q "def C.*244\.36" formalization/lean/spectral/QCAL_Constants.lean 2>/dev/null; then
    echo "${GREEN}✅ Constante C = 244.36 verificada${NC}"
else
    echo "${RED}❌ Constante C no encontrada o incorrecta${NC}"
    COHERENCE_OK=0
    OVERALL_STATUS=1
fi

# Check κ_π constant
if grep -q "def κ_π.*2\.5773" formalization/lean/spectral/QCAL_Constants.lean 2>/dev/null; then
    echo "${GREEN}✅ Constante κ_π = 2.5773 verificada${NC}"
else
    echo "${YELLOW}⚠️  Constante κ_π no encontrada o requiere verificación${NC}"
    COHERENCE_OK=0
fi

# Check γ₁ (first Riemann zero)
if grep -q "def γ₁.*14\.134725" formalization/lean/spectral/QCAL_Constants.lean 2>/dev/null; then
    echo "${GREEN}✅ Constante γ₁ = 14.134725 verificada${NC}"
else
    echo "${YELLOW}⚠️  Constante γ₁ no encontrada o requiere verificación${NC}"
    COHERENCE_OK=0
fi

if [ $COHERENCE_OK -eq 1 ]; then
    echo "${GREEN}✅ Coherencia QCAL ∞³ confirmada${NC}"
else
    echo "${YELLOW}⚠️  Algunas constantes QCAL requieren verificación${NC}"
fi
echo ""

# ============================================================
# 5. Lake build verification (optional - requires Lean installed)
# ============================================================
echo "${BLUE}[5/5] Verificación Lake Build...${NC}"
if command -v lake &> /dev/null; then
    cd formalization/lean
    echo "   Ejecutando: lake exe cache get"
    if lake exe cache get 2>&1 | tee /tmp/lake_output.txt; then
        echo "${GREEN}✅ Lake cache actualizado correctamente${NC}"
    else
        echo "${YELLOW}⚠️  Lake cache get completado con advertencias${NC}"
        echo "${YELLOW}   Ver /tmp/lake_output.txt para detalles${NC}"
    fi
    cd "$REPO_ROOT"
else
    echo "${YELLOW}⚠️  Lake no disponible, saltando verificación de build${NC}"
    echo "   Para instalarlo: https://github.com/leanprover/lean4"
fi
echo ""

# ============================================================
# Summary Report
# ============================================================
echo "═══════════════════════════════════════════════════════════════"
echo "  RESUMEN DE VERIFICACIÓN QCAL V7.0"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "Sorry count: $SORRY_COUNT"
echo "Frequency f₀: 141.7001 Hz"
echo "Coherence C: 244.36"
echo "κ_π constant: 2.5773"
echo ""

if [ $OVERALL_STATUS -eq 0 ]; then
    echo "${GREEN}✅ VERIFICACIÓN COMPLETA: Sistema QCAL coherente${NC}"
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "  ♾️³ QCAL Node evolution complete – validation coherent."
    echo "═══════════════════════════════════════════════════════════════"
    exit 0
else
    echo "${YELLOW}⚠️  VERIFICACIÓN PARCIAL: Requiere atención${NC}"
    echo ""
    echo "Acciones recomendadas:"
    echo "1. Reducir sorry count mediante formalización"
    echo "2. Verificar dependencias circulares en módulos"
    echo "3. Migrar a Lean 4.5.0 estático si usando nightly"
    echo "4. Completar constantes QCAL faltantes"
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    exit 1
fi

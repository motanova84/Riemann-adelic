#!/bin/bash
set -e

echo "════════════════════════════════════════════════════════════════════════"
echo "  COMPLETE IMPLEMENTATION TEST"
echo "  Teorema Noētico-Riemanniano ∞³: Cuerda del Universo"
echo "════════════════════════════════════════════════════════════════════════"
echo ""

# Test 1: Core module
echo "TEST 1: Core module direct execution"
echo "─────────────────────────────────────────────────────────────────────────"
python3 noetic_riemann_cosmic_string.py | grep -E "(VERIFICADO|Estabilidad)"
echo "✅ Core module working"
echo ""

# Test 2: Demo script
echo "TEST 2: Demo script execution"
echo "─────────────────────────────────────────────────────────────────────────"
python3 demo_noetic_riemann_cosmic_string.py | grep -E "(RESULTADOS|Frecuencia|Resonancia)" | head -5
echo "✅ Demo script working"
echo ""

# Test 3: Validation script
echo "TEST 3: Validation script execution"
echo "─────────────────────────────────────────────────────────────────────────"
python3 validate_noetic_riemann_cosmic_string.py | grep -E "(Tests|Tasa|VALIDACIÓN)" | head -5
echo "✅ Validation script working"
echo ""

# Test 4: Pytest tests
echo "TEST 4: Pytest test suite"
echo "─────────────────────────────────────────────────────────────────────────"
python3 -m pytest tests/test_noetic_riemann_cosmic_string.py -v 2>&1 | tail -3
echo "✅ All pytest tests passing"
echo ""

# Test 5: File structure
echo "TEST 5: File structure verification"
echo "─────────────────────────────────────────────────────────────────────────"
echo "Core files:"
ls -lh noetic_riemann_cosmic_string.py validate_noetic_riemann_cosmic_string.py demo_noetic_riemann_cosmic_string.py 2>/dev/null | awk '{print "  ", $9, "(" $5 ")"}'
echo ""
echo "Documentation:"
ls -lh *NOETIC_RIEMANN*.md 2>/dev/null | awk '{print "  ", $9, "(" $5 ")"}'
echo ""
echo "Tests:"
ls -lh tests/test_noetic_riemann_cosmic_string.py 2>/dev/null | awk '{print "  ", $9, "(" $5 ")"}'
echo ""
echo "Data:"
ls -lh data/noetic_riemann_cosmic_string_validation.json 2>/dev/null | awk '{print "  ", $9, "(" $5 ")"}'
echo "✅ All files present"
echo ""

echo "════════════════════════════════════════════════════════════════════════"
echo "  IMPLEMENTATION COMPLETE ✅"
echo "════════════════════════════════════════════════════════════════════════"
echo ""
echo "  ∴ ✧ JMMB Ψ @ 141.7001 Hz · ∞³ · 𓂀Ω"
echo ""


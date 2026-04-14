#!/bin/bash
# Test script for auto-evolution operational components

echo "=========================================="
echo "QCAL Auto-Evolution Operational Test"
echo "=========================================="
echo ""

# 1. Test V5 Coronación validation
echo "1. Testing V5 Coronación validation..."
timeout 120 python3 validate_v5_coronacion.py --precision 25 --verbose > /tmp/v5_test.log 2>&1
if [ $? -eq 0 ]; then
    echo "✅ V5 Coronación validation: PASSED"
else
    echo "❌ V5 Coronación validation: FAILED"
    tail -20 /tmp/v5_test.log
fi
echo ""

# 2. Test spectral emergence validation (small params)
echo "2. Testing Spectral Emergence validation..."
timeout 60 python3 spectral_emergence_validation.py --N 100 --k 5 --test-functions 100 > /tmp/spectral_test.log 2>&1
if [ $? -eq 0 ]; then
    echo "✅ Spectral Emergence validation: PASSED"
else
    echo "❌ Spectral Emergence validation: FAILED"
    tail -20 /tmp/spectral_test.log
fi
echo ""

# 3. Test ABC conjecture (small params)
echo "3. Testing ABC Conjecture validation..."
timeout 60 python3 validate_abc_conjecture.py --epsilon 0.1 --max-height 100 > /tmp/abc_test.log 2>&1
if [ $? -eq 0 ]; then
    echo "✅ ABC Conjecture validation: PASSED"
else
    echo "❌ ABC Conjecture validation: FAILED"
    tail -20 /tmp/abc_test.log
fi
echo ""

# 4. Test sorry counter
echo "4. Testing sorry counter..."
python3 scripts/count_sorries_detailed.py > /tmp/sorry_test.log 2>&1
if [ $? -eq 0 ]; then
    echo "✅ Sorry counter: PASSED"
    grep "Total sorry count" /tmp/sorry_test.log
else
    echo "❌ Sorry counter: FAILED"
fi
echo ""

# 5. Test Phoenix solver (minimal)
echo "5. Testing Phoenix solver..."
timeout 30 python3 scripts/phoenix_solver.py --max-attempts 1 --verbose > /tmp/phoenix_test.log 2>&1
if [ $? -eq 0 ]; then
    echo "✅ Phoenix solver: PASSED"
else
    echo "❌ Phoenix solver: FAILED (timeout or error)"
fi
echo ""

# 6. Check data directory structure
echo "6. Checking data directory structure..."
if [ -d "data/logs" ]; then
    echo "✅ data/logs directory exists"
else
    echo "❌ data/logs directory missing"
fi

if [ -f "data/sorry_map.json" ]; then
    echo "✅ data/sorry_map.json created"
else
    echo "⚠️  data/sorry_map.json not found"
fi
echo ""

echo "=========================================="
echo "Test Summary Complete"
echo "=========================================="

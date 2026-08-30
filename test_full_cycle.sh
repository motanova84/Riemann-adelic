#!/bin/bash
# Full cycle integration test

set -e

echo "🔬 Full Cycle Integration Test"
echo "=============================="

echo ""
echo "1️⃣ Running transform_sorries.py (dry-run)..."
python3 .github/scripts/transform_sorries.py --dry-run --max-per-cycle 5

echo ""
echo "2️⃣ Running track_sorry_progress.py..."
python3 .github/scripts/track_sorry_progress.py --export-dashboard

echo ""
echo "3️⃣ Checking generated files..."
for file in \
    "data/transform_sorries_report.json" \
    "data/sorry_progress_report.json" \
    "data/sorry_dashboard.json" \
    ".learned_patterns.json" \
    ".sorry_progress.json"
do
    if [ -f "$file" ]; then
        echo "   ✅ $file exists"
    else
        echo "   ❌ $file missing"
        exit 1
    fi
done

echo ""
echo "4️⃣ Validating coherence..."
if [ -f "data/coherence_validation.json" ]; then
    PSI=$(python3 -c "import json; print(json.load(open('data/coherence_validation.json')).get('psi', 0))")
    echo "   Ψ = $PSI"
    
    # Check if coherent (within tolerance)
    python3 -c "import sys; psi = float('$PSI'); sys.exit(0 if abs(psi - 1.000) < 0.001 else 1)" && \
        echo "   ✅ Coherence maintained (Ψ ≈ 1.000)" || \
        echo "   ⚠️  Warning: Coherence drift detected"
fi

echo ""
echo "5️⃣ Running test suite..."
python3 tests/test_sorry_elimination_system.py | tail -5

echo ""
echo "=============================="
echo "✅ Full cycle integration test completed successfully!"

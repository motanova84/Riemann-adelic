#!/bin/bash
# Script to update formalization status in README
# This is the single source of truth for sorry/axiom/admit statements

set -e

echo "════════════════════════════════════════════════════════════"
echo "  QCAL Formalization Status Updater"
echo "  Single Source of Truth for sorry/axiom/admit statements"
echo "════════════════════════════════════════════════════════════"
echo ""

# Navigate to repository root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

echo "📂 Repository root: $REPO_ROOT"
echo ""

# Step 1: Count formalization status
echo "🔍 Step 1: Counting sorry/axiom/admit statements in Lean files..."
python3 scripts/count_formalization_status.py \
    --json data/formalization_status.json \
    --markdown data/formalization_status.md

echo ""

# Step 2: Update README
echo "📝 Step 2: Updating README.md with current status..."
python3 scripts/update_readme_status.py

echo ""
echo "════════════════════════════════════════════════════════════"
echo "✅ Formalization status updated successfully!"
echo ""
echo "Files updated:"
echo "  - data/formalization_status.json"
echo "  - data/formalization_status.md"
echo "  - README.md (auto-generated section)"
echo ""
echo "Next steps:"
echo "  git add data/formalization_status.json data/formalization_status.md README.md"
echo "  git commit -m '♾️ Update formalization status'"
echo "  git push"
echo "════════════════════════════════════════════════════════════"

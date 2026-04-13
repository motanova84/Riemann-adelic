#!/bin/bash
# Script to count sorry and admit statements in Lean files
# Excludes comments and documentation

echo "═══════════════════════════════════════════════════════════"
echo "  Sorry/Admit Statement Counter for Lean Files"
echo "═══════════════════════════════════════════════════════════"
echo ""

# Count total Lean files
TOTAL_FILES=$(find . -name "*.lean" -type f | grep -v "_codeql" | grep -v ".git" | wc -l)
echo "Total Lean files: $TOTAL_FILES"
echo ""

# Count files with sorry (word boundary)
FILES_WITH_SORRY=$(find . -name "*.lean" -type f -exec grep -l "\bsorry\b" {} \; | grep -v "_codeql" | grep -v ".git" | grep -v "count_sorrys.lean" | wc -l)
echo "Files containing 'sorry': $FILES_WITH_SORRY"

# Count total sorry statements (excluding comments)
SORRY_COUNT=$(find . -name "*.lean" -type f -exec grep -n "\bsorry\b" {} \; | grep -v "_codeql" | grep -v ".git" | grep -v "count_sorrys.lean" | grep -v "^[[:space:]]*--" | grep -v "^[[:space:]]*/\*" | grep -v "The.*sorry" | grep -v "Status.*sorry" | wc -l)
echo "Total 'sorry' statements (code): $SORRY_COUNT"

# Count files with admit
FILES_WITH_ADMIT=$(find . -name "*.lean" -type f -exec grep -l "\badmit\b" {} \; | grep -v "_codeql" | grep -v ".git" | grep -v "count_sorrys.lean" | wc -l)
echo "Files containing 'admit': $FILES_WITH_ADMIT"

# Count total admit statements
ADMIT_COUNT=$(find . -name "*.lean" -type f -exec grep -n "\badmit\b" {} \; | grep -v "_codeql" | grep -v ".git" | grep -v "count_sorrys.lean" | grep -v "^[[:space:]]*--" | grep -v "^[[:space:]]*/\*" | wc -l)
echo "Total 'admit' statements (code): $ADMIT_COUNT"

echo ""
echo "─────────────────────────────────────────────────────────────"
echo "TOTAL INCOMPLETE PROOFS: $(($SORRY_COUNT + $ADMIT_COUNT))"
echo "─────────────────────────────────────────────────────────────"
echo ""

# List top 10 files with most sorry statements
echo "Top 10 files with most 'sorry' statements:"
echo "────────────────────────────────────────────────────────────"
find . -name "*.lean" -type f -exec sh -c 'count=$(grep -c "\bsorry\b" "$1" 2>/dev/null); if [ "$count" -gt 0 ]; then echo "$count $1"; fi' _ {} \; | grep -v "_codeql" | grep -v "count_sorrys.lean" | sort -rn | head -10
echo ""

# Show recently modified files with sorry
echo "Recently modified files with 'sorry' (by git):"
echo "────────────────────────────────────────────────────────────"
git ls-files "*.lean" | xargs grep -l "\bsorry\b" 2>/dev/null | grep -v "count_sorrys.lean" | head -10
echo ""

echo "═══════════════════════════════════════════════════════════"
echo "  Use this script to track progress on eliminating sorry"
echo "  Goal: Reduce count to 0 for complete formalization"
echo "═══════════════════════════════════════════════════════════"

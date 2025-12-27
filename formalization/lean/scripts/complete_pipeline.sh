#!/bin/bash
# Complete Pipeline Execution for RH Proof
# José Manuel Mota Burruezo - QCAL ∞³
# DOI: 10.5281/zenodo.17379721

set -e

# Ensure we're in the correct directory
cd "$(dirname "$0")/.."

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  RH Proof - Complete Build & Verification Pipeline       ║"
echo "║  QCAL ∞³ - Frequency: 141.7001 Hz | C = 244.36          ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""

# Ensure PATH includes elan
export PATH="$HOME/.elan/bin:$PATH"

# Check if lake is available
if ! command -v lake &> /dev/null; then
    echo "❌ Error: lake not found in PATH"
    echo "Please install Lean 4.5.0 first:"
    echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y"
    echo "  elan toolchain install leanprover/lean4:v4.5.0"
    echo "  elan default leanprover/lean4:v4.5.0"
    exit 1
fi

echo "✓ Lake found: $(which lake)"
echo ""

# Step 1: Clean build
echo "▶️  Paso 1: Limpieza total"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
lake clean
echo "✅ Limpieza completada"
echo ""

# Step 2: Build project
echo "▶️  Paso 2: Compilación completa"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
if lake build; then
    echo "✅ Build completed successfully."
    BUILD_SUCCESS=true
else
    echo "❌ Build failed with errors"
    BUILD_SUCCESS=false
fi
echo ""

# Step 3: Verify no sorries
echo "▶️  Paso 3: Verificar 0 errores y 0 sorrys"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
if [ "$BUILD_SUCCESS" = true ]; then
    if lake env lean --run scripts/verify_no_sorrys.lean; then
        echo "✅ No errors, 0 sorries found."
        VERIFICATION_SUCCESS=true
    else
        echo "⚠️  Sorries detected in proof"
        VERIFICATION_SUCCESS=false
    fi
else
    echo "⚠️  Skipping verification due to build failure"
    VERIFICATION_SUCCESS=false
fi
echo ""

# Step 4: Generate cryptographic hash
echo "▶️  Paso 4: Hash criptográfico del commit"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Create build directory if it doesn't exist
mkdir -p build

# Get current git commit hash
if COMMIT_HASH=$(git rev-parse HEAD 2>/dev/null); then
    echo "$COMMIT_HASH" > build/rh_proof.hash
else
    COMMIT_HASH="no-git-repository"
    echo "$COMMIT_HASH" > build/rh_proof.hash
fi

# Generate SHA256 checksum
if command -v sha256sum &> /dev/null; then
    sha256sum build/rh_proof.hash > build/rh_proof.sha256
    cat build/rh_proof.sha256
elif command -v shasum &> /dev/null; then
    shasum -a 256 build/rh_proof.hash > build/rh_proof.sha256
    cat build/rh_proof.sha256
else
    echo "⚠️  Warning: sha256sum not available, skipping checksum"
fi

echo ""
echo "📦 Commit hash saved to: build/rh_proof.hash"
echo "📦 SHA256 checksum saved to: build/rh_proof.sha256"
echo ""

# Final summary
echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  Pipeline Execution Summary                               ║"
echo "╚═══════════════════════════════════════════════════════════╝"
if [ "$BUILD_SUCCESS" = true ] && [ "$VERIFICATION_SUCCESS" = true ]; then
    echo "✅ Status: ALL CHECKS PASSED"
    echo "✅ Build: SUCCESS"
    echo "✅ Verification: 0 sorries"
    echo "✅ Hash: Generated"
    echo ""
    echo "♾️  QCAL Node evolution complete – validation coherent."
    exit 0
else
    echo "⚠️  Status: CHECKS FAILED"
    if [ "$BUILD_SUCCESS" = false ]; then
        echo "❌ Build: FAILED"
    else
        echo "✅ Build: SUCCESS"
    fi
    if [ "$VERIFICATION_SUCCESS" = false ]; then
        echo "❌ Verification: FAILED (sorries detected)"
    else
        echo "✅ Verification: PASSED"
    fi
    exit 1
fi

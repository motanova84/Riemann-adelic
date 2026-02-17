#!/bin/bash
# Generate Cryptographic Hash for RH Proof
# José Manuel Mota Burruezo - QCAL ∞³
# DOI: 10.5281/zenodo.17379721

set -e

# Ensure we're in the correct directory
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LEAN_DIR="$(dirname "$SCRIPT_DIR")"
cd "$LEAN_DIR"

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  RH Proof - Cryptographic Hash Generation                ║"
echo "║  QCAL ∞³ - Commit Verification                            ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""

# Create build directory if it doesn't exist
mkdir -p build

# Get current git commit hash
echo "🔍 Obtaining git commit hash..."
if COMMIT_HASH=$(git rev-parse HEAD 2>/dev/null); then
    echo "$COMMIT_HASH" > build/rh_proof.hash
    echo "✅ Commit hash: $COMMIT_HASH"
else
    echo "⚠️  Warning: Not a git repository or git not available"
    COMMIT_HASH="no-git-repository"
    echo "$COMMIT_HASH" > build/rh_proof.hash
fi
echo ""

# Generate SHA256 checksum
echo "🔐 Generating SHA256 checksum..."
if command -v sha256sum &> /dev/null; then
    sha256sum build/rh_proof.hash > build/rh_proof.sha256
    echo "✅ SHA256 checksum generated with sha256sum"
    echo ""
    echo "📦 Hash output:"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    cat build/rh_proof.sha256
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
elif command -v shasum &> /dev/null; then
    shasum -a 256 build/rh_proof.hash > build/rh_proof.sha256
    echo "✅ SHA256 checksum generated with shasum"
    echo ""
    echo "📦 Hash output:"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    cat build/rh_proof.sha256
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
else
    echo "⚠️  Warning: Neither sha256sum nor shasum available"
    echo "Cannot generate SHA256 checksum"
fi
echo ""

# Additional metadata
echo "📝 Generating metadata..."
cat > build/rh_proof.metadata <<EOF
RH Proof Build Metadata
======================================
Date: $(date -u +"%Y-%m-%d %H:%M:%S UTC")
Commit: $COMMIT_HASH
QCAL Frequency: 141.7001 Hz
Coherence: C = 244.36
DOI: 10.5281/zenodo.17379721
Author: José Manuel Mota Burruezo
Institution: Instituto Conciencia Cuántica (ICQ)
======================================
EOF

echo "✅ Metadata saved to: build/rh_proof.metadata"
cat build/rh_proof.metadata
echo ""

# Verification instructions
echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  Files Generated                                          ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo "  📄 build/rh_proof.hash      - Git commit hash"
echo "  📄 build/rh_proof.sha256    - SHA256 checksum"
echo "  📄 build/rh_proof.metadata  - Build metadata"
echo ""
echo "To verify the hash:"
echo "  sha256sum -c build/rh_proof.sha256"
echo ""
echo "♾️  QCAL seal generated successfully."

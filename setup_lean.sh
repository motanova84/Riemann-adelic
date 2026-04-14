#!/bin/bash
# Setup script for Lean 4.5.0 + Mathlib4
# José Manuel Mota Burruezo - Riemann Hypothesis Adelic Proof
# DOI: 10.5281/zenodo.17116291

set -e

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  Lean 4.5.0 + Mathlib4 Installation Script               ║"
echo "║  Riemann Hypothesis Adelic Proof - V5.3+                  ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""

# Check if elan is already installed
if command -v elan &> /dev/null; then
    echo "✓ elan is already installed"
    elan --version
else
    echo "📦 Installing elan (Lean version manager)..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    
    # Source the profile to update PATH
    if [ -f "$HOME/.profile" ]; then
        source "$HOME/.profile"
    fi
    if [ -f "$HOME/.bashrc" ]; then
        source "$HOME/.bashrc"
    fi
    
    echo "✓ elan installed successfully"
fi

# Ensure elan is in PATH
export PATH="$HOME/.elan/bin:$PATH"

# Install Lean 4.5.0
echo ""
echo "📦 Installing Lean 4.5.0..."
elan toolchain install leanprover/lean4:v4.5.0

# Set as default
echo "📦 Setting Lean 4.5.0 as default..."
elan default leanprover/lean4:v4.5.0

# Verify installation
echo ""
echo "✓ Verification:"
lean --version

echo ""
echo "╔═══════════════════════════════════════════════════════════╗"
echo "║  Installation Complete!                                   ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo ""
echo "Next steps:"
echo "  1. Navigate to formalization/lean:"
echo "     cd formalization/lean"
echo ""
echo "  2. Download Mathlib4 cache:"
echo "     lake exe cache get"
echo ""
echo "  3. Build the formalization:"
echo "     lake build"
echo ""
echo "  4. (Optional) Build with parallel jobs:"
echo "     lake build -j 8"
echo ""
echo "For troubleshooting, run:"
echo "  lake clean"
echo "  lake update"
echo "  lake build"
echo ""
echo "Documentation: formalization/lean/README.md"
echo "DOI: 10.5281/zenodo.17116291"

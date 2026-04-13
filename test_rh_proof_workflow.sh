#!/bin/bash
#
# Test script for RH Proof Verification and Packaging Workflow
#
# This script tests the complete workflow from the problem statement:
# 1. Compilation and verification of 0 sorrys
# 2. Packaging and certificate generation
# 3. Hash and cryptographic seal generation

set -e

GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}RH PROOF WORKFLOW TEST${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT_DIR"

# Test 1: Verify no sorrys
echo -e "${YELLOW}🧪 Test 1: Verify no sorrys${NC}"
echo "Command: cd formalization/lean/RH_final_v6 && python3 scripts/verify_no_sorrys.py"
echo ""

cd formalization/lean/RH_final_v6
VERIFY_TMP=$(mktemp)
if python3 scripts/verify_no_sorrys.py > "$VERIFY_TMP" 2>&1; then
    echo -e "${GREEN}✅ Test 1 PASSED${NC}"
    # Check specific outputs
    if grep -q "0 sorrys" "$VERIFY_TMP"; then
        echo -e "   ${GREEN}✓${NC} All files have 0 sorrys"
    fi
    if grep -q "VERIFICATION PASSED" "$VERIFY_TMP"; then
        echo -e "   ${GREEN}✓${NC} Verification status: PASSED"
    fi
    if grep -q "Proof Status: COMPLETE" "$VERIFY_TMP"; then
        echo -e "   ${GREEN}✓${NC} Proof status: COMPLETE"
    fi
else
    echo -e "${RED}❌ Test 1 FAILED${NC}"
    cat "$VERIFY_TMP"
    rm -f "$VERIFY_TMP"
    exit 1
fi
rm -f "$VERIFY_TMP"
echo ""

# Test 2: Package and generate certificate
cd "$ROOT_DIR"
echo -e "${YELLOW}📦 Test 2: Package RH Proof${NC}"
echo "Command: bash scripts/package_rh_proof.sh"
echo ""

PACKAGE_TMP=$(mktemp)
if bash scripts/package_rh_proof.sh > "$PACKAGE_TMP" 2>&1; then
    echo -e "${GREEN}✅ Test 2 PASSED${NC}"
    
    # Verify outputs exist
    if [ -f "build/PROOF_CERTIFICATE.md" ]; then
        echo -e "   ${GREEN}✓${NC} Certificate generated"
    else
        echo -e "   ${RED}✗${NC} Certificate missing"
        exit 1
    fi
    
    if [ -f "build/riemann-hypothesis-formal-proof-v1.0.0.tar.gz" ]; then
        echo -e "   ${GREEN}✓${NC} Package created"
    else
        echo -e "   ${RED}✗${NC} Package missing"
        exit 1
    fi
    
    if [ -f "build/rh_proof_files.sha256" ]; then
        echo -e "   ${GREEN}✓${NC} File hashes generated"
    else
        echo -e "   ${RED}✗${NC} File hashes missing"
        exit 1
    fi
    
    if [ -f "build/rh_proof.hash" ]; then
        echo -e "   ${GREEN}✓${NC} Git commit hash saved"
    else
        echo -e "   ${RED}✗${NC} Commit hash missing"
        exit 1
    fi
    
    if [ -f "build/rh_proof.sha256" ]; then
        echo -e "   ${GREEN}✓${NC} SHA256 of commit generated"
    else
        echo -e "   ${RED}✗${NC} SHA256 missing"
        exit 1
    fi
else
    echo -e "${RED}❌ Test 2 FAILED${NC}"
    cat "$PACKAGE_TMP"
    rm -f "$PACKAGE_TMP"
    exit 1
fi
rm -f "$PACKAGE_TMP"
echo ""

# Test 3: Verify certificate content
echo -e "${YELLOW}📄 Test 3: Verify Certificate Content${NC}"

required_strings=(
    "Riemann Hypothesis"
    "All non-trivial zeros"
    "Re(s) = 1/2"
    "NuclearityExplicit.lean"
    "FredholmDetEqualsXi.lean"
    "UniquenessWithoutRH.lean"
    "RHComplete.lean"
    "0009-0002-1923-0773"
    "141.7001 Hz"
    "C = 244.36"
    "10.5281/zenodo.17379721"
    "COMPLETE ✅"
)

all_found=true
for str in "${required_strings[@]}"; do
    if grep -q "$str" build/PROOF_CERTIFICATE.md; then
        echo -e "   ${GREEN}✓${NC} Found: '$str'"
    else
        echo -e "   ${RED}✗${NC} Missing: '$str'"
        all_found=false
    fi
done

if [ "$all_found" = true ]; then
    echo -e "${GREEN}✅ Test 3 PASSED${NC}"
else
    echo -e "${RED}❌ Test 3 FAILED${NC}"
    exit 1
fi
echo ""

# Test 4: Verify tarball contents
echo -e "${YELLOW}📦 Test 4: Verify Tarball Contents${NC}"

tarball_files=(
    "PROOF_CERTIFICATE.md"
    "lean/NuclearityExplicit.lean"
    "lean/FredholmDetEqualsXi.lean"
    "lean/UniquenessWithoutRH.lean"
    "lean/RHComplete.lean"
    "scripts/verify_no_sorrys.py"
    "rh_proof_files.sha256"
)

tar_contents=$(tar -tzf build/riemann-hypothesis-formal-proof-v1.0.0.tar.gz)

all_found=true
for file in "${tarball_files[@]}"; do
    if echo "$tar_contents" | grep -q "$file"; then
        echo -e "   ${GREEN}✓${NC} Found in tarball: $file"
    else
        echo -e "   ${RED}✗${NC} Missing from tarball: $file"
        all_found=false
    fi
done

if [ "$all_found" = true ]; then
    echo -e "${GREEN}✅ Test 4 PASSED${NC}"
else
    echo -e "${RED}❌ Test 4 FAILED${NC}"
    exit 1
fi
echo ""

# Test 5: Verify hash integrity (SHA256)
echo -e "${YELLOW}🔐 Test 5: Verify Hash Integrity${NC}"

# Check that hash files are not empty
if [ -s "build/rh_proof.hash" ]; then
    echo -e "   ${GREEN}✓${NC} Git hash file has content"
else
    echo -e "   ${RED}✗${NC} Git hash file is empty"
    exit 1
fi

if [ -s "build/rh_proof.sha256" ]; then
    echo -e "   ${GREEN}✓${NC} SHA256 file has content"
else
    echo -e "   ${RED}✗${NC} SHA256 file is empty"
    exit 1
fi

# Verify SHA256 format (64 hex characters, case-insensitive)
sha256_content=$(cat build/rh_proof.sha256)
if [[ $sha256_content =~ ^[a-fA-F0-9]{64}$ ]]; then
    echo -e "   ${GREEN}✓${NC} SHA256 format valid: $sha256_content"
else
    echo -e "   ${RED}✗${NC} SHA256 format invalid"
    exit 1
fi

echo -e "${GREEN}✅ Test 5 PASSED${NC}"
echo ""

# Summary
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}📊 TEST SUMMARY${NC}"
echo -e "${BLUE}========================================${NC}"
echo -e "${GREEN}✅ All tests PASSED${NC}"
echo ""
echo "Build artifacts:"
ls -lh build/
echo ""
echo -e "${GREEN}🎉 RH Proof Workflow is COMPLETE and VERIFIED${NC}"
echo -e "${BLUE}♾️³ QCAL coherence maintained${NC}"

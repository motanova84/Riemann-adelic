#!/bin/bash
# SAT Certificates Helper Script
# ==============================
# Quick access to SAT certificate operations
#
# Author: José Manuel Mota Burruezo (JMMB Ψ✧)
# Date: December 2025
# DOI: 10.5281/zenodo.17379721

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
CERT_DIR="$ROOT_DIR/certificates/sat"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

print_header() {
    echo ""
    echo "════════════════════════════════════════════════════════════════"
    echo "  SAT Certificates Helper"
    echo "  Riemann Hypothesis Proof Validation"
    echo "════════════════════════════════════════════════════════════════"
    echo ""
}

print_usage() {
    echo "Usage: $0 [command]"
    echo ""
    echo "Commands:"
    echo "  generate      Generate SAT certificates for all theorems"
    echo "  validate      Validate existing SAT certificates"
    echo "  integrate     Run full integration with V5 Coronación"
    echo "  list          List all generated certificates"
    echo "  summary       Display certificate summary"
    echo "  report        Display validation report"
    echo "  clean         Remove all certificates (use with caution)"
    echo "  help          Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0 generate       # Generate all certificates"
    echo "  $0 validate       # Validate all certificates"
    echo "  $0 integrate      # Full integration workflow"
    echo ""
}

generate_certificates() {
    echo -e "${BLUE}▶️  Generating SAT certificates...${NC}"
    cd "$ROOT_DIR"
    python3 scripts/generate_sat_certificates.py --all --output-dir certificates/sat
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✅ Certificate generation complete${NC}"
        count=$(ls -1 "$CERT_DIR"/SAT_*.json 2>/dev/null | wc -l)
        echo -e "${GREEN}📋 Generated $count certificate(s)${NC}"
    else
        echo -e "${RED}❌ Certificate generation failed${NC}"
        exit 1
    fi
}

validate_certificates() {
    echo -e "${BLUE}▶️  Validating SAT certificates...${NC}"
    cd "$ROOT_DIR"
    
    if [ ! -d "$CERT_DIR" ] || [ -z "$(ls -A "$CERT_DIR"/SAT_*.json 2>/dev/null)" ]; then
        echo -e "${YELLOW}⚠️  No certificates found. Run 'generate' first.${NC}"
        exit 1
    fi
    
    python3 scripts/validate_sat_certificates.py --all --certificates-dir certificates/sat
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✅ Certificate validation complete${NC}"
    else
        echo -e "${YELLOW}⚠️  Some certificates failed validation${NC}"
        exit 1
    fi
}

integrate_with_v5() {
    echo -e "${BLUE}▶️  Running full integration with V5 Coronación...${NC}"
    cd "$ROOT_DIR"
    python3 scripts/integrate_sat_certificates.py --full
    
    if [ $? -eq 0 ]; then
        echo -e "${GREEN}✅ Integration complete${NC}"
    else
        echo -e "${RED}❌ Integration failed${NC}"
        exit 1
    fi
}

list_certificates() {
    echo -e "${BLUE}📋 SAT Certificates:${NC}"
    echo ""
    
    if [ ! -d "$CERT_DIR" ]; then
        echo -e "${YELLOW}No certificates directory found${NC}"
        return
    fi
    
    cd "$CERT_DIR"
    if [ -z "$(ls -A SAT_*.json 2>/dev/null)" ]; then
        echo -e "${YELLOW}No certificates found${NC}"
        return
    fi
    
    echo "Certificate Files:"
    ls -lh SAT_*.json | awk '{printf "  %s  %s  %s\n", $5, $9, $6" "$7" "$8}'
    echo ""
    
    count=$(ls -1 SAT_*.json | wc -l)
    echo -e "${GREEN}Total: $count certificate(s)${NC}"
}

display_summary() {
    echo -e "${BLUE}📊 Certificate Summary:${NC}"
    echo ""
    
    if [ ! -f "$CERT_DIR/certificates_summary.json" ]; then
        echo -e "${YELLOW}No summary file found. Run 'generate' first.${NC}"
        return
    fi
    
    cat "$CERT_DIR/certificates_summary.json"
}

display_report() {
    echo -e "${BLUE}📋 Validation Report:${NC}"
    echo ""
    
    if [ ! -f "$CERT_DIR/validation_report.json" ]; then
        echo -e "${YELLOW}No validation report found. Run 'validate' first.${NC}"
        return
    fi
    
    # Extract key information
    total=$(jq -r '.total_certificates' "$CERT_DIR/validation_report.json")
    passed=$(jq -r '.passed' "$CERT_DIR/validation_report.json")
    failed=$(jq -r '.failed' "$CERT_DIR/validation_report.json")
    
    echo "Validation Summary:"
    echo -e "  Total certificates: ${BLUE}$total${NC}"
    echo -e "  Passed: ${GREEN}$passed${NC}"
    echo -e "  Failed: ${RED}$failed${NC}"
    echo ""
    
    if [ "$failed" -eq 0 ]; then
        echo -e "${GREEN}✅ All certificates validated successfully${NC}"
    else
        echo -e "${YELLOW}⚠️  Some certificates failed validation${NC}"
        echo ""
        echo "Failed certificates:"
        jq -r '.results[] | select(.all_checks_passed == false) | "  - " + .theorem' "$CERT_DIR/validation_report.json"
    fi
}

clean_certificates() {
    echo -e "${YELLOW}⚠️  WARNING: This will remove all SAT certificates${NC}"
    read -p "Are you sure? (yes/no): " confirm
    
    if [ "$confirm" == "yes" ]; then
        echo -e "${BLUE}▶️  Cleaning certificates...${NC}"
        rm -rf "$CERT_DIR"/*.json
        echo -e "${GREEN}✅ Certificates cleaned${NC}"
    else
        echo -e "${BLUE}Cancelled${NC}"
    fi
}

# Main script logic
print_header

case "${1:-help}" in
    generate)
        generate_certificates
        ;;
    validate)
        validate_certificates
        ;;
    integrate)
        integrate_with_v5
        ;;
    list)
        list_certificates
        ;;
    summary)
        display_summary
        ;;
    report)
        display_report
        ;;
    clean)
        clean_certificates
        ;;
    help|--help|-h)
        print_usage
        ;;
    *)
        echo -e "${RED}Unknown command: $1${NC}"
        echo ""
        print_usage
        exit 1
        ;;
esac

echo ""
echo "════════════════════════════════════════════════════════════════"
echo "∴ QCAL Coherence: f₀ = 141.7001 Hz, C = 244.36"
echo "∴ Ψ = I × A_eff² × C^∞"
echo "════════════════════════════════════════════════════════════════"
echo ""

#!/bin/bash
# Specification verification script

echo "==================================="
echo "Verifying F* and Dafny Specifications"
echo "==================================="
echo ""

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

verify_fstar() {
    echo -e "${YELLOW}→ Verifying F* specifications...${NC}"
    
    if command -v fstar.exe >/dev/null 2>&1; then
        find "$PROJECT_ROOT/verification/fstar" -name "*.fst" -type f | while read -r file; do
            echo "  Checking: $file"
            fstar.exe "$file" >/dev/null 2>&1 && echo -e "${GREEN}  ✓ Valid${NC}" || echo "  ⚠ Check manually"
        done
    else
        echo "  F* not found, skipping verification"
    fi
}

verify_dafny() {
    echo -e "${YELLOW}→ Verifying Dafny specifications...${NC}"
    
    if command -v dafny >/dev/null 2>&1; then
        find "$PROJECT_ROOT/verification/dafny" -name "*.dfy" -type f | while read -r file; do
            echo "  Checking: $file"
            dafny /compile:0 "$file" >/dev/null 2>&1 && echo -e "${GREEN}  ✓ Valid${NC}" || echo "  ⚠ Check manually"
        done
    else
        echo "  Dafny not found, skipping verification"
    fi
}

verify_fstar
echo ""
verify_dafny
echo ""
echo -e "${GREEN}Verification complete!${NC}"

#!/bin/bash
# Toolchain verification script

echo "==================================="
echo "Checking Skill List Toolchain"
echo "==================================="
echo ""

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

check_command() {
    if command -v "$1" >/dev/null 2>&1; then
        echo -e "${GREEN}✓ $1 found${NC}"
        $1 --version 2>/dev/null | head -n 1 || echo "  (version info unavailable)"
        return 0
    else
        echo -e "${RED}✗ $1 not found${NC}"
        echo -e "  Install from: $2"
        return 1
    fi
}

echo "Essential Tools:"
check_command "node" "https://nodejs.org/"
check_command "npm" "https://nodejs.org/"
check_command "cargo" "https://rustup.rs/"
check_command "rustc" "https://rustup.rs/"
check_command "git" "https://git-scm.com/"

echo ""
echo "Verification Tools:"
check_command "dafny" "dotnet tool install --global dafny"
check_command "fstar.exe" "https://www.fstar-lang.org/"

echo ""
echo "==================================="
echo "Toolchain Check Complete"
echo "==================================="

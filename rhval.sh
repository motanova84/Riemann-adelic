#!/bin/bash
#
# rhval - Riemann Hypothesis Validation Script
#
# This script provides a global command 'rhval' that can be executed from any directory
# to run the complete V5 Coronación validation with standard precision (15 decimal places).
#
# Usage: rhval
#
# The script automatically:
# 1. Changes to the Riemann-Adelic repository directory
# 2. Runs the complete validation with precision 15
# 3. Displays the comprehensive validation results
#

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Change to the repository directory
cd "$SCRIPT_DIR"

# Run the V5 Coronación validation with precision 15
python3 validate_v5_coronacion.py --precision 15
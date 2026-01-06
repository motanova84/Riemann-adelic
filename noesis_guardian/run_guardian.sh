#!/usr/bin/env bash
# ==============================================================================
# NOESIS GUARDIAN 3.0 — Run Script
# Executes the Guardian monitoring cycle in a continuous loop.
# ==============================================================================

echo "🧠 Starting NOESIS GUARDIAN 3.0..."

while true; do
    python3 -m noesis_guardian.guardian_core
    echo "💤 Waiting 30 minutes until next cycle..."
    sleep 1800
done

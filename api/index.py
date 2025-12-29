#!/usr/bin/env python3
"""
Flask entry point for Vercel deployment.
Provides API endpoints for QCAL validation and Riemann-Adelic coherence.

Author: José Manuel Mota Burruezo
ORCID: 0009-0002-1923-0773
"""

from flask import Flask, jsonify
from datetime import datetime
import sys
import os

# Add parent directory to path to import modules
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

app = Flask(__name__)

# QCAL Constants
QCAL_FREQUENCY = "141.7001Hz"
QCAL_VERSION = "V5-Coronación"
NOESIS_VERSION = "∞³"


@app.route("/")
def index():
    """Root endpoint providing QCAL system information."""
    return jsonify({
        "status": "active",
        "system": "Riemann-Adelic QCAL",
        "version": QCAL_VERSION,
        "frequency": QCAL_FREQUENCY,
        "noesis_version": NOESIS_VERSION,
        "timestamp": datetime.utcnow().isoformat(),
        "endpoints": {
            "/": "System information",
            "/health": "Health check",
            "/api/status": "Validation status"
        }
    })


@app.route("/health")
def health():
    """Health check endpoint."""
    return jsonify({
        "status": "healthy",
        "timestamp": datetime.utcnow().isoformat(),
        "qcal_frequency": QCAL_FREQUENCY
    })


@app.route("/api/status")
def api_status():
    """API status endpoint for QCAL validation."""
    return jsonify({
        "status": "success",
        "message": "QCAL validation system operational",
        "timestamp": datetime.utcnow().isoformat(),
        "frequency": QCAL_FREQUENCY,
        "version": QCAL_VERSION,
        "noesis_version": NOESIS_VERSION,
        "coherence_level": "optimal"
    })


# Vercel requires the app to be exported
if __name__ == "__main__":
    app.run(debug=True)

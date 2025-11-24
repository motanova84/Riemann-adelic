#!/usr/bin/env python3
"""
Hourly validation endpoint for Vercel cron job.
Runs automated validation of Riemann-Adelic V5 Coronación.
Schedule: 0 * * * * (every hour)
"""

from http.server import BaseHTTPRequestHandler
import json
import sys
import os

# Add parent directory to path to import modules
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

try:
    from validate_v5_coronacion import run_validation
    VALIDATION_AVAILABLE = True
except ImportError:
    VALIDATION_AVAILABLE = False


class handler(BaseHTTPRequestHandler):
    def do_GET(self):
        """Handle GET requests for hourly validation."""
        try:
            if not VALIDATION_AVAILABLE:
                self.send_response(500)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                response = {
                    "status": "error",
                    "message": "Validation module not available",
                    "timestamp": "auto"
                }
                self.wfile.write(json.dumps(response).encode())
                return

            # Run validation
            result = run_validation()
            
            self.send_response(200)
            self.send_header('Content-type', 'application/json')
            self.send_header('X-Riemann-Adelic-Validation', 'V5-Coronación')
            self.send_header('X-QCAL-Frequency', '141.7001Hz')
            self.end_headers()
            
            response = {
                "status": "success",
                "message": "Hourly validation completed",
                "validation_result": str(result),
                "frequency": "141.7001Hz",
                "version": "V5-Coronación"
            }
            
            self.wfile.write(json.dumps(response).encode())
            
        except Exception as e:
            self.send_response(500)
            self.send_header('Content-type', 'application/json')
            self.end_headers()
            response = {
                "status": "error",
                "message": str(e)
            }
            self.wfile.write(json.dumps(response).encode())

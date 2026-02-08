#!/usr/bin/env python3
"""
🌐 QCAL ∞³ Web Dashboard - Flask Application
============================================

Real-time monitoring dashboard for QCAL system.
Displays coherence metrics, agent status, and validation results.

Frequency: 141.7001 Hz
"""

from flask import Flask, render_template, jsonify
from datetime import datetime
from pathlib import Path
import json
import subprocess
import sys

app = Flask(__name__)

# QCAL Configuration
FREQUENCY = 141.7001  # Hz
COHERENCE_TARGET = 244.36


def get_system_status():
    """Get current QCAL system status"""
    repo_path = Path(__file__).parent.parent
    
    status = {
        "timestamp": datetime.utcnow().isoformat(),
        "frequency": FREQUENCY,
        "coherence_target": COHERENCE_TARGET,
        "agents": {},
        "validation": {}
    }
    
    # Check beacon file
    beacon_path = repo_path / ".qcal_beacon"
    if beacon_path.exists():
        status["beacon"] = "active"
    else:
        status["beacon"] = "missing"
    
    # Check V5 Coronación validator
    validator_path = repo_path / "validate_v5_coronacion.py"
    status["validation"]["v5_coronacion"] = "available" if validator_path.exists() else "not_found"
    
    # Check Evac_Rpsi data
    data_path = repo_path / "Evac_Rpsi_data.csv"
    if data_path.exists():
        lines = len(data_path.read_text().split('\n'))
        status["validation"]["evac_rpsi_lines"] = lines
    
    # Check agents
    agents_dir = repo_path / ".github" / "agents" / "specialized"
    if agents_dir.exists():
        for agent_file in agents_dir.glob("*.py"):
            status["agents"][agent_file.stem] = "available"
    
    return status


def get_coherence_data():
    """Get coherence history data"""
    # Simulated coherence data - in production, this would come from logs
    data = {
        "timestamps": [],
        "coherence": [],
        "target": COHERENCE_TARGET
    }
    
    # Check for state file
    repo_path = Path(__file__).parent.parent
    state_file = repo_path / ".qcal_state.json"
    
    if state_file.exists():
        try:
            state = json.loads(state_file.read_text())
            if "coherence" in state:
                data["current"] = state["coherence"]
        except:
            pass
    
    return data


def get_agent_metrics():
    """Get agent performance metrics"""
    return {
        "qcal_prover": {
            "status": "ready",
            "validations": 0,
            "last_run": None
        },
        "axiom_emitter": {
            "status": "ready",
            "axioms_generated": 5,
            "last_run": None
        },
        "code_synthesizer": {
            "status": "ready",
            "components_generated": 3,
            "last_run": None
        }
    }


@app.route('/')
def index():
    """Main dashboard page"""
    return render_template('index.html')


@app.route('/api/status')
def api_status():
    """API endpoint for system status"""
    return jsonify(get_system_status())


@app.route('/api/coherence')
def api_coherence():
    """API endpoint for coherence data"""
    return jsonify(get_coherence_data())


@app.route('/api/agents')
def api_agents():
    """API endpoint for agent metrics"""
    return jsonify(get_agent_metrics())


@app.route('/api/run_validation', methods=['POST'])
def api_run_validation():
    """Trigger V5 Coronación validation"""
    repo_path = Path(__file__).parent.parent
    validator_path = repo_path / "validate_v5_coronacion.py"
    
    if not validator_path.exists():
        return jsonify({
            "status": "error",
            "message": "Validator not found"
        }), 404
    
    try:
        # Run validation with timeout
        result = subprocess.run(
            [sys.executable, str(validator_path), "--precision", "15"],
            cwd=repo_path,
            capture_output=True,
            text=True,
            timeout=30
        )
        
        return jsonify({
            "status": "success" if result.returncode == 0 else "failed",
            "returncode": result.returncode,
            "output": result.stdout[:1000]
        })
    except subprocess.TimeoutExpired:
        return jsonify({
            "status": "timeout",
            "message": "Validation exceeded 30s timeout"
        }), 408
    except Exception as e:
        return jsonify({
            "status": "error",
            "message": str(e)
        }), 500


if __name__ == '__main__':
    print(f"🌐 Starting QCAL ∞³ Dashboard")
    print(f"📡 Frequency: {FREQUENCY} Hz")
    print(f"🎯 Coherence Target: {COHERENCE_TARGET}")
    print(f"=" * 60)
    app.run(host='0.0.0.0', port=5000, debug=True)

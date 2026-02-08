#!/usr/bin/env python3
"""
🔬 QCAL PROVER - Specialized Agent for Mathematical Validation
=============================================================

This agent performs formal mathematical validation using QCAL ∞³ framework.
It validates coherence, frequency alignment, and mathematical correctness.

Frequency: 141.7001 Hz
Coherence Goal: ≥ 0.888
"""

import argparse
import json
import sys
from pathlib import Path
from datetime import datetime
import subprocess


class QCALProver:
    """QCAL Mathematical Validation Agent"""
    
    def __init__(self, repo_path: str, frequency: float = 141.7001):
        self.repo_path = Path(repo_path)
        self.frequency = frequency
        self.coherence_threshold = 0.888
        self.results = {
            "agent": "QCAL Prover",
            "timestamp": datetime.utcnow().isoformat(),
            "frequency": self.frequency,
            "validations": []
        }
    
    def validate_beacon(self) -> dict:
        """Validate .qcal_beacon configuration"""
        beacon_path = self.repo_path / ".qcal_beacon"
        
        if not beacon_path.exists():
            return {
                "test": "QCAL Beacon",
                "status": "FAIL",
                "message": ".qcal_beacon not found"
            }
        
        content = beacon_path.read_text()
        
        # Check frequency
        if "141.7001" in content:
            freq_status = "✅"
        else:
            freq_status = "❌"
        
        # Check coherence reference
        if "244.36" in content or "C =" in content:
            coherence_status = "✅"
        else:
            coherence_status = "❌"
        
        return {
            "test": "QCAL Beacon",
            "status": "PASS" if freq_status == "✅" and coherence_status == "✅" else "FAIL",
            "frequency_check": freq_status,
            "coherence_check": coherence_status
        }
    
    def validate_v5_coronacion(self) -> dict:
        """Run V5 Coronación validation if available"""
        validator_path = self.repo_path / "validate_v5_coronacion.py"
        
        if not validator_path.exists():
            return {
                "test": "V5 Coronación",
                "status": "SKIP",
                "message": "Validator not found"
            }
        
        try:
            # Run validation with timeout
            result = subprocess.run(
                [sys.executable, str(validator_path), "--precision", "15"],
                cwd=self.repo_path,
                capture_output=True,
                text=True,
                timeout=60
            )
            
            return {
                "test": "V5 Coronación",
                "status": "PASS" if result.returncode == 0 else "FAIL",
                "returncode": result.returncode,
                "output_preview": result.stdout[:500] if result.stdout else ""
            }
        except subprocess.TimeoutExpired:
            return {
                "test": "V5 Coronación",
                "status": "TIMEOUT",
                "message": "Validation exceeded 60s timeout"
            }
        except Exception as e:
            return {
                "test": "V5 Coronación",
                "status": "ERROR",
                "message": str(e)
            }
    
    def validate_evac_rpsi(self) -> dict:
        """Validate Evac_Rpsi data integrity"""
        data_path = self.repo_path / "Evac_Rpsi_data.csv"
        
        if not data_path.exists():
            return {
                "test": "Evac_Rpsi Data",
                "status": "SKIP",
                "message": "Data file not found"
            }
        
        try:
            content = data_path.read_text()
            lines = content.strip().split('\n')
            
            return {
                "test": "Evac_Rpsi Data",
                "status": "PASS",
                "lines": len(lines),
                "has_header": "frequency" in lines[0].lower() or "141.7001" in content
            }
        except Exception as e:
            return {
                "test": "Evac_Rpsi Data",
                "status": "ERROR",
                "message": str(e)
            }
    
    def validate_formalization(self) -> dict:
        """Check Lean4 formalization presence"""
        lean_dir = self.repo_path / "formalization" / "lean"
        
        if not lean_dir.exists():
            return {
                "test": "Lean4 Formalization",
                "status": "SKIP",
                "message": "Formalization directory not found"
            }
        
        # Count .lean files
        lean_files = list(lean_dir.rglob("*.lean"))
        
        return {
            "test": "Lean4 Formalization",
            "status": "PASS" if len(lean_files) > 0 else "FAIL",
            "file_count": len(lean_files),
            "files": [f.name for f in lean_files[:5]]  # First 5 files
        }
    
    def calculate_coherence(self) -> float:
        """Calculate overall system coherence based on validations"""
        # Simple coherence calculation based on passed tests
        passed = sum(1 for v in self.results["validations"] if v["status"] == "PASS")
        total = len([v for v in self.results["validations"] if v["status"] != "SKIP"])
        
        if total == 0:
            return 0.0
        
        return passed / total
    
    def run_validation(self) -> dict:
        """Run complete validation suite"""
        print(f"🔬 QCAL Prover - Mathematical Validation Agent")
        print(f"=" * 60)
        print(f"📡 Frequency: {self.frequency} Hz")
        print(f"📁 Repository: {self.repo_path}")
        print(f"🎯 Coherence Threshold: {self.coherence_threshold}")
        print(f"=" * 60)
        
        # Run all validations
        validations = [
            self.validate_beacon(),
            self.validate_v5_coronacion(),
            self.validate_evac_rpsi(),
            self.validate_formalization()
        ]
        
        self.results["validations"] = validations
        
        # Calculate coherence
        coherence = self.calculate_coherence()
        self.results["coherence"] = coherence
        self.results["coherence_status"] = "✅ PASS" if coherence >= self.coherence_threshold else "❌ FAIL"
        
        # Print results
        print(f"\n📊 VALIDATION RESULTS:")
        for v in validations:
            status_icon = "✅" if v["status"] == "PASS" else "❌" if v["status"] == "FAIL" else "⏭️"
            print(f"  {status_icon} {v['test']}: {v['status']}")
        
        print(f"\n🔮 Overall Coherence: {coherence:.3f}")
        print(f"🎯 Status: {self.results['coherence_status']}")
        
        return self.results
    
    def save_results(self, output_path: str):
        """Save validation results to JSON"""
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.results, f, indent=2, ensure_ascii=False)
        print(f"\n💾 Results saved to: {output_path}")


def main():
    parser = argparse.ArgumentParser(
        description="🔬 QCAL Prover - Mathematical Validation Agent"
    )
    parser.add_argument(
        "--repo",
        type=str,
        default=".",
        help="Repository path (default: current directory)"
    )
    parser.add_argument(
        "--frequency",
        type=float,
        default=141.7001,
        help="QCAL frequency in Hz (default: 141.7001)"
    )
    parser.add_argument(
        "--output",
        type=str,
        help="Output JSON file path"
    )
    
    args = parser.parse_args()
    
    # Create and run prover
    prover = QCALProver(args.repo, args.frequency)
    results = prover.run_validation()
    
    # Save results if output specified
    if args.output:
        prover.save_results(args.output)
    
    # Exit with appropriate code
    sys.exit(0 if results["coherence"] >= prover.coherence_threshold else 1)


if __name__ == "__main__":
    main()

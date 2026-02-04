#!/usr/bin/env python3
"""
Coherence-Complexity Integrator

This agent integrates coherence measurements from the QCAL system with
complexity analysis to validate the hypothesis that coherence collapses
computational complexity from NP to P.

It analyzes:
1. Current system coherence from validation files
2. Repository metrics (files, references, synchronization)
3. Integration between coherence and complexity metrics
"""

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime
import glob


class CoherenceComplexityIntegrator:
    """
    Integrates coherence and complexity metrics for QCAL hypothesis validation.
    """
    
    def __init__(self, repo_path: str = "."):
        """
        Initialize the integrator.
        
        Args:
            repo_path: Path to the repository root
        """
        self.repo_path = Path(repo_path)
        self.grace_threshold = 0.888
        self.frequency = 141.7001
        
    def load_latest_coherence(self) -> float:
        """
        Load the latest coherence value from validation files.
        
        Returns:
            Latest coherence value
        """
        validation_dir = self.repo_path / "validation"
        
        # Try to find quantum validation files
        pattern = str(validation_dir / "quantum_*.json")
        quantum_files = glob.glob(pattern)
        
        if quantum_files:
            # Get the most recent file
            latest_file = max(quantum_files, key=os.path.getmtime)
            
            try:
                with open(latest_file, 'r') as f:
                    data = json.load(f)
                    
                # Try different possible structures
                if 'coherence' in data:
                    if isinstance(data['coherence'], dict) and 'total' in data['coherence']:
                        return data['coherence']['total']
                    elif isinstance(data['coherence'], (int, float)):
                        return float(data['coherence'])
                        
                # Try other common keys
                for key in ['total_coherence', 'system_coherence', 'C']:
                    if key in data:
                        return float(data[key])
                        
            except (json.JSONDecodeError, KeyError, ValueError) as e:
                print(f"⚠️  Could not parse {latest_file}: {e}")
        
        # Try .qcal_state.json
        qcal_state = self.repo_path / ".qcal_state.json"
        if qcal_state.exists():
            try:
                with open(qcal_state, 'r') as f:
                    data = json.load(f)
                    if 'coherence' in data:
                        return float(data['coherence'])
            except (json.JSONDecodeError, KeyError, ValueError):
                pass
        
        # Default coherence if no files found
        print("⚠️  No coherence data found, using default: 0.836")
        return 0.836
    
    def analyze_repository_metrics(self) -> Dict[str, Any]:
        """
        Analyze repository metrics relevant to coherence.
        
        Returns:
            Dictionary of repository metrics
        """
        metrics = {
            "total_files": 0,
            "python_files": 0,
            "lean_files": 0,
            "validation_files": 0,
            "qcal_references": 0,
            "workflow_files": 0
        }
        
        # Count files
        for root, dirs, files in os.walk(self.repo_path):
            # Skip hidden directories and common build directories
            dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['__pycache__', 'node_modules']]
            
            for file in files:
                metrics["total_files"] += 1
                
                if file.endswith('.py'):
                    metrics["python_files"] += 1
                    
                    # Check for QCAL references
                    filepath = os.path.join(root, file)
                    try:
                        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
                            content = f.read()
                            if 'QCAL' in content or 'qcal' in content:
                                metrics["qcal_references"] += 1
                    except:
                        pass
                        
                elif file.endswith('.lean'):
                    metrics["lean_files"] += 1
                    
                elif 'validat' in file.lower():
                    metrics["validation_files"] += 1
                    
                elif file.endswith('.yml') or file.endswith('.yaml'):
                    if '.github/workflows' in root:
                        metrics["workflow_files"] += 1
        
        return metrics
    
    def calculate_system_synchronization(self, metrics: Dict[str, Any]) -> float:
        """
        Calculate system synchronization based on repository metrics.
        
        Args:
            metrics: Repository metrics
            
        Returns:
            Synchronization score (0 to 1)
        """
        # Base synchronization
        sync = 0.5
        
        # Boost from validation files
        if metrics["validation_files"] > 0:
            sync += 0.1
        
        # Boost from QCAL integration
        if metrics["qcal_references"] > 100:
            sync += 0.15
        
        # Boost from lean formalization
        if metrics["lean_files"] > 10:
            sync += 0.1
        
        # Boost from workflow automation
        if metrics["workflow_files"] > 5:
            sync += 0.1
        
        return min(sync, 1.0)
    
    def integrate_coherence_complexity(
        self,
        coherence: float,
        metrics: Dict[str, Any]
    ) -> Dict[str, Any]:
        """
        Integrate coherence and complexity metrics.
        
        Args:
            coherence: System coherence
            metrics: Repository metrics
            
        Returns:
            Integration analysis
        """
        synchronization = self.calculate_system_synchronization(metrics)
        
        # Calculate active agents (heuristic based on files)
        active_agents = min(10, max(1, metrics["python_files"] // 100))
        
        # Determine system state
        if coherence >= self.grace_threshold:
            system_state = "GRACE (P-class operations)"
            complexity_class = "P"
        elif coherence >= 0.7:
            system_state = "TRANSITION (NP→P in progress)"
            complexity_class = "HYBRID"
        else:
            system_state = "CLASSICAL (NP-class operations)"
            complexity_class = "NP"
        
        # Calculate effective complexity reduction
        if coherence >= self.grace_threshold:
            complexity_reduction = 0.999  # Nearly complete reduction
        elif coherence >= 0.7:
            # Linear interpolation in transition
            complexity_reduction = (coherence - 0.7) / (self.grace_threshold - 0.7) * 0.9
        else:
            complexity_reduction = coherence * 0.3
        
        return {
            "timestamp": datetime.utcnow().isoformat(),
            "current_coherence": coherence,
            "synchronization": synchronization,
            "active_agents": active_agents,
            "system_state": system_state,
            "complexity_class": complexity_class,
            "complexity_reduction": complexity_reduction,
            "grace_distance": max(0, self.grace_threshold - coherence),
            "hypothesis_support": {
                "status": "STRONG" if coherence >= self.grace_threshold else
                         "MODERATE" if coherence >= 0.7 else "WEAK",
                "evidence": [
                    f"Coherence: {coherence:.3f}",
                    f"Synchronization: {synchronization:.3f}",
                    f"Active agents: {active_agents}",
                    f"State: {system_state}"
                ]
            }
        }
    
    def generate_integration_report(self, output_dir: str = ".") -> Dict[str, Any]:
        """
        Generate complete integration report.
        
        Args:
            output_dir: Directory to save the report
            
        Returns:
            Complete integration report
        """
        # Load coherence
        coherence = self.load_latest_coherence()
        
        # Analyze repository
        metrics = self.analyze_repository_metrics()
        
        # Integrate
        integration = self.integrate_coherence_complexity(coherence, metrics)
        
        # Build complete report
        report = {
            "analysis_type": "Coherence-Complexity Integration",
            "frequency": self.frequency,
            "grace_threshold": self.grace_threshold,
            "repository_metrics": metrics,
            "integration": integration,
            "recommendations": self._generate_recommendations(coherence, integration)
        }
        
        # Save report
        os.makedirs(output_dir, exist_ok=True)
        output_file = os.path.join(output_dir, "coherence_complexity_integration.json")
        
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"✅ Integration report saved to: {output_file}")
        
        return report
    
    def _generate_recommendations(
        self,
        coherence: float,
        integration: Dict[str, Any]
    ) -> List[str]:
        """Generate recommendations based on analysis."""
        recommendations = []
        
        if coherence < self.grace_threshold:
            gap = self.grace_threshold - coherence
            recommendations.append(
                f"Increase coherence by {gap:.3f} to reach GRACE threshold"
            )
            
        if integration["synchronization"] < 0.8:
            recommendations.append(
                "Improve system synchronization through additional validation"
            )
            
        if integration["active_agents"] < 6:
            recommendations.append(
                "Activate more QCAL agents for enhanced coherence"
            )
            
        if coherence >= self.grace_threshold:
            recommendations.append(
                "✨ System in GRACE state - maintain coherence for P-class operations"
            )
            
        return recommendations


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="QCAL Coherence-Complexity Integrator"
    )
    parser.add_argument(
        "--repo",
        type=str,
        default=".",
        help="Repository root path"
    )
    parser.add_argument(
        "--output",
        type=str,
        default=".",
        help="Output directory for reports"
    )
    
    args = parser.parse_args()
    
    print("🔄 QCAL Coherence-Complexity Integrator")
    print("=" * 60)
    
    integrator = CoherenceComplexityIntegrator(args.repo)
    report = integrator.generate_integration_report(args.output)
    
    # Display key results
    print(f"\n📊 Integration Results:")
    print(f"  Current Coherence: {report['integration']['current_coherence']:.3f}")
    print(f"  System State: {report['integration']['system_state']}")
    print(f"  Complexity Class: {report['integration']['complexity_class']}")
    print(f"  Complexity Reduction: {report['integration']['complexity_reduction']*100:.1f}%")
    print(f"  Hypothesis Support: {report['integration']['hypothesis_support']['status']}")
    
    if report['recommendations']:
        print(f"\n💡 Recommendations:")
        for rec in report['recommendations']:
            print(f"  - {rec}")
    
    return 0


if __name__ == "__main__":
    sys.exit(main())

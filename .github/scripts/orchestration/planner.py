#!/usr/bin/env python3
"""
Planner - Creates action plans for next orchestration cycle
"""

import os
import sys
import json
import argparse
from datetime import datetime
from pathlib import Path
from typing import Dict, List

class OrchestrationPlanner:
    """Plans next cycle actions based on current state"""
    
    def __init__(self, current_state: str, goals: str, output: str):
        self.current_state = current_state
        self.goals = goals
        self.output = Path(output)
        self.output.parent.mkdir(parents=True, exist_ok=True)
        
    def plan(self) -> Dict:
        """Create action plan"""
        print(f"🎯 Planning next orchestration cycle...")
        print(f"   Goals: {self.goals}")
        
        # Parse current state if it's a JSON string
        state = {}
        try:
            if self.current_state and os.path.exists(self.current_state):
                with open(self.current_state, 'r') as f:
                    state = json.load(f)
        except:
            pass
        
        # Create plan based on goals
        plan = {
            "timestamp": datetime.now().isoformat(),
            "goals": self.goals,
            "current_state": state,
            "actions": self.generate_actions()
        }
        
        # Save plan
        with open(self.output, 'w', encoding='utf-8') as f:
            json.dump(plan, f, indent=2, ensure_ascii=False)
        
        print(f"✅ Plan created: {self.output}")
        print(f"   Actions planned: {len(plan['actions'])}")
        
        return plan
    
    def generate_actions(self) -> List[Dict]:
        """Generate action items based on goals"""
        actions = []
        
        if "complete_rh_proof" in self.goals.lower():
            actions.extend([
                {
                    "priority": "HIGH",
                    "agent": "noesis88",
                    "task": "Continue spectral analysis of H_ψ operator",
                    "estimated_time": "2h"
                },
                {
                    "priority": "HIGH",
                    "agent": "qcal_prover",
                    "task": "Validate zero localization on critical line",
                    "estimated_time": "1h"
                },
                {
                    "priority": "MEDIUM",
                    "agent": "axiom_emitter",
                    "task": "Generate additional spectral axioms",
                    "estimated_time": "30min"
                }
            ])
        
        # Always add standard maintenance actions
        actions.extend([
            {
                "priority": "LOW",
                "agent": "system",
                "task": "Clean up temporary files",
                "estimated_time": "10min"
            },
            {
                "priority": "LOW",
                "agent": "system",
                "task": "Archive old reports",
                "estimated_time": "5min"
            }
        ])
        
        return actions

def main():
    parser = argparse.ArgumentParser(description='Orchestration Planner')
    parser.add_argument('--current-state', type=str,
                       help='Path to current state JSON or JSON string')
    parser.add_argument('--goals', type=str, required=True,
                       help='Goals for next cycle')
    parser.add_argument('--output', type=str, required=True,
                       help='Output file for plan')
    
    args = parser.parse_args()
    
    planner = OrchestrationPlanner(
        current_state=args.current_state,
        goals=args.goals,
        output=args.output
    )
    planner.plan()
    
    return 0

if __name__ == "__main__":
    sys.exit(main())

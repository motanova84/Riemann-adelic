#!/usr/bin/env python3
"""
Main orchestration script for plagiarism monitoring.
Runs all monitoring checks and generates consolidated alerts.
"""
import sys
import json
import time
from pathlib import Path
from datetime import datetime

# Import monitoring modules
try:
    from fingerprints_create import create_fingerprints
    from search_github import monitor_github, get_github_token
    from search_crossref import monitor_crossref
except ImportError:
    # If running as script, try relative imports
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    try:
        from fingerprints_create import create_fingerprints
        from search_github import monitor_github, get_github_token
        from search_crossref import monitor_crossref
    except ImportError as e:
        print(f"Error importing monitoring modules: {e}")
        print("Make sure all monitoring scripts are in the same directory.")
        sys.exit(1)


def load_config():
    """Load monitoring configuration."""
    config_path = Path(__file__).resolve().parent / "config.json"
    
    default_config = {
        "monitoring": {
            "enabled": True,
            "github": True,
            "crossref": True,
            "web_search": False  # Requires API keys
        },
        "thresholds": {
            "exact_match": 100,
            "high_similarity": 80,
            "medium_similarity": 50,
            "low_similarity": 30
        },
        "search_queries": {
            "github": [
                "10.5281/zenodo.17116291",
                "Evac R_Psi alpha",
                "adelic operator Riemann",
                "José Manuel Mota Burruezo",
                "S-Finite Adelic Spectral"
            ]
        },
        "notifications": {
            "enabled": False,
            "email": None,
            "slack_webhook": None
        }
    }
    
    if config_path.exists():
        with open(config_path) as f:
            config = json.load(f)
        # Merge with defaults
        for key in default_config:
            if key not in config:
                config[key] = default_config[key]
        return config
    else:
        # Create default config
        with open(config_path, 'w') as f:
            json.dump(default_config, indent=2, fp=f)
        return default_config


def run_monitoring():
    """Run all monitoring checks."""
    print("=" * 70)
    print("PLAGIARISM MONITORING SYSTEM")
    print("Riemann Hypothesis Proof - Version V5 Coronación")
    print("DOI: 10.5281/zenodo.17116291")
    print("=" * 70)
    print(f"Started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print()
    
    repo_root = Path(__file__).resolve().parents[1]
    config = load_config()
    
    results = {
        "timestamp": datetime.now().isoformat(),
        "fingerprints": None,
        "github_alerts": [],
        "crossref_results": None,
        "summary": {
            "total_alerts": 0,
            "high_severity": 0,
            "medium_severity": 0,
            "low_severity": 0
        }
    }
    
    # Step 1: Update fingerprints
    print("\n" + "=" * 70)
    print("STEP 1: Updating Fingerprints")
    print("=" * 70)
    try:
        fingerprints = create_fingerprints()
        results["fingerprints"] = "updated"
    except Exception as e:
        print(f"Error creating fingerprints: {e}")
        results["fingerprints"] = f"error: {e}"
    
    # Step 2: Monitor GitHub
    if config["monitoring"]["github"]:
        print("\n" + "=" * 70)
        print("STEP 2: Monitoring GitHub")
        print("=" * 70)
        
        token = get_github_token()
        if not token:
            print("⚠ Warning: GITHUB_TOKEN not set. Results will be limited.")
        
        try:
            queries = config["search_queries"]["github"]
            github_alerts = monitor_github(queries)
            results["github_alerts"] = github_alerts
            
            for alert in github_alerts:
                severity = alert.get("severity", "low")
                results["summary"]["total_alerts"] += 1
                if severity == "high":
                    results["summary"]["high_severity"] += 1
                elif severity == "medium":
                    results["summary"]["medium_severity"] += 1
                else:
                    results["summary"]["low_severity"] += 1
        except Exception as e:
            print(f"Error monitoring GitHub: {e}")
            results["github_alerts"] = f"error: {e}"
    
    # Step 3: Monitor Crossref
    if config["monitoring"]["crossref"]:
        print("\n" + "=" * 70)
        print("STEP 3: Monitoring Crossref")
        print("=" * 70)
        
        try:
            crossref_results = monitor_crossref()
            results["crossref_results"] = crossref_results
            
            if crossref_results.get("alerts"):
                for alert in crossref_results["alerts"]:
                    severity = alert.get("severity", "low")
                    results["summary"]["total_alerts"] += 1
                    if severity == "high":
                        results["summary"]["high_severity"] += 1
                    elif severity == "medium":
                        results["summary"]["medium_severity"] += 1
                    else:
                        results["summary"]["low_severity"] += 1
        except Exception as e:
            print(f"Error monitoring Crossref: {e}")
            results["crossref_results"] = f"error: {e}"
    
    # Save consolidated results
    output_dir = repo_root / "monitoring" / "alerts"
    output_dir.mkdir(exist_ok=True)
    
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    output_file = output_dir / f"monitoring_report_{timestamp}.json"
    
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    # Print summary
    print("\n" + "=" * 70)
    print("MONITORING SUMMARY")
    print("=" * 70)
    print(f"Total Alerts: {results['summary']['total_alerts']}")
    print(f"  High Severity: {results['summary']['high_severity']}")
    print(f"  Medium Severity: {results['summary']['medium_severity']}")
    print(f"  Low Severity: {results['summary']['low_severity']}")
    print(f"\nReport saved to: {output_file}")
    print("=" * 70)
    
    return results


def main():
    """Main entry point."""
    try:
        results = run_monitoring()
        
        # Exit with error code if there are high severity alerts
        if results["summary"]["high_severity"] > 0:
            print("\n⚠ HIGH SEVERITY ALERTS DETECTED!")
            return 1
        elif results["summary"]["medium_severity"] > 0:
            print("\n⚠ Medium severity alerts detected")
            return 0  # Don't fail, just warn
        else:
            print("\n✓ Monitoring complete, no critical issues found")
            return 0
    except Exception as e:
        print(f"\nError running monitoring: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())

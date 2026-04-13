#!/usr/bin/env python3
"""
Monitor Riemann-Adelic Validation Workflows via GitHub API
Checks the status of validation-related workflows and provides a summary.
"""

import requests
import sys
import os
from datetime import datetime
from typing import List, Dict, Optional

# Repository configuration
REPO = "motanova84/-jmmotaburr-riemann-adelic"
API_BASE = f"https://api.github.com/repos/{REPO}"

# Validation workflow names to monitor
VALIDATION_WORKFLOWS = [
    'V5 Coronación Proof Check',
    'Comprehensive CI',
    'CI Validación',
    'Riemann Validation with Test Functions',
    'Advanced Validation',
    'Critical Line Verification',
    'LaTeX and Proof',
    'Lean',
    'Full'
]

def get_headers() -> dict:
    """Get headers for GitHub API requests."""
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28"
    }
    
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    
    return headers

def get_validation_status(limit: int = 20) -> int:
    """
    Get status of recent validation workflows.
    
    Args:
        limit: Number of workflow runs to fetch
        
    Returns:
        0 if all validations pass, 1 otherwise
    """
    url = f"{API_BASE}/actions/runs"
    headers = get_headers()
    
    try:
        response = requests.get(url, headers=headers, params={"per_page": limit})
        response.raise_for_status()
    except requests.exceptions.RequestException as e:
        print(f"❌ Error fetching workflow runs: {e}")
        return 1
    
    runs = response.json()['workflow_runs']
    
    # Filter validation-related workflows
    validation_runs = [
        run for run in runs
        if any(name.lower() in run['name'].lower() for name in 
               ['validation', 'verify', 'proof', 'check', 'ci'])
    ]
    
    if not validation_runs:
        print("ℹ️  No validation workflows found.")
        return 0
    
    # Print header
    print("\n" + "=" * 100)
    print("RIEMANN-ADELIC VALIDATION WORKFLOW STATUS")
    print("=" * 100)
    print(f"\n{'Status':<5} {'Workflow':<45} {'Conclusion':<12} {'Branch':<20} {'Created':<20}")
    print("-" * 100)
    
    # Track statistics
    completed = []
    success = []
    failed = []
    in_progress = []
    
    # Print workflow status
    for run in validation_runs[:15]:
        name = run['name'][:43]
        status = run['status']
        conclusion = run['conclusion'] or 'N/A'
        branch = run['head_branch'][:18]
        created = run['created_at'][:19].replace('T', ' ')
        
        # Determine icon
        if status == 'completed':
            completed.append(run)
            if conclusion == 'success':
                status_icon = '✅'
                success.append(run)
            else:
                status_icon = '❌'
                failed.append(run)
        elif status == 'in_progress':
            status_icon = '🔄'
            in_progress.append(run)
        elif status == 'queued':
            status_icon = '⏳'
        else:
            status_icon = '❓'
        
        print(f"{status_icon:<5} {name:<45} {conclusion:<12} {branch:<20} {created}")
    
    # Print summary
    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"Total validation workflows: {len(validation_runs)}")
    print(f"Completed: {len(completed)}")
    print(f"  ✅ Success: {len(success)}")
    print(f"  ❌ Failed: {len(failed)}")
    print(f"🔄 In Progress: {len(in_progress)}")
    
    # Overall status
    print("\n" + "=" * 100)
    if completed and len(success) == len(completed):
        print("✅ ALL VALIDATION WORKFLOWS PASSING!")
        print("=" * 100 + "\n")
        return 0
    elif failed:
        print("⚠️  SOME VALIDATION WORKFLOWS FAILED")
        print("=" * 100)
        print("\nFailed workflows:")
        for run in failed[:5]:
            print(f"  ❌ {run['name']}")
            print(f"     URL: {run['html_url']}")
        print()
        return 1
    elif in_progress:
        print("🔄 VALIDATION WORKFLOWS IN PROGRESS")
        print("=" * 100 + "\n")
        return 0
    else:
        print("ℹ️  NO COMPLETED VALIDATION WORKFLOWS")
        print("=" * 100 + "\n")
        return 0

def check_specific_workflow(workflow_name: str) -> Optional[Dict]:
    """
    Check the status of a specific workflow by name.
    
    Args:
        workflow_name: Name of the workflow to check
        
    Returns:
        Latest run information or None if not found
    """
    url = f"{API_BASE}/actions/runs"
    headers = get_headers()
    
    try:
        response = requests.get(url, headers=headers, params={"per_page": 50})
        response.raise_for_status()
    except requests.exceptions.RequestException as e:
        print(f"❌ Error: {e}")
        return None
    
    runs = response.json()['workflow_runs']
    
    # Find matching workflow
    for run in runs:
        if workflow_name.lower() in run['name'].lower():
            return run
    
    return None

def main():
    """Main function to monitor validation status."""
    # Check authentication
    if os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN"):
        auth_status = "✅ Authenticated"
    else:
        auth_status = "⚠️  Unauthenticated (rate limits apply)"
    
    print("\n" + "=" * 100)
    print("GITHUB API VALIDATION MONITOR")
    print(f"Repository: {REPO}")
    print(f"Authentication: {auth_status}")
    print("=" * 100)
    
    # Get and display validation status
    exit_code = get_validation_status()
    
    # Check rate limit
    try:
        response = requests.get("https://api.github.com/rate_limit", headers=get_headers())
        if response.status_code == 200:
            data = response.json()
            core = data['resources']['core']
            print("=" * 100)
            print(f"API Rate Limit: {core['remaining']}/{core['limit']} remaining")
            print("=" * 100 + "\n")
    except:
        pass
    
    return exit_code

if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        print("\n\n⚠️  Interrupted by user")
        sys.exit(130)
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")
        sys.exit(1)

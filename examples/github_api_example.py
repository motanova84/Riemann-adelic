#!/usr/bin/env python3
"""
GitHub API Example for Riemann-Adelic Repository
Demonstrates basic usage of GitHub REST API to access repository information.
"""

import requests
import json
import os
from typing import Optional

# Repository configuration
REPO_OWNER = "motanova84"
REPO_NAME = "-jmmotaburr-riemann-adelic"
BASE_URL = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}"

# Headers for API requests
def get_headers() -> dict:
    """Get headers for GitHub API requests."""
    headers = {
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28"
    }
    
    # Add token if available
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    
    return headers

def get_repository_info():
    """Get basic repository information."""
    print("\n" + "=" * 70)
    print("REPOSITORY INFORMATION")
    print("=" * 70)
    
    response = requests.get(BASE_URL, headers=get_headers())
    if response.status_code == 200:
        data = response.json()
        print(f"Repository: {data['full_name']}")
        print(f"Description: {data.get('description', 'N/A')}")
        print(f"Stars: ⭐ {data['stargazers_count']}")
        print(f"Forks: 🍴 {data['forks_count']}")
        print(f"Open Issues: 🐛 {data['open_issues_count']}")
        print(f"Default Branch: {data['default_branch']}")
        print(f"Language: {data.get('language', 'N/A')}")
        print(f"Created: {data['created_at']}")
        print(f"Last Updated: {data['updated_at']}")
        print(f"URL: {data['html_url']}")
    else:
        print(f"❌ Error: {response.status_code}")
        if response.status_code == 403:
            print("Rate limit may be exceeded. Try authenticating with a token.")

def get_latest_release():
    """Get the latest release information."""
    print("\n" + "=" * 70)
    print("LATEST RELEASE")
    print("=" * 70)
    
    url = f"{BASE_URL}/releases/latest"
    response = requests.get(url, headers=get_headers())
    if response.status_code == 200:
        data = response.json()
        print(f"Version: {data['tag_name']}")
        print(f"Name: {data['name']}")
        print(f"Published: {data['published_at']}")
        print(f"Author: {data['author']['login']}")
        print(f"URL: {data['html_url']}")
        if data.get('body'):
            print(f"\nRelease Notes:\n{data['body'][:200]}...")
    elif response.status_code == 404:
        print("ℹ️  No releases found.")
    else:
        print(f"❌ Error: {response.status_code}")

def get_workflow_runs(limit: int = 5):
    """Get recent workflow runs."""
    print("\n" + "=" * 70)
    print(f"RECENT WORKFLOW RUNS (Last {limit})")
    print("=" * 70)
    
    url = f"{BASE_URL}/actions/runs"
    params = {"per_page": limit}
    response = requests.get(url, headers=get_headers(), params=params)
    
    if response.status_code == 200:
        data = response.json()
        if not data['workflow_runs']:
            print("No workflow runs found.")
            return
        
        for i, run in enumerate(data['workflow_runs'], 1):
            status_icon = {
                'completed': '✅' if run['conclusion'] == 'success' else '❌',
                'in_progress': '🔄',
                'queued': '⏳'
            }.get(run['status'], '❓')
            
            print(f"\n{i}. {status_icon} {run['name']}")
            print(f"   ID: {run['id']}")
            print(f"   Status: {run['status']}")
            print(f"   Conclusion: {run['conclusion'] or 'N/A'}")
            print(f"   Branch: {run['head_branch']}")
            print(f"   Created: {run['created_at']}")
            print(f"   URL: {run['html_url']}")
    else:
        print(f"❌ Error: {response.status_code}")

def check_validation_status():
    """Check the status of validation workflows."""
    print("\n" + "=" * 70)
    print("VALIDATION WORKFLOWS STATUS")
    print("=" * 70)
    
    url = f"{BASE_URL}/actions/runs"
    params = {"per_page": 20}
    response = requests.get(url, headers=get_headers(), params=params)
    
    if response.status_code == 200:
        data = response.json()
        validation_runs = [
            run for run in data['workflow_runs']
            if 'validation' in run['name'].lower() or 
               'verify' in run['name'].lower() or
               'proof' in run['name'].lower() or
               'check' in run['name'].lower()
        ]
        
        if not validation_runs:
            print("No validation workflows found.")
            return
        
        print(f"Found {len(validation_runs)} validation-related workflow runs:\n")
        
        for run in validation_runs[:5]:
            status_icon = {
                'completed': '✅' if run['conclusion'] == 'success' else '❌',
                'in_progress': '🔄',
                'queued': '⏳'
            }.get(run['status'], '❓')
            
            print(f"{status_icon} {run['name']}")
            print(f"   Status: {run['status']} | Conclusion: {run['conclusion'] or 'N/A'}")
            print(f"   Created: {run['created_at']}")
            print()
    else:
        print(f"❌ Error: {response.status_code}")

def get_branches(limit: int = 10):
    """Get repository branches."""
    print("\n" + "=" * 70)
    print(f"BRANCHES (Last {limit})")
    print("=" * 70)
    
    url = f"{BASE_URL}/branches"
    params = {"per_page": limit}
    response = requests.get(url, headers=get_headers(), params=params)
    
    if response.status_code == 200:
        branches = response.json()
        for i, branch in enumerate(branches, 1):
            protected = "🔒" if branch.get('protected') else ""
            print(f"{i}. {protected} {branch['name']}")
            print(f"   Commit SHA: {branch['commit']['sha'][:7]}")
    else:
        print(f"❌ Error: {response.status_code}")

def get_rate_limit():
    """Check API rate limit status."""
    print("\n" + "=" * 70)
    print("API RATE LIMIT STATUS")
    print("=" * 70)
    
    url = "https://api.github.com/rate_limit"
    response = requests.get(url, headers=get_headers())
    
    if response.status_code == 200:
        data = response.json()
        core = data['resources']['core']
        print(f"Limit: {core['limit']}")
        print(f"Remaining: {core['remaining']}")
        print(f"Used: {core['used']}")
        print(f"Resets at: {core['reset']}")
        
        if core['remaining'] < core['limit'] * 0.1:
            print("\n⚠️  Warning: Less than 10% of rate limit remaining!")
    else:
        print(f"❌ Error: {response.status_code}")

def main():
    """Main function to run all examples."""
    print("\n" + "=" * 70)
    print("GITHUB REST API EXAMPLE")
    print("Repository: motanova84/-jmmotaburr-riemann-adelic")
    print("=" * 70)
    
    # Check if token is available
    if os.environ.get("GITHUB_TOKEN"):
        print("✅ Authenticated with GitHub token")
    else:
        print("ℹ️  Running without authentication (rate limits apply)")
        print("   Set GITHUB_TOKEN environment variable for higher limits")
    
    try:
        get_repository_info()
        get_latest_release()
        get_branches()
        get_workflow_runs()
        check_validation_status()
        get_rate_limit()
        
        print("\n" + "=" * 70)
        print("✅ All API calls completed successfully!")
        print("=" * 70 + "\n")
        
    except requests.exceptions.RequestException as e:
        print(f"\n❌ Request error: {e}")
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Monitor GitHub for potential plagiarism of code and research.
Searches GitHub code and repositories for key snippets and DOI.
"""
import os
import sys
import json
import time
from pathlib import Path
from typing import List, Dict, Any

try:
    import requests
except ImportError:
    print("Error: requests library not installed. Run: pip install requests")
    sys.exit(1)


def get_github_token():
    """Get GitHub token from environment."""
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        print("Warning: GITHUB_TOKEN not set. API rate limits will be very restrictive.")
        return None
    return token


def search_github_code(query: str, per_page: int = 20) -> Dict[str, Any]:
    """
    Search GitHub code for specific query.
    
    Args:
        query: Search query (supports GitHub code search syntax)
        per_page: Results per page (max 100)
    
    Returns:
        Dictionary with search results
    """
    token = get_github_token()
    headers = {}
    if token:
        headers["Authorization"] = f"token {token}"
    
    url = "https://api.github.com/search/code"
    params = {"q": query, "per_page": per_page}
    
    try:
        response = requests.get(url, headers=headers, params=params, timeout=30)
        
        # Check rate limit
        remaining = response.headers.get('X-RateLimit-Remaining', '?')
        print(f"GitHub API rate limit remaining: {remaining}")
        
        if response.status_code == 403:
            print(f"Rate limit exceeded. Reset time: {response.headers.get('X-RateLimit-Reset', 'unknown')}")
            return {"items": [], "total_count": 0, "error": "rate_limit"}
        
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        print(f"Error searching GitHub: {e}", file=sys.stderr)
        return {"items": [], "total_count": 0, "error": str(e)}


def search_github_repositories(query: str, per_page: int = 20) -> Dict[str, Any]:
    """
    Search GitHub repositories.
    
    Args:
        query: Search query
        per_page: Results per page
    
    Returns:
        Dictionary with search results
    """
    token = get_github_token()
    headers = {}
    if token:
        headers["Authorization"] = f"token {token}"
    
    url = "https://api.github.com/search/repositories"
    params = {"q": query, "per_page": per_page}
    
    try:
        response = requests.get(url, headers=headers, params=params, timeout=30)
        response.raise_for_status()
        return response.json()
    except requests.exceptions.RequestException as e:
        print(f"Error searching GitHub repositories: {e}", file=sys.stderr)
        return {"items": [], "total_count": 0, "error": str(e)}


def monitor_github(queries: List[str]) -> List[Dict[str, Any]]:
    """
    Monitor GitHub for multiple queries.
    
    Args:
        queries: List of search queries
    
    Returns:
        List of alerts for suspicious matches
    """
    alerts = []
    our_repo = "motanova84/-jmmotaburr-riemann-adelic"
    
    for query in queries:
        print(f"\nSearching GitHub for: {query}")
        results = search_github_code(query)
        
        if "error" in results:
            continue
        
        for item in results.get("items", []):
            repo_full_name = item.get("repository", {}).get("full_name", "")
            
            # Skip our own repository
            if repo_full_name == our_repo:
                continue
            
            alert = {
                "source": "github_code",
                "query": query,
                "match_url": item.get("html_url", ""),
                "repository": repo_full_name,
                "path": item.get("path", ""),
                "score": item.get("score", 0),
                "severity": "medium"
            }
            
            print(f"  Found: {repo_full_name} - {item.get('path', '')}")
            alerts.append(alert)
        
        # Rate limiting - sleep between queries
        time.sleep(2)
    
    return alerts


def main():
    """Main monitoring function."""
    repo_root = Path(__file__).resolve().parents[1]
    
    # Load fingerprints to get key snippets
    fingerprints_path = repo_root / "monitoring" / "fingerprints.json"
    if not fingerprints_path.exists():
        print("Error: fingerprints.json not found. Run fingerprints_create.py first.")
        sys.exit(1)
    
    with open(fingerprints_path) as f:
        fingerprints = json.load(f)
    
    # Define search queries
    queries = [
        # DOI search
        "10.5281/zenodo.17116291",
        
        # Key LaTeX expressions (search as text, not LaTeX)
        "Evac R_Psi alpha",
        "adelic operator Riemann",
        "discrete symmetry vacuum energy",
        
        # Author name
        "José Manuel Mota Burruezo",
        "Mota Burruezo Riemann",
        
        # Unique terms
        "S-Finite Adelic Spectral",
        "Coronación V5",
    ]
    
    print("=" * 60)
    print("GitHub Monitoring - Plagiarism Detection")
    print("=" * 60)
    
    alerts = monitor_github(queries)
    
    # Save alerts
    if alerts:
        output_dir = repo_root / "monitoring" / "alerts"
        output_dir.mkdir(exist_ok=True)
        
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        output_file = output_dir / f"github_alerts_{timestamp}.json"
        
        with open(output_file, 'w') as f:
            json.dump({
                "timestamp": timestamp,
                "total_alerts": len(alerts),
                "alerts": alerts
            }, f, indent=2)
        
        print(f"\n⚠ Found {len(alerts)} potential matches")
        print(f"Saved alerts to: {output_file}")
    else:
        print("\n✓ No suspicious matches found")
    
    return alerts


if __name__ == "__main__":
    main()

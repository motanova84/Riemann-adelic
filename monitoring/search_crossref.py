#!/usr/bin/env python3
"""
Monitor Crossref for citations and usage of DOI.
Check if the DOI is being cited or referenced properly.
"""
import sys
import json
import time
from pathlib import Path
from typing import Dict, Any, List

try:
    import requests
except ImportError:
    print("Error: requests library not installed. Run: pip install requests")
    sys.exit(1)


def query_crossref_doi(doi: str) -> Dict[str, Any]:
    """
    Query Crossref API for DOI information.
    
    Args:
        doi: DOI to query
    
    Returns:
        Dictionary with DOI metadata or None if not found
    """
    url = f"https://api.crossref.org/works/{doi}"
    
    try:
        response = requests.get(url, timeout=30)
        if response.status_code == 200:
            return response.json()
        elif response.status_code == 404:
            print(f"DOI not found in Crossref: {doi}")
            return None
        else:
            print(f"Crossref API error: {response.status_code}")
            return None
    except requests.exceptions.RequestException as e:
        print(f"Error querying Crossref: {e}", file=sys.stderr)
        return None


def search_crossref_citations(doi: str) -> List[Dict[str, Any]]:
    """
    Search for works that cite the given DOI.
    
    Args:
        doi: DOI to search citations for
    
    Returns:
        List of citing works
    """
    # Note: Not all DOIs have citation data in Crossref
    # This is a basic implementation
    url = f"https://api.crossref.org/works/{doi}"
    
    try:
        response = requests.get(url, timeout=30)
        if response.status_code == 200:
            data = response.json()
            message = data.get("message", {})
            
            # Check if there are references or citations
            is_referenced_by_count = message.get("is-referenced-by-count", 0)
            
            return {
                "doi": doi,
                "citations_count": is_referenced_by_count,
                "title": message.get("title", [""])[0],
                "published": message.get("published", {}),
                "type": message.get("type", ""),
                "url": message.get("URL", "")
            }
    except requests.exceptions.RequestException as e:
        print(f"Error searching citations: {e}", file=sys.stderr)
        return None


def search_crossref_by_title(title: str, limit: int = 10) -> List[Dict[str, Any]]:
    """
    Search Crossref by title to find potential duplicates or references.
    
    Args:
        title: Title to search for
        limit: Maximum number of results
    
    Returns:
        List of matching works
    """
    url = "https://api.crossref.org/works"
    params = {
        "query.title": title,
        "rows": limit
    }
    
    try:
        response = requests.get(url, params=params, timeout=30)
        response.raise_for_status()
        data = response.json()
        
        items = data.get("message", {}).get("items", [])
        results = []
        
        for item in items:
            results.append({
                "doi": item.get("DOI", ""),
                "title": item.get("title", [""])[0] if item.get("title") else "",
                "authors": [
                    f"{a.get('given', '')} {a.get('family', '')}"
                    for a in item.get("author", [])
                ],
                "published": item.get("published", {}),
                "type": item.get("type", ""),
                "url": item.get("URL", "")
            })
        
        return results
    except requests.exceptions.RequestException as e:
        print(f"Error searching by title: {e}", file=sys.stderr)
        return []


def monitor_crossref() -> Dict[str, Any]:
    """
    Monitor Crossref for our DOI and related works.
    
    Returns:
        Dictionary with monitoring results
    """
    our_doi = "10.5281/zenodo.17116291"
    our_title = "Version V5 — Coronación: A Definitive Proof of the Riemann Hypothesis"
    
    print("=" * 60)
    print("Crossref Monitoring - Citation & Usage Detection")
    print("=" * 60)
    
    results = {
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "doi_info": None,
        "citations": None,
        "similar_titles": [],
        "alerts": []
    }
    
    # Check our DOI
    print(f"\nQuerying DOI: {our_doi}")
    doi_info = query_crossref_doi(our_doi)
    results["doi_info"] = doi_info
    
    if doi_info:
        print("✓ DOI found in Crossref")
    else:
        # This is expected for Zenodo DOIs as they may not all be in Crossref
        print("ℹ DOI not indexed in Crossref (normal for Zenodo records)")
    
    # Search for citations
    print(f"\nSearching for citations...")
    citations = search_crossref_citations(our_doi)
    results["citations"] = citations
    
    if citations and citations.get("citations_count", 0) > 0:
        print(f"✓ Found {citations['citations_count']} citations")
    
    # Search for similar titles (potential plagiarism)
    print(f"\nSearching for similar titles...")
    similar = search_crossref_by_title(our_title)
    
    for work in similar:
        # Skip our own DOI
        if work["doi"] == our_doi:
            continue
        
        results["similar_titles"].append(work)
        
        # Check if it's suspicious
        if "riemann" in work["title"].lower() and "hypothesis" in work["title"].lower():
            alert = {
                "severity": "medium",
                "reason": "Similar title with Riemann Hypothesis keywords",
                "doi": work["doi"],
                "title": work["title"],
                "url": work["url"]
            }
            results["alerts"].append(alert)
            print(f"  ⚠ Potential match: {work['title'][:60]}...")
            print(f"     DOI: {work['doi']}")
    
    if not results["alerts"]:
        print("✓ No suspicious similar titles found")
    
    return results


def main():
    """Main monitoring function."""
    repo_root = Path(__file__).resolve().parents[1]
    
    results = monitor_crossref()
    
    # Save results
    output_dir = repo_root / "monitoring" / "alerts"
    output_dir.mkdir(exist_ok=True)
    
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    output_file = output_dir / f"crossref_monitoring_{timestamp}.json"
    
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    print(f"\nResults saved to: {output_file}")
    
    if results["alerts"]:
        print(f"\n⚠ Found {len(results['alerts'])} alerts")
        return 1
    else:
        print("\n✓ Monitoring complete, no issues found")
        return 0


if __name__ == "__main__":
    sys.exit(main())

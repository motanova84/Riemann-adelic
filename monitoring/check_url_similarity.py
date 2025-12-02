#!/usr/bin/env python3
"""
Check URL similarity against our fingerprints.
Uses text comparison to detect potential copies.
"""
import sys
import json
import hashlib
from pathlib import Path
from typing import Dict, Any, Optional

try:
    import requests
except ImportError:
    print("Error: requests library not installed. Run: pip install requests")
    sys.exit(1)


def sha256_of_text(text: str) -> str:
    """Compute SHA256 hash of text."""
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def simple_similarity_score(text1: str, text2: str) -> float:
    """
    Calculate simple word-based similarity between two texts.
    Returns a score between 0 and 100.
    """
    # Normalize texts
    words1 = set(text1.lower().split())
    words2 = set(text2.lower().split())
    
    if not words1 or not words2:
        return 0.0
    
    # Jaccard similarity
    intersection = len(words1.intersection(words2))
    union = len(words1.union(words2))
    
    return (intersection / union) * 100 if union > 0 else 0.0


def check_url_for_fingerprints(url: str, fingerprints: Dict[str, Any]) -> Dict[str, Any]:
    """
    Check if a URL contains content matching our fingerprints.
    
    Args:
        url: URL to check
        fingerprints: Our fingerprint data
    
    Returns:
        Dictionary with check results
    """
    result = {
        "url": url,
        "accessible": False,
        "sha256_match": False,
        "snippet_matches": [],
        "similarity_scores": {},
        "status": "unknown"
    }
    
    try:
        print(f"Checking URL: {url}")
        response = requests.get(url, timeout=30, headers={
            'User-Agent': 'Mozilla/5.0 (Research Monitoring Bot)'
        })
        response.raise_for_status()
        
        result["accessible"] = True
        result["status_code"] = response.status_code
        
        content = response.text
        content_hash = sha256_of_text(content)
        
        # Check for exact hash matches
        for file_name, file_info in fingerprints.get("files", {}).items():
            if content_hash == file_info.get("sha256"):
                result["sha256_match"] = True
                result["matched_file"] = file_name
                print(f"  ⚠ EXACT MATCH found for {file_name}!")
                break
        
        # Check for LaTeX snippet matches
        for snippet_name, snippet_info in fingerprints.get("latex_snippets", {}).items():
            snippet_content = snippet_info.get("content", "")
            
            # Check if snippet appears in content
            if snippet_content in content:
                result["snippet_matches"].append({
                    "name": snippet_name,
                    "content": snippet_content
                })
                print(f"  ⚠ Found snippet: {snippet_name}")
        
        # Check for DOI mention
        doi = fingerprints.get("doi", "")
        if doi and doi in content:
            result["doi_found"] = True
            print(f"  ℹ DOI found in content")
        
        # Calculate similarity (basic version)
        # In production, use more sophisticated methods
        result["content_length"] = len(content)
        
        if result["sha256_match"] or result["snippet_matches"]:
            result["status"] = "suspicious"
        else:
            result["status"] = "clean"
            
    except requests.exceptions.RequestException as e:
        result["error"] = str(e)
        result["status"] = "error"
        print(f"  Error accessing URL: {e}")
    
    return result


def check_multiple_urls(urls: list, fingerprints: Dict[str, Any]) -> list:
    """
    Check multiple URLs against fingerprints.
    
    Args:
        urls: List of URLs to check
        fingerprints: Our fingerprint data
    
    Returns:
        List of check results
    """
    results = []
    
    for url in urls:
        result = check_url_for_fingerprints(url, fingerprints)
        results.append(result)
        
        # Be polite - wait between requests
        import time
        time.sleep(1)
    
    return results


def main():
    """Main URL checking function."""
    repo_root = Path(__file__).resolve().parents[1]
    
    # Load fingerprints
    fingerprints_path = repo_root / "monitoring" / "fingerprints.json"
    if not fingerprints_path.exists():
        print("Error: fingerprints.json not found. Run fingerprints_create.py first.")
        sys.exit(1)
    
    with open(fingerprints_path) as f:
        fingerprints = json.load(f)
    
    print("=" * 60)
    print("URL Similarity Checker")
    print("=" * 60)
    
    # Example: Check specific URLs
    # In production, this would come from command line or config
    test_urls = [
        # Add suspicious URLs here
        # "https://example.com/potential-copy"
    ]
    
    if len(sys.argv) > 1:
        # URLs provided as command line arguments
        test_urls = sys.argv[1:]
    
    if not test_urls:
        print("\nNo URLs to check.")
        print("Usage: python check_url_similarity.py <url1> [url2] ...")
        return 0
    
    results = check_multiple_urls(test_urls, fingerprints)
    
    # Save results
    output_dir = repo_root / "monitoring" / "alerts"
    output_dir.mkdir(exist_ok=True)
    
    import time
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    output_file = output_dir / f"url_check_{timestamp}.json"
    
    with open(output_file, 'w') as f:
        json.dump({
            "timestamp": timestamp,
            "checked_urls": len(results),
            "results": results
        }, f, indent=2)
    
    print(f"\nResults saved to: {output_file}")
    
    # Check if any suspicious results
    suspicious = [r for r in results if r.get("status") == "suspicious"]
    if suspicious:
        print(f"\n⚠ Found {len(suspicious)} suspicious URLs")
        return 1
    else:
        print("\n✓ All checked URLs are clean")
        return 0


if __name__ == "__main__":
    sys.exit(main())

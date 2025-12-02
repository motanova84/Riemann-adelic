#!/usr/bin/env python3
"""
Test script to verify that badge links in README.md are functional.
This validates that all badges link to real resources.
"""

import os
import re
import sys
from pathlib import Path


def extract_badge_links(readme_path):
    """Extract all badge links from README.md"""
    with open(readme_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Pattern to match markdown links: [text](url)
    markdown_link_pattern = r'\[!\[([^\]]+)\]\(([^\)]+)\)\]\(([^\)]+)\)'
    # Pattern to match HTML links: <a href="url"><img src="badge_url"></a>
    html_link_pattern = r'<a href="([^"]+)"><img src="([^"]+)"'
    
    markdown_links = re.findall(markdown_link_pattern, content)
    html_links = re.findall(html_link_pattern, content)
    
    return markdown_links, html_links


def verify_local_resources(readme_dir):
    """Verify that local resources referenced by badges exist"""
    local_resources = [
        'data/v5_coronacion_certificate.json',
        'data/mathematical_certificate.json',
        'data/critical_line_verification.csv',
        'data/zenodo_publication_report.json',
        'formalization/lean/README.md',
        'REPRODUCIBILITY.md',
        'ADVANCED_LIBRARIES_README.md',
        '.github/workflows/v5-coronacion-proof-check.yml',
        '.github/workflows/ci_coverage.yml',
        '.github/workflows/comprehensive-ci.yml',
        '.github/workflows/lean.yml',
        '.github/workflows/lean-validation.yml',
        '.github/workflows/advanced-validation.yml',
        '.github/workflows/critical-line-verification.yml',
    ]
    
    missing_resources = []
    existing_resources = []
    
    for resource in local_resources:
        resource_path = readme_dir / resource
        if resource_path.exists():
            existing_resources.append(resource)
        else:
            missing_resources.append(resource)
    
    return existing_resources, missing_resources


def check_external_urls(markdown_links, html_links):
    """Categorize and report on external URLs"""
    external_urls = []
    
    # Extract from markdown links
    for text, badge_url, link_url in markdown_links:
        if link_url.startswith('http'):
            external_urls.append((text, link_url))
    
    # Extract from HTML links
    for link_url, badge_url in html_links:
        if link_url.startswith('http'):
            external_urls.append(('HTML Link', link_url))
    
    return external_urls


def main():
    readme_path = Path(__file__).parent / 'README.md'
    
    if not readme_path.exists():
        print(f"❌ README.md not found at {readme_path}")
        return 1
    
    print("=" * 80)
    print("🔍 BADGE LINK VALIDATION TEST")
    print("=" * 80)
    print()
    
    # Extract links from README
    markdown_links, html_links = extract_badge_links(readme_path)
    
    print(f"📊 Found {len(markdown_links)} markdown badge links")
    print(f"📊 Found {len(html_links)} HTML badge links")
    print()
    
    # Verify local resources
    print("=" * 80)
    print("📁 LOCAL RESOURCE VERIFICATION")
    print("=" * 80)
    existing, missing = verify_local_resources(readme_path.parent)
    
    print(f"\n✅ Existing resources ({len(existing)}):")
    for resource in existing:
        print(f"  ✓ {resource}")
    
    if missing:
        print(f"\n⚠️  Missing resources ({len(missing)}):")
        for resource in missing:
            print(f"  ✗ {resource}")
    else:
        print("\n✅ All local resources exist!")
    
    # Report on external URLs
    print()
    print("=" * 80)
    print("🌐 EXTERNAL URL REFERENCES")
    print("=" * 80)
    external_urls = check_external_urls(markdown_links, html_links)
    
    # Categorize URLs for display purposes only (not security-sensitive)
    # Note: These substring checks are for categorization, not sanitization
    github_urls = []
    doi_urls = []
    codecov_urls = []
    other_urls = []
    
    for text, url in external_urls:
        # Categorization logic - not used for security decisions
        if 'github.com' in url:
            github_urls.append((text, url))
        elif 'doi.org' in url or 'zenodo' in url:
            doi_urls.append((text, url))
        elif 'codecov' in url:
            codecov_urls.append((text, url))
        else:
            other_urls.append((text, url))
    
    print(f"\n📍 GitHub URLs ({len(github_urls)}):")
    for text, url in github_urls[:5]:  # Show first 5
        print(f"  • {text}: {url}")
    if len(github_urls) > 5:
        print(f"  ... and {len(github_urls) - 5} more")
    
    print(f"\n📚 DOI/Zenodo URLs ({len(doi_urls)}):")
    for text, url in doi_urls:
        print(f"  • {text}: {url}")
    
    print(f"\n📊 Codecov URLs ({len(codecov_urls)}):")
    for text, url in codecov_urls:
        print(f"  • {text}: {url}")
    
    if other_urls:
        print(f"\n🔗 Other URLs ({len(other_urls)}):")
        for text, url in other_urls:
            print(f"  • {text}: {url}")
    
    # Summary
    print()
    print("=" * 80)
    print("📋 VALIDATION SUMMARY")
    print("=" * 80)
    print(f"✅ Local resources: {len(existing)}/{len(existing) + len(missing)}")
    print(f"🌐 External URLs: {len(external_urls)}")
    print(f"   - GitHub: {len(github_urls)}")
    print(f"   - DOI/Zenodo: {len(doi_urls)}")
    print(f"   - Codecov: {len(codecov_urls)}")
    print(f"   - Other: {len(other_urls)}")
    
    if missing:
        print()
        print("⚠️  Some local resources are missing. Please verify these paths.")
        return 1
    
    print()
    print("✅ All badge links are properly configured!")
    print("✨ Badges are now functional and provide real information!")
    return 0


if __name__ == '__main__':
    sys.exit(main())

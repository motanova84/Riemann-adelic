# GitHub REST API Quickstart for Riemann-Adelic

This guide helps you quickly start using the GitHub REST API to interact with the Riemann-Adelic repository programmatically.

## Table of Contents
- [Introduction](#introduction)
- [Using GitHub CLI](#using-github-cli)
- [Using curl](#using-curl)
- [Using Python](#using-python)
- [Common Use Cases](#common-use-cases)
- [Authentication](#authentication)

## Introduction

The GitHub REST API allows you to programmatically access repository data, workflows, releases, and more. This guide provides examples specific to the `motanova84/-jmmotaburr-riemann-adelic` repository.

## Using GitHub CLI

GitHub CLI (`gh`) is the easiest way to use the GitHub REST API from the command line.

### Installation

Install GitHub CLI on your system:

- **macOS**: `brew install gh`
- **Linux**: See [GitHub CLI installation](https://github.com/cli/cli#installation)
- **Windows**: Download from [GitHub CLI releases](https://github.com/cli/cli/releases)

### Authentication

```bash
gh auth login
```

Follow the prompts to authenticate with GitHub.

### Examples

#### Get Repository Information

```bash
gh api /repos/motanova84/-jmmotaburr-riemann-adelic
```

#### List Recent Workflow Runs

```bash
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/actions/runs \
  --jq '.workflow_runs[] | {id: .id, name: .name, status: .status, conclusion: .conclusion}'
```

#### Get Latest Release

```bash
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/releases/latest
```

#### List Issues

```bash
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/issues \
  --jq '.[] | {number: .number, title: .title, state: .state}'
```

## Using curl

You can use `curl` to make direct HTTP requests to the GitHub API.

### Basic Request (Public Data)

```bash
curl -H "Accept: application/vnd.github+json" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic
```

### With Authentication

```bash
# Using a personal access token
curl -H "Accept: application/vnd.github+json" \
     -H "Authorization: Bearer YOUR_TOKEN" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic
```

### Examples

#### Get Repository Tags

```bash
curl -H "Accept: application/vnd.github+json" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic/tags
```

#### Get Workflow Status

```bash
curl -H "Accept: application/vnd.github+json" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic/actions/workflows
```

#### Get Contents of a File

```bash
curl -H "Accept: application/vnd.github+json" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic/contents/README.md
```

## Using Python

Python with the `requests` library provides a convenient way to interact with the GitHub API.

### Installation

```bash
pip install requests
```

### Example Script

```python
import requests
import json

# Base configuration
REPO_OWNER = "motanova84"
REPO_NAME = "-jmmotaburr-riemann-adelic"
BASE_URL = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}"

# Headers for API requests
headers = {
    "Accept": "application/vnd.github+json",
    # Uncomment and add your token for authenticated requests
    # "Authorization": "Bearer YOUR_TOKEN"
}

def get_repository_info():
    """Get basic repository information."""
    response = requests.get(BASE_URL, headers=headers)
    if response.status_code == 200:
        data = response.json()
        print(f"Repository: {data['full_name']}")
        print(f"Description: {data['description']}")
        print(f"Stars: {data['stargazers_count']}")
        print(f"Forks: {data['forks_count']}")
    else:
        print(f"Error: {response.status_code}")

def get_latest_release():
    """Get the latest release information."""
    url = f"{BASE_URL}/releases/latest"
    response = requests.get(url, headers=headers)
    if response.status_code == 200:
        data = response.json()
        print(f"Latest Release: {data['tag_name']}")
        print(f"Published: {data['published_at']}")
        print(f"URL: {data['html_url']}")
    else:
        print(f"Error: {response.status_code}")

def get_workflow_runs(workflow_name=None, limit=5):
    """Get recent workflow runs."""
    url = f"{BASE_URL}/actions/runs"
    params = {"per_page": limit}
    response = requests.get(url, headers=headers, params=params)
    if response.status_code == 200:
        data = response.json()
        for run in data['workflow_runs']:
            print(f"Run #{run['id']}: {run['name']} - {run['status']} ({run['conclusion']})")
    else:
        print(f"Error: {response.status_code}")

def check_validation_status():
    """Check the status of validation workflows."""
    url = f"{BASE_URL}/actions/runs"
    params = {"per_page": 10}
    response = requests.get(url, headers=headers, params=params)
    if response.status_code == 200:
        data = response.json()
        validation_runs = [
            run for run in data['workflow_runs']
            if 'validation' in run['name'].lower() or 'verify' in run['name'].lower()
        ]
        print(f"Found {len(validation_runs)} validation workflow runs:")
        for run in validation_runs[:5]:
            status_icon = "✅" if run['conclusion'] == "success" else "❌"
            print(f"{status_icon} {run['name']}: {run['status']} ({run['conclusion']})")
    else:
        print(f"Error: {response.status_code}")

if __name__ == "__main__":
    print("=== Repository Information ===")
    get_repository_info()
    print("\n=== Latest Release ===")
    get_latest_release()
    print("\n=== Recent Workflow Runs ===")
    get_workflow_runs()
    print("\n=== Validation Status ===")
    check_validation_status()
```

Save this as `github_api_example.py` and run:

```bash
python3 github_api_example.py
```

## Common Use Cases

### 1. Monitor Validation Workflows

Check if the latest validation workflows have passed:

```bash
# Using GitHub CLI
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/actions/runs \
  --jq '.workflow_runs[] | select(.name | contains("validation")) | {name: .name, status: .status, conclusion: .conclusion}' \
  | head -5
```

### 2. Get File Contents

Retrieve the contents of validation scripts:

```bash
# Using curl
curl -H "Accept: application/vnd.github.raw" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic/contents/test_enhancements.py
```

### 3. List All Tags (Versions)

```bash
# Using GitHub CLI
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/tags --jq '.[].name'
```

### 4. Check CI/CD Status

Get the status of the comprehensive CI workflow:

```bash
# Using GitHub CLI
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/comprehensive-ci.yml/runs \
  --jq '.workflow_runs[0] | {status: .status, conclusion: .conclusion, url: .html_url}'
```

### 5. Download Workflow Artifacts

List and download artifacts from workflow runs:

```bash
# List artifacts for a specific run
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/actions/runs/RUN_ID/artifacts

# Download an artifact (replace ARTIFACT_ID)
gh api /repos/motanova84/-jmmotaburr-riemann-adelic/actions/artifacts/ARTIFACT_ID/zip > artifact.zip
```

## Authentication

### Personal Access Token (Classic)

1. Go to GitHub Settings → Developer settings → Personal access tokens → Tokens (classic)
2. Click "Generate new token (classic)"
3. Select scopes:
   - `repo` - Full control of private repositories
   - `workflow` - Update GitHub Action workflows
4. Generate and copy the token

### Using the Token

**GitHub CLI:**
```bash
gh auth login
# Or set the token directly
export GH_TOKEN=your_token_here
```

**curl:**
```bash
export GITHUB_TOKEN=your_token_here
curl -H "Authorization: Bearer $GITHUB_TOKEN" \
     https://api.github.com/repos/motanova84/-jmmotaburr-riemann-adelic
```

**Python:**
```python
headers = {
    "Accept": "application/vnd.github+json",
    "Authorization": f"Bearer {os.environ['GITHUB_TOKEN']}"
}
```

### Using in GitHub Actions

In GitHub Actions workflows, use the built-in `GITHUB_TOKEN`:

```yaml
- name: Use GitHub API
  env:
    GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}
  run: |
    gh api /repos/motanova84/-jmmotaburr-riemann-adelic/releases/latest
```

## Advanced: Monitoring Validation Results

Here's a complete Python script to monitor validation status:

```python
#!/usr/bin/env python3
"""Monitor Riemann-Adelic validation workflows via GitHub API."""

import requests
import sys
from datetime import datetime

REPO = "motanova84/-jmmotaburr-riemann-adelic"
API_BASE = f"https://api.github.com/repos/{REPO}"

def get_validation_status():
    """Get status of recent validation workflows."""
    url = f"{API_BASE}/actions/runs"
    headers = {"Accept": "application/vnd.github+json"}
    
    response = requests.get(url, headers=headers, params={"per_page": 20})
    if response.status_code != 200:
        print(f"Error: {response.status_code}")
        sys.exit(1)
    
    runs = response.json()['workflow_runs']
    
    # Filter validation-related workflows
    validation_workflows = [
        'V5 Coronación Proof Check',
        'Comprehensive CI',
        'CI Validación',
        'Riemann Validation with Test Functions',
        'Advanced Validation',
        'Critical Line Verification'
    ]
    
    validation_runs = [
        run for run in runs
        if any(name in run['name'] for name in validation_workflows)
    ]
    
    if not validation_runs:
        print("No validation workflows found.")
        return
    
    print(f"{'Workflow':<40} {'Status':<12} {'Conclusion':<12} {'Created':<20}")
    print("-" * 90)
    
    for run in validation_runs[:10]:
        name = run['name'][:38]
        status = run['status']
        conclusion = run['conclusion'] or 'N/A'
        created = run['created_at'][:19].replace('T', ' ')
        
        status_icon = {
            'completed': '✅' if conclusion == 'success' else '❌',
            'in_progress': '🔄',
            'queued': '⏳'
        }.get(status, '❓')
        
        print(f"{status_icon} {name:<38} {status:<12} {conclusion:<12} {created}")
    
    # Summary
    completed = [r for r in validation_runs if r['status'] == 'completed']
    success = [r for r in completed if r['conclusion'] == 'success']
    
    print("\n" + "=" * 90)
    print(f"Summary: {len(success)}/{len(completed)} workflows successful")
    
    if completed and len(success) == len(completed):
        print("✅ All validation workflows passing!")
        return 0
    else:
        print("⚠️  Some validation workflows failed or are pending")
        return 1

if __name__ == "__main__":
    sys.exit(get_validation_status())
```

Save as `monitor_validations.py` and run:

```bash
python3 monitor_validations.py
```

## Rate Limits

- **Unauthenticated requests**: 60 per hour
- **Authenticated requests**: 5,000 per hour

Check your rate limit status:

```bash
gh api /rate_limit
```

## Additional Resources

- [GitHub REST API Documentation](https://docs.github.com/en/rest)
- [GitHub CLI Manual](https://cli.github.com/manual/)
- [Repository README](README.md)
- [Validation Guide](QUICKSTART.md)

## Next Steps

After exploring the GitHub API:

1. **Automate Validation Checks**: Create scripts to monitor CI/CD status
2. **Download Results**: Fetch workflow artifacts and validation results
3. **Integration**: Integrate with your own monitoring or alerting systems
4. **Contribute**: Use the API to help improve the repository

## Support

For issues specific to this repository, open an issue at:
https://github.com/motanova84/-jmmotaburr-riemann-adelic/issues

For GitHub API issues, see:
https://github.com/community/community/discussions

---

**Last Updated**: October 2025  
**Version**: 1.0  
**Status**: Production-ready

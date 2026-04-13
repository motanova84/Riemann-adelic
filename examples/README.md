# GitHub API Examples

This directory contains example scripts demonstrating how to interact with the Riemann-Adelic repository using the GitHub REST API.

## Scripts

### `github_api_example.py`

Comprehensive example showing basic GitHub API usage:
- Repository information retrieval
- Release information
- Branch listing
- Workflow status
- Validation monitoring
- Rate limit checking

**Usage:**
```bash
python3 examples/github_api_example.py
```

**With authentication:**
```bash
export GITHUB_TOKEN=your_token_here
python3 examples/github_api_example.py
```

### `monitor_validations.py`

Specialized script for monitoring validation workflow status:
- Tracks all validation-related workflows
- Shows success/failure status
- Provides summary statistics
- Exit code indicates overall status (0 = success, 1 = failures)

**Usage:**
```bash
python3 examples/monitor_validations.py
```

**Use in automation:**
```bash
if python3 examples/monitor_validations.py; then
    echo "All validations passing!"
else
    echo "Some validations failed"
fi
```

## Requirements

All scripts require the `requests` library:

```bash
pip install requests
```

This is already included in the main `requirements.txt`.

## Authentication

For higher rate limits and access to private data, set a GitHub token:

```bash
# Using GITHUB_TOKEN
export GITHUB_TOKEN=your_token_here

# Or using GH_TOKEN (GitHub CLI convention)
export GH_TOKEN=your_token_here
```

To create a token:
1. Go to GitHub Settings → Developer settings → Personal access tokens
2. Generate new token (classic)
3. Select `repo` scope for full repository access
4. Copy and save the token

## Rate Limits

- **Unauthenticated**: 60 requests/hour
- **Authenticated**: 5,000 requests/hour

## Documentation

For complete documentation, see [GITHUB_API_QUICKSTART.md](../GITHUB_API_QUICKSTART.md)

## Examples Output

### Repository Information
```
======================================================================
REPOSITORY INFORMATION
======================================================================
Repository: motanova84/-jmmotaburr-riemann-adelic
Description: Riemann Hypothesis Proof via Adelic Spectral Systems
Stars: ⭐ XX
Forks: 🍴 XX
Open Issues: 🐛 XX
```

### Validation Status
```
======================================================================
VALIDATION WORKFLOWS STATUS
======================================================================
✅ V5 Coronación Proof Check
   Status: completed | Conclusion: success
   Created: 2025-10-19 06:00:00

🔄 Comprehensive CI
   Status: in_progress | Conclusion: N/A
   Created: 2025-10-19 06:05:00
```

## Integration Examples

### Use in GitHub Actions

```yaml
- name: Check validation status
  run: |
    python3 examples/monitor_validations.py
  env:
    GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

### Use in cron job

```bash
#!/bin/bash
# check_validations.sh
cd /path/to/repo
python3 examples/monitor_validations.py || \
  echo "Validations failed!" | mail -s "Validation Alert" admin@example.com
```

## Contributing

To add new examples:
1. Follow the existing script structure
2. Include error handling
3. Add docstrings and comments
4. Update this README
5. Test with and without authentication

## License

These examples are part of the Riemann-Adelic repository and follow the same license.

# Monitoring System - Usage Examples

This document provides practical examples of how to use the plagiarism monitoring system.

## 📋 Quick Start

### First Time Setup

1. **Clone the repository** (if not already done):
   ```bash
   git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
   cd -jmmotaburr-riemann-adelic
   ```

2. **Install dependencies**:
   ```bash
   pip install -r requirements.txt
   ```

3. **Set up GitHub token** (optional but recommended):
   ```bash
   export GITHUB_TOKEN="your_github_token_here"
   ```

4. **Generate initial fingerprints**:
   ```bash
   python3 monitoring/fingerprints_create.py
   ```

## 🔍 Usage Examples

### Example 1: Full Monitoring Run

Run all monitoring checks:

```bash
cd /path/to/-jmmotaburr-riemann-adelic
python3 monitoring/run_monitor.py
```

**Expected output:**
```
======================================================================
PLAGIARISM MONITORING SYSTEM
Riemann Hypothesis Proof - Version V5 Coronación
DOI: 10.5281/zenodo.17116291
======================================================================

STEP 1: Updating Fingerprints
✓ Fingerprinted: paper/main.pdf
✓ Fingerprinted: paper/main.tex
...

STEP 2: Monitoring GitHub
Searching GitHub for: 10.5281/zenodo.17116291
...

STEP 3: Monitoring Crossref
...

MONITORING SUMMARY
Total Alerts: 0
  High Severity: 0
  Medium Severity: 0
  Low Severity: 0
```

### Example 2: Update Fingerprints Only

If you've made changes to papers or code:

```bash
python3 monitoring/fingerprints_create.py
```

This generates `monitoring/fingerprints.json` with:
- SHA256 hashes of all key files
- Fingerprints of LaTeX snippets
- Metadata hashes

### Example 3: Search GitHub Only

To specifically search GitHub:

```bash
export GITHUB_TOKEN="your_token"
python3 monitoring/search_github.py
```

**What it searches:**
- Your DOI: `10.5281/zenodo.17116291`
- Key equations and formulas
- Author name
- Unique mathematical terms

### Example 4: Check Crossref Citations

Monitor Crossref for citations and similar works:

```bash
python3 monitoring/search_crossref.py
```

### Example 5: Verify Specific URLs

Check if a suspicious URL contains your content:

```bash
python3 monitoring/check_url_similarity.py https://example.com/suspicious-page
```

You can check multiple URLs:

```bash
python3 monitoring/check_url_similarity.py \
    https://example.com/page1 \
    https://example.com/page2 \
    https://another-site.com/page3
```

## 🤖 Automated Monitoring with GitHub Actions

### View Workflow Runs

1. Go to your repository on GitHub
2. Click "Actions" tab
3. Select "Plagiarism Monitoring" workflow
4. View recent runs

### Manual Trigger

1. Go to Actions → Plagiarism Monitoring
2. Click "Run workflow" button
3. Select branch (usually `main`)
4. Click "Run workflow"

### Scheduled Runs

The workflow runs automatically:
- **Daily** at 02:00 UTC
- **On push** to main branch (when monitoring files change)

### Download Results

After each run:
1. Go to the workflow run
2. Scroll to "Artifacts" section
3. Download `monitoring-reports` artifact
4. Unzip to view JSON reports

## 📊 Understanding Results

### Alert Severity Levels

**HIGH** 🔴:
- Exact SHA256 match of files
- Multiple LaTeX snippets found
- DOI used without attribution

**MEDIUM** 🟡:
- Single snippet match
- Similar title in academic database
- Partial content similarity

**LOW** 🟢:
- Mention of author name
- General topic similarity
- Repository reference

### Result Files

Check `monitoring/alerts/` for:

```
monitoring/alerts/
├── monitoring_report_20251016_235619.json   # Consolidated report
├── github_alerts_20251016_235619.json       # GitHub findings
└── crossref_monitoring_20251016_235619.json # Crossref findings
```

### Sample Alert JSON

```json
{
  "timestamp": "2025-10-16T23:56:19",
  "summary": {
    "total_alerts": 2,
    "high_severity": 1,
    "medium_severity": 1,
    "low_severity": 0
  },
  "github_alerts": [
    {
      "source": "github_code",
      "query": "10.5281/zenodo.17116291",
      "match_url": "https://github.com/other-user/repo/blob/main/file.md",
      "repository": "other-user/repo",
      "severity": "high"
    }
  ]
}
```

## 🛠️ Configuration

### Edit Config File

Edit `monitoring/config.json`:

```json
{
  "monitoring": {
    "enabled": true,
    "github": true,
    "crossref": true
  },
  "search_queries": {
    "github": [
      "10.5281/zenodo.17116291",
      "your custom search term"
    ]
  }
}
```

### Add Custom Search Terms

To monitor for specific terms, add to `config.json`:

```json
{
  "search_queries": {
    "github": [
      "your equation or term",
      "another unique identifier"
    ]
  }
}
```

## 📝 Responding to Alerts

### Step 1: Review Alert

```bash
# View latest report
cat monitoring/alerts/monitoring_report_*.json | jq '.'
```

### Step 2: Manual Verification

1. Click the URL in the alert
2. Review the content
3. Determine if it's legitimate use or violation

### Step 3: Collect Evidence

If violation is confirmed:

```bash
# Download the page
wget -O evidence.html "https://suspicious-url.com/page"

# Take screenshot (if you have pyppeteer)
python3 -c "
import asyncio
from pyppeteer import launch

async def screenshot():
    browser = await launch()
    page = await browser.newPage()
    await page.goto('https://suspicious-url.com/page')
    await page.screenshot({'path': 'evidence.png'})
    await browser.close()

asyncio.get_event_loop().run_until_complete(screenshot())
"
```

### Step 4: Contact

For minor issues:
```
Subject: Unauthorized Use of Research - [DOI]

Dear [Name],

I noticed that [URL] contains content from my research 
"Version V5 — Coronación" (DOI: 10.5281/zenodo.17116291)
without proper attribution.

Please either:
1. Add proper citation, or
2. Remove the content

Best regards,
José Manuel Mota Burruezo
```

### Step 5: DMCA (if needed)

For GitHub repositories:
1. Go to https://github.com/contact/dmca
2. Fill out the DMCA form
3. Include evidence and URLs

## 🔐 Security Best Practices

### Protect Your Tokens

**Never** commit tokens to the repository:

```bash
# Set in environment
export GITHUB_TOKEN="token"

# Or use .env file (add to .gitignore)
echo "GITHUB_TOKEN=your_token" > .env
```

### Use GitHub Secrets

For GitHub Actions:
1. Go to Settings → Secrets and variables → Actions
2. Add `MONITOR_GITHUB_TOKEN`
3. The workflow will use it automatically

### Rate Limits

To avoid rate limits:
- Use authenticated requests (provide token)
- Space out manual runs (don't run too frequently)
- Adjust `rate_limits` in config.json

## 🐛 Troubleshooting

### Issue: "fingerprints.json not found"

**Solution:**
```bash
python3 monitoring/fingerprints_create.py
```

### Issue: "GitHub rate limit exceeded"

**Solution:**
1. Wait 1 hour (rate limits reset)
2. Set `GITHUB_TOKEN` environment variable
3. Reduce search queries in config

### Issue: "requests module not found"

**Solution:**
```bash
pip install requests
```

### Issue: Network errors

Some networks may block API access. Try:
```bash
# Use a VPN if corporate network blocks APIs
# Or run from a different network
```

## 📚 Advanced Usage

### Custom Fingerprints

Add your own fingerprints in `monitoring/fingerprints_create.py`:

```python
def extract_key_latex_snippets():
    snippets = {
        "my_theorem": r"\text{My custom theorem}",
        "my_equation": r"E = mc^2",
    }
    return snippets
```

### Integrate with Notifications

Add to `monitoring/run_monitor.py`:

```python
import requests

def send_slack_notification(alert):
    webhook_url = os.environ.get("SLACK_WEBHOOK_URL")
    if webhook_url:
        requests.post(webhook_url, json={
            "text": f"Alert: {alert}"
        })
```

### Create Custom Monitors

Create `monitoring/search_custom.py`:

```python
def monitor_custom_source():
    # Your custom monitoring logic
    alerts = []
    # ... search logic ...
    return alerts
```

## 📖 Further Reading

- [GitHub Code Search Syntax](https://docs.github.com/en/search-github/github-code-search/understanding-github-code-search-syntax)
- [Crossref API Documentation](https://github.com/CrossRef/rest-api-doc)
- [DMCA Takedown Guide](https://docs.github.com/en/site-policy/content-removal-policies/dmca-takedown-policy)

## 🆘 Getting Help

If you need assistance:

1. **Check logs**: Review workflow logs in GitHub Actions
2. **Test locally**: Run scripts manually to debug
3. **Open issue**: Create GitHub issue with error details
4. **Contact**: institutoconsciencia@proton.me

## 📅 Maintenance

### Weekly Tasks

- [ ] Review monitoring reports
- [ ] Check for alerts
- [ ] Update fingerprints if files changed

### Monthly Tasks

- [ ] Review and update search queries
- [ ] Check GitHub Actions usage/limits
- [ ] Update monitoring README if needed

### As Needed

- [ ] Respond to alerts
- [ ] Update configuration
- [ ] Add new monitoring sources

---

**Last Updated**: 2025-10-16  
**Version**: 1.0  
**For Questions**: See monitoring/README.md

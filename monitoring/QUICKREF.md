# Monitoring System - Quick Reference

**One-page guide for the plagiarism monitoring system**

## 🚀 Quick Start

```bash
# Run full monitoring
python3 monitoring/run_monitor.py

# Update fingerprints only
python3 monitoring/fingerprints_create.py

# Check specific URL
python3 monitoring/check_url_similarity.py https://suspicious-url.com
```

## 📁 Files Overview

| File | Purpose |
|------|---------|
| `fingerprints_create.py` | Generate SHA256 hashes and fingerprints |
| `search_github.py` | Monitor GitHub for code/content copies |
| `search_crossref.py` | Check Crossref for citations and similar works |
| `check_url_similarity.py` | Verify specific URLs for similarity |
| `run_monitor.py` | **Main script** - runs all checks |
| `config.json` | Configuration (search terms, thresholds) |
| `fingerprints.json` | Generated fingerprints (auto-updated) |

## 🔍 What Gets Monitored

### Files Fingerprinted
- `paper/main.pdf` - Main paper PDF
- `paper/main.tex` - LaTeX source
- `paper_standalone.tex` - Standalone paper
- `RIEMANNJMMB84.pdf` - Research document

### Key Snippets Tracked
- Vacuum energy equation
- Adelic operator definition
- Spectral theorem
- Riemann hypothesis statement
- Discrete symmetry notation

### Metadata
- DOI: `10.5281/zenodo.17116291`
- Author: José Manuel Mota Burruezo
- Citation info from CITATION.cff

## 🎯 Search Queries

Default GitHub searches:
- DOI number
- Key equations (text form)
- Author name
- Unique terms: "S-Finite Adelic Spectral", "Coronación V5"

Edit `config.json` to customize.

## ⚡ GitHub Actions

**Schedule**: Daily at 02:00 UTC

**Manual run**:
1. Go to Actions tab
2. Select "Plagiarism Monitoring"
3. Click "Run workflow"

**Artifacts**: Download from workflow runs (90 days retention)

## 🚨 Alert Levels

| Level | Trigger | Action |
|-------|---------|--------|
| 🔴 **HIGH** | Exact file match, multiple snippets | Auto-create GitHub issue |
| 🟡 **MEDIUM** | Single snippet, similar title | Review manually |
| 🟢 **LOW** | Name mention, general similarity | Log only |

## 📊 Check Results

```bash
# View latest report
cat monitoring/alerts/monitoring_report_*.json | jq '.'

# Count alerts by severity
jq '.summary' monitoring/alerts/monitoring_report_*.json
```

## 🔧 Configuration

### Set GitHub Token
```bash
export GITHUB_TOKEN="ghp_your_token_here"
```

### Edit Search Terms
Edit `monitoring/config.json`:
```json
{
  "search_queries": {
    "github": [
      "your custom term",
      "another search"
    ]
  }
}
```

## 🛠️ Troubleshooting

| Issue | Solution |
|-------|----------|
| "fingerprints.json not found" | Run `fingerprints_create.py` |
| "Rate limit exceeded" | Set `GITHUB_TOKEN` or wait 1 hour |
| "Module not found" | Run `pip install requests` |
| Network errors | Check firewall/VPN settings |

## 📝 Response Workflow

1. **Alert received** → Review monitoring report
2. **Verify** → Click URL, check content manually
3. **Confirm** → Is it really plagiarism?
4. **Collect** → Save evidence (HTML, screenshot)
5. **Contact** → Email site owner (see templates)
6. **Escalate** → DMCA if no response

## 🔐 Security Notes

- ✅ Never commit `GITHUB_TOKEN` to repo
- ✅ Use GitHub Secrets for Actions
- ✅ Evidence files are auto-ignored (.gitignore)
- ✅ Alert JSONs are not committed

## 📚 Documentation

- **Full Guide**: `monitoring/README.md`
- **Examples**: `monitoring/USAGE_EXAMPLES.md`
- **Security**: `SECURITY.md` (repo root)
- **Copyright**: `COPYRIGHT.md` (repo root)

## 🧪 Testing

```bash
# Run monitoring tests
python3 -m pytest tests/test_monitoring.py -v

# Should see: 12 passed
```

## 🆘 Support

- **Email**: institutoconsciencia@proton.me
- **Issues**: GitHub issue tracker
- **Docs**: Check README files first

## 📅 Maintenance Checklist

**Weekly**:
- [ ] Review monitoring reports
- [ ] Check for high/medium alerts

**Monthly**:
- [ ] Update search queries if needed
- [ ] Verify fingerprints are current

**As Needed**:
- [ ] Respond to confirmed alerts
- [ ] Update configuration

---

**Version**: 1.0 | **Updated**: 2025-10-16 | **DOI**: 10.5281/zenodo.17116291

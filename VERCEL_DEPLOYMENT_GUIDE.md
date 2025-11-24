# Vercel Deployment Guide - Riemann Adelic V5 Coronación

This guide documents the comprehensive Vercel configuration for the `-jmmotaburr-riemann-adelic` repository, enabling automated validation and deployment of the Riemann-Adelic V5 Coronación framework.

## 🚀 Configuration Overview

The `vercel.json` configuration file has been enhanced with the following capabilities:

### ✅ Core Settings
- **Schema**: OpenAPI Vercel JSON schema for validation
- **Clean URLs**: Enabled (`cleanUrls: true`)
- **Trailing Slash**: Disabled for consistency
- **Output Directory**: `public/` for static HTML content
- **Framework**: None (static HTML + Python execution)

### 🔧 Build Configuration
```json
{
  "buildCommand": "echo 'No build step required. Static HTML + Python execution only'",
  "installCommand": "pip install -r requirements.txt"
}
```

### 📡 Custom Headers
All responses include symbolic Riemann-Adelic metadata:
- `X-Riemann-Adelic-Validation: V5-Coronación`
- `X-QCAL-Frequency: 141.7001Hz` (coherence frequency)
- `X-Noesis-Version: ∞³` (noetic versioning)

### 🔀 URL Rewrites
Clean, intuitive endpoints for validation and demonstration:
- `/validate` → `validate_v5_coronacion.py`
- `/demo` → `demo_paradigm_shift.py`
- `/notebook` → `notebooks/validation.ipynb`

### ⏰ Automated Cron Jobs

#### Hourly Validation
- **Endpoint**: `/api/validate-hourly`
- **Schedule**: `0 * * * *` (every hour)
- **Purpose**: Continuous validation of Riemann-Adelic coherence

#### Daily Synchronization
- **Endpoint**: `/api/sync-riemann`
- **Schedule**: `14 14 * * *` (daily at 14:14 UTC)
- **Purpose**: Adelic alignment at resonance time

### ⚙️ Serverless Functions
Optimized resource allocation for different computation types:

| Pattern | Max Duration | Memory | Purpose |
|---------|-------------|--------|---------|
| `api/*.py` | 60s | 2048 MB | API endpoints, cron jobs |
| `notebooks/*.ipynb` | 300s | 4096 MB | Complex validation notebooks |

> **⚠️ Important Pattern Note**: The pattern `api/*.py` matches files directly in the `api/` directory.
> Do NOT use `api/**/*.py` as this pattern only matches files in subdirectories (e.g., `api/subdir/*.py`)
> and will NOT match files at the root level like `api/validate-hourly.py`. This is a common mistake
> that causes deployment failures with the error:
> "El patrón 'api/**/*.py' definido en `functions` no coincide con ninguna función sin servidor"

### 🖼️ Image Optimization
- **Formats**: WebP (modern, efficient)
- **Sizes**: 512px, 1080px, 2048px
- **Cache TTL**: 60 seconds
- **SVG Security**: Disabled (`dangerouslyAllowSVG: false`)

### 🌍 Regional Distribution
Multi-region deployment with automatic failover:
- **Primary Regions**: Frankfurt (fra1), Washington D.C. (iad1), São Paulo (gru1)
- **Failover Region**: Tokyo (hnd1)

## 📁 Repository Structure

```
.
├── vercel.json                      # Main Vercel configuration
├── api/                             # Serverless functions
│   ├── validate-hourly.py          # Hourly validation endpoint
│   ├── sync-riemann.py             # Daily sync endpoint
│   └── README.md                   # API documentation
├── validate_v5_coronacion.py       # Core validation script
├── demo_paradigm_shift.py          # Paradigm demonstration
├── notebooks/
│   └── validation.ipynb            # Interactive validation notebook
├── public/                         # Static HTML files
├── requirements.txt                # Python dependencies
└── test_vercel_config.py          # Configuration tests
```

## 🚀 Deployment Instructions

### Initial Setup

1. **Link Repository to Vercel**:
   ```bash
   vercel link
   ```

2. **Deploy to Production**:
   ```bash
   vercel --prod
   ```

### Automated Deployment
The configuration supports automatic deployments:
- Push to main branch → automatic production deployment
- Push to other branches → preview deployment

### Manual Deployment
```bash
# Deploy with custom configuration
vercel deploy --prod --yes

# Check deployment status
vercel ls

# View logs
vercel logs
```

## 🧪 Testing

A comprehensive test suite validates the configuration:

```bash
# Run configuration tests
pytest test_vercel_config.py -v

# Expected output: 12/12 tests passing
```

### Test Coverage
- ✅ JSON validity and structure
- ✅ Schema reference
- ✅ URL and directory settings
- ✅ Custom headers configuration
- ✅ Rewrites and routing
- ✅ Cron job definitions
- ✅ Function resource limits
- ✅ Regional distribution
- ✅ Referenced files existence
- ✅ File permissions

## 🔍 Validation Endpoints

### Access Validation
```bash
# Direct validation script
curl https://your-deployment.vercel.app/validate

# Paradigm demonstration
curl https://your-deployment.vercel.app/demo

# Interactive notebook
curl https://your-deployment.vercel.app/notebook
```

### Check Cron Jobs
Vercel automatically manages cron jobs. Monitor their execution:
```bash
vercel logs --follow
```

## 🛡️ Security Features

1. **Header Validation**: Custom headers for authenticity verification
2. **SVG Protection**: SVG uploads disabled to prevent XSS
3. **Resource Limits**: Strict memory and duration constraints
4. **Regional Failover**: Automatic failover for high availability

## 📊 Monitoring

### Check Headers
```bash
curl -I https://your-deployment.vercel.app/

# Should include:
# X-Riemann-Adelic-Validation: V5-Coronación
# X-QCAL-Frequency: 141.7001Hz
# X-Noesis-Version: ∞³
```

### Verify Cron Execution
Check Vercel dashboard for cron job logs:
- Navigate to your project
- Go to "Deployments" → "Functions"
- Check execution logs for `/api/validate-hourly` and `/api/sync-riemann`

## 🔧 Troubleshooting

### Common Issues

**Issue**: Functions timing out
- **Solution**: Increase `maxDuration` in `functions` configuration

**Issue**: Memory errors
- **Solution**: Increase `memory` allocation for specific patterns

**Issue**: Cron jobs not running
- **Solution**: Verify deployment is on production, not preview

**Issue**: Missing dependencies
- **Solution**: Ensure `requirements.txt` includes all needed packages

## 📝 Configuration Reference

Full configuration schema: https://openapi.vercel.sh/vercel.json

## 🎯 Key Features

✅ **Zero-build deployment**: Static HTML + Python serverless  
✅ **Automated validation**: Hourly coherence checks  
✅ **Resonance synchronization**: Daily adelic alignment at 14:14 UTC  
✅ **Multi-region redundancy**: 3 primary + 1 failover region  
✅ **Optimized functions**: Resource-aware allocation  
✅ **Clean URLs**: SEO-friendly routing  
✅ **Custom headers**: Symbolic metadata embedding  
✅ **Image optimization**: WebP with multiple sizes  

## 📚 Additional Resources

- [Vercel Documentation](https://vercel.com/docs)
- [Vercel JSON Schema](https://openapi.vercel.sh/vercel.json)
- [Serverless Functions Guide](https://vercel.com/docs/functions)
- [Cron Jobs Documentation](https://vercel.com/docs/cron-jobs)

---

**Frequency**: 141.7001 Hz (QCAL Coherence Standard)  
**Version**: V5-Coronación  
**Noesis**: ∞³

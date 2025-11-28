# Vercel API Endpoints

This directory contains serverless functions for Vercel deployment, specifically designed for automated validation and synchronization of the Riemann-Adelic V5 Coronación framework.

## Endpoints

### `/api/validate-hourly`
**Purpose**: Hourly automated validation of Riemann-Adelic coherence.

**Schedule**: `0 * * * *` (every hour)

**Response Headers**:
- `X-Riemann-Adelic-Validation: V5-Coronación`
- `X-QCAL-Frequency: 141.7001Hz`

**Response Format**:
```json
{
  "status": "success",
  "message": "Hourly validation completed",
  "validation_result": "...",
  "frequency": "141.7001Hz",
  "version": "V5-Coronación"
}
```

### `/api/sync-riemann`
**Purpose**: Daily synchronization of Riemann-Adelic framework at resonance time.

**Schedule**: `14 14 * * *` (daily at 14:14 UTC)

**Response Headers**:
- `X-Riemann-Adelic-Validation: V5-Coronación`
- `X-QCAL-Frequency: 141.7001Hz`
- `X-Noesis-Version: ∞³`

**Response Format**:
```json
{
  "status": "success",
  "message": "Riemann synchronization completed at 14:14 UTC",
  "timestamp": "2025-10-16T14:14:00.000Z",
  "frequency": "141.7001Hz",
  "version": "V5-Coronación",
  "noesis_version": "∞³",
  "coherence_level": "optimal",
  "sync_type": "daily_adelic_alignment"
}
```

## Configuration

These endpoints are configured in `vercel.json` under the `crons` section with specific memory and duration limits:

```json
"functions": {
  "api/*.py": {
    "maxDuration": 60,
    "memory": 2048
  }
}
```

> **⚠️ Pattern Configuration Note**: 
> - Use `api/*.py` to match files directly in this directory
> - Do NOT use `api/**/*.py` - this only matches files in subdirectories and will cause deployment failures
> - Our functions are at the root level (`api/validate-hourly.py`), not in subdirectories

## Development

To test locally:
```bash
# Install dependencies
pip install -r ../requirements.txt

# Test endpoint
python3 validate-hourly.py
```

## Notes

- All endpoints follow the Vercel serverless function pattern using `BaseHTTPRequestHandler`
- Endpoints are automatically scheduled by Vercel's cron infrastructure
- Maximum execution time: 60 seconds
- Memory allocation: 2048 MB
- Frequency alignment: 141.7001 Hz (QCAL coherence standard)

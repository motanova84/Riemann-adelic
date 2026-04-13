# QCAL Production Workflow Guide

## Overview

The QCAL Production Cycle is an automated workflow that runs continuous validation of the Riemann Hypothesis proof using the V5 Coronación framework. This workflow ensures ongoing verification and publishes results for transparency and reproducibility.

## Workflow: `production-qcal.yml`

### Triggers

1. **Scheduled Execution**: Runs automatically every 4 hours
   - Cron schedule: `0 */4 * * *`
   - Ensures continuous validation of the mathematical proof

2. **Manual Execution**: Can be triggered manually via GitHub Actions UI
   - Navigate to: Actions → QCAL Production Cycle → Run workflow
   - Configurable parameters:
     - **Precision**: Decimal places for validation (default: 30)
     - **Publish Results**: Whether to publish to HuggingFace (default: false)

### Workflow Steps

1. **Environment Setup**
   - Uses Python 3.11 on Ubuntu latest
   - Caches pip dependencies for faster execution
   - Installs all requirements from `requirements.txt`

2. **Core Validation**
   - Runs `validate_v5_coronacion.py` with specified precision
   - Performs comprehensive 5-step verification of RH proof
   - Generates validation certificates and results

3. **Results Aggregation**
   - Executes `scripts/aggregate_results.py`
   - Collects results from multiple validation runs
   - Generates both JSON and HTML reports
   - Calculates success rates and statistics

4. **Artifact Upload**
   - Uploads validation results and aggregated reports
   - Retention period: 90 days
   - Accessible from the workflow run page

5. **HuggingFace Publishing** (Optional)
   - Publishes datasets to HuggingFace Hub
   - Repository: `motanova84/qcal-cloud`
   - Requires: `HF_TOKEN` secret
   - Automatically runs on scheduled executions

6. **Docker Image Build**
   - Builds production Docker image
   - Tags: `qcal/production:latest` and `qcal/production:<run_number>`
   - Based on Lean 4 formal verification environment

7. **Docker Image Push** (Optional)
   - Pushes image to Docker Hub
   - Requires: `DOCKERHUB_TOKEN` and `DOCKERHUB_USERNAME` secrets
   - Enables easy deployment and reproducibility

## Required Secrets

Configure these secrets in: Settings → Secrets and variables → Actions

| Secret | Description | Required For |
|--------|-------------|--------------|
| `HF_TOKEN` | HuggingFace API token | Dataset publishing to HuggingFace Hub |
| `DOCKERHUB_TOKEN` | Docker Hub authentication token | Pushing Docker images |
| `DOCKERHUB_USERNAME` | Docker Hub username | Pushing Docker images |

## Results Aggregation Script

### Usage

```bash
# Basic usage
python3 scripts/aggregate_results.py

# Custom directories
python3 scripts/aggregate_results.py --data-dir /path/to/data --output-dir /path/to/output

# JSON only
python3 scripts/aggregate_results.py --format json

# HTML only
python3 scripts/aggregate_results.py --format html
```

### Outputs

1. **JSON Report** (`aggregated_results.json`)
   - Machine-readable statistics
   - Total runs, success rates, precision averages
   - Latest run information
   - Aggregation timestamp

2. **HTML Report** (`aggregated_results.html`)
   - Human-readable dashboard
   - Visual statistics cards
   - Success/failure metrics
   - Latest run details

### Statistics Tracked

- Total validation runs
- Successful runs
- Failed runs
- Success rate (percentage)
- Average precision (decimal places)
- Latest run details (status, timestamp, precision)

## GitHub Copilot Integration

The workflow is enhanced with GitHub Copilot instructions (`.github/copilot-instructions.md`) that enable:

- **Automatic Updates**: Detects changes to validation scripts and suggests workflow updates
- **Optimization**: Proposes performance improvements (parallelization, GPU usage, caching)
- **Secret Management**: Identifies missing secrets and suggests adding them
- **Best Practices**: Ensures workflows follow CI/CD best practices
- **Documentation**: Maintains up-to-date workflow documentation

### Copilot Instructions Summary

Copilot monitors for:
1. Changes to `validate_*` scripts → Suggest workflow updates
2. New dependencies in `requirements.txt` → Check compatibility
3. Missing secrets or environment variables → Suggest configuration
4. Performance bottlenecks → Propose optimization strategies
5. Repetitive tasks → Generate new automation workflows

## Monitoring and Debugging

### View Workflow Runs

1. Navigate to the Actions tab in GitHub
2. Select "QCAL Production Cycle"
3. View run history, logs, and artifacts

### Check Aggregated Results

1. Download artifacts from a completed workflow run
2. View `aggregated_results.html` in a browser
3. Or parse `aggregated_results.json` programmatically

### Debugging Failed Runs

1. Check the workflow logs for error messages
2. Review validation output from `validate_v5_coronacion.py`
3. Verify all required secrets are configured
4. Check for dependency conflicts in `requirements.txt`

## Best Practices

1. **Monitor Success Rate**: Keep track of validation success rates over time
2. **Adjust Precision**: Increase precision for research-quality validation
3. **Regular Publishing**: Enable HuggingFace publishing for transparency
4. **Review Artifacts**: Periodically download and analyze aggregated results
5. **Update Secrets**: Rotate tokens and credentials regularly

## Future Enhancements

Potential improvements suggested by Copilot:

- **GPU Acceleration**: Use GPU runners for computationally intensive validations
- **Matrix Strategy**: Test multiple precision levels in parallel
- **Notification System**: Send alerts on validation failures
- **Result Visualization**: Generate plots and charts from aggregated data
- **Performance Tracking**: Monitor validation execution time trends

## Related Documentation

- [Main README](README.md) - Project overview and status
- [V5 Coronación Validation](validate_v5_coronacion.py) - Core validation script
- [Copilot Instructions](.github/copilot-instructions.md) - Automation rules
- [Reproducibility Guide](REPRODUCIBILITY.md) - Ensuring reproducible results
- [Advanced Validation](ADVANCED_LIBRARIES_README.md) - Advanced mathematical libraries

## Support

For issues or questions:
1. Check workflow logs in GitHub Actions
2. Review documentation in this repository
3. Open an issue on GitHub with workflow run details
4. Include relevant logs and error messages

---

**Last Updated**: 2025-10-20  
**Workflow Version**: 1.0  
**Compatibility**: Python 3.11, Ubuntu latest

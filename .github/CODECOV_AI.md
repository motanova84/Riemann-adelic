# Codecov AI Integration Guide

## Overview

This repository uses Codecov for code coverage reporting and now supports Codecov AI, an AI-powered assistant developed by Codecov at Sentry. Codecov AI helps review code changes and provides improvement suggestions before merging pull requests.

## ⚠️ Important: Install Codecov GitHub App

To ensure reliable processing of coverage uploads and PR comments, the Codecov GitHub App must be installed:

### Installing Codecov GitHub App (Required)

1. Visit: **[https://github.com/apps/codecov](https://github.com/apps/codecov)**
2. Click "Install" and select the `motanova84` organization
3. Grant permissions to the `Riemann-adelic` repository (or all repositories)
4. The app will enable:
   - ✅ Reliable coverage uploads
   - ✅ PR comments with coverage reports
   - ✅ Coverage badge generation (SVG)
   - ✅ Status checks on PRs

### Codecov Badge

Once installed, use this SVG badge in your README:

```markdown
[![codecov](https://codecov.io/gh/motanova84/Riemann-adelic/graph/badge.svg)](https://codecov.io/gh/motanova84/Riemann-adelic)
```

Preview: [![codecov](https://codecov.io/gh/motanova84/Riemann-adelic/graph/badge.svg)](https://codecov.io/gh/motanova84/Riemann-adelic)

## Current Configuration

The repository is configured to upload coverage reports to Codecov through GitHub Actions workflows:
- `.github/workflows/ci_coverage.yml` - Coverage workflow for core tests
- `.github/workflows/coverage.yml` - Standard coverage workflow
- `.github/workflows/advanced-validation.yml` - Advanced validation with coverage
- `codecov.yml` - Codecov configuration file

## Tokenless Upload

Your organization no longer requires upload tokens. Administrators manage token configuration globally. Coverage can be uploaded without a token, though the `CODECOV_TOKEN` secret is maintained for backward compatibility.

## Installing Codecov AI

### For Repository Administrators

To enable Codecov AI for this repository:

1. Visit the [Codecov AI GitHub App installation page](https://github.com/apps/codecov-ai)
2. Install the app for the `motanova84` organization or specific repositories
3. Grant the necessary permissions for PR analysis

### For Non-Administrators

If you're not an administrator, share this message with your organization owner:

> Hello, could you help us approve the installation of the Codecov AI Reviewer GitHub app for our organization? Here's the installation link: [Codecov AI Installation](https://github.com/apps/codecov-ai)

## Using Codecov AI Commands

Once the Codecov AI app is installed, you can use these commands in pull request comments:

### Generate Tests
```
@codecov-ai-reviewer test
```
The assistant will generate tests for the pull request. Test generation may take some time.

### Code Review
```
@codecov-ai-reviewer review
```
The assistant will review the pull request and make suggestions. Comment generation may take some time.

## Example Usage

### Test Generation Example
1. Open a pull request with your changes
2. Add a comment: `@codecov-ai-reviewer test`
3. Wait for the AI to analyze your changes and generate test suggestions
4. Review the generated tests and incorporate them into your code

### Code Review Example
1. Open a pull request with your changes
2. Add a comment: `@codecov-ai-reviewer review`
3. Wait for the AI to analyze your changes
4. Review the suggestions and address any issues identified

## Integration with QCAL Validation

Codecov AI complements the existing QCAL validation framework:

- **Coverage Reports**: Monitor test coverage for mathematical validation code
- **AI Review**: Get suggestions for improving test coverage and code quality
- **Test Generation**: Automatically generate tests for new mathematical functions
- **QCAL Compatibility**: AI-generated tests should maintain the repository's mathematical rigor and precision requirements (25+ dps)

## Best Practices

1. **Run AI Review Before Merge**: Use `@codecov-ai-reviewer review` before requesting human review
2. **Generate Tests for New Features**: Use `@codecov-ai-reviewer test` when adding new mathematical functions
3. **Validate AI Suggestions**: Always validate AI-generated tests using the existing validation framework:
   - Run `validate_v5_coronacion.py` for V5 Coronación validation
   - Execute `pytest tests/` to ensure all tests pass
   - Verify mathematical correctness and precision
4. **Maintain Coverage**: Aim to maintain or improve coverage with each PR
5. **Check Codecov Reports**: Review coverage reports at the Codecov dashboard

## Coverage Workflow Status

Check coverage workflow status:
- CI Coverage: Monitor `.github/workflows/ci_coverage.yml` workflow runs
- Advanced Validation: Monitor `.github/workflows/advanced-validation.yml` workflow runs

## Additional Resources

- [Codecov AI Documentation](https://docs.codecov.com/docs/codecov-ai) - Official Codecov AI guide
- [Codecov Dashboard](https://app.codecov.io/gh/motanova84/Riemann-adelic) - Repository coverage dashboard
- [About Codecov AI](https://sentry.io/) - Codecov AI is developed by Codecov at Sentry

## Support

For issues with Codecov AI:
- Visit the [Codecov Support](https://codecov.io/support) page
- Check [Codecov Documentation](https://docs.codecov.com/)
- Contact your organization's Codecov administrator

---

© 2025 Sentry  
[Terms](https://sentry.io/terms/) | [Privacy](https://sentry.io/privacy/) | [Security](https://sentry.io/security/) | [GDPR](https://sentry.io/gdpr/)

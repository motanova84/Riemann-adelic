# Security Fix: actions/download-artifact Vulnerability

**Date**: December 7, 2025  
**CVE**: Arbitrary File Write via artifact extraction  
**Severity**: High  
**Component**: @actions/download-artifact  
**Affected Versions**: >= 4.0.0, < 4.1.3  
**Patched Version**: 4.1.3  

## Vulnerability Description

The `actions/download-artifact` action had an **Arbitrary File Write vulnerability** 
via artifact extraction in versions 4.0.0 through 4.1.2. This could potentially allow
an attacker to write files to arbitrary locations during artifact extraction.

**Reference**: GitHub Security Advisory for actions/download-artifact

## Impact on Repository

The vulnerability affected **5 workflow files** with **8 total instances** of the 
vulnerable action:

### Affected Workflows

1. `.github/workflows/comprehensive-ci.yml` (4 instances)
2. `.github/workflows/critical-line-verification.yml` (1 instance)
3. `.github/workflows/rh-ds-validation.yml` (1 instance)
4. `.github/workflows/riemann-validation-with-test-functions.yml` (1 instance)
5. `.github/workflows/sabio-symbiotic-matrix.yml` (1 instance)

## Fix Applied

All instances of `actions/download-artifact@v4` have been updated to the patched 
version `actions/download-artifact@v4.1.3`.

### Changes Made

```diff
- uses: actions/download-artifact@v4
+ uses: actions/download-artifact@v4.1.3
```

### Files Modified

- ✅ `.github/workflows/comprehensive-ci.yml` - 4 instances updated
- ✅ `.github/workflows/critical-line-verification.yml` - 1 instance updated
- ✅ `.github/workflows/rh-ds-validation.yml` - 1 instance updated
- ✅ `.github/workflows/riemann-validation-with-test-functions.yml` - 1 instance updated
- ✅ `.github/workflows/sabio-symbiotic-matrix.yml` - 1 instance updated

**Total**: 8 instances across 5 files

## Verification

### Before Fix
```bash
$ grep "actions/download-artifact@v4[^.]" .github/workflows/*.yml
# Found 8 vulnerable instances
```

### After Fix
```bash
$ grep "actions/download-artifact@v4[^.]" .github/workflows/*.yml
# No vulnerable instances found

$ grep "actions/download-artifact@v4.1.3" .github/workflows/*.yml
# Found 8 patched instances
```

## Recommendation

All users should:
1. ✅ Update to `actions/download-artifact@v4.1.3` or later
2. ✅ Review any custom artifact handling code
3. ✅ Monitor GitHub Security Advisories for future updates

## Additional Security Measures

### Related Actions Checked

- `actions/upload-artifact` - Using v3 and v4 (no known vulnerabilities)
- `actions/checkout` - Versions checked, all up to date
- `actions/setup-python` - Versions checked, all up to date

### Security Best Practices Applied

1. ✅ Pin to specific patch versions (v4.1.3) instead of major versions (v4)
2. ✅ All workflow files scanned for vulnerable dependencies
3. ✅ Automated security scanning with codeql_checker
4. ✅ Documentation of security fixes

## Testing

After applying the fix:

```bash
# Run codeql security scan
✅ No security alerts found

# Verify workflow syntax
✅ All workflows validate successfully

# Check for remaining vulnerabilities
✅ No additional vulnerabilities detected
```

## Timeline

- **Detection**: December 7, 2025 - Vulnerability reported by user
- **Analysis**: December 7, 2025 - Identified 8 vulnerable instances
- **Fix Applied**: December 7, 2025 - Updated all instances to v4.1.3
- **Verification**: December 7, 2025 - Confirmed fix applied successfully
- **Documentation**: December 7, 2025 - Security fix documented

## References

- GitHub Actions: https://github.com/actions/download-artifact
- Security Advisory: GitHub Security Advisories
- Patched Version: v4.1.3
- Minimum Safe Version: >= 4.1.3

## Status

✅ **FIXED** - All vulnerable instances updated to patched version v4.1.3

---

**Security Contact**: José Manuel Mota Burruezo  
**ORCID**: 0009-0002-1923-0773  
**Repository**: https://github.com/motanova84/Riemann-adelic  
**Date**: December 7, 2025

Ψ ∴ ∞³ □

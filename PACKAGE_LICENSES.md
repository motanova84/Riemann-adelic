# Package Licenses Documentation

This document lists the licenses for key packages used in this project to ensure compliance and transparency.

## Core Dependencies

### Progress and Development Tools

- **tqdm 4.67.2**
  - License: MPL-2.0 AND MIT
  - Purpose: Progress bar utility for long-running operations
  - PyPI: https://pypi.org/project/tqdm/
  - Source: https://github.com/tqdm/tqdm

- **debugpy 1.8.0** (Optional development dependency)
  - License: MIT
  - Purpose: Python debugger for VS Code and other IDEs
  - PyPI: https://pypi.org/project/debugpy/
  - Source: https://github.com/microsoft/debugpy
  - Note: Listed as optional in requirements.txt (commented out)

## Package Naming Standards

This project follows strict package naming standards to ensure compatibility and avoid confusion:

1. **Use exact PyPI names**: All package names must match their official PyPI package names exactly.

2. **No translations**: Package names must never be translated to other languages. Examples of incorrect names:
   - ❌ `depuración` (Spanish) - should be `debugpy`
   - ❌ `ancho de banda` (Spanish) - should be `bandwidth`
   - ❌ `progreso` (Spanish) - should be `tqdm`

3. **English only**: All package names in requirements files must be in English as they appear on PyPI.

4. **Version pinning**: Critical packages should use exact version pinning (==) rather than ranges (>=) when reproducibility is essential.

## Validation

All requirements files in this repository are validated to ensure:
- No translated package names
- Correct PyPI package names
- No non-ASCII characters in package names
- Proper version specifications

To validate requirements files, check that all package names:
1. Exist on PyPI: https://pypi.org/
2. Use the exact spelling as listed on PyPI
3. Have clear license information
4. Are appropriate for the project's license

## License Compatibility

This project uses packages with the following license types:
- MIT License: Permissive open source license
- MPL-2.0: Mozilla Public License 2.0 (permissive copyleft)
- Apache 2.0: Permissive open source license
- BSD: Various BSD licenses (permissive)

All dependencies are compatible with open source distribution.

## Updates

When updating package versions:
1. Verify the package exists on PyPI
2. Check the license hasn't changed
3. Test compatibility with existing code
4. Update this documentation if adding new core dependencies

---

**Last Updated**: 2026-01-31
**Validated**: All requirements files checked for correct PyPI naming

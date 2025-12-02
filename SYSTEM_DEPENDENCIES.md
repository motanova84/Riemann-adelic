# System Dependencies for CI/CD

This document explains the system-level dependencies required for the Riemann-Adelic repository and how they are configured in CI/CD workflows.

## Overview

The repository uses several advanced mathematical libraries that require system-level dependencies:

1. **numba + llvmlite**: Requires LLVM compiler infrastructure
2. **python-igraph**: Requires libigraph C library
3. **numexpr**: Requires proper CPU detection in virtual runners

## System Dependencies

### LLVM for numba/llvmlite

**Why it's needed:**
- `numba` provides JIT (Just-In-Time) compilation for Python functions
- `llvmlite` is the LLVM backend for numba
- LLVM compiler tools are required to compile Python code to machine code

**Packages installed:**
```bash
sudo apt-get install -y llvm-14 llvm-14-dev
```

**What it provides:**
- LLVM compiler infrastructure (version 14)
- Development headers and libraries
- Target machine code generation
- Optimization passes

### libigraph for python-igraph

**Why it's needed:**
- `python-igraph` is a Python wrapper around the igraph C library
- Graph algorithms are implemented in C for performance
- The C library provides core graph data structures and algorithms

**Packages installed:**
```bash
sudo apt-get install -y libigraph-dev libigraph3t64
```

**What it provides:**
- igraph C library (version 0.10+)
- Development headers for Python bindings
- High-performance graph algorithms
- Network analysis capabilities

## Environment Variables

### numexpr Configuration

**Why it's needed:**
- `numexpr` uses multi-threading for array operations
- Virtual runners may have inconsistent CPU detection
- Explicit thread configuration prevents runtime issues

**Environment variables set:**
```bash
NUMEXPR_MAX_THREADS=4    # Maximum number of threads
NUMEXPR_NUM_THREADS=2    # Default number of threads
```

**Benefits:**
- Consistent behavior across different runner types
- Prevents CPU detection failures
- Optimizes performance for typical CI/CD environments

## CI/CD Workflow Integration

### Workflows Updated

The following workflows have been updated with system dependencies:

1. **comprehensive-ci.yml**: Main CI/CD pipeline
2. **advanced-validation.yml**: Advanced mathematical validation
3. **performance-benchmark.yml**: Performance benchmarking
4. **test.yml**: Basic operator validation
5. **ci.yml**: Legacy CI pipeline

### Installation Pattern

Each workflow now follows this pattern:

```yaml
steps:
  - name: Checkout repository
    uses: actions/checkout@v4
    
  - name: Set up Python
    uses: actions/setup-python@v5
    with:
      python-version: '3.11'
  
  - name: Install system dependencies
    run: |
      sudo apt-get update
      sudo apt-get install -y llvm-14 llvm-14-dev libigraph-dev libigraph3t64
      
  - name: Install dependencies
    env:
      NUMEXPR_MAX_THREADS: 4
      NUMEXPR_NUM_THREADS: 2
    run: |
      python -m pip install --upgrade pip==24.3.1
      pip install -r requirements-lock.txt
```

### Cache Key Update

Cache keys have been updated to include the new system dependencies:

**Old key:**
```yaml
key: ${{ runner.os }}-python-${{ steps.setup-python.outputs.python-version }}-${{ hashFiles('**/requirements-lock.txt') }}
```

**New key (with -v2):**
```yaml
key: ${{ runner.os }}-python-${{ steps.setup-python.outputs.python-version }}-${{ hashFiles('**/requirements-lock.txt') }}-v2
```

This ensures that the cache is invalidated when system dependencies change.

## Testing

### System Dependencies Test Suite

A comprehensive test suite has been added: `tests/test_system_dependencies.py`

**Test categories:**

1. **LLVM Dependencies**
   - llvmlite import and version
   - LLVM binding and target machine
   - numba JIT compilation

2. **igraph Dependencies**
   - C library availability
   - python-igraph import
   - Graph algorithms

3. **numexpr Dependencies**
   - Import and version
   - CPU detection
   - Expression evaluation
   - Environment variable handling

4. **System Packages**
   - LLVM installation check (via llvm-config)
   - libigraph installation check (via pkg-config)

5. **Integration**
   - All libraries available
   - Comprehensive summary

### Running Tests

Run the system dependencies test suite:

```bash
pytest tests/test_system_dependencies.py -v
```

Run all tests including system dependencies:

```bash
pytest tests/ -v
```

## Troubleshooting

### LLVM/numba Issues

**Problem:** numba fails to compile functions
**Solution:** Ensure LLVM development packages are installed:
```bash
sudo apt-get update
sudo apt-get install -y llvm-14 llvm-14-dev
pip install --upgrade --force-reinstall llvmlite numba
```

### igraph Issues

**Problem:** python-igraph fails to import
**Solution:** Ensure libigraph C library is installed:
```bash
sudo apt-get update
sudo apt-get install -y libigraph-dev libigraph3t64
pip install --upgrade --force-reinstall python-igraph
```

### numexpr Issues

**Problem:** numexpr fails with CPU detection errors
**Solution:** Set environment variables:
```bash
export NUMEXPR_MAX_THREADS=4
export NUMEXPR_NUM_THREADS=2
```

Or in Python:
```python
import os
os.environ['NUMEXPR_MAX_THREADS'] = '4'
os.environ['NUMEXPR_NUM_THREADS'] = '2'
import numexpr as ne
```

## Performance Impact

### With System Dependencies

- **numba**: 5-100x speedup for numerical loops
- **igraph**: 10-1000x speedup for graph algorithms vs pure Python
- **numexpr**: 2-10x speedup for complex array expressions

### Benchmarks

Run performance benchmarks:

```bash
python demo_advanced_math_libraries.py
```

## Version Compatibility

| Library | Minimum Version | Tested Version | System Requirement |
|---------|----------------|----------------|-------------------|
| llvmlite | 0.41.0 | 0.45.1 | LLVM 11-14 |
| numba | 0.58.0 | 0.62.1 | llvmlite |
| python-igraph | 0.10.8 | 0.11.9 | libigraph 0.10+ |
| numexpr | 2.8.5 | 2.14.1 | None (optional) |

## References

- [numba documentation](https://numba.pydata.org/)
- [llvmlite documentation](https://llvmlite.readthedocs.io/)
- [python-igraph documentation](https://igraph.org/python/)
- [numexpr documentation](https://numexpr.readthedocs.io/)
- [LLVM project](https://llvm.org/)
- [igraph C library](https://igraph.org/)

## Contributing

When adding new dependencies that require system libraries:

1. Update this document
2. Add system package installation to all relevant workflows
3. Add tests to `tests/test_system_dependencies.py`
4. Update cache keys if necessary
5. Document any environment variables needed

## Security Considerations

- System packages are installed from official Ubuntu repositories
- Package versions are specified when possible
- `sudo apt-get update` is run before installation
- No custom PPAs or third-party repositories are used

## License

This configuration is part of the Riemann-Adelic repository and follows the same license terms.

# Contributing to Riemann-Adelic Mathematical Archive

Thank you for your interest in contributing to the Riemann-Adelic project! This document provides guidelines for contributing to ensure clean integrations and verifiable additions to our mathematical archive.

## 🎯 Objective

Our goal is to maintain a high-quality mathematical archive that:
- Integrates formal proofs from various proof assistants (Lean, Coq, Isabelle, etc.)
- Provides rich metadata for discoverability and verification
- Ensures reproducibility and verification of all mathematical content
- Maintains coherence across the entire archive

## 📋 General Guidelines

### Before Contributing

1. **Discuss major changes**: Open an issue to discuss significant changes before starting work
2. **Check existing work**: Search issues and PRs to avoid duplicate efforts
3. **Follow code style**: We use `black`, `flake8`, and `isort` for Python code
4. **Write tests**: All new functionality should include appropriate tests
5. **Update documentation**: Keep documentation in sync with code changes

### Code Quality Standards

- **Python code**: Follow PEP 8, use type hints where appropriate
- **Mathematical content**: Provide clear proofs and explanations
- **Metadata**: Always include complete JSON-LD metadata for formal content
- **Tests**: Aim for comprehensive test coverage
- **Commit messages**: Use clear, descriptive commit messages

## 🔧 Development Workflow

### 1. Setting Up Your Environment

**Prerequisites:**
- Python 3.11 or higher (required for JAX and other dependencies)
- Git

```bash
# Clone the repository
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic

# Create and activate virtual environment (recommended)
python3 -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt

# Install pre-commit hooks
pip install pre-commit
pre-commit install
```

### 2. Creating a Branch

```bash
# Create a feature branch
git checkout -b feature/your-feature-name

# Or for bug fixes
git checkout -b fix/issue-description
```

### 3. Making Changes

#### For Code Changes:
- Write clean, documented code
- Add or update tests
- Run linters and tests locally before committing

#### For Mathematical Content:
- Provide complete formalization in the appropriate proof assistant
- Include comprehensive metadata (see schema/metadata_example.jsonld)
- Add verification tests
- Document assumptions and dependencies clearly

#### For Metadata:
All formal mathematical objects must include JSON-LD metadata with:
- `@context`: Standard vocabularies (DC, Schema.org, custom)
- `@id`: Unique identifier (URN)
- `@type`: Object type (theorem, proof, definition, axiom, etc.)
- `dc:title`: Human-readable title
- `dc:creator`: Author information
- `dc:date`: Creation/formalization date
- `checksum`: SHA-256 hash of the artifact
- `dependencies`: List of required theorems/axioms
- `formalizedIn`: Proof system information
- `verifiedBy`: Verification kernel information

### 4. Testing Your Changes

```bash
# Run linters
black . --check
flake8 .
isort . --check

# Run all tests
pytest tests/ -v

# Run specific test file
pytest tests/test_your_feature.py -v

# Validate metadata
python tools/verify_metadata.py schema/*.jsonld

# Test converter (if applicable)
python tools/convert_example.py formalization/lean/YourFile.lean
```

### 5. Committing Changes

```bash
# Stage your changes
git add .

# Commit with descriptive message
git commit -m "feat: add spectral operator formalization"

# Pre-commit hooks will run automatically
# Fix any issues they report
```

### 6. Pushing and Creating Pull Request

```bash
# Push your branch
git push origin feature/your-feature-name

# Create PR on GitHub with:
# - Clear description of changes
# - Reference to related issues
# - Test results and validation output
# - Screenshots (if UI changes)
```

## 📝 Pull Request Guidelines

### PR Description Template

```markdown
## Description
[Clear description of what this PR does]

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Mathematical formalization
- [ ] Documentation update
- [ ] CI/CD improvement

## Changes Made
- [List specific changes]

## Testing
- [ ] All tests pass
- [ ] New tests added (if applicable)
- [ ] Metadata validated
- [ ] Converter tested (if applicable)

## Checklist
- [ ] Code follows project style guidelines
- [ ] Documentation updated
- [ ] Tests added/updated
- [ ] All CI checks pass
- [ ] Metadata includes checksums
- [ ] Dependencies documented

## Related Issues
Closes #[issue number]
```

### Review Process

1. **Automated checks**: CI will run tests, linters, and validation
2. **Code review**: Maintainers will review code quality and correctness
3. **Mathematical review**: For formal content, experts will verify correctness
4. **Approval**: At least one maintainer approval required
5. **Merge**: Squash and merge after all checks pass

## 🔬 Adding Mathematical Content

### For Formal Proofs

1. **Choose proof assistant**: Lean 4 is preferred, but others are supported
2. **Place in correct directory**:
   - Lean: `formalization/lean/`
   - Coq: `formalization/coq/`
   - Isabelle: `formalization/isabelle/`

3. **Create metadata file**: 
   ```bash
   cp schema/metadata_example.jsonld schema/your_theorem.jsonld
   # Edit with your theorem's details
   ```

4. **Add conversion test**:
   ```bash
   python tools/convert_example.py formalization/lean/YourTheorem.lean \
       -o output/your_theorem.dk \
       -m schema/your_theorem.jsonld
   ```

5. **Add verification test**:
   ```python
   # In tests/test_your_theorem.py
   def test_your_theorem_verification():
       # Test that theorem verifies correctly
       assert verify_theorem("your_theorem")
   ```

### For Computational Validation

1. **Add to appropriate module**: Follow existing structure
2. **Include numerical tests**: Verify against known results
3. **Document precision**: Specify numerical precision requirements
4. **Add benchmark**: If performance-critical, add benchmark

## 🛠️ Tools and Scripts

### Metadata Validation
```bash
# Validate single file
python tools/verify_metadata.py schema/your_file.jsonld

# Validate all metadata
python tools/verify_metadata.py schema/*.jsonld
```

### Conversion Tools
```bash
# Convert Lean to intermediate
python tools/convert_example.py formalization/lean/Main.lean

# With output
python tools/convert_example.py input.lean -o output.dk -m output.jsonld
```

### Testing Tools
```bash
# Run specific test category
pytest tests/test_formalization*.py -v

# Run with coverage
pytest --cov=. --cov-report=html

# Run fast tests only
pytest -m "not slow"
```

## 📚 Documentation

- **Code comments**: Use docstrings for all public functions/classes
- **Mathematical notation**: Use LaTeX in docstrings and markdown
- **Examples**: Provide usage examples in docstrings
- **README updates**: Update README.md for user-facing changes

## 🐛 Reporting Bugs

Use GitHub Issues with the bug template:

```markdown
**Describe the bug**
A clear description of what the bug is.

**To Reproduce**
Steps to reproduce the behavior:
1. Go to '...'
2. Run '....'
3. See error

**Expected behavior**
What you expected to happen.

**Actual behavior**
What actually happened.

**Environment**
- OS: [e.g., Ubuntu 22.04]
- Python version: [e.g., 3.11]
- Package version: [e.g., 1.0.0]

**Additional context**
Any other context about the problem.
```

## 💡 Feature Requests

Use GitHub Issues with the feature template:

```markdown
**Is your feature request related to a problem?**
A clear description of the problem.

**Describe the solution you'd like**
A clear description of what you want to happen.

**Describe alternatives you've considered**
Alternative solutions or features you've considered.

**Additional context**
Any other context, screenshots, or examples.
```

## 🔐 Security

- **Never commit secrets**: No API keys, passwords, or tokens
- **Validate inputs**: All user inputs must be validated
- **Review dependencies**: Check dependencies for vulnerabilities
- **Report security issues**: Email security concerns privately to maintainers

## 📞 Getting Help

- **Documentation**: Check docs/ directory
- **Issues**: Search existing issues for similar problems
- **Discussions**: Use GitHub Discussions for questions
- **Discord**: Join our community Discord (link in README)

## 🙏 Recognition

Contributors are recognized in:
- CONTRIBUTORS.md file
- GitHub contributor graph
- Project documentation
- Academic citations (for significant mathematical contributions)

## 📜 License

By contributing, you agree that your contributions will be licensed under:
- **Code**: MIT License (LICENSE file)
- **Mathematical content**: CC BY 4.0 (LICENSE-CODE file)

---

Thank you for contributing to advancing mathematics and formal verification! 🎓✨

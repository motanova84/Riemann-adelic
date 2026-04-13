"""
Test CI Simbiótico SABIO workflow configuration.

This test validates that the CI workflow file is properly configured
and follows the expected structure for the SABIO ∞³ system.
"""

import yaml
import pytest
from pathlib import Path


def test_ci_workflow_exists():
    """Verify CI workflow file exists."""
    ci_file = Path('.github/workflows/ci.yml')
    assert ci_file.exists(), "CI workflow file should exist"


def test_ci_workflow_valid_yaml():
    """Verify CI workflow is valid YAML."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    assert config is not None, "CI workflow should be valid YAML"


def test_ci_workflow_name():
    """Verify CI workflow has the correct name."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    assert 'name' in config, "CI workflow should have a name"
    assert 'SABIO' in config['name'] or 'Simbiótico' in config['name'], \
        "CI workflow name should reference SABIO or Simbiótico"


def test_ci_workflow_triggers():
    """Verify CI workflow has all required triggers."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    # YAML parses 'on' as True
    triggers = config.get(True, {})
    
    assert 'push' in triggers, "CI should trigger on push"
    assert 'pull_request' in triggers, "CI should trigger on pull_request"
    assert 'workflow_dispatch' in triggers, "CI should support manual dispatch"


def test_ci_workflow_dispatch_input():
    """Verify workflow_dispatch has run_full_validation input."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    triggers = config.get(True, {})
    dispatch = triggers.get('workflow_dispatch', {})
    inputs = dispatch.get('inputs', {})
    
    assert 'run_full_validation' in inputs, \
        "workflow_dispatch should have run_full_validation input"
    
    input_config = inputs['run_full_validation']
    assert input_config.get('type') == 'choice', \
        "run_full_validation should be a choice input"
    assert input_config.get('default') == 'false', \
        "run_full_validation should default to false"
    assert 'true' in input_config.get('options', []), \
        "run_full_validation should have true option"
    assert 'false' in input_config.get('options', []), \
        "run_full_validation should have false option"


def test_ci_workflow_jobs():
    """Verify CI workflow has expected jobs."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    jobs = config.get('jobs', {})
    
    assert 'validacion-simbolica' in jobs, \
        "CI should have validacion-simbolica job"
    assert 'validate-metadata' in jobs, \
        "CI should have validate-metadata job"
    assert 'verify-conversion' in jobs, \
        "CI should have verify-conversion job"


def test_ci_validation_level_env():
    """Verify validacion-simbolica job has VALIDATION_LEVEL."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    job = config['jobs']['validacion-simbolica']
    env = job.get('env', {})
    
    assert 'VALIDATION_LEVEL' in env, \
        "validacion-simbolica should define VALIDATION_LEVEL"
    
    level_expr = env['VALIDATION_LEVEL']
    assert '500' in level_expr, "VALIDATION_LEVEL should reference 500"
    assert '100' in level_expr, "VALIDATION_LEVEL should reference 100"


def test_ci_workflow_steps():
    """Verify validacion-simbolica has all expected steps."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    job = config['jobs']['validacion-simbolica']
    steps = job.get('steps', [])
    
    step_names = [step.get('name', '') for step in steps]
    
    # Check for key steps
    assert any('Checkout' in name or 'checkout' in name.lower() 
               for name in step_names), \
        "Should have checkout step"
    
    assert any('Python' in name or 'python' in name.lower() 
               for name in step_names), \
        "Should have Python setup step"
    
    assert any('test' in name.lower() or 'validación' in name.lower() 
               for name in step_names), \
        "Should have test/validation step"
    
    assert any('reporte' in name.lower() or 'simbiótico' in name.lower() 
               for name in step_names), \
        "Should have symbiotic report step"


def test_ci_conditional_execution():
    """Verify steps have conditional execution based on validation level."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        config = yaml.safe_load(f)
    
    job = config['jobs']['validacion-simbolica']
    steps = job.get('steps', [])
    
    # Find test steps
    test_steps = [s for s in steps 
                  if 'test' in s.get('name', '').lower() 
                  or 'validación' in s.get('name', '').lower()]
    
    # Check that at least one has a conditional
    has_conditional = any('if' in step for step in test_steps)
    assert has_conditional, \
        "At least one test step should have conditional execution"


def test_ci_pytest_commands():
    """Verify pytest commands include proper flags."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        content = f.read()
    
    # Check for pytest with proper flags
    assert 'pytest' in content, "Workflow should use pytest"
    assert '--disable-warnings' in content, \
        "pytest should use --disable-warnings"
    assert '--maxfail' in content, "pytest should use --maxfail"
    assert 'not slow' in content, \
        "Basic validation should filter slow tests"


def test_ci_sabio_signature():
    """Verify workflow includes SABIO/QCAL signature."""
    ci_file = Path('.github/workflows/ci.yml')
    with open(ci_file) as f:
        content = f.read()
    
    # Check for QCAL/SABIO elements
    assert '141.7001' in content, "Should include QCAL frequency 141.7001 Hz"
    assert 'JMMB' in content or 'Ψ' in content, \
        "Should include JMMB signature"


def test_ci_documentation_exists():
    """Verify CI Simbiótico SABIO documentation exists."""
    doc_file = Path('CI_SIMBIOTICO_SABIO_README.md')
    assert doc_file.exists(), \
        "CI_SIMBIOTICO_SABIO_README.md should exist"


def test_ci_readme_references():
    """Verify README references the CI workflow."""
    readme = Path('README.md')
    assert readme.exists(), "README.md should exist"
    
    with open(readme) as f:
        content = f.read()
    
    assert 'CI Simbiótico SABIO' in content or 'ci.yml' in content, \
        "README should reference CI Simbiótico SABIO workflow"
    
    # Check for badge
    assert 'actions/workflows/ci.yml/badge.svg' in content, \
        "README should include CI workflow badge"

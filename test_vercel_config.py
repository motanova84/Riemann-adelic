#!/usr/bin/env python3
"""
Test suite for vercel.json configuration.
Validates the structure and content of the Vercel configuration file.
"""

import json
import os
import pytest


def test_vercel_json_exists():
    """Test that vercel.json exists in the repository root."""
    assert os.path.exists('vercel.json'), "vercel.json should exist in repository root"


def test_vercel_json_valid():
    """Test that vercel.json is valid JSON."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert isinstance(config, dict), "vercel.json should contain a JSON object"


def test_vercel_json_has_schema():
    """Test that vercel.json has the OpenAPI schema reference."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert '$schema' in config, "vercel.json should have $schema field"
    assert config['$schema'] == 'https://openapi.vercel.sh/vercel.json'


def test_vercel_json_has_clean_urls():
    """Test that vercel.json has cleanUrls configuration."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'cleanUrls' in config
    assert config['cleanUrls'] is True


def test_vercel_json_has_output_directory():
    """Test that vercel.json has outputDirectory set to 'public'."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'outputDirectory' in config
    assert config['outputDirectory'] == 'public'


def test_vercel_json_has_custom_headers():
    """Test that vercel.json has custom headers configured."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'headers' in config
    assert len(config['headers']) > 0
    
    # Check for Riemann-Adelic specific headers
    headers = config['headers'][0]['headers']
    header_keys = [h['key'] for h in headers]
    assert 'X-Riemann-Adelic-Validation' in header_keys
    assert 'X-QCAL-Frequency' in header_keys
    assert 'X-Noesis-Version' in header_keys


def test_vercel_json_has_rewrites():
    """Test that vercel.json has rewrites configured."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'rewrites' in config
    assert len(config['rewrites']) >= 3
    
    # Check specific rewrites
    rewrite_sources = [r['source'] for r in config['rewrites']]
    assert '/validate' in rewrite_sources
    assert '/demo' in rewrite_sources
    assert '/notebook' in rewrite_sources


def test_vercel_json_has_crons():
    """Test that vercel.json has cron jobs configured."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'crons' in config
    assert len(config['crons']) == 2
    
    # Check cron paths
    cron_paths = [c['path'] for c in config['crons']]
    assert '/api/validate-hourly' in cron_paths
    assert '/api/sync-riemann' in cron_paths


def test_vercel_json_has_functions_config():
    """Test that vercel.json has functions configuration."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'functions' in config
    assert 'api/*.py' in config['functions']
    assert 'notebooks/*.ipynb' in config['functions']


def test_api_pattern_matches_existing_files():
    """
    Test that the API function pattern correctly matches existing API files.
    
    This test prevents the common mistake of using 'api/**/*.py' which only
    matches files in subdirectories, not files directly in the api/ directory.
    The correct pattern is 'api/*.py' for files at the root level of api/.
    """
    import glob
    
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    
    # Get the API pattern from vercel.json
    functions_config = config.get('functions', {})
    api_patterns = [k for k in functions_config.keys() if k.startswith('api/') and k.endswith('.py')]
    
    assert len(api_patterns) > 0, "Should have at least one API pattern"
    
    # Verify the pattern matches actual files
    for pattern in api_patterns:
        matched_files = glob.glob(pattern)
        assert len(matched_files) > 0, f"Pattern '{pattern}' should match at least one file"
    
    # Verify we don't use the problematic 'api/**/*.py' pattern
    assert 'api/**/*.py' not in functions_config, \
        "Pattern 'api/**/*.py' only matches subdirectories, use 'api/*.py' instead"


def test_api_functions_are_valid_handlers():
    """Test that API functions have the correct handler structure for Vercel."""
    api_files = ['api/validate-hourly.py', 'api/sync-riemann.py']
    
    for api_file in api_files:
        with open(api_file, 'r') as f:
            content = f.read()
        
        # Check for required handler class
        assert 'class handler' in content, \
            f"{api_file} should define a 'handler' class for Vercel serverless functions"
        
        # Check for BaseHTTPRequestHandler
        assert 'BaseHTTPRequestHandler' in content, \
            f"{api_file} should extend BaseHTTPRequestHandler"


def test_vercel_json_has_regions():
    """Test that vercel.json has regions configured."""
    with open('vercel.json', 'r') as f:
        config = json.load(f)
    assert 'regions' in config
    assert 'fra1' in config['regions']
    assert 'iad1' in config['regions']
    assert 'gru1' in config['regions']


def test_referenced_files_exist():
    """Test that all files referenced in vercel.json exist."""
    # Check Python scripts
    assert os.path.exists('validate_v5_coronacion.py'), "validate_v5_coronacion.py should exist"
    assert os.path.exists('demo_paradigm_shift.py'), "demo_paradigm_shift.py should exist"
    
    # Check notebook
    assert os.path.exists('notebooks/validation.ipynb'), "notebooks/validation.ipynb should exist"
    
    # Check API endpoints
    assert os.path.exists('api/validate-hourly.py'), "api/validate-hourly.py should exist"
    assert os.path.exists('api/sync-riemann.py'), "api/sync-riemann.py should exist"


def test_api_scripts_are_executable():
    """Test that API scripts have executable permissions."""
    import stat
    
    for script in ['api/validate-hourly.py', 'api/sync-riemann.py']:
        st = os.stat(script)
        is_executable = bool(st.st_mode & stat.S_IXUSR)
        assert is_executable, f"{script} should be executable"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])

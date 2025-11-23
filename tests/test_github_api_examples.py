"""
Tests for GitHub API examples.
Tests basic functionality without actually calling the GitHub API.
"""
import sys
from pathlib import Path
from unittest.mock import Mock, patch
import pytest

# Add examples directory to path
examples_dir = Path(__file__).resolve().parents[1] / "examples"
sys.path.insert(0, str(examples_dir))


def test_github_api_example_imports():
    """Test that github_api_example.py imports without errors."""
    import github_api_example
    
    # Check that main functions exist
    assert hasattr(github_api_example, 'get_repository_info')
    assert hasattr(github_api_example, 'get_latest_release')
    assert hasattr(github_api_example, 'get_workflow_runs')
    assert hasattr(github_api_example, 'check_validation_status')
    assert hasattr(github_api_example, 'get_branches')
    assert hasattr(github_api_example, 'get_rate_limit')
    assert hasattr(github_api_example, 'main')


def test_monitor_validations_imports():
    """Test that monitor_validations.py imports without errors."""
    import monitor_validations
    
    # Check that main functions exist
    assert hasattr(monitor_validations, 'get_validation_status')
    assert hasattr(monitor_validations, 'check_specific_workflow')
    assert hasattr(monitor_validations, 'main')


def test_github_api_example_headers():
    """Test that headers are properly formatted."""
    import github_api_example
    
    headers = github_api_example.get_headers()
    
    # Check required headers
    assert 'Accept' in headers
    assert headers['Accept'] == 'application/vnd.github+json'
    assert 'X-GitHub-Api-Version' in headers


def test_monitor_validations_headers():
    """Test that headers are properly formatted."""
    import monitor_validations
    
    headers = monitor_validations.get_headers()
    
    # Check required headers
    assert 'Accept' in headers
    assert headers['Accept'] == 'application/vnd.github+json'


def test_github_api_example_constants():
    """Test that constants are properly defined."""
    import github_api_example
    
    assert github_api_example.REPO_OWNER == "motanova84"
    assert github_api_example.REPO_NAME == "-jmmotaburr-riemann-adelic"
    assert "motanova84/-jmmotaburr-riemann-adelic" in github_api_example.BASE_URL


def test_monitor_validations_constants():
    """Test that constants are properly defined."""
    import monitor_validations
    
    assert monitor_validations.REPO == "motanova84/-jmmotaburr-riemann-adelic"
    assert "motanova84/-jmmotaburr-riemann-adelic" in monitor_validations.API_BASE
    assert len(monitor_validations.VALIDATION_WORKFLOWS) > 0


@patch('github_api_example.requests.get')
def test_github_api_example_repository_info_mock(mock_get):
    """Test get_repository_info with mocked response."""
    import github_api_example
    
    # Mock successful response
    mock_response = Mock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        'full_name': 'motanova84/-jmmotaburr-riemann-adelic',
        'description': 'Test description',
        'stargazers_count': 10,
        'forks_count': 5,
        'open_issues_count': 2,
        'default_branch': 'main',
        'language': 'Python',
        'created_at': '2025-01-01T00:00:00Z',
        'updated_at': '2025-01-01T00:00:00Z',
        'html_url': 'https://github.com/motanova84/-jmmotaburr-riemann-adelic'
    }
    mock_get.return_value = mock_response
    
    # Call the function (it prints, so we just check it doesn't error)
    try:
        github_api_example.get_repository_info()
    except Exception as e:
        pytest.fail(f"get_repository_info raised an exception: {e}")


@patch('monitor_validations.requests.get')
def test_monitor_validations_status_mock(mock_get):
    """Test get_validation_status with mocked response."""
    import monitor_validations
    
    # Mock successful response
    mock_response = Mock()
    mock_response.status_code = 200
    mock_response.json.return_value = {
        'workflow_runs': [
            {
                'name': 'V5 Coronación Proof Check',
                'status': 'completed',
                'conclusion': 'success',
                'head_branch': 'main',
                'created_at': '2025-01-01T00:00:00Z',
                'html_url': 'https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/runs/1'
            }
        ]
    }
    mock_get.return_value = mock_response
    
    # Call the function
    exit_code = monitor_validations.get_validation_status()
    
    # Should return 0 (success) since we have a successful validation
    assert exit_code == 0


def test_github_api_quickstart_exists():
    """Test that the quickstart guide exists."""
    quickstart_path = Path(__file__).resolve().parents[1] / "GITHUB_API_QUICKSTART.md"
    assert quickstart_path.exists(), "GITHUB_API_QUICKSTART.md should exist"
    
    # Check that it has reasonable content
    content = quickstart_path.read_text()
    assert "GitHub REST API" in content
    assert "motanova84/-jmmotaburr-riemann-adelic" in content
    assert "curl" in content or "GitHub CLI" in content


def test_examples_readme_exists():
    """Test that the examples README exists."""
    readme_path = examples_dir / "README.md"
    assert readme_path.exists(), "examples/README.md should exist"
    
    # Check that it has reasonable content
    content = readme_path.read_text()
    assert "github_api_example.py" in content
    assert "monitor_validations.py" in content


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

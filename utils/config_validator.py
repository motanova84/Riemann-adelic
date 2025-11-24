#!/usr/bin/env python3
"""
Configuration validation utilities for Riemann-Adelic repository.

This module provides functions to validate parameters and configurations
used across different validation scripts.
"""

from typing import Dict, Any, Tuple, Optional
import mpmath as mp


def validate_precision(dps: int) -> Tuple[bool, str]:
    """
    Validate precision parameter.
    
    Args:
        dps: Decimal places for mpmath precision
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    if not isinstance(dps, int):
        return False, "Precision must be an integer"
    if dps < 10:
        return False, "Precision must be at least 10 decimal places"
    if dps > 100:
        return False, "Precision cannot exceed 100 decimal places (performance limit)"
    return True, ""


def validate_computational_params(max_primes: int, max_zeros: int, 
                                integration_t: float) -> Tuple[bool, str]:
    """
    Validate computational parameters.
    
    Args:
        max_primes: Maximum number of primes to use
        max_zeros: Maximum number of zeros to use  
        integration_t: Integration limit parameter
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    if max_primes <= 0:
        return False, "max_primes must be positive"
    if max_primes > 100000:
        return False, "max_primes cannot exceed 100,000 (memory limit)"
    
    if max_zeros <= 0:
        return False, "max_zeros must be positive"
    if max_zeros > 50000:
        return False, "max_zeros cannot exceed 50,000 (performance limit)"
    
    if integration_t <= 0:
        return False, "integration_t must be positive"
    if integration_t > 1000:
        return False, "integration_t cannot exceed 1000 (convergence limit)"
    
    return True, ""


def validate_test_function(func_name: str) -> Tuple[bool, str]:
    """
    Validate test function name.
    
    Args:
        func_name: Name of the test function
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    valid_functions = ['f1', 'f2', 'f3', 'truncated_gaussian', 'gaussian']
    if func_name not in valid_functions:
        return False, f"Invalid test function. Must be one of: {valid_functions}"
    return True, ""


def validate_config(config: Dict[str, Any]) -> Tuple[bool, str]:
    """
    Validate a complete configuration dictionary.
    
    Args:
        config: Configuration dictionary
        
    Returns:
        Tuple of (is_valid, error_message)
    """
    # Check required keys
    required_keys = ['precision_dps', 'max_primes', 'max_zeros', 'integration_t']
    for key in required_keys:
        if key not in config:
            return False, f"Missing required configuration key: {key}"
    
    # Validate precision
    is_valid, error = validate_precision(config['precision_dps'])
    if not is_valid:
        return False, f"Precision validation failed: {error}"
    
    # Validate computational parameters
    is_valid, error = validate_computational_params(
        config['max_primes'], 
        config['max_zeros'], 
        config['integration_t']
    )
    if not is_valid:
        return False, f"Parameter validation failed: {error}"
    
    # Validate test functions if provided
    if 'test_functions' in config:
        for func_name in config['test_functions']:
            is_valid, error = validate_test_function(func_name)
            if not is_valid:
                return False, f"Test function validation failed: {error}"
    
    return True, ""


def get_safe_defaults() -> Dict[str, Any]:
    """
    Get safe default configuration values.
    
    Returns:
        Dictionary with safe default values
    """
    return {
        'precision_dps': 15,
        'max_primes': 1000,
        'max_zeros': 1000,
        'integration_t': 20,
        'test_functions': ['truncated_gaussian'],
        'timeout': 300
    }


def apply_config_with_validation(config: Dict[str, Any]) -> None:
    """
    Apply configuration with validation.
    
    Args:
        config: Configuration dictionary
        
    Raises:
        ValueError: If configuration is invalid
    """
    is_valid, error = validate_config(config)
    if not is_valid:
        raise ValueError(f"Invalid configuration: {error}")
    
    # Apply precision setting
    mp.mp.dps = config['precision_dps']
    
    print(f"✅ Configuration validated and applied:")
    print(f"   Precision: {config['precision_dps']} decimal places")
    print(f"   Max primes: {config['max_primes']}")
    print(f"   Max zeros: {config['max_zeros']}")
    print(f"   Integration T: {config['integration_t']}")
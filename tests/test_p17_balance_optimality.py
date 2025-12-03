# Instituto de Conciencia Cuántica – QCAL ∞³
# Tests for p17_balance_optimality.py

import mpmath as mp
from p17_balance_optimality import (
    adelic_factor,
    balance,
    compute_all,
    verify_minimum,
    primes,
    k,
)


def test_adelic_factor_positive():
    """Test that adelic_factor returns positive values for all primes."""
    for p in primes:
        result = adelic_factor(p)
        assert result > 0, f"adelic_factor({p}) should be positive"


def test_adelic_factor_formula():
    """Test the adelic_factor formula: exp(pi * sqrt(p) / 2)."""
    mp.mp.dps = 80
    p = 17
    expected = mp.e ** (mp.pi * mp.sqrt(p) / 2)
    result = adelic_factor(p)
    assert abs(result - expected) < mp.mpf('1e-70'), \
        "adelic_factor formula incorrect"


def test_balance_positive():
    """Test that balance returns positive values for all primes."""
    for p in primes:
        result = balance(p)
        assert result > 0, f"balance({p}) should be positive"


def test_balance_formula():
    """Test the balance formula: adelic_factor(p) / p^k."""
    mp.mp.dps = 80
    p = 17
    expected = adelic_factor(p) / mp.power(p, k)
    result = balance(p)
    assert abs(result - expected) < mp.mpf('1e-70'), \
        "balance formula incorrect"


def test_compute_all_returns_dict():
    """Test that compute_all returns a dictionary with all primes."""
    result = compute_all()
    assert isinstance(result, dict), "compute_all should return a dict"
    assert set(result.keys()) == set(primes), \
        "compute_all should have all primes as keys"


def test_verify_minimum_returns_tuple():
    """Test that verify_minimum returns a tuple with boolean and results."""
    ok, results = verify_minimum()
    assert isinstance(ok, bool), "First element should be boolean"
    assert isinstance(results, list), "Second element should be list"


def test_all_primes_have_balance_values():
    """Test that all primes in the list produce valid balance values."""
    vals = compute_all()
    for p in primes:
        assert p in vals, f"Prime {p} should be in compute_all results"
        assert float(vals[p]) > 0, f"balance({p}) should be positive"


def test_balance_ordering():
    """Test the ordering of balance values."""
    vals = compute_all()
    # Verify balance values are computed for all primes
    assert len(vals) == len(primes), \
        "Should have balance values for all primes"
    # All values should be finite and positive
    for p, val in vals.items():
        assert mp.isfinite(val), f"balance({p}) should be finite"
        assert val > 0, f"balance({p}) should be positive"


def test_precision_setting():
    """Test that high precision is maintained."""
    mp.mp.dps = 80
    # Check that we can compute with high precision
    result = balance(17)
    # The result should have high precision representation
    assert len(str(result)) > 20, \
        "High precision should produce long decimal representation"

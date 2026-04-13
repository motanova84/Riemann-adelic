#!/usr/bin/env python3
"""
Tests for πCODE emission system
"""

import sys
import os
from pathlib import Path

# Add the picode_emission module to the path
sys.path.insert(0, str(Path(__file__).parent))

from picode_emission import PiCodeCoin, PiCodeEconomy, ZetaResonance


def test_coin_creation():
    """Test creating a πCODE coin"""
    zero = complex(0.5, 14.134725)
    coherence = 0.999999
    frequency = 141.7001
    
    coin = PiCodeCoin.from_zeta_zero(zero, coherence, frequency)
    
    assert coin.zero_real == 0.5
    assert coin.zero_imag == 14.134725
    assert coin.coherence == coherence
    assert coin.frequency == frequency
    assert len(coin.vibrational_hash) == 64  # SHA256 hex digest
    
    print("✓ test_coin_creation passed")


def test_coin_verification():
    """Test coin verification"""
    zero = complex(0.5, 14.134725)
    coin = PiCodeCoin.from_zeta_zero(zero, 0.999999, 141.7001)
    
    verification = coin.verify()
    
    assert verification['hash_valid'] == True
    assert verification['coherence_valid'] == True
    assert verification['frequency_valid'] == True
    assert verification['overall_valid'] == True
    
    print("✓ test_coin_verification passed")


def test_coin_value_calculation():
    """Test economic value calculation"""
    zero = complex(0.5, 14.134725)
    coin = PiCodeCoin.from_zeta_zero(zero, 0.999999, 141.7001)
    
    coin_dict = coin.to_dict()
    value = coin_dict['economic_value']
    
    assert 'base_value' in value
    assert 'coherence_bonus' in value
    assert 'resonance_bonus' in value
    assert 'position_bonus' in value
    assert 'total_value' in value
    assert value['currency'] == 'πCOIN'
    assert value['total_value'] > 0
    
    print("✓ test_coin_value_calculation passed")


def test_economy_creation():
    """Test creating a πCODE economy"""
    import tempfile
    
    fd, ledger_file = tempfile.mkstemp(suffix='.json')
    os.close(fd)  # Close file descriptor
    os.unlink(ledger_file)  # Delete the empty file
    
    try:
        economy = PiCodeEconomy(ledger_file=ledger_file)
        assert economy.base_frequency == 141.7001
        assert economy.coherence_threshold == 0.999999
        
        print("✓ test_economy_creation passed")
    finally:
        if os.path.exists(ledger_file):
            os.unlink(ledger_file)


def test_coin_emission():
    """Test emitting a coin into the economy"""
    import tempfile
    
    fd, ledger_file = tempfile.mkstemp(suffix='.json')
    os.close(fd)  # Close file descriptor
    os.unlink(ledger_file)  # Delete the empty file
    
    try:
        economy = PiCodeEconomy(ledger_file=ledger_file)
        
        zero = complex(0.5, 14.134725)
        coin = economy.emit_coin(zero, 0.999999, 141.7001)
        
        assert coin is not None
        
        # Check ledger
        stats = economy.get_economy_stats()
        assert stats['total_coins'] == 1
        assert stats['total_value'] > 0
        
        print("✓ test_coin_emission passed")
    finally:
        if os.path.exists(ledger_file):
            os.unlink(ledger_file)


def test_economy_stats():
    """Test economy statistics"""
    import tempfile
    
    fd, ledger_file = tempfile.mkstemp(suffix='.json')
    os.close(fd)  # Close file descriptor
    os.unlink(ledger_file)  # Delete the empty file
    
    try:
        economy = PiCodeEconomy(ledger_file=ledger_file)
        
        # Emit multiple coins
        for n in range(1, 4):
            t = 14.134725 + n * 10
            zero = complex(0.5, t)
            economy.emit_coin(zero, 0.999999, 141.7001)
        
        stats = economy.get_economy_stats()
        
        assert stats['total_coins'] == 3
        assert stats['average_coherence'] > 0.99
        assert 'health_status' in stats
        assert stats['economy_health'] > 0
        
        print("✓ test_economy_stats passed")
    finally:
        if os.path.exists(ledger_file):
            os.unlink(ledger_file)


def test_zeta_resonance():
    """Test ZetaResonance frequency mapping"""
    resonance = ZetaResonance()
    
    zero = complex(0.5, 14.134725)
    frequency = resonance.zero_to_frequency(zero)
    
    # Should be close to base frequency
    assert abs(frequency - 141.7001) < 15.0  # Within reasonable range
    
    print("✓ test_zeta_resonance passed")


def test_nft_metadata():
    """Test NFT metadata generation"""
    zero = complex(0.5, 14.134725)
    coin = PiCodeCoin.from_zeta_zero(zero, 0.999999, 141.7001)
    
    metadata = coin.nft_metadata
    
    assert 'name' in metadata
    assert 'description' in metadata
    assert 'attributes' in metadata
    assert isinstance(metadata['attributes'], list)
    assert len(metadata['attributes']) >= 4
    
    print("✓ test_nft_metadata passed")


def main():
    """Run all tests"""
    print("🧪 Testing πCODE Emission System")
    print("=" * 60)
    
    tests = [
        test_coin_creation,
        test_coin_verification,
        test_coin_value_calculation,
        test_economy_creation,
        test_coin_emission,
        test_economy_stats,
        test_zeta_resonance,
        test_nft_metadata,
    ]
    
    failed = 0
    for test in tests:
        try:
            test()
        except AssertionError as e:
            print(f"✗ {test.__name__} failed: {e}")
            failed += 1
        except Exception as e:
            print(f"✗ {test.__name__} error: {e}")
            failed += 1
    
    print("=" * 60)
    if failed == 0:
        print(f"✅ All {len(tests)} tests passed!")
        return 0
    else:
        print(f"❌ {failed}/{len(tests)} tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())

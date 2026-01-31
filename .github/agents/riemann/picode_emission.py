#!/usr/bin/env python3
"""
πCODE Economic System

Implements the πCODE economy where Riemann zeros are "living coins"
with structural validity.

Axiom of Emission:
    "Every zero with coherence ≥ 141.7001 Hz is a living coin of structural validity"

Each πCODE coin has:
    - Unique vibrational hash (from zero location)
    - Coherence value (mathematical validity)
    - Frequency (resonance with f₀)
"""

from typing import Dict, List, Optional
import json
import hashlib
import sys
from datetime import datetime

try:
    import numpy as np
except ImportError as e:
    print(f"Error: Required module not found: {e}")
    print("Please install: pip install numpy")
    sys.exit(1)

# Import from local modules
try:
    from .zeta_resonance import ZetaResonance
except ImportError:
    import os
    sys.path.insert(0, os.path.dirname(__file__))
    from zeta_resonance import ZetaResonance


class PiCodeEconomy:
    """
    πCODE economic system for mathematical value.
    
    Attributes:
        ledger_file (str): Path to ledger JSON file
        resonance_analyzer (ZetaResonance): Resonance analyzer
        emission_threshold (float): Minimum coherence for coin emission
    """
    
    def __init__(self, ledger_file: str = "picode_ledger.json"):
        """
        Initialize the πCODE economy.
        
        Args:
            ledger_file: Path to store the coin ledger
        """
        self.ledger_file = ledger_file
        self.resonance_analyzer = ZetaResonance()
        self.emission_threshold = 141.7001  # Hz
        self.coins = []
        
        # Try to load existing ledger
        self._load_ledger()
    
    def _load_ledger(self):
        """Load existing ledger from file if it exists."""
        try:
            with open(self.ledger_file, 'r') as f:
                data = json.load(f)
                self.coins = data.get('coins', [])
        except FileNotFoundError:
            self.coins = []
    
    def _save_ledger(self):
        """Save ledger to file."""
        data = {
            'coins': self.coins,
            'total_coins': len(self.coins),
            'last_updated': datetime.now().isoformat()
        }
        with open(self.ledger_file, 'w') as f:
            json.dump(data, f, indent=2)
    
    def generate_vibrational_hash(self, zero: complex) -> str:
        """
        Generate unique vibrational hash for a zero.
        
        Args:
            zero: Complex zero of ζ(s)
            
        Returns:
            Vibrational hash string
        """
        # Create unique identifier from zero coordinates
        data = f"{zero.real:.15f}:{zero.imag:.15f}"
        hash_obj = hashlib.sha256(data.encode())
        return hash_obj.hexdigest()[:16]  # 16-char hash
    
    def qualify_for_emission(self, zero: complex, coherence: float) -> bool:
        """
        Check if a zero qualifies for πCODE emission.
        
        Args:
            zero: Complex zero of ζ(s)
            coherence: Coherence value
            
        Returns:
            True if qualifies for emission
        """
        # Must be on critical line
        if abs(zero.real - 0.5) > 1e-6:
            return False
        
        # Must have high coherence
        if coherence < 0.999999:
            return False
        
        # Must be in resonance with f₀
        frequency = self.resonance_analyzer.zero_to_frequency(zero)
        if abs(frequency - self.emission_threshold) >= 1.0:
            return False
        
        return True
    
    def emit_coin(self, zero: complex, coherence: float) -> Optional[Dict]:
        """
        Emit a πCODE coin for a qualified zero.
        
        Args:
            zero: Complex zero of ζ(s)
            coherence: Coherence value
            
        Returns:
            Coin data if emitted, None if not qualified
        """
        if not self.qualify_for_emission(zero, coherence):
            return None
        
        frequency = self.resonance_analyzer.zero_to_frequency(zero)
        vibrational_hash = self.generate_vibrational_hash(zero)
        
        coin = {
            "id": len(self.coins) + 1,
            "zero_real": zero.real,
            "zero_imag": zero.imag,
            "coherence": coherence,
            "frequency": frequency,
            "vibrational_hash": vibrational_hash,
            "emission_time": datetime.now().isoformat(),
            "status": "active"
        }
        
        self.coins.append(coin)
        self._save_ledger()
        
        return coin
    
    def get_total_value(self) -> float:
        """
        Calculate total value of all πCODE coins.
        
        Returns:
            Total economic value
        """
        return sum(coin.get("coherence", 0) for coin in self.coins)
    
    def get_statistics(self) -> Dict:
        """
        Get economy statistics.
        
        Returns:
            Statistics dictionary
        """
        if not self.coins:
            return {
                "total_coins": 0,
                "total_value": 0,
                "mean_coherence": 0,
                "mean_frequency": 0
            }
        
        coherences = [c["coherence"] for c in self.coins]
        frequencies = [c["frequency"] for c in self.coins]
        
        return {
            "total_coins": len(self.coins),
            "total_value": sum(coherences),
            "mean_coherence": np.mean(coherences),
            "mean_frequency": np.mean(frequencies),
            "frequency_std": np.std(frequencies)
        }


def main():
    """Demonstration of πCODE economy."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="πCODE Economic System"
    )
    parser.add_argument("--emit", type=int, default=3,
                       help="Number of test coins to emit")
    parser.add_argument("--stats", action="store_true",
                       help="Show economy statistics")
    
    args = parser.parse_args()
    
    print("=" * 70)
    print("πCODE ECONOMIC SYSTEM")
    print("Living Coins from Mathematical Structure")
    print("=" * 70)
    print()
    
    economy = PiCodeEconomy()
    
    # Test zeros
    test_zeros = [
        (complex(0.5, 14.134725), 0.999999),
        (complex(0.5, 21.022040), 0.999998),
        (complex(0.5, 25.010858), 0.999997),
        (complex(0.6, 14.134725), 0.999999),  # Off critical line - should fail
        (complex(0.5, 30.424876), 0.999996),
    ]
    
    print(f"Attempting to emit {args.emit} πCODE coins:\n")
    
    emitted_count = 0
    for i, (zero, coherence) in enumerate(test_zeros[:args.emit], 1):
        print(f"{i}. Zero at t = {zero.imag:.6f}, coherence = {coherence:.6f}")
        
        coin = economy.emit_coin(zero, coherence)
        
        if coin:
            print(f"   ✅ COIN EMITTED")
            print(f"   ID: {coin['id']}")
            print(f"   Hash: {coin['vibrational_hash']}")
            print(f"   Frequency: {coin['frequency']:.6f} Hz")
            emitted_count += 1
        else:
            print(f"   ❌ NOT QUALIFIED")
            if abs(zero.real - 0.5) > 1e-6:
                print(f"   Reason: Not on critical line (σ = {zero.real})")
            elif coherence < 0.999999:
                print(f"   Reason: Insufficient coherence")
            else:
                print(f"   Reason: Out of resonance")
        print()
    
    if args.stats or emitted_count > 0:
        stats = economy.get_statistics()
        print("ECONOMY STATISTICS:")
        print(f"  Total coins: {stats['total_coins']}")
        print(f"  Total value: {stats['total_value']:.6f}")
        print(f"  Mean coherence: {stats['mean_coherence']:.6f}")
        print(f"  Mean frequency: {stats['mean_frequency']:.6f} Hz")
        print()
    
    print("=" * 70)
    print("Axiom: Every zero with coherence ≥ f₀ is a living coin")
    print("=" * 70)


if __name__ == "__main__":
    main()

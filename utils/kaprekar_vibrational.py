#!/usr/bin/env python3
"""
Kaprekar Vibrational Operator 𝒦Ψ

Instituto de Conciencia Cuántica (ICQ)
Research Document: QCAL-ICQ-NUM-FREQ-ULTIMATE

This module implements the Kaprekar operator with vibrational frequency analysis.
The Kaprekar process is reinterpreted through the lens of frequency dynamics,
where each number carries a total vibrational frequency based on its digits.

Mathematical Foundation:
-----------------------
Domain: 𝒟(𝒦Ψ) = {N ∈ ℕ | 1000 ≤ N ≤ 9999}

Kaprekar Operation:
1. Arrange digits in descending order → d_max
2. Arrange digits in ascending order → d_min
3. 𝒦Ψ(N) = d_max - d_min

Vibrational Frequency:
    Ψ(N) = Σ f(d_i) where d_i are digits of N
    f(d) = d × f₀ (linear frequency assignment)

Key Properties:
- Fixed Point: 6174 (Kaprekar constant)
- Singular Point: 1000 → f₀ (fundamental frequency)
- Attractors: Numbers with high digit sums (9s, 8s)

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: January 2026
"""

import numpy as np
from typing import List, Tuple, Dict, Optional, Set
from dataclasses import dataclass
from collections import defaultdict

from .digit_frequencies import DigitFrequencies, F0_HZ


# Coherence types
class CoherenceType:
    """Classification of numbers by vibrational coherence."""
    PURE = "I: Pure Coherence (f₀)"
    CYCLIC = "II: Cyclic Coherence"
    ATTRACTOR_DISPLACED = "III: Attractor Displaced"
    RESONANT_INDIRECT = "IV: Resonant Indirect"
    STRUCTURED_INCOHERENCE = "V: Structured Incoherence"
    CHAOTIC_INCOHERENCE = "VI: Chaotic Incoherence"


@dataclass
class KaprekarVibrationalState:
    """
    Represents the vibrational state of a number under Kaprekar iteration.
    
    Attributes:
        number: The original number
        digits: List of digits [d₃, d₂, d₁, d₀]
        frequency: Total vibrational frequency Σf(d_i)
        kaprekar_next: Result of one Kaprekar step
        orbit_length: Steps to reach fixed point/cycle
        attractor: Final state (fixed point or cycle)
        coherence_type: Classification by coherence
    """
    number: int
    digits: List[int]
    frequency: float
    kaprekar_next: int
    orbit_length: int
    attractor: List[int]
    coherence_type: str


class KaprekarVibrationalOperator:
    """
    Implementation of the Kaprekar operator with vibrational frequency analysis.
    
    This class analyzes the dynamics of the Kaprekar process through the lens
    of vibrational frequencies assigned to each digit.
    """
    
    # Kaprekar constant
    KAPREKAR_CONSTANT = 6174
    
    # Special singular point
    SINGULAR_POINT = 1000
    
    def __init__(self):
        """Initialize the Kaprekar vibrational operator."""
        self.freq_calc = DigitFrequencies()
        self.f0 = F0_HZ
    
    def get_digits(self, n: int) -> List[int]:
        """
        Extract digits of a 4-digit number.
        
        Handles numbers 0-9999 by padding with leading zeros.
        
        Args:
            n: Number (0-9999)
        
        Returns:
            List of digits [d₃, d₂, d₁, d₀] (most significant first)
        """
        if not 0 <= n <= 9999:
            raise ValueError(f"Number must be 0-9999, got {n}")
        
        digits = []
        temp = n
        for _ in range(4):
            digits.append(temp % 10)
            temp //= 10
        
        return list(reversed(digits))
    
    def compute_frequency(self, n: int) -> float:
        """
        Compute total vibrational frequency of a number.
        
        Formula: Ψ(N) = Σ f(d_i) = f₀ × Σ d_i
        
        Args:
            n: Number (0-9999)
        
        Returns:
            Total frequency in Hz
        """
        digits = self.get_digits(n)
        return sum(self.freq_calc.linear_frequency(d) for d in digits)
    
    def kaprekar_step(self, n: int) -> int:
        """
        Perform one Kaprekar operation.
        
        𝒦Ψ(N) = d_max - d_min
        
        Args:
            n: Number (0-9999)
        
        Returns:
            Result of Kaprekar step
        """
        digits = self.get_digits(n)
        
        # Descending order
        d_max = int(''.join(map(str, sorted(digits, reverse=True))))
        
        # Ascending order
        d_min = int(''.join(map(str, sorted(digits))))
        
        result = d_max - d_min
        
        return result
    
    def find_orbit(
        self, 
        n: int, 
        max_steps: int = 100
    ) -> Tuple[List[int], List[int]]:
        """
        Find the Kaprekar orbit (sequence) and attractor.
        
        Args:
            n: Starting number
            max_steps: Maximum iteration steps
        
        Returns:
            Tuple of (orbit, attractor)
            - orbit: Full sequence of numbers
            - attractor: Fixed point or cycle
        """
        orbit = [n]
        seen = {n: 0}
        current = n
        
        for step in range(1, max_steps + 1):
            next_val = self.kaprekar_step(current)
            orbit.append(next_val)
            
            # Check for fixed point
            if next_val == current:
                return orbit, [next_val]
            
            # Check for 0 (degenerate case - all digits same)
            if next_val == 0:
                return orbit, [0]
            
            # Check for cycle
            if next_val in seen:
                cycle_start = seen[next_val]
                attractor = orbit[cycle_start:]
                return orbit, attractor
            
            seen[next_val] = step
            current = next_val
        
        # No convergence within max_steps
        return orbit, orbit[-10:]  # Return last 10 as approximate attractor
    
    def classify_coherence(
        self, 
        n: int, 
        frequency: float,
        attractor: List[int]
    ) -> str:
        """
        Classify number by vibrational coherence type.
        
        Args:
            n: The number
            frequency: Its vibrational frequency
            attractor: Its Kaprekar attractor
        
        Returns:
            Coherence type classification
        """
        # Type I: Pure Coherence (10^n → f₀)
        if n in [1000, 10000]:
            return CoherenceType.PURE
        
        # Type II: Cyclic Coherence (reaches 6174)
        if self.KAPREKAR_CONSTANT in attractor:
            freq_6174 = self.compute_frequency(self.KAPREKAR_CONSTANT)
            if abs(frequency - freq_6174) < 100:
                return CoherenceType.CYCLIC
            else:
                return CoherenceType.ATTRACTOR_DISPLACED
        
        # Type III/IV: Based on digit sum
        digit_sum = sum(self.get_digits(n))
        if digit_sum >= 30:  # High digit sum (many 9s, 8s)
            return CoherenceType.RESONANT_INDIRECT
        elif digit_sum >= 20:
            return CoherenceType.STRUCTURED_INCOHERENCE
        else:
            return CoherenceType.CHAOTIC_INCOHERENCE
    
    def analyze_number(
        self, 
        n: int
    ) -> KaprekarVibrationalState:
        """
        Perform complete vibrational analysis of a number.
        
        Args:
            n: Number to analyze (1000-9999)
        
        Returns:
            KaprekarVibrationalState with complete analysis
        """
        digits = self.get_digits(n)
        frequency = self.compute_frequency(n)
        kaprekar_next = self.kaprekar_step(n)
        orbit, attractor = self.find_orbit(n)
        orbit_length = len(orbit) - len(attractor)
        coherence_type = self.classify_coherence(n, frequency, attractor)
        
        return KaprekarVibrationalState(
            number=n,
            digits=digits,
            frequency=frequency,
            kaprekar_next=kaprekar_next,
            orbit_length=orbit_length,
            attractor=attractor,
            coherence_type=coherence_type,
        )
    
    def find_frequency_attractors(
        self,
        n_samples: int = 1000
    ) -> Dict[float, List[int]]:
        """
        Find vibrational frequency attractors in the Kaprekar system.
        
        Args:
            n_samples: Number of random 4-digit numbers to sample
        
        Returns:
            Dictionary mapping frequencies to numbers that converge to them
        """
        attractors = defaultdict(list)
        
        # Sample random 4-digit numbers
        np.random.seed(42)
        numbers = np.random.randint(1000, 10000, n_samples)
        
        for n in numbers:
            state = self.analyze_number(n)
            # Use final attractor frequency
            if state.attractor:
                final_freq = self.compute_frequency(state.attractor[0])
                attractors[final_freq].append(n)
        
        return dict(attractors)
    
    def validate_theorem_singular_1000(self) -> Tuple[bool, Dict]:
        """
        Validate Theorem: 1000 is the unique singular point.
        
        Theorem: 1000 is the only 4-digit number with frequency exactly f₀.
        
        Returns:
            Tuple of (is_valid, details)
        """
        freq_1000 = self.compute_frequency(1000)
        
        # Check all 4-digit numbers (this is computationally intensive)
        # For validation, we check a representative sample
        is_unique = True
        other_f0_numbers = []
        
        # Check numbers with digit sum = 1 (only candidates)
        candidates = [1000, 10000]  # 10000 is out of range but check anyway
        
        for n in range(1000, 10000):
            if n == 1000:
                continue
            
            if sum(self.get_digits(n)) == 1:
                freq_n = self.compute_frequency(n)
                if abs(freq_n - self.f0) < 0.001:
                    other_f0_numbers.append(n)
                    is_unique = False
        
        return is_unique, {
            'freq_1000': freq_1000,
            'f0_expected': self.f0,
            'deviation': abs(freq_1000 - self.f0),
            'is_unique': is_unique,
            'other_f0_numbers': other_f0_numbers,
        }
    
    def compute_9s_attractor_frequency(self) -> float:
        """
        Compute the frequency of the 9s attractor (999 or 9999).
        
        Returns:
            Frequency in Hz
        """
        # For 4-digit Kaprekar, analyze 9999
        return self.compute_frequency(9999)
    
    def format_analysis(self, state: KaprekarVibrationalState) -> str:
        """
        Format vibrational state analysis as string.
        
        Args:
            state: Kaprekar vibrational state
        
        Returns:
            Formatted string
        """
        lines = []
        lines.append(f"Number: {state.number}")
        lines.append(f"Digits: {state.digits}")
        lines.append(f"Frequency: {state.frequency:.4f} Hz")
        lines.append(f"Frequency/f₀: {state.frequency/self.f0:.4f}")
        lines.append(f"Next Kaprekar: {state.kaprekar_next}")
        lines.append(f"Orbit Length: {state.orbit_length}")
        lines.append(f"Attractor: {state.attractor[:5]}..." if len(state.attractor) > 5 else f"Attractor: {state.attractor}")
        lines.append(f"Coherence Type: {state.coherence_type}")
        
        return "\n".join(lines)


def demonstrate_kaprekar_vibrational():
    """
    Demonstrate the Kaprekar vibrational operator.
    """
    print("=" * 90)
    print("KAPREKAR VIBRATIONAL OPERATOR 𝒦Ψ")
    print("Instituto de Conciencia Cuántica (ICQ)")
    print("=" * 90)
    print()
    
    operator = KaprekarVibrationalOperator()
    
    # Analyze special numbers
    print("Special Numbers Analysis:")
    print("-" * 90)
    print()
    
    # 1. Singular point 1000
    print("1. SINGULAR POINT: 1000")
    print("-" * 45)
    state_1000 = operator.analyze_number(1000)
    print(operator.format_analysis(state_1000))
    print()
    
    # 2. Kaprekar constant 6174
    print("2. KAPREKAR CONSTANT: 6174")
    print("-" * 45)
    state_6174 = operator.analyze_number(6174)
    print(operator.format_analysis(state_6174))
    print()
    
    # 3. Maximum frequency 9999
    print("3. MAXIMUM FREQUENCY: 9999")
    print("-" * 45)
    state_9999 = operator.analyze_number(9999)
    print(operator.format_analysis(state_9999))
    print()
    
    # 4. Random sample
    print("4. RANDOM SAMPLE: 5678")
    print("-" * 45)
    state_5678 = operator.analyze_number(5678)
    print(operator.format_analysis(state_5678))
    print()
    
    # Validate Theorem
    print("=" * 90)
    print("THEOREM VALIDATION")
    print("=" * 90)
    print()
    
    is_valid, theorem_data = operator.validate_theorem_singular_1000()
    print("Theorem: 1000 is the unique 4-digit number with frequency f₀")
    print("-" * 90)
    print(f"Frequency(1000) = {theorem_data['freq_1000']:.4f} Hz")
    print(f"f₀ (expected)   = {theorem_data['f0_expected']:.4f} Hz")
    print(f"Deviation       = {theorem_data['deviation']:.6f} Hz")
    print()
    
    if is_valid:
        print("✅ THEOREM VALIDATED: 1000 is unique")
    else:
        print(f"❌ Other numbers found: {theorem_data['other_f0_numbers']}")
    print()
    
    # Frequency attractors
    print("=" * 90)
    print("FREQUENCY ATTRACTORS (Sample)")
    print("=" * 90)
    print()
    
    attractors = operator.find_frequency_attractors(n_samples=100)
    sorted_attractors = sorted(attractors.items(), key=lambda x: x[0])
    
    print(f"Found {len(sorted_attractors)} distinct frequency attractors")
    print()
    print("Top 5 attractors by frequency:")
    print("-" * 90)
    
    for freq, numbers in sorted_attractors[-5:]:
        print(f"Frequency: {freq:10.4f} Hz ({freq/operator.f0:.4f} × f₀)")
        print(f"  Examples: {numbers[:5]}")
        print()
    
    # Summary
    print("=" * 90)
    print("KEY INSIGHTS")
    print("=" * 90)
    print()
    print("1. Singular Point 1000:")
    print(f"   - Only 4-digit number with frequency exactly f₀ = {operator.f0} Hz")
    print("   - Represents 'origin' in vibrational space")
    print()
    print("2. Kaprekar Constant 6174:")
    print(f"   - Frequency: {operator.compute_frequency(6174):.4f} Hz")
    print(f"   - Ratio to f₀: {operator.compute_frequency(6174)/operator.f0:.4f}")
    print("   - Universal attractor in Kaprekar dynamics")
    print()
    print("3. Maximum Frequency 9999:")
    print(f"   - Frequency: {operator.compute_frequency(9999):.4f} Hz")
    print(f"   - Exactly 36 × f₀ (digit sum = 36)")
    print("   - Represents 'totality' before collapse")
    print()
    print("=" * 90)


if __name__ == "__main__":
    demonstrate_kaprekar_vibrational()

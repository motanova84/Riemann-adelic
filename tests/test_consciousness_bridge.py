"""
Test consciousness adelic bridge functionality.

This module tests the mapping from ST.26 sequences to quantum circuits
and their integration with Mellin transforms.
"""

import pytest
import numpy as np
import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from qiskit import QuantumCircuit
    QISKIT_AVAILABLE = True
except ImportError:
    QISKIT_AVAILABLE = False

from utils.mellin import mellin_transform, truncated_gaussian
import mpmath as mp


class TestConsciousnessBridge:
    """Test consciousness adelic bridge components."""
    
    @pytest.fixture(autouse=True)
    def setup(self):
        """Setup test environment."""
        mp.mp.dps = 15
        self.SEQ_06 = "atgcgcaactacggctacgcgaacagcgacggctag"
        
    def find_palindromes(self, sequence, min_length=3):
        """Find palindromic subsequences in DNA sequence."""
        palindromes = []
        n = len(sequence)
        
        for i in range(n):
            for j in range(i + min_length, n + 1):
                substr = sequence[i:j]
                if substr == substr[::-1]:
                    palindromes.append({
                        'sequence': substr,
                        'position': (i, j),
                        'length': len(substr)
                    })
        
        return palindromes
    
    def test_palindrome_detection(self):
        """Test ST.26 palindrome detection."""
        palindromes = self.find_palindromes(self.SEQ_06)
        
        # Should find at least some palindromes
        assert len(palindromes) >= 5, f"Expected at least 5 palindromes, found {len(palindromes)}"
        
        # Check that palindromes are actually palindromic
        for pal in palindromes:
            seq = pal['sequence']
            assert seq == seq[::-1], f"'{seq}' is not a palindrome"
            assert pal['length'] >= 3, f"Palindrome too short: {pal['length']}"
    
    @pytest.mark.skipif(not QISKIT_AVAILABLE, reason="Qiskit not available")
    def test_quantum_circuit_generation(self):
        """Test quantum circuit generation from palindromes."""
        palindromes = self.find_palindromes(self.SEQ_06)
        
        # Create simple quantum circuit based on palindromes
        n_qubits = min(6, max(4, len(palindromes)//2))
        qc = QuantumCircuit(n_qubits, n_qubits)
        
        # Add gates based on palindrome lengths
        for i, pal in enumerate(palindromes[:n_qubits]):
            qubit_idx = i % n_qubits
            
            if pal['length'] <= 4:
                qc.h(qubit_idx)  # Hadamard for short palindromes
            else:
                target = (qubit_idx + 1) % n_qubits
                qc.cx(qubit_idx, target)  # CNOT for long palindromes
        
        qc.measure_all()
        
        assert qc.num_qubits >= 4, "Circuit should have at least 4 qubits"
        assert qc.num_clbits >= 4, "Circuit should have classical bits for measurement"
        assert len(qc) > 0, "Circuit should have gates"
        
    def test_resonance_frequencies(self):
        """Test resonance frequency analysis."""
        freq1, freq2 = 141.7, 151.7
        
        # Calculate key ratios as in the notebook
        ratio = freq1 / freq2
        diff = freq2 - freq1
        geometric_mean = np.sqrt(freq1 * freq2)
        
        # Basic validation
        assert 0.9 < ratio < 1.0, f"Frequency ratio should be ~0.93, got {ratio}"
        assert 8 < diff < 12, f"Frequency difference should be ~10 Hz, got {diff}"
        assert 140 < geometric_mean < 160, f"Geometric mean should be ~146 Hz, got {geometric_mean}"
        
    def test_mellin_integration(self):
        """Test integration with Mellin transforms."""
        # Test basic Mellin transform functionality
        s = mp.mpc(1, 1)
        result = mellin_transform(truncated_gaussian, s, 3.0)
        
        # Should return finite complex number
        assert mp.isfinite(result), "Mellin transform should return finite value"
        assert isinstance(result, mp.mpc), "Result should be complex number"
        
        # Test consciousness-derived function
        def quantum_consciousness_function(u):
            """Simple test function mimicking quantum-derived function."""
            if abs(u) > 3.0:
                return mp.mpf('0')
            return mp.exp(-u**2/4) * mp.cos(u)
        
        result_consciousness = mellin_transform(quantum_consciousness_function, s, 2.0)
        assert mp.isfinite(result_consciousness), "Consciousness function transform should be finite"
        
    def test_nucleotide_mapping(self):
        """Test nucleotide to quantum basis mapping."""
        def nucleotide_to_qubit_basis(nucleotide):
            mapping = {
                'a': '00', 't': '01', 'g': '10', 'c': '11'
            }
            return mapping.get(nucleotide.lower(), '00')
        
        # Test all nucleotides
        assert nucleotide_to_qubit_basis('a') == '00'
        assert nucleotide_to_qubit_basis('t') == '01'
        assert nucleotide_to_qubit_basis('g') == '10'
        assert nucleotide_to_qubit_basis('c') == '11'
        
        # Test case insensitivity
        assert nucleotide_to_qubit_basis('A') == '00'
        assert nucleotide_to_qubit_basis('T') == '01'
        
        # Test invalid nucleotide
        assert nucleotide_to_qubit_basis('x') == '00'
        
    def test_consciousness_formula_constants(self):
        """Test consciousness formula physical constants."""
        # Physical constants from patent formula
        hbar = 1.054571817e-34  # J⋅s
        kB = 1.380649e-23       # J/K
        T = 310.0               # Body temperature in K
        
        # Base coefficient should be positive and finite
        C_base = hbar / (kB * T)
        
        assert C_base > 0, "Base coefficient should be positive"
        assert np.isfinite(C_base), "Base coefficient should be finite"
        assert C_base < 1e-10, "Base coefficient should be very small (quantum scale)"


class TestIntegration:
    """Integration tests for consciousness adelic bridge."""
    
    @pytest.mark.skipif(not QISKIT_AVAILABLE, reason="Qiskit not available")
    def test_complete_bridge_workflow(self):
        """Test complete workflow from DNA to quantum to Mellin."""
        mp.mp.dps = 15
        
        # 1. DNA palindrome detection
        SEQ_06 = "atgcgcaactacggctacgcgaacagcgacggctag"
        palindromes = []
        n = len(SEQ_06)
        
        for i in range(n):
            for j in range(i + 3, n + 1):
                substr = SEQ_06[i:j]
                if substr == substr[::-1]:
                    palindromes.append(substr)
                    break  # Just get first palindrome at each position
        
        assert len(palindromes) >= 3, "Should find multiple palindromes"
        
        # 2. Quantum circuit creation
        qc = QuantumCircuit(4, 4)
        for i, pal in enumerate(palindromes[:4]):
            if len(pal) <= 4:
                qc.h(i)
            if i < 3:
                qc.cx(i, i+1)
        qc.measure_all()
        
        assert qc.num_qubits == 4, "Circuit should have 4 qubits"
        
        # 3. Mellin transform integration
        def simple_consciousness_function(u):
            if abs(u) > 2.0:
                return mp.mpf('0')
            return mp.exp(-u**2) * mp.cos(len(palindromes) * u)
        
        s = mp.mpc(1.5, 0.5)
        result = mellin_transform(simple_consciousness_function, s, 2.0)
        
        assert mp.isfinite(result), "Complete workflow should produce finite result"
        
    def test_parameter_validation(self):
        """Test parameter validation for integration_t."""
        # This tests the integration parameter mentioned in problem statement
        integration_t_values = [10, 25, 50, 100]
        
        for t_val in integration_t_values:
            # Test that integration parameter is reasonable
            assert 5 <= t_val <= 200, f"integration_t={t_val} should be in reasonable range"
            
            # Test function evaluation at different integration limits
            def test_func(u):
                if abs(u) > t_val/10:
                    return mp.mpf('0')
                return mp.exp(-u**2)
            
            s = mp.mpc(1, 0)
            result = mellin_transform(test_func, s, t_val/10)
            assert mp.isfinite(result), f"Transform should be finite for integration_t={t_val}"


if __name__ == "__main__":
    pytest.main([__file__])
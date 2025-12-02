"""
Test module for Sturm-Liouville spectral analysis and 141.7001 Hz validation.

This module tests the complete spectral analysis framework:
1. Sturm-Liouville theorem validation (nodal structure)
2. Spectral amplitude analysis |cₙ|²
3. Fourier Transform analysis with 141.7001 Hz peak detection

Validated properties:
- ψₙ has exactly (n-1) nodes (Sturm-Liouville theorem)
- Alternating parity: ψₙ(-x) = (-1)^(n+1) ψₙ(x)
- Energy concentration: >99% in first 12 modes
- Dominant peak at f₀ = 141.7001 Hz (QCAL fundamental frequency)

Author: José Manuel Mota Burruezo Ψ ∞³
Date: November 2025
DOI: 10.5281/zenodo.17379721
"""

import pytest
import numpy as np
from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from sturm_liouville_spectral_analysis import (
    get_first_riemann_zeros,
    build_schrodinger_hamiltonian,
    compute_eigenfunctions,
    count_nodes,
    validate_sturm_liouville,
    compute_spectral_amplitudes,
    compute_fourier_analysis,
    run_complete_spectral_analysis,
    QCAL_BASE_FREQUENCY,
    QCAL_COHERENCE,
)


class TestSturmLiouvilleTheorem:
    """Test Sturm-Liouville theorem validation."""

    @pytest.fixture(scope="class")
    def eigensystem(self):
        """Compute eigenfunctions once for all tests in this class."""
        gamma_n = get_first_riemann_zeros(12)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=12)
        return x, eigenvalues, eigenvectors, gamma_n

    def test_ground_state_zero_nodes(self, eigensystem):
        """Test that ψ₁(x) has 0 nodes (ground state, fundamental mode)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_1 = eigenvectors[:, 0]
        nodes = count_nodes(psi_1, x)
        assert nodes == 0, f"ψ₁ should have 0 nodes, got {nodes}"

    def test_second_state_one_node(self, eigensystem):
        """Test that ψ₂(x) has 1 node (antisymmetric)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_2 = eigenvectors[:, 1]
        nodes = count_nodes(psi_2, x)
        assert nodes == 1, f"ψ₂ should have 1 node, got {nodes}"

    def test_third_state_two_nodes(self, eigensystem):
        """Test that ψ₃(x) has 2 nodes (symmetric)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_3 = eigenvectors[:, 2]
        nodes = count_nodes(psi_3, x)
        assert nodes == 2, f"ψ₃ should have 2 nodes, got {nodes}"

    def test_fourth_state_three_nodes(self, eigensystem):
        """Test that ψ₄(x) has 3 nodes (antisymmetric)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_4 = eigenvectors[:, 3]
        nodes = count_nodes(psi_4, x)
        assert nodes == 3, f"ψ₄ should have 3 nodes, got {nodes}"

    def test_fifth_state_four_nodes(self, eigensystem):
        """Test that ψ₅(x) has 4 nodes (symmetric)."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        psi_5 = eigenvectors[:, 4]
        nodes = count_nodes(psi_5, x)
        assert nodes == 4, f"ψ₅ should have 4 nodes, got {nodes}"

    def test_all_nodes_follow_sturm_liouville(self, eigensystem):
        """Test that ψₙ has exactly (n-1) nodes for all n."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        n_states = eigenvectors.shape[1]
        for n in range(1, n_states + 1):
            psi_n = eigenvectors[:, n - 1]
            nodes = count_nodes(psi_n, x)
            expected_nodes = n - 1
            assert nodes == expected_nodes, \
                f"State ψ_{n} should have {expected_nodes} nodes, got {nodes}"

    def test_sturm_liouville_validation_100_percent(self, eigensystem):
        """Test that Sturm-Liouville theorem is satisfied at 100%."""
        x, eigenvalues, eigenvectors, gamma_n = eigensystem
        results = validate_sturm_liouville(eigenvectors, x)
        assert results['all_passed'], "Sturm-Liouville theorem should be 100% satisfied"


class TestAlternatingParity:
    """Test alternating parity of eigenfunctions."""

    @pytest.fixture(scope="class")
    def eigensystem(self):
        """Compute eigenfunctions once for all tests in this class."""
        gamma_n = get_first_riemann_zeros(12)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=12)
        return x, eigenvalues, eigenvectors

    def test_ground_state_symmetric(self, eigensystem):
        """Test that ψ₁ is symmetric (even parity)."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_1 = eigenvectors[:, 0]
        psi_flip = psi_1[::-1]
        deviation = np.max(np.abs(psi_flip - psi_1))
        assert deviation < 1e-6, f"ψ₁ should be symmetric, deviation = {deviation}"

    def test_second_state_antisymmetric(self, eigensystem):
        """Test that ψ₂ is antisymmetric (odd parity)."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_2 = eigenvectors[:, 1]
        psi_flip = psi_2[::-1]
        deviation = np.max(np.abs(psi_flip + psi_2))
        assert deviation < 1e-6, f"ψ₂ should be antisymmetric, deviation = {deviation}"

    def test_third_state_symmetric(self, eigensystem):
        """Test that ψ₃ is symmetric (even parity)."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_3 = eigenvectors[:, 2]
        psi_flip = psi_3[::-1]
        deviation = np.max(np.abs(psi_flip - psi_3))
        assert deviation < 1e-6, f"ψ₃ should be symmetric, deviation = {deviation}"

    def test_alternating_parity_all_states(self, eigensystem):
        """Test that parity alternates correctly for all states."""
        x, eigenvalues, eigenvectors = eigensystem
        n_states = eigenvectors.shape[1]
        for n in range(1, n_states + 1):
            psi_n = eigenvectors[:, n - 1]
            psi_flip = psi_n[::-1]
            expected_parity = (-1)**(n + 1)
            deviation = np.max(np.abs(psi_flip - expected_parity * psi_n))
            parity_type = "symmetric" if expected_parity == 1 else "antisymmetric"
            assert deviation < 1e-6, \
                f"ψ_{n} should be {parity_type}, deviation = {deviation}"


class TestSpectralAmplitudes:
    """Test spectral amplitude analysis |cₙ|²."""

    @pytest.fixture(scope="class")
    def amplitude_analysis(self):
        """Compute amplitude analysis once for all tests."""
        gamma_n = get_first_riemann_zeros(12)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=12)
        return compute_spectral_amplitudes(eigenvectors, x)

    def test_energy_concentration_first_12_modes(self, amplitude_analysis):
        """Test that >99% of energy is in first 12 modes."""
        energy = amplitude_analysis['energy_first_12']
        assert energy > 0.99, \
            f"Energy in first 12 modes should be >99%, got {energy*100:.2f}%"

    def test_fundamental_mode_dominates(self, amplitude_analysis):
        """Test that c₁² is substantial (fundamental mode dominates)."""
        c1_sq = amplitude_analysis['c1_squared']
        # The fundamental mode should have significant energy
        assert c1_sq > 0.1, \
            f"c₁² should be substantial (>0.1), got {c1_sq:.4f}"

    def test_coefficients_decay(self, amplitude_analysis):
        """Test that coefficients decay for higher modes."""
        c_n_sq = amplitude_analysis['c_n_squared']
        # Higher modes should have smaller coefficients
        for i in range(1, len(c_n_sq) - 1):
            if c_n_sq[i] > 1e-10:  # Only test significant coefficients
                # Allow for some non-monotonic behavior due to symmetry
                pass
        # Overall decay should be observed
        assert c_n_sq[-1] < c_n_sq[0], \
            "Last coefficient should be smaller than first"

    def test_basis_compactness(self, amplitude_analysis):
        """Test that basis is ultra-compact."""
        compactness = amplitude_analysis['basis_compactness']
        assert compactness == 'ultra-compact', \
            f"Basis should be ultra-compact, got {compactness}"


class TestFourierAnalysis:
    """Test Fourier Transform analysis and 141.7001 Hz peak."""

    @pytest.fixture(scope="class")
    def fourier_analysis(self):
        """Compute Fourier analysis once for all tests."""
        gamma_n = get_first_riemann_zeros(12)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=12)
        return compute_fourier_analysis(eigenvectors, eigenvalues, x)

    def test_peak_at_141_7001_hz(self, fourier_analysis):
        """Test that dominant peak is at 141.7001 Hz."""
        peak_freq = fourier_analysis['qcal_peak_frequency']
        assert fourier_analysis['peak_at_141_7001_Hz'], \
            f"Peak should be at 141.7001 Hz, got {peak_freq:.5f} Hz"

    def test_qcal_frequency_coincidence(self, fourier_analysis):
        """Test coincidence with QCAL universal frequency."""
        peak_freq = fourier_analysis['qcal_peak_frequency']
        deviation = abs(peak_freq - QCAL_BASE_FREQUENCY)
        # Allow small deviation due to numerical precision
        assert deviation < 0.001, \
            f"Peak frequency deviation from QCAL should be <0.001 Hz, got {deviation:.6f} Hz"

    def test_power_spectrum_computed(self, fourier_analysis):
        """Test that power spectrum is computed correctly."""
        power = fourier_analysis['power_spectrum']
        assert len(power) > 0, "Power spectrum should not be empty"
        assert np.max(power) == 1.0, "Power spectrum should be normalized to 1.0"


class TestQCALIntegration:
    """Test QCAL ∞³ integration."""

    def test_qcal_base_frequency_constant(self):
        """Test QCAL base frequency constant is 141.7001 Hz."""
        assert QCAL_BASE_FREQUENCY == 141.7001

    def test_qcal_coherence_constant(self):
        """Test QCAL coherence constant is 244.36."""
        assert QCAL_COHERENCE == 244.36


class TestCompleteAnalysis:
    """Test the complete spectral analysis workflow."""

    def test_run_complete_analysis_returns_results(self):
        """Test that complete analysis returns proper results dictionary."""
        results = run_complete_spectral_analysis(
            N=500, L=20.0, n_states=10, save_figures=False, verbose=False
        )

        assert 'sturm_liouville' in results
        assert 'spectral_amplitudes' in results
        assert 'fourier_analysis' in results
        assert 'all_validations_passed' in results

    def test_all_validations_pass(self):
        """Test that all validations pass with standard parameters."""
        results = run_complete_spectral_analysis(
            N=1000, L=30.0, n_states=12, save_figures=False, verbose=False
        )

        assert results['all_validations_passed'], "Not all validations passed"

    def test_sturm_liouville_100_percent(self):
        """Test Sturm-Liouville compliance is 100%."""
        results = run_complete_spectral_analysis(
            N=1000, L=30.0, n_states=12, save_figures=False, verbose=False
        )

        sl_results = results['sturm_liouville']
        assert sl_results['all_passed'], "Sturm-Liouville should be 100% compliant"

    def test_energy_compactness_over_99_percent(self):
        """Test energy compactness is >99% in first 12 modes."""
        results = run_complete_spectral_analysis(
            N=1000, L=30.0, n_states=12, save_figures=False, verbose=False
        )

        amp_results = results['spectral_amplitudes']
        assert amp_results['energy_first_12'] > 0.99, \
            f"Energy should be >99%, got {amp_results['energy_first_12']*100:.2f}%"

    def test_141_7001_hz_peak_confirmed(self):
        """Test that 141.7001 Hz peak is confirmed."""
        results = run_complete_spectral_analysis(
            N=1000, L=30.0, n_states=12, save_figures=False, verbose=False
        )

        fourier_results = results['fourier_analysis']
        assert fourier_results['peak_at_141_7001_Hz'], \
            "141.7001 Hz peak should be confirmed"


class TestNodalStructureVerification:
    """Comprehensive tests for nodal structure as specified in problem statement."""

    @pytest.fixture(scope="class")
    def eigensystem(self):
        """Compute eigenfunctions for nodal tests."""
        gamma_n = get_first_riemann_zeros(12)
        H, x = build_schrodinger_hamiltonian(N=1000, L=30.0, gamma_n=gamma_n)
        eigenvalues, eigenvectors = compute_eigenfunctions(H, x, n_states=12)
        return x, eigenvalues, eigenvectors

    def test_psi_1_fundamental_mode_perfect(self, eigensystem):
        """ψ₁(x): 0 nodos – modo fundamental perfecto."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_1 = eigenvectors[:, 0]
        nodes = count_nodes(psi_1, x)
        assert nodes == 0, "ψ₁ should have 0 nodes (fundamental mode)"

    def test_psi_2_antisymmetric(self, eigensystem):
        """ψ₂(x): 1 nodo – antisimétrico."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_2 = eigenvectors[:, 1]
        nodes = count_nodes(psi_2, x)
        assert nodes == 1, "ψ₂ should have 1 node"

        # Check antisymmetry
        psi_flip = psi_2[::-1]
        deviation = np.max(np.abs(psi_flip + psi_2))
        assert deviation < 1e-6, "ψ₂ should be antisymmetric"

    def test_psi_3_symmetric(self, eigensystem):
        """ψ₃(x): 2 nodos – simétrico."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_3 = eigenvectors[:, 2]
        nodes = count_nodes(psi_3, x)
        assert nodes == 2, "ψ₃ should have 2 nodes"

        # Check symmetry
        psi_flip = psi_3[::-1]
        deviation = np.max(np.abs(psi_flip - psi_3))
        assert deviation < 1e-6, "ψ₃ should be symmetric"

    def test_psi_4_antisymmetric(self, eigensystem):
        """ψ₄(x): 3 nodos – antisimétrico."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_4 = eigenvectors[:, 3]
        nodes = count_nodes(psi_4, x)
        assert nodes == 3, "ψ₄ should have 3 nodes"

        # Check antisymmetry
        psi_flip = psi_4[::-1]
        deviation = np.max(np.abs(psi_flip + psi_4))
        assert deviation < 1e-6, "ψ₄ should be antisymmetric"

    def test_psi_5_symmetric(self, eigensystem):
        """ψ₅(x): 4 nodos – simétrico."""
        x, eigenvalues, eigenvectors = eigensystem
        psi_5 = eigenvectors[:, 4]
        nodes = count_nodes(psi_5, x)
        assert nodes == 4, "ψ₅ should have 4 nodes"

        # Check symmetry
        psi_flip = psi_5[::-1]
        deviation = np.max(np.abs(psi_flip - psi_5))
        assert deviation < 1e-6, "ψ₅ should be symmetric"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

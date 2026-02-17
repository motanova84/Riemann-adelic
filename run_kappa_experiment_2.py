#!/usr/bin/env python3
"""
run_kappa_experiment_2.py

Orchestrator ∞³ for complete modal curvature experiment.

This module orchestrates the full experimental pipeline:
1. Build orthonormal Fourier basis φ_n(t) = √(2/T) cos(nπt/T)
2. Compute modal covariance operator O_nm = ⟨φ_n·φ_m·F⟩
3. Construct adjacency graph A_nm from modal similarities
4. Analyze curvature κ(n) and fit to ~1/(n log n)
5. Generate comprehensive report and visualizations

Mathematical Framework:
    This experiment tests the hypothesis that curvature emerges in
    modal space even without direct interaction, purely through
    resonance with common forcing F(t).
    
    Expected result: κ(n) ~ C/(n log n)
    
    This mirrors the prime number theorem density and validates
    the spectral-geometric correspondence in QCAL framework.

QCAL Integration:
    - f₀ = 141.7001 Hz fundamental frequency
    - C = 244.36 coherence constant
    - Validates spectral emergence principles

Author: José Manuel Mota Burruezo Ψ ∴ ∞³
Date: February 2026
DOI: 10.5281/zenodo.17379721
"""

import numpy as np
from typing import Optional, Dict
import matplotlib.pyplot as plt
from pathlib import Path
import json
from datetime import datetime

from build_orthonormal_basis import OrthonormalFourierBasis
from compute_covariance_operator import ModalCovarianceOperator
from analyze_kappa_curve import KappaCurveAnalyzer

# QCAL Constants
F0 = 141.7001  # Fundamental frequency (Hz)
OMEGA_0 = 2 * np.pi * F0
C_QCAL = 244.36  # QCAL coherence constant


class KappaExperiment:
    """
    Orchestrator for complete modal curvature experiment.
    
    Runs full pipeline:
    1. Basis construction
    2. Operator computation
    3. Graph construction
    4. Curvature analysis
    5. Report generation
    
    Attributes:
        config: Experiment configuration
        results: Dictionary storing all results
        output_dir: Directory for outputs
    """
    
    def __init__(self, config: Optional[Dict] = None, output_dir: str = './kappa_experiment_results'):
        """
        Initialize experiment orchestrator.
        
        Args:
            config: Configuration dictionary (if None, uses defaults)
            output_dir: Directory for output files
        """
        self.config = config or self.default_config()
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        
        self.results = {
            'timestamp': datetime.now().isoformat(),
            'config': self.config,
            'basis': {},
            'operator': {},
            'graph': {},
            'curvature': {}
        }
        
        # Components
        self.basis = None
        self.cov_op = None
        self.analyzer = None
        
    @staticmethod
    def default_config() -> Dict:
        """
        Default experiment configuration.
        
        Returns:
            Configuration dictionary
        """
        return {
            'T': 1.0,  # Period
            'n_modes': 50,  # Number of modes
            'n_points': 2000,  # Time discretization
            'forcing': {
                'type': 'resonant',  # 'resonant' or 'custom'
                'modes': [1, 3, 5],  # Active modes in forcing
                'amplitudes': [1.0, 0.5, 0.3]  # Amplitudes
            },
            'graph': {
                'theta': 0.1  # Adjacency threshold
            },
            'curvature': {
                'method': 'laplacian',  # 'laplacian' or 'normalized'
                'fit_range': (3, 40)  # Range for asymptotic fit
            },
            'qcal': {
                'f0': F0,
                'C': C_QCAL
            }
        }
    
    def run_full_experiment(self):
        """
        Run complete experiment pipeline.
        """
        print("=" * 80)
        print("KAPPA EXPERIMENT ∞³ - MODAL CURVATURE ANALYSIS")
        print("QCAL Framework - Spectral Emergence Validation")
        print("=" * 80)
        print()
        
        # Step 1: Build orthonormal basis
        print("Step 1: Building orthonormal Fourier basis...")
        self._build_basis()
        print()
        
        # Step 2: Compute covariance operator
        print("Step 2: Computing modal covariance operator...")
        self._compute_operator()
        print()
        
        # Step 3: Construct adjacency graph
        print("Step 3: Constructing adjacency graph...")
        self._construct_graph()
        print()
        
        # Step 4: Analyze curvature
        print("Step 4: Analyzing curvature κ(n)...")
        self._analyze_curvature()
        print()
        
        # Step 5: Generate visualizations
        print("Step 5: Generating visualizations...")
        self._generate_visualizations()
        print()
        
        # Step 6: Save results
        print("Step 6: Saving results...")
        self._save_results()
        print()
        
        print("=" * 80)
        print("✓ EXPERIMENT COMPLETE")
        print(f"✓ Results saved to {self.output_dir}")
        print("=" * 80)
        
    def _build_basis(self):
        """Step 1: Build orthonormal Fourier basis."""
        self.basis = OrthonormalFourierBasis(
            T=self.config['T'],
            n_modes=self.config['n_modes'],
            n_points=self.config['n_points']
        )
        
        # Verify orthonormality
        verification = self.basis.verify_orthonormality(n_check=10)
        
        self.results['basis'] = {
            'T': self.config['T'],
            'n_modes': self.config['n_modes'],
            'orthonormality_verified': verification['is_orthonormal'],
            'max_diagonal_error': verification['max_diagonal_error'],
            'max_offdiag_error': verification['max_offdiag_error']
        }
        
        print(f"  ✓ Basis with {self.config['n_modes']} modes constructed")
        print(f"  ✓ Orthonormality verified: {verification['is_orthonormal']}")
        
    def _compute_operator(self):
        """Step 2: Compute modal covariance operator with forcing."""
        self.cov_op = ModalCovarianceOperator(self.basis)
        
        # Construct forcing function F(t)
        forcing_config = self.config['forcing']
        forcing_coeffs = np.zeros(self.config['n_modes'] + 1)
        
        if forcing_config['type'] == 'resonant':
            for mode, amp in zip(forcing_config['modes'], forcing_config['amplitudes']):
                if mode <= self.config['n_modes']:
                    forcing_coeffs[mode] = amp
        
        # Compute covariance matrix (for comparison)
        O_cov = self.cov_op.compute_covariance_matrix(max_mode=self.config['n_modes'])
        
        # Compute forcing operator
        O_forcing = self.cov_op.compute_forcing_operator(forcing_coeffs, 
                                                         max_mode=self.config['n_modes'])
        
        self.results['operator'] = {
            'forcing_modes': forcing_config['modes'],
            'forcing_amplitudes': forcing_config['amplitudes'],
            'O_cov_norm': float(np.linalg.norm(O_cov)),
            'O_forcing_norm': float(np.linalg.norm(O_forcing)),
            'matrix_shape': O_forcing.shape
        }
        
        print(f"  ✓ Covariance operator computed: ‖O_cov‖ = {np.linalg.norm(O_cov):.4f}")
        print(f"  ✓ Forcing operator computed: ‖O_F‖ = {np.linalg.norm(O_forcing):.4f}")
        
    def _construct_graph(self):
        """Step 3: Construct adjacency graph from modal similarities."""
        theta = self.config['graph']['theta']
        
        A_graph = self.cov_op.compute_adjacency_graph(theta=theta, use_forcing=True)
        graph_props = self.cov_op.analyze_graph_properties()
        
        self.results['graph'] = {
            'theta': theta,
            'n_nodes': graph_props['n_nodes'],
            'n_edges': graph_props['n_edges'],
            'density': graph_props['density'],
            'mean_degree': graph_props['mean_degree'],
            'max_degree': graph_props['max_degree']
        }
        
        print(f"  ✓ Graph with {graph_props['n_nodes']} nodes, {graph_props['n_edges']} edges")
        print(f"  ✓ Density: {graph_props['density']:.4f}, Mean degree: {graph_props['mean_degree']:.2f}")
        
    def _analyze_curvature(self):
        """Step 4: Analyze curvature κ(n) and fit asymptotic form."""
        self.analyzer = KappaCurveAnalyzer(self.cov_op.A_graph)
        
        # Compute spectral curvature
        method = self.config['curvature']['method']
        kappa = self.analyzer.compute_spectral_curvature(method=method)
        
        # Fit asymptotic form
        n_min, n_max = self.config['curvature']['fit_range']
        fit_results = self.analyzer.fit_asymptotic_form(n_min=n_min, n_max=n_max)
        
        # Analyze convergence
        conv_results = self.analyzer.analyze_convergence(window_size=5)
        
        self.results['curvature'] = {
            'method': method,
            'n_points': len(kappa),
            'kappa_1': float(kappa[0]) if len(kappa) > 0 else None,
            'kappa_10': float(kappa[9]) if len(kappa) > 9 else None,
            'fit': {
                'C': fit_results['C'],
                'offset': fit_results['offset'],
                'r_squared': fit_results['r_squared'],
                'rms_residual': fit_results['rms_residual'],
                'fit_range': fit_results['fit_range']
            },
            'convergence': {
                'mean_relative_error': conv_results['mean_relative_error'],
                'final_relative_error': conv_results['final_relative_error'],
                'convergence_rate': conv_results['convergence_rate']
            }
        }
        
        print(f"  ✓ Curvature κ(n) computed: {len(kappa)} values")
        print(f"  ✓ Asymptotic fit: C = {fit_results['C']:.4f}, R² = {fit_results['r_squared']:.4f}")
        print(f"  ✓ Convergence rate: {conv_results['convergence_rate']:.4f}")
        
    def _generate_visualizations(self):
        """Step 5: Generate all visualizations."""
        # Basis functions
        basis_path = self.output_dir / 'basis_functions.png'
        self.basis.visualize_basis(modes_to_plot=[0, 1, 2, 5, 10], 
                                   save_path=str(basis_path))
        
        # Covariance matrix
        cov_path = self.output_dir / 'covariance_matrix.png'
        self.cov_op.visualize_covariance_matrix(matrix_type='covariance',
                                               save_path=str(cov_path))
        
        # Forcing operator
        forcing_path = self.output_dir / 'forcing_operator.png'
        self.cov_op.visualize_covariance_matrix(matrix_type='forcing',
                                               save_path=str(forcing_path))
        
        # Adjacency graph
        graph_path = self.output_dir / 'adjacency_graph.png'
        self.cov_op.visualize_adjacency_graph(save_path=str(graph_path))
        
        # Curvature analysis
        kappa_path = self.output_dir / 'kappa_curve.png'
        self.analyzer.visualize_kappa_curve(show_fit=True, save_path=str(kappa_path))
        
        print(f"  ✓ All visualizations saved to {self.output_dir}")
        
    def _save_results(self):
        """Step 6: Save results to JSON file."""
        results_path = self.output_dir / 'experiment_results.json'
        
        # Convert numpy types to Python types for JSON serialization
        def convert_numpy(obj):
            if isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, (np.integer, np.int64)):
                return int(obj)
            elif isinstance(obj, (np.floating, np.float64)):
                return float(obj)
            elif isinstance(obj, (np.bool_, bool)):
                return bool(obj)
            elif isinstance(obj, dict):
                return {key: convert_numpy(value) for key, value in obj.items()}
            elif isinstance(obj, list):
                return [convert_numpy(item) for item in obj]
            else:
                return obj
        
        results_clean = convert_numpy(self.results)
        
        with open(results_path, 'w') as f:
            json.dump(results_clean, f, indent=2)
        
        print(f"  ✓ Results saved to {results_path}")
        
        # Print summary
        self._print_summary()
        
    def _print_summary(self):
        """Print experiment summary."""
        print()
        print("=" * 80)
        print("EXPERIMENT SUMMARY")
        print("=" * 80)
        
        print("\nBasis:")
        print(f"  Period T = {self.results['basis']['T']}")
        print(f"  Modes = {self.results['basis']['n_modes']}")
        print(f"  Orthonormal = {self.results['basis']['orthonormality_verified']}")
        
        print("\nOperator:")
        print(f"  Forcing modes = {self.results['operator']['forcing_modes']}")
        print(f"  ‖O_F‖ = {self.results['operator']['O_forcing_norm']:.4f}")
        
        print("\nGraph:")
        print(f"  Nodes = {self.results['graph']['n_nodes']}")
        print(f"  Edges = {self.results['graph']['n_edges']}")
        print(f"  Density = {self.results['graph']['density']:.4f}")
        
        print("\nCurvature:")
        fit = self.results['curvature']['fit']
        conv = self.results['curvature']['convergence']
        print(f"  Fit: κ(n) ~ {fit['C']:.4f}/(n log n) + {fit['offset']:.4f}")
        print(f"  R² = {fit['r_squared']:.4f}")
        print(f"  Mean relative error = {conv['mean_relative_error']:.4f}")
        
        print("\nQCAL Coherence:")
        print(f"  f₀ = {F0} Hz")
        print(f"  C = {C_QCAL}")
        print(f"  Ψ = I × A_eff² × C^∞")
        
        print("=" * 80)


def main():
    """
    Main entry point for kappa experiment.
    """
    # Create custom configuration if needed
    config = KappaExperiment.default_config()
    
    # Customize for larger experiment
    config['n_modes'] = 60
    config['forcing']['modes'] = [1, 2, 3, 5, 8]
    config['forcing']['amplitudes'] = [1.0, 0.7, 0.5, 0.3, 0.2]
    config['graph']['theta'] = 0.08
    config['curvature']['fit_range'] = (5, 50)
    
    # Run experiment
    experiment = KappaExperiment(config=config)
    experiment.run_full_experiment()


if __name__ == "__main__":
    main()

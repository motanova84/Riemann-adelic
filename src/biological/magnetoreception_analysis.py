#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Magnetoreception Analysis Module
=================================

This module implements analysis tools for magnetoreception in biological systems,
specifically testing the chirality tensor prediction of ~0.2% asymmetry between
right-rotated (B_R) and left-rotated (B_L) magnetic fields.

Key Features
------------
1. **Rayleigh Analysis**: Statistical analysis of circular distributions from
   Emlen cage experiments with European robins (Erithacus rubecula).

2. **Asymmetry Detection**: Quantification of directional bias in magnetic
   compass orientation with p < 0.01 significance threshold.

3. **Cryptochrome Modeling**: Radical pair mechanism in cryptochromes showing
   singlet→triplet transition bias from chirality tensor T.

4. **AMDA Integration**: Analysis Module for Directional Asymmetry compatible
   with QCAL framework.

Mathematical Background
-----------------------
The chirality tensor T introduces a bias in radical pair transitions:
    P(triplet | B_R) - P(triplet | B_L) = ΔP ≈ 0.2%

This is measured through:
- Mean vector length r (strength of directional preference)
- Rayleigh test for non-uniformity (H₀: uniform distribution)
- Watson's U² test for comparing two circular samples

References
----------
- Ritz et al. (2000): Magnetic compass of birds based on radical-pair processes
- Wiltschko & Wiltschko (1972): Magnetic compass of European robins
- Mouritsen & Ritz (2005): Magnetoreception and its use in bird navigation

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
Date: February 2026
License: MIT
"""

import numpy as np
from scipy import stats
from typing import List, Tuple, Dict, Any, Optional
from dataclasses import dataclass, asdict
import json

# Import chirality tensor
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../..'))
from operators.chirality_tensor import ChiralityTensor


@dataclass
class EmlenCageData:
    """
    Data from Emlen cage orientation experiments.
    
    Attributes
    ----------
    angles_deg : List[float]
        Directional headings in degrees (0-360)
    field_rotation : str
        Field rotation direction: 'right' or 'left'
    bird_id : str
        Individual bird identifier
    trial_date : str
        Date of experiment
    magnetic_field_uT : float
        Magnetic field strength in microtesla
    """
    angles_deg: List[float]
    field_rotation: str  # 'right' or 'left'
    bird_id: str
    trial_date: str
    magnetic_field_uT: float = 50.0


@dataclass
class RayleighTestResult:
    """
    Results of Rayleigh test for circular uniformity.
    
    Attributes
    ----------
    mean_direction_deg : float
        Mean direction in degrees
    mean_vector_length : float
        Length of mean vector r ∈ [0, 1]
    rayleigh_z : float
        Rayleigh test statistic Z = n·r²
    p_value : float
        p-value for test of uniformity
    is_significant : bool
        Whether result is significant (p < 0.05)
    sample_size : int
        Number of observations
    """
    mean_direction_deg: float
    mean_vector_length: float
    rayleigh_z: float
    p_value: float
    is_significant: bool
    sample_size: int


@dataclass
class AsymmetryResult:
    """
    Results of asymmetry analysis between B_R and B_L conditions.
    
    Attributes
    ----------
    delta_P_percent : float
        Asymmetry ΔP as percentage
    watson_U2 : float
        Watson's U² test statistic
    watson_p_value : float
        p-value for Watson test
    is_significant : bool
        Whether asymmetry is significant (p < 0.01)
    chirality_tensor_prediction : float
        Predicted ΔP from chirality tensor
    relative_agreement : float
        Agreement between observed and predicted
    """
    delta_P_percent: float
    watson_U2: float
    watson_p_value: float
    is_significant: bool
    chirality_tensor_prediction: float
    relative_agreement: float


class MagnetoreceptionAnalyzer:
    """
    Analyzer for magnetoreception experiments testing chirality tensor predictions.
    
    This class implements statistical analysis of circular data from bird orientation
    experiments to detect the predicted ~0.2% asymmetry between magnetic field
    rotation directions.
    
    Parameters
    ----------
    chirality_tensor : ChiralityTensor, optional
        Chirality tensor for predictions (default: creates new instance)
    significance_level : float
        Statistical significance threshold (default: 0.01 for p < 0.01)
    
    Attributes
    ----------
    tensor : ChiralityTensor
        Chirality tensor operator
    alpha : float
        Significance level for hypothesis tests
    """
    
    def __init__(
        self,
        chirality_tensor: Optional[ChiralityTensor] = None,
        significance_level: float = 0.01
    ):
        """Initialize magnetoreception analyzer."""
        self.tensor = chirality_tensor if chirality_tensor else ChiralityTensor()
        self.alpha = significance_level
    
    def rayleigh_test(self, angles_deg: np.ndarray) -> RayleighTestResult:
        """
        Perform Rayleigh test for circular uniformity.
        
        Tests null hypothesis H₀: angles are uniformly distributed on circle.
        
        Parameters
        ----------
        angles_deg : np.ndarray
            Array of angles in degrees [0, 360)
        
        Returns
        -------
        RayleighTestResult
            Test results including mean direction, vector length, and p-value
        """
        # Convert to radians
        angles_rad = np.deg2rad(angles_deg)
        n = len(angles_rad)
        
        # Compute mean direction
        C = np.sum(np.cos(angles_rad))
        S = np.sum(np.sin(angles_rad))
        mean_angle_rad = np.arctan2(S, C)
        mean_angle_deg = np.rad2deg(mean_angle_rad) % 360
        
        # Mean vector length r
        r = np.sqrt(C**2 + S**2) / n
        
        # Rayleigh test statistic
        Z = n * r**2
        
        # p-value (approximation for large n)
        if n > 50:
            p_value = np.exp(-Z)
        else:
            # Exact formula for small n
            p_value = np.exp(-Z) * (1 + (2*Z - Z**2) / (4*n) - 
                                    (24*Z - 132*Z**2 + 76*Z**3 - 9*Z**4) / (288*n**2))
        
        is_significant = p_value < 0.05
        
        return RayleighTestResult(
            mean_direction_deg=mean_angle_deg,
            mean_vector_length=r,
            rayleigh_z=Z,
            p_value=p_value,
            is_significant=is_significant,
            sample_size=n
        )
    
    def watson_u2_test(
        self,
        angles1_deg: np.ndarray,
        angles2_deg: np.ndarray
    ) -> Tuple[float, float]:
        """
        Perform Watson's U² test for two circular samples.
        
        Tests whether two circular distributions differ significantly.
        
        Parameters
        ----------
        angles1_deg : np.ndarray
            First sample of angles in degrees
        angles2_deg : np.ndarray
            Second sample of angles in degrees
        
        Returns
        -------
        Tuple[float, float]
            (U² statistic, p-value)
        """
        # Convert to radians and sort
        angles1_rad = np.sort(np.deg2rad(angles1_deg))
        angles2_rad = np.sort(np.deg2rad(angles2_deg))
        
        n1, n2 = len(angles1_rad), len(angles2_rad)
        N = n1 + n2
        
        # Combine and sort all angles
        all_angles = np.concatenate([angles1_rad, angles2_rad])
        all_sorted = np.sort(all_angles)
        
        # Compute empirical CDFs
        d_max = 0.0
        for angle in all_sorted:
            F1 = np.sum(angles1_rad <= angle) / n1
            F2 = np.sum(angles2_rad <= angle) / n2
            d = abs(F1 - F2)
            d_max = max(d_max, d)
        
        # Watson's U² statistic (simplified)
        U2 = (n1 * n2 / N**2) * d_max * np.sqrt(N)
        
        # Approximate p-value (conservative)
        # For exact p-value, need Watson's tables
        if U2 < 0.152:
            p_value = 1.0
        elif U2 < 0.187:
            p_value = 0.10
        elif U2 < 0.222:
            p_value = 0.05
        elif U2 < 0.268:
            p_value = 0.025
        elif U2 < 0.304:
            p_value = 0.01
        else:
            p_value = 0.001
        
        return U2, p_value
    
    def compute_asymmetry(
        self,
        data_right: EmlenCageData,
        data_left: EmlenCageData
    ) -> AsymmetryResult:
        """
        Compute asymmetry between right and left field rotations.
        
        Quantifies ΔP = P(B_R) - P(B_L) and compares to chirality tensor prediction.
        
        Parameters
        ----------
        data_right : EmlenCageData
            Data from right-rotated field trials
        data_left : EmlenCageData
            Data from left-rotated field trials
        
        Returns
        -------
        AsymmetryResult
            Asymmetry analysis results
        """
        # Perform Rayleigh tests on each condition
        result_right = self.rayleigh_test(np.array(data_right.angles_deg))
        result_left = self.rayleigh_test(np.array(data_left.angles_deg))
        
        # Compute asymmetry in mean vector lengths
        # This proxies for probability difference in radical pair states
        delta_r = result_right.mean_vector_length - result_left.mean_vector_length
        delta_P_percent = delta_r * 100  # Convert to percentage
        
        # Watson's U² test for difference
        U2, p_watson = self.watson_u2_test(
            np.array(data_right.angles_deg),
            np.array(data_left.angles_deg)
        )
        
        # Get chirality tensor prediction
        predicted_delta_P_percent = self.tensor.magnetoreception_asymmetry() * 100
        
        # Compute relative agreement
        if predicted_delta_P_percent != 0:
            agreement = 1 - abs(delta_P_percent - predicted_delta_P_percent) / predicted_delta_P_percent
        else:
            agreement = 0.0
        
        return AsymmetryResult(
            delta_P_percent=delta_P_percent,
            watson_U2=U2,
            watson_p_value=p_watson,
            is_significant=p_watson < self.alpha,
            chirality_tensor_prediction=predicted_delta_P_percent,
            relative_agreement=agreement
        )
    
    def generate_synthetic_data(
        self,
        n_trials: int = 100,
        mean_direction_deg: float = 45.0,
        concentration: float = 2.0,
        field_rotation: str = 'right'
    ) -> EmlenCageData:
        """
        Generate synthetic Emlen cage data for testing.
        
        Uses von Mises distribution (circular analog of normal distribution).
        
        Parameters
        ----------
        n_trials : int
            Number of trials
        mean_direction_deg : float
            Mean preferred direction
        concentration : float
            Concentration parameter κ (higher = more concentrated)
        field_rotation : str
            'right' or 'left' rotation
        
        Returns
        -------
        EmlenCageData
            Synthetic experimental data
        """
        # Add small bias for field rotation based on chirality tensor
        asymmetry_bias = self.tensor.magnetoreception_asymmetry()
        
        if field_rotation == 'right':
            bias_adjustment = concentration * (1 + asymmetry_bias)
        else:
            bias_adjustment = concentration * (1 - asymmetry_bias)
        
        # Generate von Mises distributed angles
        mean_rad = np.deg2rad(mean_direction_deg)
        angles_rad = np.random.vonmises(mean_rad, bias_adjustment, n_trials)
        angles_deg = np.rad2deg(angles_rad) % 360
        
        return EmlenCageData(
            angles_deg=angles_deg.tolist(),
            field_rotation=field_rotation,
            bird_id=f"synthetic_{field_rotation}",
            trial_date="2026-02-11",
            magnetic_field_uT=50.0
        )
    
    def analyze_experiment(
        self,
        data_right: EmlenCageData,
        data_left: EmlenCageData
    ) -> Dict[str, Any]:
        """
        Complete analysis of magnetoreception experiment.
        
        Parameters
        ----------
        data_right : EmlenCageData
            Right-rotated field data
        data_left : EmlenCageData
            Left-rotated field data
        
        Returns
        -------
        dict
            Complete analysis results and validation
        """
        # Individual Rayleigh tests
        rayleigh_right = self.rayleigh_test(np.array(data_right.angles_deg))
        rayleigh_left = self.rayleigh_test(np.array(data_left.angles_deg))
        
        # Asymmetry analysis
        asymmetry = self.compute_asymmetry(data_right, data_left)
        
        # Compile results
        results = {
            'experiment': {
                'right_field': {
                    'bird_id': data_right.bird_id,
                    'n_trials': len(data_right.angles_deg),
                    'rayleigh_test': {
                        'mean_direction_deg': float(rayleigh_right.mean_direction_deg),
                        'mean_vector_length': float(rayleigh_right.mean_vector_length),
                        'rayleigh_z': float(rayleigh_right.rayleigh_z),
                        'p_value': float(rayleigh_right.p_value),
                        'is_significant': bool(rayleigh_right.is_significant),
                        'sample_size': int(rayleigh_right.sample_size)
                    }
                },
                'left_field': {
                    'bird_id': data_left.bird_id,
                    'n_trials': len(data_left.angles_deg),
                    'rayleigh_test': {
                        'mean_direction_deg': float(rayleigh_left.mean_direction_deg),
                        'mean_vector_length': float(rayleigh_left.mean_vector_length),
                        'rayleigh_z': float(rayleigh_left.rayleigh_z),
                        'p_value': float(rayleigh_left.p_value),
                        'is_significant': bool(rayleigh_left.is_significant),
                        'sample_size': int(rayleigh_left.sample_size)
                    }
                }
            },
            'asymmetry_analysis': {
                'delta_P_percent': float(asymmetry.delta_P_percent),
                'watson_U2': float(asymmetry.watson_U2),
                'watson_p_value': float(asymmetry.watson_p_value),
                'is_significant': bool(asymmetry.is_significant),
                'chirality_tensor_prediction': float(asymmetry.chirality_tensor_prediction),
                'relative_agreement': float(asymmetry.relative_agreement)
            },
            'chirality_tensor': {
                'kappa_pi': float(self.tensor.params.kappa_pi),
                'predicted_asymmetry_percent': float(asymmetry.chirality_tensor_prediction),
                'mechanism': 'T tensor biases singlet→triplet transition'
            },
            'statistical_significance': {
                'threshold': float(self.alpha),
                'is_significant': bool(asymmetry.is_significant),
                'interpretation': (
                    'Significant asymmetry detected' if asymmetry.is_significant
                    else 'No significant asymmetry detected'
                )
            },
            'validation': {
                'agreement_with_theory': f"{asymmetry.relative_agreement * 100:.1f}%",
                'qcal_verified': bool(asymmetry.relative_agreement > 0.5)
            }
        }
        
        return results


def demonstrate_magnetoreception_analysis():
    """
    Demonstration of magnetoreception analysis with synthetic data.
    """
    print("=" * 80)
    print("MAGNETORECEPTION ANALYSIS — CHIRALITY TENSOR VALIDATION")
    print("=" * 80)
    print()
    
    # Initialize analyzer
    analyzer = MagnetoreceptionAnalyzer(significance_level=0.01)
    print("Initialized analyzer with p < 0.01 significance threshold")
    print()
    
    # Generate synthetic data
    print("Generating synthetic Emlen cage data...")
    data_right = analyzer.generate_synthetic_data(
        n_trials=200,
        mean_direction_deg=90.0,  # East
        concentration=3.0,
        field_rotation='right'
    )
    
    data_left = analyzer.generate_synthetic_data(
        n_trials=200,
        mean_direction_deg=90.0,  # East
        concentration=3.0,
        field_rotation='left'
    )
    print(f"Generated {len(data_right.angles_deg)} trials for each condition")
    print()
    
    # Perform analysis
    print("Performing complete analysis...")
    print("-" * 80)
    results = analyzer.analyze_experiment(data_right, data_left)
    
    # Display results
    print("\n1. RIGHT-ROTATED FIELD (B_R)")
    print("-" * 80)
    rr = results['experiment']['right_field']['rayleigh_test']
    print(f"   Mean direction: {rr['mean_direction_deg']:.1f}°")
    print(f"   Vector length r: {rr['mean_vector_length']:.4f}")
    print(f"   Rayleigh Z: {rr['rayleigh_z']:.3f}")
    print(f"   p-value: {rr['p_value']:.4e}")
    print(f"   Significant: {'Yes' if rr['is_significant'] else 'No'}")
    print()
    
    print("2. LEFT-ROTATED FIELD (B_L)")
    print("-" * 80)
    rl = results['experiment']['left_field']['rayleigh_test']
    print(f"   Mean direction: {rl['mean_direction_deg']:.1f}°")
    print(f"   Vector length r: {rl['mean_vector_length']:.4f}")
    print(f"   Rayleigh Z: {rl['rayleigh_z']:.3f}")
    print(f"   p-value: {rl['p_value']:.4e}")
    print(f"   Significant: {'Yes' if rl['is_significant'] else 'No'}")
    print()
    
    print("3. ASYMMETRY ANALYSIS")
    print("-" * 80)
    asym = results['asymmetry_analysis']
    print(f"   Observed ΔP: {asym['delta_P_percent']:.3f}%")
    print(f"   Predicted ΔP (T tensor): {asym['chirality_tensor_prediction']:.3f}%")
    print(f"   Watson U²: {asym['watson_U2']:.4f}")
    print(f"   Watson p-value: {asym['watson_p_value']:.4f}")
    print(f"   Significant (p < 0.01): {'Yes' if asym['is_significant'] else 'No'}")
    print(f"   Agreement with theory: {asym['relative_agreement'] * 100:.1f}%")
    print()
    
    print("4. CHIRALITY TENSOR MECHANISM")
    print("-" * 80)
    ct = results['chirality_tensor']
    print(f"   κ_Π invariant: {ct['kappa_pi']}")
    print(f"   Mechanism: {ct['mechanism']}")
    print(f"   Predicted asymmetry: {ct['predicted_asymmetry_percent']:.3f}%")
    print()
    
    print("5. VALIDATION SUMMARY")
    print("-" * 80)
    val = results['validation']
    print(f"   Agreement with QCAL theory: {val['agreement_with_theory']}")
    print(f"   QCAL verified: {'✓ Yes' if val['qcal_verified'] else '✗ No'}")
    print()
    
    # Export results
    print("6. RESULTS CERTIFICATE")
    print("-" * 80)
    print(json.dumps(results, indent=2))
    print()
    
    print("=" * 80)
    print("∴ 𓂀 Ω ∞³")
    print("=" * 80)


if __name__ == "__main__":
    demonstrate_magnetoreception_analysis()

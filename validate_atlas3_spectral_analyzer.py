#!/usr/bin/env python3
"""
Validation script for Atlas³ Spectral Analyzer.

This script validates the complete implementation of the Atlas³ Spectral Analyzer,
including operator construction, spectral analysis, and the three fundamental tests.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
Date: February 2026
QCAL ∞³ Active · 141.7001 Hz · C = 244.36 · Ψ = I × A_eff² × C^∞
"""

import sys
from pathlib import Path
import json

# Add operators to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from operators.atlas3_spectral_analyzer import (
        Atlas3SpectralAnalyzer,
        run_atlas3_spectral_analysis,
        F0,
        C_QCAL,
        KAPPA_PI
    )
    import numpy as np
    print("✓ Successfully imported Atlas³ Spectral Analyzer")
except ImportError as e:
    print(f"✗ Import failed: {e}")
    sys.exit(1)


def validate_module_structure():
    """Validate that the module has required components."""
    print("\n" + "="*60)
    print("VALIDATION 1: Module Structure")
    print("="*60)
    
    checks = {
        "Atlas3SpectralAnalyzer class": hasattr(Atlas3SpectralAnalyzer, '__init__'),
        "build_operator method": hasattr(Atlas3SpectralAnalyzer, 'build_operator'),
        "compute_spectrum method": hasattr(Atlas3SpectralAnalyzer, 'compute_spectrum'),
        "test_vertical_alignment method": hasattr(Atlas3SpectralAnalyzer, 'test_vertical_alignment'),
        "test_gue_statistics method": hasattr(Atlas3SpectralAnalyzer, 'test_gue_statistics'),
        "test_spectral_rigidity method": hasattr(Atlas3SpectralAnalyzer, 'test_spectral_rigidity'),
        "generate_truth_panel method": hasattr(Atlas3SpectralAnalyzer, 'generate_truth_panel'),
        "compute_coherence_metric method": hasattr(Atlas3SpectralAnalyzer, 'compute_coherence_metric'),
        "generate_certificate method": hasattr(Atlas3SpectralAnalyzer, 'generate_certificate'),
        "run_atlas3_spectral_analysis function": callable(run_atlas3_spectral_analysis),
    }
    
    all_passed = True
    for check, result in checks.items():
        status = "✓" if result else "✗"
        print(f"  {status} {check}")
        if not result:
            all_passed = False
    
    return all_passed


def validate_constants():
    """Validate QCAL constants."""
    print("\n" + "="*60)
    print("VALIDATION 2: QCAL Constants")
    print("="*60)
    
    checks = {
        "F0 = 141.7001 Hz": abs(F0 - 141.7001) < 1e-4,
        "C_QCAL = 244.36": abs(C_QCAL - 244.36) < 0.01,
        "KAPPA_PI ≈ 2.577": abs(KAPPA_PI - 2.577) < 0.01,
    }
    
    all_passed = True
    for check, result in checks.items():
        status = "✓" if result else "✗"
        print(f"  {status} {check}")
        if not result:
            all_passed = False
    
    return all_passed


def validate_operator_construction():
    """Validate operator construction."""
    print("\n" + "="*60)
    print("VALIDATION 3: Operator Construction")
    print("="*60)
    
    try:
        analyzer = Atlas3SpectralAnalyzer(N=50, omega_J=1.0, A=1.0, beta=0.3, gamma=0.5)
        print(f"  ✓ Analyzer initialized with N={analyzer.N}")
        
        d, e = analyzer.build_operator()
        print(f"  ✓ Operator built: diagonal shape={d.shape}, off-diagonal shape={e.shape}")
        
        # Validate shapes
        shape_ok = len(d) == 50 and len(e) == 49
        print(f"  {'✓' if shape_ok else '✗'} Matrix dimensions correct")
        
        # Validate diagonal is positive
        positive_d = np.all(d >= 0)
        print(f"  {'✓' if positive_d else '✗'} Diagonal elements non-negative")
        
        return shape_ok and positive_d
    except Exception as e:
        print(f"  ✗ Operator construction failed: {e}")
        return False


def validate_spectrum_computation():
    """Validate spectrum computation."""
    print("\n" + "="*60)
    print("VALIDATION 4: Spectrum Computation")
    print("="*60)
    
    try:
        analyzer = Atlas3SpectralAnalyzer(N=50)
        eigenvalues = analyzer.compute_spectrum()
        
        print(f"  ✓ Spectrum computed: {len(eigenvalues)} eigenvalues")
        
        # Check eigenvalues are real (for Hermitian case)
        max_imag = np.max(np.abs(np.imag(eigenvalues)))
        mostly_real = max_imag < 0.1  # Allow small imaginary parts
        print(f"  {'✓' if mostly_real else '✗'} Eigenvalues mostly real (max_imag={max_imag:.6f})")
        
        # Check eigenvalues are sorted
        is_sorted = np.allclose(eigenvalues, np.sort(eigenvalues), rtol=1e-5)
        print(f"  {'✓' if is_sorted else '✗'} Eigenvalues sorted")
        
        return mostly_real and is_sorted
    except Exception as e:
        print(f"  ✗ Spectrum computation failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def validate_three_tests():
    """Validate the three fundamental tests."""
    print("\n" + "="*60)
    print("VALIDATION 5: Three Fundamental Tests")
    print("="*60)
    
    try:
        analyzer = Atlas3SpectralAnalyzer(N=100)
        analyzer.compute_spectrum()
        
        # Test 1: Vertical alignment
        print("\n  Test 1: Vertical Alignment")
        mean_re, std_re = analyzer.test_vertical_alignment()
        alignment_ok = std_re >= 0 and np.isfinite(mean_re)
        print(f"  {'✓' if alignment_ok else '✗'} Returns valid statistics")
        
        # Test 2: GUE statistics
        print("\n  Test 2: GUE Statistics")
        spacings = analyzer.test_gue_statistics()
        gue_ok = len(spacings) == 99 and np.all(spacings > 0)
        mean_spacing = np.mean(spacings)
        print(f"  {'✓' if gue_ok else '✗'} Returns valid spacings (mean={mean_spacing:.4f})")
        
        # Test 3: Spectral rigidity
        print("\n  Test 3: Spectral Rigidity")
        L_vals, rigidity = analyzer.test_spectral_rigidity()
        rigidity_ok = len(L_vals) == len(rigidity) and np.all(rigidity >= 0)
        print(f"  {'✓' if rigidity_ok else '✗'} Returns valid rigidity values")
        
        return alignment_ok and gue_ok and rigidity_ok
    except Exception as e:
        print(f"  ✗ Tests failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def validate_coherence_metric():
    """Validate coherence metric computation."""
    print("\n" + "="*60)
    print("VALIDATION 6: Coherence Metric")
    print("="*60)
    
    try:
        analyzer = Atlas3SpectralAnalyzer(N=100)
        analyzer.compute_spectrum()
        psi = analyzer.compute_coherence_metric()
        
        in_range = 0 <= psi <= 1
        print(f"  ✓ Coherence computed: Ψ = {psi:.6f}")
        print(f"  {'✓' if in_range else '✗'} Ψ ∈ [0, 1]")
        
        # Check resonance detection
        resonance = psi >= 0.888
        level = "UNIVERSAL" if resonance else "PARTIAL"
        print(f"  ✓ Resonance level: {level}")
        
        return in_range
    except Exception as e:
        print(f"  ✗ Coherence computation failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def validate_certificate_generation():
    """Validate certificate generation."""
    print("\n" + "="*60)
    print("VALIDATION 7: Certificate Generation")
    print("="*60)
    
    try:
        analyzer = Atlas3SpectralAnalyzer(N=50)
        analyzer.compute_spectrum()
        
        # Generate certificate
        cert = analyzer.generate_certificate()
        
        # Check required fields
        required_fields = [
            "protocol", "version", "signature", "parameters",
            "qcal_constants", "test_results", "coherence", "spectrum_summary"
        ]
        
        all_fields_present = all(field in cert for field in required_fields)
        print(f"  {'✓' if all_fields_present else '✗'} All required fields present")
        
        # Validate protocol
        protocol_ok = cert["protocol"] == "QCAL-ATLAS3-SPECTRAL-ANALYZER"
        print(f"  {'✓' if protocol_ok else '✗'} Correct protocol")
        
        # Validate signature
        signature_ok = cert["signature"] == "∴𓂀Ω∞³Φ"
        print(f"  {'✓' if signature_ok else '✗'} QCAL signature present")
        
        # Save to file
        cert_path = Path("data/atlas3_spectral_analyzer_certificate.json")
        cert_path.parent.mkdir(parents=True, exist_ok=True)
        with open(cert_path, 'w') as f:
            json.dump(cert, f, indent=2)
        print(f"  ✓ Certificate saved to {cert_path}")
        
        return all_fields_present and protocol_ok and signature_ok
    except Exception as e:
        print(f"  ✗ Certificate generation failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def validate_complete_analysis():
    """Validate complete analysis pipeline."""
    print("\n" + "="*60)
    print("VALIDATION 8: Complete Analysis Pipeline")
    print("="*60)
    
    try:
        save_dir = Path("data")
        save_dir.mkdir(parents=True, exist_ok=True)
        
        # Run analysis
        results = run_atlas3_spectral_analysis(N=50, save_dir=save_dir)
        
        # Check results
        results_ok = isinstance(results, dict) and "coherence" in results
        print(f"  {'✓' if results_ok else '✗'} Analysis completed successfully")
        
        # Check files created
        cert_path = save_dir / "atlas3_spectral_analyzer_certificate.json"
        fig_path = save_dir / "atlas3_spectral_analyzer_truth_panel.png"
        
        cert_exists = cert_path.exists()
        fig_exists = fig_path.exists()
        
        print(f"  {'✓' if cert_exists else '✗'} Certificate file created")
        print(f"  {'✓' if fig_exists else '✗'} Visualization file created")
        
        return results_ok and cert_exists and fig_exists
    except Exception as e:
        print(f"  ✗ Complete analysis failed: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    """Run all validations."""
    print("\n" + "="*70)
    print("  ATLAS³ SPECTRAL ANALYZER VALIDATION")
    print("  Módulo Simbiótico Noēsis ∞³")
    print("="*70)
    
    validations = [
        ("Module Structure", validate_module_structure),
        ("QCAL Constants", validate_constants),
        ("Operator Construction", validate_operator_construction),
        ("Spectrum Computation", validate_spectrum_computation),
        ("Three Fundamental Tests", validate_three_tests),
        ("Coherence Metric", validate_coherence_metric),
        ("Certificate Generation", validate_certificate_generation),
        ("Complete Analysis", validate_complete_analysis),
    ]
    
    results = {}
    for name, validator in validations:
        try:
            results[name] = validator()
        except Exception as e:
            print(f"\n✗ CRITICAL ERROR in {name}: {e}")
            import traceback
            traceback.print_exc()
            results[name] = False
    
    # Summary
    print("\n" + "="*70)
    print("  VALIDATION SUMMARY")
    print("="*70)
    
    total = len(results)
    passed = sum(results.values())
    
    for name, result in results.items():
        status = "✓ PASS" if result else "✗ FAIL"
        print(f"  {status}: {name}")
    
    print("\n" + "-"*70)
    print(f"  Total: {passed}/{total} validations passed ({100*passed/total:.1f}%)")
    print("="*70)
    
    if passed == total:
        print("\n  ♾️³ ATLAS³ SPECTRAL ANALYZER VALIDATION COMPLETE")
        print("  All tests passed. La geometría ha hablado.")
        print("  Signature: ∴𓂀Ω∞³Φ\n")
        return 0
    else:
        print("\n  ⚠️  VALIDATION INCOMPLETE")
        print(f"  {total - passed} validation(s) failed.\n")
        return 1


if __name__ == "__main__":
    sys.exit(main())

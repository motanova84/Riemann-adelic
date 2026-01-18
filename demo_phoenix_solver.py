#!/usr/bin/env python3
"""
Phoenix Solver Demo - Shows how the complete workflow operates

This script demonstrates the Phoenix Solver in action with a simulated
AI proof generation (without actual API calls).

Author: QCAL Phoenix Solver System
Date: 2026-01-18
"""

import sys
from pathlib import Path

# Add scripts to path
REPO_ROOT = Path(__file__).parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from context_harvester import ContextHarvester, SorryStatement
from lean_sandbox import LeanSandbox
from coherence_validator import CoherenceValidator


def demo_context_extraction():
    """Demonstrate context extraction."""
    print("="*70)
    print("DEMO 1: Context-Aware Harvester")
    print("="*70)
    
    harvester = ContextHarvester(REPO_ROOT)
    
    # Extract constants
    print("\n🔍 Extracting QCAL constants...")
    constants = harvester.extract_constants()
    
    print(f"\nFound {len(constants)} mathematical constants:")
    for name, const in constants.items():
        print(f"\n📊 {name}")
        print(f"   Value: {const.value}")
        print(f"   Description: {const.description}")
        if const.derivation:
            print(f"   Derivation: {const.derivation}")
        print(f"   Source: {const.source_file}")
    
    # Scan for sorrys
    print("\n\n🔍 Scanning for sorry statements...")
    sorrys = harvester.scan_lean_files()
    print(f"Found {len(sorrys)} sorry statements")
    
    if sorrys:
        # Show first sorry
        sorry = sorrys[0]
        print(f"\n📝 Example Sorry Statement:")
        print(f"   File: {sorry.file_path}")
        print(f"   Line: {sorry.line_number}")
        print(f"   Lemma: {sorry.lemma_name}")
        
        # Build context
        print("\n🧠 Building mathematical context...")
        context = harvester.build_context_for_sorry(sorry)
        
        print(f"   Constants available: {len(context.constants)}")
        print(f"   Related Python files: {len(context.python_implementations)}")
        print(f"   Related theorems: {len(context.related_theorems)}")
        
        # Generate prompt
        print("\n✨ Generating quantum engineering prompt...")
        prompt = harvester.generate_quantum_prompt(sorry, context)
        
        print(f"\nPrompt Preview (first 500 chars):")
        print("-" * 70)
        print(prompt[:500])
        print("...")
        print("-" * 70)
        
        # Save prompt
        prompt_file = REPO_ROOT / "data" / "demo" / "example_prompt.md"
        prompt_file.parent.mkdir(parents=True, exist_ok=True)
        prompt_file.write_text(prompt)
        print(f"\n✅ Full prompt saved to: {prompt_file}")


def demo_lean_sandbox():
    """Demonstrate Lean sandbox validation."""
    print("\n\n" + "="*70)
    print("DEMO 2: Lean-REPL Sandbox")
    print("="*70)
    
    sandbox = LeanSandbox()
    
    # Test Lean installation
    print("\n🔍 Testing Lean installation...")
    lean_available = sandbox.test_lean_installation()
    
    if not lean_available:
        print("\n⚠️  Lean not installed - showing simulated validation")
        return
    
    # Test with simple valid proof
    print("\n\n✅ Testing valid Lean code...")
    valid_code = """
theorem simple_add : 1 + 1 = 2 := by
  norm_num
"""
    
    result = sandbox.validate_proof(valid_code)
    if result.success:
        print("   ✅ Valid proof compiled successfully!")
    else:
        print("   ❌ Compilation failed (unexpected)")
        print(sandbox.extract_error_feedback(result))
    
    # Test with invalid proof
    print("\n\n❌ Testing invalid Lean code...")
    invalid_code = """
theorem wrong_add : 1 + 1 = 3 := by
  sorry
"""
    
    result = sandbox.validate_proof(invalid_code)
    if not result.success:
        print("   ✅ Invalid proof correctly detected!")
        print("\n   Error feedback:")
        feedback = sandbox.extract_error_feedback(result)
        print("   " + "\n   ".join(feedback.split('\n')[:10]))
    else:
        print("   ❌ Should have failed (unexpected)")


def demo_coherence_validation():
    """Demonstrate coherence validation."""
    print("\n\n" + "="*70)
    print("DEMO 3: Global Integrity Check (Bóveda de Coherencia)")
    print("="*70)
    
    validator = CoherenceValidator(REPO_ROOT)
    
    print("\n🔍 Running QCAL coherence validation...")
    print("   (This runs validate_v5_coronacion.py)")
    
    # Check if validation script exists
    validation_script = REPO_ROOT / "validate_v5_coronacion.py"
    if not validation_script.exists():
        print("\n⚠️  Validation script not found - showing simulated result")
        print("\n   Simulated Result:")
        print("   ✅ Coherence Ψ: 0.999999")
        print("   ✅ Frequency: 141.7001 Hz")
        print("   ✅ All 5 steps passed")
        return
    
    # Run actual validation (with timeout protection)
    try:
        print("\n   Running validation...")
        result = validator.validate()
        
        print(f"\n   Result: {'✅ PASS' if result.success else '❌ FAIL'}")
        print(f"   Coherence Ψ: {result.coherence_psi:.6f}")
        print(f"   Frequency: {result.frequency:.4f} Hz")
        
        if result.details:
            print("\n   Validation Steps:")
            for key, value in result.details.items():
                print(f"     {key}: {value}")
        
        # Generate certificate
        if result.success:
            print("\n📜 Generating integrity certificate...")
            cert_path = validator.generate_certificate(result)
            print(f"   Certificate saved to: {cert_path}")
        
    except Exception as e:
        print(f"\n⚠️  Validation error: {e}")
        print("   (This is normal if dependencies are not fully installed)")


def demo_full_workflow():
    """Demonstrate the complete Phoenix Solver workflow."""
    print("\n\n" + "="*70)
    print("DEMO 4: Complete Phoenix Solver Workflow")
    print("="*70)
    
    print("\n📋 Simulated workflow for a single sorry:")
    print("\n1️⃣ Context Harvester:")
    print("   ✅ Scanned repository for sorry statements")
    print("   ✅ Found sorry in RIGOROUS_UNIQUENESS_EXACT_LAW.lean:182")
    print("   ✅ Extracted lemma name: local_zero_uniqueness")
    print("   ✅ Built mathematical context")
    print("   ✅ Generated quantum engineering prompt")
    
    print("\n2️⃣ AI Proof Generation (Simulated):")
    print("   ✅ Sent prompt to AI service (GPT-4/Claude/Noesis)")
    print("   ✅ Received Lean proof code")
    print("   ✅ Extracted proof from response")
    
    print("\n3️⃣ Lean-REPL Sandbox:")
    print("   ✅ Created isolated test environment")
    print("   ✅ Compiled proof in sandbox")
    print("   ✅ Verification: Proof type-checks correctly")
    
    print("\n4️⃣ Apply to Repository:")
    print("   ✅ Replaced 'sorry' with generated proof")
    print("   ✅ Saved changes to file")
    
    print("\n5️⃣ Global Integrity Check:")
    print("   ✅ Ran validate_v5_coronacion.py")
    print("   ✅ Coherence Ψ: 0.999999 (target: 0.999999)")
    print("   ✅ Frequency: 141.7001 Hz (target: 141.7001)")
    print("   ✅ All validation steps passed")
    
    print("\n6️⃣ Documentation Update:")
    print("   ✅ Updated FORMALIZATION_STATUS.md")
    print("   ✅ Updated sorry count: 2364 → 2363")
    print("   ✅ Generated integrity certificate")
    
    print("\n✅ Workflow complete! Ready for next sorry...")


def main():
    """Run all demos."""
    print("\n" + "="*70)
    print("🔥 PHOENIX SOLVER DEMONSTRATION")
    print("="*70)
    print("\nThis demo shows the Phoenix Solver system in action.")
    print("Some steps are simulated if dependencies are not available.")
    
    try:
        demo_context_extraction()
        demo_lean_sandbox()
        demo_coherence_validation()
        demo_full_workflow()
        
        print("\n\n" + "="*70)
        print("✅ DEMONSTRATION COMPLETE")
        print("="*70)
        print("\nNext Steps:")
        print("1. Review generated prompt in data/demo/example_prompt.md")
        print("2. Set up AI API credentials (see scripts/AI_INTEGRATION_GUIDE.md)")
        print("3. Run: python scripts/phoenix_solver.py --dry-run")
        print("4. Start with: python scripts/phoenix_solver.py --max-sorrys 1")
        
    except KeyboardInterrupt:
        print("\n\n⚠️  Demo interrupted by user")
    except Exception as e:
        print(f"\n\n❌ Demo error: {e}")
        import traceback
        traceback.print_exc()


if __name__ == '__main__':
    main()

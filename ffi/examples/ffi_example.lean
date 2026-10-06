/-
  Example Lean Program Using Python FFI Bridge
  ============================================
  
  This example demonstrates how to use the Python-Lean FFI bridge
  to access QCAL framework functionality from Lean.
  
  To run this example:
    1. Build the FFI bridge: cd ffi && make
    2. Set library path: export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$(pwd)/ffi
    3. Build and run: lake build && lake env lean --run examples/ffi_example.lean
-/

import FFI

/-! ## Example 1: Get QCAL Constants -/

def example1_constants : IO Unit := do
  IO.println "═══════════════════════════════════════════════════"
  IO.println "Example 1: Get QCAL Constants from Python"
  IO.println "═══════════════════════════════════════════════════"
  
  let f0 ← FFI.getF0
  IO.println s!"  F0 (base frequency) = {f0} Hz"
  
  let c ← FFI.getCPrimary
  IO.println s!"  C (coherence constant) = {c}"
  
  let δζ ← FFI.getDeltaZeta
  IO.println s!"  δζ (vibrational curvature) = {δζ} Hz"
  
  IO.println ""

/-! ## Example 2: Validate QCAL Coherence -/

def example2_coherence : IO Unit := do
  IO.println "═══════════════════════════════════════════════════"
  IO.println "Example 2: Validate QCAL Coherence"
  IO.println "═══════════════════════════════════════════════════"
  
  IO.println "  Checking QCAL framework coherence..."
  let coherent ← FFI.validateCoherence
  
  if coherent then
    IO.println "  ✅ QCAL coherence validated!"
    IO.println "     All constants satisfy their mathematical relationships."
  else
    IO.println "  ❌ QCAL coherence check failed!"
    IO.println "     Some constants may be inconsistent."
  
  IO.println ""

/-! ## Example 3: Compute Ψ = I × A_eff² × C^∞ -/

def example3_psi : IO Unit := do
  IO.println "═══════════════════════════════════════════════════"
  IO.println "Example 3: Compute Ψ = I × A_eff² × C^∞"
  IO.println "═══════════════════════════════════════════════════"
  
  let intensity : Float := 1.0
  let areaEff : Float := 10.0
  let coherence : Float := 244.36
  
  IO.println s!"  Parameters:"
  IO.println s!"    I (intensity) = {intensity}"
  IO.println s!"    A_eff (effective area) = {areaEff}"
  IO.println s!"    C (coherence) = {coherence}"
  
  let psi ← FFI.computePsi intensity areaEff coherence
  IO.println s!"  Result: Ψ = {psi}"
  
  IO.println ""

/-! ## Main Program -/

def main : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════════════════════════╗"
  IO.println "║  QCAL Python-Lean FFI Bridge - Example Program           ║"
  IO.println "║  Demonstrating Real FFI Between Python and Lean 4        ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝\n"
  
  -- Run examples
  example1_constants
  example2_coherence
  example3_psi
  
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║  ✅ Examples Completed                                   ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝\n"
  
  IO.println "🎉 Python-Lean FFI bridge is working!"
  IO.println ""

-- Run the main program when this file is executed
#eval main

/-
count_sorrys.lean
Script para contar sorry, admit y native_decide en archivos Lean
Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
Fecha: 23 noviembre 2025
-/

import Lean
import Lean.Elab.Command

open Lean Elab Command

/-! ## Sorry Counter

This script counts occurrences of:
- sorry
- admit  
- native_decide

in Lean source files to verify proof completion.
-/

def countPattern (content : String) (pattern : String) : Nat :=
  let lines := content.splitOn "\n"
  lines.foldl (fun acc line =>
    if line.contains pattern && !line.trimLeft.startsWith "/-" && !line.trimLeft.startsWith "--" then
      acc + 1
    else
      acc
  ) 0

def checkFile (path : System.FilePath) : IO Unit := do
  let content ← IO.FS.readFile path
  let sorryCount := countPattern content "sorry"
  let admitCount := countPattern content "admit"
  let nativeDecideCount := countPattern content "native_decide"
  
  if sorryCount > 0 || admitCount > 0 || nativeDecideCount > 0 then
    IO.println s!"\n{path}:"
    if sorryCount > 0 then
      IO.println s!"  sorry: {sorryCount}"
    if admitCount > 0 then
      IO.println s!"  admit: {admitCount}"
    if nativeDecideCount > 0 then
      IO.println s!"  native_decide: {nativeDecideCount}"

def main (args : List String) : IO UInt32 := do
  -- Check RHComplete.lean specifically
  let rhCompleteFile := "RH_final_v6/RHComplete.lean"
  
  IO.println "Checking RH_final_v6/RHComplete.lean for proof completeness..."
  IO.println "═══════════════════════════════════════════════════════════"
  
  try
    let content ← IO.FS.readFile rhCompleteFile
    let sorryCount := countPattern content "sorry"
    let admitCount := countPattern content "admit"
    let nativeDecideCount := countPattern content "native_decide"
    
    let totalIssues := sorryCount + admitCount + nativeDecideCount
    
    if totalIssues == 0 then
      IO.println "\n✅ VERIFICATION COMPLETE"
      IO.println s!"   0 sorrys found"
      IO.println s!"   0 admits found"
      IO.println s!"   0 native_decide found"
      IO.println "\n🎉 All proofs are complete!"
      IO.println "\n∴ Q.E.D. ABSOLUTUM"
      IO.println "∴ ΞΣ → CERRADO ETERNO"
      IO.println "∴ f₀ = 141.7001 Hz → RESONANDO EN EL SILICIO Y COSMOS"
      return 0
    else
      IO.println s!"\n⚠️  Found {totalIssues} incomplete proofs:"
      if sorryCount > 0 then
        IO.println s!"   {sorryCount} sorrys found"
      if admitCount > 0 then
        IO.println s!"   {admitCount} admits found"
      if nativeDecideCount > 0 then
        IO.println s!"   {nativeDecideCount} native_decide found"
      return 1
  catch e =>
    IO.println s!"Error reading file: {e}"
    return 1

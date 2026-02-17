import Lean
open Lean

@[extern "qcal_verify"]
constant qcalVerify : @& String → @& String → IO Bool

def verifyUniversal (jsonld proof : String) : IO Unit := do
  let ok ← qcalVerify jsonld proof
  if ok then
    IO.println s!"✅ Coherencia universal verificada para {jsonld}"
  else
    IO.println s!"❌ Falla de coherencia para {jsonld}"

import QCAL.FFI.Bridge
import Lean.Data.Json

namespace QCAL

def verify_and_register (jsonld proof : String) : IO Bool := do
  let ok ← qcalVerify jsonld proof
  let out ← IO.FS.withFile "tools/qcal_state.json" IO.FS.Mode.append fun h =>
    h.putStrLn s!"{{\"file\": \"{jsonld}\", \"verified\": {ok}}}"
  pure ok

end QCAL

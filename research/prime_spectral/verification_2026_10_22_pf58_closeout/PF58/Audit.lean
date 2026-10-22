import XiBand58
import Reinmann.XiFinitePFCertified

example : Reinmann.FinitePF Reinmann.XiMomentCoeff 58 := Reinmann.XiBand58.finitePF58

open Lean in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut seen : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m == `XiBand58 || "XiBand58.".isPrefixOf m.toString then
      let d := env.header.moduleData[i]!
      for j in [:d.constNames.size] do
        let n := d.constNames[j]!
        if d.constants[j]!.isTheorem && !seen.contains n then
          seen := seen.insert n
          names := names.push n
  for n in names.qsort Name.lt do
    let axioms ← collectAxioms n
    if axioms.isEmpty then
      logInfo m!"'{n.toString}' does not depend on any axioms"
    else
      logInfo m!"'{n.toString}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
  logInfo m!"BAND_AUDIT_COUNT {names.size}"

#print axioms Reinmann.XiFinitePFCertified.finitePF58_of_low_height_width
#print axioms Reinmann.XiFinitePFCertified.finitePF58

import Reinmann.XiFinitePFCertified
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if "Reinmann.PNTPlus.".isPrefixOf m.toString ||
        m == `Reinmann.XiHadamardProduct || m == `Reinmann.XiFinitePFCertified then
      IO.println s!"AUDIT_MODULE {m}"
      let d := env.header.moduleData[i]!
      for j in [:d.constNames.size] do
        if d.constants[j]!.isTheorem then
          names := names.push d.constNames[j]!
  for n in names.qsort Name.lt do
    let axioms ← collectAxioms n
    if axioms.isEmpty then
      logInfo m!"'{n}' does not depend on any axioms"
    else
      logInfo m!"'{n}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"

#print axioms Reinmann.XiHadamardProduct.foldedXi_order
#print axioms Reinmann.XiHadamardProduct.summable_inverse_zeros
#print axioms Reinmann.XiHadamardProduct.foldedXi_product
#print axioms Reinmann.XiHadamardProduct.katkovaSectorBridge
#print axioms Reinmann.XiFinitePFCertified.finitePF43
#print axioms Reinmann.XiFinitePFCertified.finitePF58

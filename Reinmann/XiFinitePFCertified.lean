/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiHadamardProduct
import XiRectangle

/-! Finite-order consequences for the actual ordinary Xi coefficient sequence.
PF43 uses the proved rectangle and sector bridge. PF58 still asks for the
external 7/8 zero-free half-plane, which is not imported into this toolchain.
These fixed-rank statements do not prove the unbounded-rank criterion or RH. -/
namespace Reinmann.XiFinitePFCertified

/-- All ordered minors through rank 43, at every shift, are nonnegative. -/
theorem finitePF43 : FinitePF XiMomentCoeff 43 :=
  XiRectangle.finitePF43 (XiHadamardProduct.katkovaSectorBridge 43 (by norm_num))

/-- The sector and low-height inputs are discharged; the 7/8 input remains. -/
theorem finitePF58 (hq : QuasiRiemannHypothesisSevenEighths) :
    FinitePF XiMomentCoeff 58 :=
  XiRectangle.finitePF58 hq (XiHadamardProduct.katkovaSectorBridge 58 (by norm_num))

end Reinmann.XiFinitePFCertified

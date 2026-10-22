/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiHadamardProduct
import Reinmann.FiniteHeightPFCalibration
import XiRectangle
import XiBand58
import XiBand97

/-! Finite-order consequences for the actual ordinary Xi coefficient sequence.
PF43 uses the low rectangle and sector bridge. PF58 uses the finite-width
height-19 box; PF97 uses the height-32 box. The separate external seven-eighths wrapper is retained.
These fixed-rank statements do not prove the unbounded-rank criterion or RH. -/
namespace Reinmann.XiFinitePFCertified

/-- All ordered minors through rank 43, at every shift, are nonnegative. -/
theorem finitePF43 : FinitePF XiMomentCoeff 43 :=
  XiRectangle.finitePF43 (XiHadamardProduct.katkovaSectorBridge 43 (by norm_num))

/-- The sector and low-height inputs are discharged; the 7/8 input remains. -/
theorem finitePF58_of_sevenEighths (hq : QuasiRiemannHypothesisSevenEighths) :
    FinitePF XiMomentCoeff 58 :=
  XiRectangle.finitePF58 hq (XiHadamardProduct.katkovaSectorBridge 58 (by norm_num))

/-- The alternative finite-height input suffices on the existing toolchain. -/
theorem finitePF58_of_low_height_width
    (hband : FiniteHeightPFCalibration.LowHeightWidth (3 / 8) 19) :
    FinitePF XiMomentCoeff 58 :=
  FiniteHeightPFCalibration.finitePF58_of_two_bands XiRectangle.zetaNoLowStripZero hband

/-- All ordered minors through rank 58, using only local Lean 4.30 certificates. -/
theorem finitePF58 : FinitePF XiMomentCoeff 58 := XiBand58.finitePF58

/-- The finite-width alternative for rank 97, using the existing first-zero bound. -/
theorem finitePF97_of_low_height_width
    (hband : FiniteHeightPFCalibration.LowHeightWidth (9 / 40) 32) :
    FinitePF XiMomentCoeff 97 :=
  FiniteHeightPFCalibration.finitePF97_of_low_height_width XiRectangle.zetaNoLowStripZero hband

/-- All ordered minors through rank 97, using only local Lean 4.30 certificates. -/
theorem finitePF97 : FinitePF XiMomentCoeff 97 := XiBand97.finitePF97

end Reinmann.XiFinitePFCertified

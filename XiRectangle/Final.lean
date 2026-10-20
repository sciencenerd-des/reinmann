/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import XiRectangle.Tile000
import XiRectangle.Tile001
import XiRectangle.Tile002
import XiRectangle.Tile003
import XiRectangle.Tile004
import XiRectangle.Tile005
import XiRectangle.Tile006
import XiRectangle.Tile007
import XiRectangle.Tile008
import XiRectangle.Tile009
import XiRectangle.Tile010
import XiRectangle.Tile011
import XiRectangle.Tile012
import XiRectangle.Tile013
import XiRectangle.Tile014
import XiRectangle.Tile015
import XiRectangle.Tile016
import XiRectangle.Tile017
import XiRectangle.Tile018
import XiRectangle.Tile019
import XiRectangle.Tile020
import XiRectangle.Tile021
import XiRectangle.Tile022
import XiRectangle.Tile023
import XiRectangle.Tile024
import XiRectangle.Tile025
import XiRectangle.Tile026
import XiRectangle.Tile027
import XiRectangle.Tile028
import XiRectangle.Tile029
import XiRectangle.Tile030
import XiRectangle.Tile031
import XiRectangle.Tile032
import XiRectangle.Tile033
import XiRectangle.Tile034
import XiRectangle.Tile035
import XiRectangle.Tile036
import XiRectangle.Tile037
import XiRectangle.Tile038
import XiRectangle.Tile039
import XiRectangle.Tile040
import XiRectangle.Tile041
import XiRectangle.Tile042
import XiRectangle.Tile043
import XiRectangle.Cover
import Reinmann.QuasiRHInputs
import Reinmann.XiAnnihilator

/-! A finite certificate for actual Xi on a closed rectangle. This does not
assert the Riemann hypothesis, nor all-order Pólya-frequency positivity. -/
noncomputable section
namespace Reinmann.XiRectangle

theorem all_tiles_nonzero (i:Fin Data.count) {z:ℂ}
    (hz:‖z-Data.centre i‖≤(Data.radius i:ℝ)) : xiCompleted z≠0 := by
  fin_cases i
  · exact Tile000.nonzero hz
  · exact Tile001.nonzero hz
  · exact Tile002.nonzero hz
  · exact Tile003.nonzero hz
  · exact Tile004.nonzero hz
  · exact Tile005.nonzero hz
  · exact Tile006.nonzero hz
  · exact Tile007.nonzero hz
  · exact Tile008.nonzero hz
  · exact Tile009.nonzero hz
  · exact Tile010.nonzero hz
  · exact Tile011.nonzero hz
  · exact Tile012.nonzero hz
  · exact Tile013.nonzero hz
  · exact Tile014.nonzero hz
  · exact Tile015.nonzero hz
  · exact Tile016.nonzero hz
  · exact Tile017.nonzero hz
  · exact Tile018.nonzero hz
  · exact Tile019.nonzero hz
  · exact Tile020.nonzero hz
  · exact Tile021.nonzero hz
  · exact Tile022.nonzero hz
  · exact Tile023.nonzero hz
  · exact Tile024.nonzero hz
  · exact Tile025.nonzero hz
  · exact Tile026.nonzero hz
  · exact Tile027.nonzero hz
  · exact Tile028.nonzero hz
  · exact Tile029.nonzero hz
  · exact Tile030.nonzero hz
  · exact Tile031.nonzero hz
  · exact Tile032.nonzero hz
  · exact Tile033.nonzero hz
  · exact Tile034.nonzero hz
  · exact Tile035.nonzero hz
  · exact Tile036.nonzero hz
  · exact Tile037.nonzero hz
  · exact Tile038.nonzero hz
  · exact Tile039.nonzero hz
  · exact Tile040.nonzero hz
  · exact Tile041.nonzero hz
  · exact Tile042.nonzero hz
  · exact Tile043.nonzero hz

theorem quarter_nonzero : ∀ z ∈ XiAdaptiveTiles.quarter (141/10), xiCompleted z≠0 := by
  intro z hz
  obtain ⟨i,hi⟩ := Cover.quarter_covered z hz
  exact all_tiles_nonzero i hi

theorem rectangle_nonzero {z:ℂ} (hx0:0≤z.re) (hx1:z.re≤1)
    (hy:|z.im|≤(141/10:ℝ)) : xiCompleted z≠0 :=
  XiAdaptiveTiles.xi_rectangle_nonzero_of_quarter quarter_nonzero hx0 hx1 hy

theorem zetaNoLowStripZero : ZetaNoLowStripZero (141/10) := by
  intro s hs
  by_contra h
  have hxi := rectangle_nonzero hs.2.1.le hs.2.2.le (not_le.mp h).le
  exact hxi (XiAnnihilator.xi_zero_of_strip_zero hs.1 hs.2.1 hs.2.2)

/-- The sector bridge remains an explicit classical input. -/
theorem finitePF43 (hB:KatkovaSectorBridge 43) : FinitePF XiMomentCoeff 43 :=
  xi_finitePF43_of_classical zetaNoLowStripZero hB

theorem finitePF58 (hq:QuasiRiemannHypothesisSevenEighths) (hB:KatkovaSectorBridge 58) :
    FinitePF XiMomentCoeff 58 := xi_finitePF58_of_quasiRH hq zetaNoLowStripZero hB

end Reinmann.XiRectangle

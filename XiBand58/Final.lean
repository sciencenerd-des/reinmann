/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import XiBand58.Tile000
import XiBand58.Tile001
import XiBand58.Tile002
import XiBand58.Tile003
import XiBand58.Tile004
import XiBand58.Tile005
import XiBand58.Tile006
import XiBand58.Tile007
import XiBand58.Tile008
import XiBand58.Cover
import XiRectangle
import Reinmann.FiniteBandGeometry

/-! A finite-width certificate for actual Xi, assembled with the historical
low rectangle. No external quasi-RH theorem is an input. -/
noncomputable section
namespace Reinmann.XiBand58

theorem all_tiles_nonzero (i : Fin Data.count) {z : ℂ}
    (hz : ‖z - Data.centre i‖ ≤ (Data.radius i : ℝ)) : xiCompleted z ≠ 0 := by
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

theorem upper_box_nonzero : ∀ z ∈ RationalBallCover.rectangle (7/8) 1 (141/10) 19,
    xiCompleted z ≠ 0 := by
  intro z hz
  obtain ⟨i, hi⟩ := Cover.box_covered z hz
  exact all_tiles_nonzero i hi

theorem box_nonzero {z : ℂ} (hx0 : (7/8 : ℝ) ≤ z.re) (hx1 : z.re ≤ 1)
    (hy : |z.im| ≤ (19 : ℝ)) : xiCompleted z ≠ 0 :=
  FiniteBandGeometry.box_nonzero_of_upper_box (by norm_num)
    (fun z hx0 hx1 hy => XiRectangle.rectangle_nonzero hx0 hx1 hy)
    upper_box_nonzero hx0 hx1 hy

theorem lowHeightWidth : FiniteHeightPFCalibration.LowHeightWidth (3/8) 19 := by
  have h := FiniteBandGeometry.lowHeightWidth_of_box (σ := 7/8) (H := 19)
    (fun z hx0 hx1 hy => box_nonzero hx0 hx1 hy)
  convert h using 1 <;> norm_num

theorem finitePF58 : FinitePF XiMomentCoeff 58 :=
  FiniteHeightPFCalibration.finitePF58_of_two_bands
    XiRectangle.zetaNoLowStripZero lowHeightWidth

end Reinmann.XiBand58

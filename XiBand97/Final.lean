/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import XiBand97.Tile000
import XiBand97.Tile001
import XiBand97.Tile002
import XiBand97.Tile003
import XiBand97.Tile004
import XiBand97.Tile005
import XiBand97.Tile006
import XiBand97.Tile007
import XiBand97.Tile008
import XiBand97.Tile009
import XiBand97.Tile010
import XiBand97.Tile011
import XiBand97.Tile012
import XiBand97.Tile013
import XiBand97.Tile014
import XiBand97.Tile015
import XiBand97.Tile016
import XiBand97.Tile017
import XiBand97.Tile018
import XiBand97.Tile019
import XiBand97.Tile020
import XiBand97.Tile021
import XiBand97.Tile022
import XiBand97.Tile023
import XiBand97.Tile024
import XiBand97.Tile025
import XiBand97.Tile026
import XiBand97.Tile027
import XiBand97.Tile028
import XiBand97.Tile029
import XiBand97.Tile030
import XiBand97.Tile031
import XiBand97.Tile032
import XiBand97.Tile033
import XiBand97.Tile034
import XiBand97.Tile035
import XiBand97.Tile036
import XiBand97.Tile037
import XiBand97.Tile038
import XiBand97.Tile039
import XiBand97.Tile040
import XiBand97.Tile041
import XiBand97.Tile042
import XiBand97.Tile043
import XiBand97.Tile044
import XiBand97.Tile045
import XiBand97.Tile046
import XiBand97.Tile047
import XiBand97.Tile048
import XiBand97.Tile049
import XiBand97.Tile050
import XiBand97.Tile051
import XiBand97.Tile052
import XiBand97.Tile053
import XiBand97.Tile054
import XiBand97.Tile055
import XiBand97.Tile056
import XiBand97.Tile057
import XiBand97.Tile058
import XiBand97.Tile059
import XiBand97.Tile060
import XiBand97.Tile061
import XiBand97.Tile062
import XiBand97.Tile063
import XiBand97.Tile064
import XiBand97.Tile065
import XiBand97.Tile066
import XiBand97.Cover
import XiRectangle
import Reinmann.FiniteBandGeometry

/-! A finite-width certificate for actual Xi, assembled with the historical
low rectangle. No external quasi-RH theorem is an input. -/
noncomputable section
namespace Reinmann.XiBand97

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
  · exact Tile044.nonzero hz
  · exact Tile045.nonzero hz
  · exact Tile046.nonzero hz
  · exact Tile047.nonzero hz
  · exact Tile048.nonzero hz
  · exact Tile049.nonzero hz
  · exact Tile050.nonzero hz
  · exact Tile051.nonzero hz
  · exact Tile052.nonzero hz
  · exact Tile053.nonzero hz
  · exact Tile054.nonzero hz
  · exact Tile055.nonzero hz
  · exact Tile056.nonzero hz
  · exact Tile057.nonzero hz
  · exact Tile058.nonzero hz
  · exact Tile059.nonzero hz
  · exact Tile060.nonzero hz
  · exact Tile061.nonzero hz
  · exact Tile062.nonzero hz
  · exact Tile063.nonzero hz
  · exact Tile064.nonzero hz
  · exact Tile065.nonzero hz
  · exact Tile066.nonzero hz

theorem upper_box_nonzero : ∀ z ∈ RationalBallCover.rectangle (29/40) 1 (141/10) 32,
    xiCompleted z ≠ 0 := by
  intro z hz
  obtain ⟨i, hi⟩ := Cover.box_covered z hz
  exact all_tiles_nonzero i hi

theorem box_nonzero {z : ℂ} (hx0 : (29/40 : ℝ) ≤ z.re) (hx1 : z.re ≤ 1)
    (hy : |z.im| ≤ (32 : ℝ)) : xiCompleted z ≠ 0 :=
  FiniteBandGeometry.box_nonzero_of_upper_box (by norm_num)
    (fun z hx0 hx1 hy => XiRectangle.rectangle_nonzero hx0 hx1 hy)
    upper_box_nonzero hx0 hx1 hy

theorem lowHeightWidth : FiniteHeightPFCalibration.LowHeightWidth (9/40) 32 := by
  have h := FiniteBandGeometry.lowHeightWidth_of_box (σ := 29/40) (H := 32)
    (fun z hx0 hx1 hy => box_nonzero hx0 hx1 hy)
  convert h using 1 <;> norm_num

theorem finitePF97 : FinitePF XiMomentCoeff 97 :=
  FiniteHeightPFCalibration.finitePF97_of_low_height_width
    XiRectangle.zetaNoLowStripZero lowHeightWidth

end Reinmann.XiBand97

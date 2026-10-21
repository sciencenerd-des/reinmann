/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RectangleModel
import Reinmann.FiniteBandBounds

/-! New height-32 perturbation and shifted-log wrappers for the unchanged
pole-free finite expression. All new constants have proved error budgets. -/
noncomputable section
namespace Reinmann.FiniteBandModel
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel Filter
open scoped Topology

 theorem gamma_sound {d:ℕ} {a:Jet d} {c:ℂ}
    (hc:c ∈ XiAdaptiveTiles.quarter 32) (ha:Sound a F_gammaFinite c) :
    Sound (fun k => inflate (a k) (4/10^14) (by norm_num)) F_gammaActual c := by
  apply sound_perturb (by norm_num) (sound_congr ha (Eventually.of_forall gammaFinite_identity))
  intro k
  simpa only [coefficient,F_gammaActual,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using
    UniformXiRemainders.gamma_coefficient_error_le hc.1 (by linarith [hc.2.1]) k.val

theorem zeta_sound {d:ℕ} {a:Jet d} {c:ℂ}
    (hc:c ∈ XiAdaptiveTiles.quarter 32) (ha:Sound a F_zetaFinite c) :
    Sound (fun k => inflate (a k) (1/5000) (by norm_num)) F_zetaActual c := by
  apply sound_perturb (by norm_num) (sound_congr ha (Eventually.of_forall zetaFinite_identity))
  intro k
  simpa only [coefficient,F_zetaActual,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_pow] using
    FiniteBandBounds.zeta_coefficient_error_le hc k.val

theorem xi_sound {d:ℕ} {a:Jet d} {c:ℂ}
    (hc:c ∈ XiAdaptiveTiles.quarter 32) (ha:Sound a F_xiProduct c) :
    Sound a xiCompleted c := by
  apply sound_congr ha
  have hc0 : 0<c.re := by linarith [hc.1]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc0] with s hs
  exact xiProduct_identity hs

theorem log_scaled32_contains {w z:QComplex} {a:Disk}
    (hscale:value w=(32:ℂ)*(1+value z)) (hz0:1+value z≠0)
    (hn:‖value z‖≤4/5) (ha:Contains a (Complex.logTaylor 160 (value z))) :
    Contains (add (mul (exact (5,0)) RectangleLogInputs.log2Disk)
      (inflate a (1/10^15) (by norm_num))) (Complex.log (value w)) := by
  have h := contains_add (contains_mul (contains_exact ((5:ℚ),0))
    RectangleLogInputs.log2_contains) (FiniteBandBounds.log_series_contains hn ha)
  have h16 : Real.log (32:ℝ)=5*Real.log 2 := by
    have h := Real.log_pow (2:ℝ) 5
    norm_num only at h
    exact h
  have he : value ((5:ℚ),0)*(Real.log (2:ℝ):ℂ)+Complex.log (1+value z)=
      Complex.log (value w) := by
    rw [hscale]
    change _=Complex.log (((32:ℝ):ℂ)*(1+value z))
    rw [Complex.log_ofReal_mul (by norm_num : (0:ℝ)<32) hz0,h16]
    simp [value]
  rw [he] at h
  exact h

end Reinmann.FiniteBandModel

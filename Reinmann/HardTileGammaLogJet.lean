/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HardTileGammaLog
import Reinmann.CertifiedTaylorComposition
import Mathlib.Tactic.FinCases

/-! All nine coefficients of the actual shifted principal logarithm at the hard
centre. Reciprocal and Log recurrences are rounded outward at every order. -/
noncomputable section
namespace Reinmann.HardTileGammaLogJet
open CertifiedTaylorModel CertifiedTaylorComposition
set_option maxRecDepth 10000

def centre : ℂ := (1 / 2 : ℂ) + 14 * Complex.I
def shifted (s : ℂ) : ℂ := 12 + (1 / 2) * s

def affineJet : Jet8 := fun k =>
  match k.val with
  | 0 => exact (49 / 4, 7)
  | 1 => exact (1 / 2, 0)
  | _ => zero

def inverseTable : ℕ → Disk
  | 0 => ⟨((4 / 65), (-16 / 455)), 0, by norm_num⟩
  | 1 => ⟨((-358939228845 / 281474976710656), (1218217988807 / 562949953421312)), (1 / 1125899906842624), by norm_num⟩
  | 2 => ⟨((1338701087 / 1125899906842624), (-100211338483 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 3 => ⟨((1720766797 / 1125899906842624), (3106963401 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 4 => ⟨((-107574599 / 1125899906842624), (-65343633 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 5 => ⟨((4458887 / 1125899906842624), (7447 / 70368744177664)), (1 / 1125899906842624), by norm_num⟩
  | 6 => ⟨((-34823 / 281474976710656), (18683 / 281474976710656)), (1 / 1125899906842624), by norm_num⟩
  | 7 => ⟨((743 / 281474976710656), (-4749 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 8 => ⟨((-1 / 140737488355328), (99 / 562949953421312)), (1 / 1125899906842624), by norm_num⟩
  | _ => zero

def inverseJet : Jet8 := fun k => inverseTable k.val

def logJet : Jet8 := fun k =>
  match k.val with
  | 0 => HardTileGammaLog.gammaLogDisk
  | 1 => ⟨((4330384257087 / 140737488355328), (-618626322441 / 35184372088832)), (1 / 1125899906842624), by norm_num⟩
  | 2 => ⟨((-358939228845 / 1125899906842624), (152277248601 / 281474976710656)), (1 / 1125899906842624), by norm_num⟩
  | 3 => ⟨((13944803 / 70368744177664), (-16701889747 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 4 => ⟨((107547925 / 562949953421312), (388370425 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 5 => ⟨((-2689365 / 281474976710656), (-6534363 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 6 => ⟨((185787 / 562949953421312), (9929 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | 7 => ⟨((-9949 / 1125899906842624), (2669 / 562949953421312)), (1 / 1125899906842624), by norm_num⟩
  | 8 => ⟨((93 / 562949953421312), (-297 / 1125899906842624)), (1 / 1125899906842624), by norm_num⟩
  | _ => zero

theorem shifted_analytic : AnalyticAt ℂ shifted centre := by
  unfold shifted
  exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

theorem shifted_value : shifted centre = (49 / 4 : ℂ) + 7 * Complex.I := by
  unfold shifted centre
  ring

theorem shifted_nonzero : shifted centre ≠ 0 := by
  rw [shifted_value]
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem shifted_slit : shifted centre ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  rw [shifted_value]
  norm_num

theorem shifted_coefficient (n : ℕ) :
    coefficient shifted centre n =
      if n = 0 then (49 / 4 : ℂ) + 7 * Complex.I else if n = 1 then 1 / 2 else 0 := by
  unfold coefficient
  rw [show shifted = (fun s : ℂ => 12 + (1 / 2) * s) from rfl]
  by_cases h0 : n = 0
  · subst n
    norm_num [centre]
    ring
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero h0), iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_id]
    by_cases h1 : n = 1
    · subst n
      norm_num
    · simp [h0, h1]

theorem affine_sound : Sound affineJet shifted centre := by
  intro k
  rw [shifted_coefficient]
  fin_cases k <;> norm_num [affineJet, Contains, exact, zero, value]

theorem inverse_sound : Sound inverseJet (fun s => (shifted s)⁻¹) centre := by
  apply inv_coefficients_sound shifted_analytic shifted_nonzero affine_sound
  · rw [shifted_value]
    norm_num [inverseJet, inverseTable, Contains, value, Complex.norm_def,
      Complex.normSq_apply, Complex.inv_re, Complex.inv_im]
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;>
      norm_num [inverseJet, inverseTable, affineJet, CertifiedTaylorModel.get, sum,
        CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qadd, qmul, size]

theorem log_sound : Sound logJet (fun s => Complex.log (shifted s)) centre := by
  apply log_coefficients_sound shifted_analytic shifted_slit affine_sound inverse_sound
  · rw [shifted_value]
    exact HardTileGammaLog.gamma_log_contains
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;>
      norm_num [logJet, inverseJet, inverseTable, affineJet, CertifiedTaylorModel.get, sum,
        CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qadd, qmul, size]

theorem log_radius (k : Fin 9) : ((logJet k).radius : ℝ) ≤ (1 / 10 ^ 12 : ℝ) := by
  fin_cases k <;> norm_num [logJet, HardTileGammaLog.gammaLogDisk]

end Reinmann.HardTileGammaLogJet

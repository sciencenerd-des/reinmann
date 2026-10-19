/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CertifiedTaylorComposition
import Reinmann.CertifiedScalarExp
import Mathlib.Tactic.FinCases

/-! Constant/variable inputs and the link from scalar exp to a degree-eight jet. -/
noncomputable section
namespace Reinmann.CertifiedTaylorInputs
open CertifiedTaylorModel CertifiedTaylorComposition Filter
open scoped Topology

def constantJet (a : Disk) : Jet8 := fun k => if k.val=0 then a else zero

def variableJet (c : QComplex) : Jet8 := fun k =>
  if k.val=0 then exact c else if k.val=1 then exact (1,0) else zero

theorem constant_sound {a : Disk} {x c : ℂ} (ha : Contains a x) :
    Sound (constantJet a) (fun _ => x) c := by
  intro k
  by_cases hk : k.val=0
  · simpa [coefficient,constantJet,hk] using ha
  · simpa [coefficient,constantJet,hk,iteratedDeriv_const] using contains_zero

theorem variable_sound (c : QComplex) : Sound (variableJet c) (fun z => z) (value c) := by
  intro k
  fin_cases k <;>
    norm_num [variableJet, coefficient, iteratedDeriv_fun_id, Contains, exact, zero, value]

theorem value_eq_of_exact {q : QComplex} {z : ℂ} (hz : Contains (exact q) z) : z=value q := by
  have h : ‖z-value q‖ ≤ 0 := by simpa [Contains, exact] using hz
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem sound_congr {a : Jet8} {f g : ℂ → ℂ} {c : ℂ}
    (ha : Sound a f c) (heq : f =ᶠ[𝓝 c] g) : Sound a g c := by
  intro k
  unfold coefficient at *
  rw [← heq.iteratedDeriv_eq]
  exact ha k

/-- The only transcendental constant in an exp-jet recurrence is its zeroth value. -/
theorem exp_sound {a b : Jet8} {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (ha : Sound a f c)
    (data : CertifiedScalarExp.Data) (hd : CertifiedScalarExp.Checks data)
    (hinput : data.input = a ⟨0,by omega⟩)
    (hzero : b ⟨0,by omega⟩ = data.squares 6)
    (hstep : ∀ (n : ℕ) (hn : n+1 < 9),
      let raw := mul (exact (1/(n+1),0))
        (sum (fun i => mul (exact (i+1,0))
          (mul (CertifiedTaylorModel.get a (i+1)) (CertifiedTaylorModel.get b (n-i)))) (n+1))
      raw.radius+size (raw.centre.1-(b ⟨n+1,hn⟩).centre.1,
        raw.centre.2-(b ⟨n+1,hn⟩).centre.2) ≤ (b ⟨n+1,hn⟩).radius) :
    Sound b (fun z => Complex.exp (f z)) c := by
  apply exp_coefficients_sound hf ha
  · rw [hzero]
    apply CertifiedScalarExp.sound data hd
    rw [hinput]
    exact centre_contains ha
  · exact hstep

end Reinmann.CertifiedTaylorInputs

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FiniteProductSplitPair
import Mathlib.Tactic.FinCases

/-! A concrete conjugate-pair instantiation checks that the root-order theorem
has satisfiable hypotheses. The product is 1+X², with alternating reciprocal coefficients. -/
noncomputable section
namespace Reinmann.FiniteProductSplitPair

def quadraticRoots : Fin 2 → ℂ := ![Complex.I, -Complex.I]

theorem quadratic_control_both_signs :
    (∀ M, ∃ r ≥ M, (rankMinor quadraticRoots 1 r).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (rankMinor quadraticRoots 1 r).re) := by
  have ha : Function.Injective quadraticRoots := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [quadraticRoots, Complex.ext_iff] at *
  have hz (i : Fin 2) : quadraticRoots i ≠ 0 := by
    fin_cases i <;> norm_num [quadraticRoots]
  have hconj (i : Fin 2) : quadraticRoots (Fin.revPerm i) = star (quadraticRoots i) := by
    fin_cases i <;> norm_num [quadraticRoots, Fin.revPerm, Fin.rev, Complex.ext_iff]
  apply finite_product_split_pair_of_root_order ha hz Fin.revPerm hconj ∅ 0 1
    (by simp) (by simp) (by decide) (by rfl) (by simp)
    (by norm_num [quadraticRoots]) (P := 1) (by norm_num) (by simp)
    (by simp)
  intro i hi
  fin_cases i <;> simp at hi

/-- A positive inner inverse zero2, followed by the pair ±i. -/
def cubicRoots (i : Fin 3) : ℂ :=
  if i.val = 0 then 1/2 else if i.val = 1 then Complex.I else -Complex.I

/-- A nonvacuous shift-two instance, covering the paper's s>=2 regime. -/
theorem cubic_control_both_signs :
    (∀ M, ∃ r ≥ M, (rankMinor cubicRoots 2 r).re < 0) ∧
    (∀ M, ∃ r ≥ M, 0 < (rankMinor cubicRoots 2 r).re) := by
  have ha : Function.Injective cubicRoots := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [cubicRoots, Complex.ext_iff] at *
  have hz (i : Fin 3) : cubicRoots i ≠ 0 := by
    fin_cases i <;> norm_num [cubicRoots]
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
  have hσ0 : σ 0 = 0 := by decide
  have hσ1 : σ 1 = 2 := by decide
  have hσ2 : σ 2 = 1 := by decide
  have hconj (i : Fin 3) : cubicRoots (σ i) = star (cubicRoots i) := by
    fin_cases i
    · change cubicRoots (σ 0) = star (cubicRoots 0)
      rw [hσ0]
      norm_num [cubicRoots]
    · change cubicRoots (σ 1) = star (cubicRoots 1)
      rw [hσ1]
      norm_num [cubicRoots]
    · change cubicRoots (σ 2) = star (cubicRoots 2)
      rw [hσ2]
      norm_num [cubicRoots]
  apply finite_product_split_pair_of_root_order ha hz σ hconj {0} 1 2
    (by simp) (by simp) (by decide) (by decide) (by decide)
    (by norm_num [cubicRoots]) (P := 2) (by norm_num) (by norm_num [cubicRoots])
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    norm_num [cubicRoots, norm_inv, norm_div]
  · intro i hi
    fin_cases i <;> simp at hi

end Reinmann.FiniteProductSplitPair

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.SetTheory.Cardinal.Finite

/-! A canonical index for zeros of a real-type entire function, retaining
analytic multiplicities and their conjugation action. No product identity or
summability of this index is asserted. -/
noncomputable section
namespace Reinmann.CanonicalZeroIndex
open Complex Filter
open scoped Topology ComplexConjugate

/-- Conjugation commutes with every derivative of a real-type entire function. -/
theorem iteratedDeriv_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (star z) = star (f z)) (n : ℕ) (z : ℂ) :
    iteratedDeriv n f (star z) = star (iteratedDeriv n f z) := by
  induction n generalizing z with
  | zero => simpa using hconj z
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hd : Differentiable ℂ (iteratedDeriv n f) :=
      (hf.contDiff : ContDiff ℂ (n + 1) f).differentiable_iteratedDeriv' n
    have hcc := ((hd (conj z)).hasDerivAt).conj_conj
    rw [Complex.conj_conj] at hcc
    have heq : iteratedDeriv n f =ᶠ[𝓝 z]
        (⇑(starRingEnd ℂ) ∘ iteratedDeriv n f ∘ ⇑(starRingEnd ℂ)) := by
      filter_upwards with w
      change iteratedDeriv n f w = star (iteratedDeriv n f (star w))
      rw [ih, star_star]
    have h := (hcc.congr_of_eventuallyEq heq).deriv
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc.symm

/-- Equality of multiplicities is proved, including the possible infinite order. -/
theorem analyticOrderAt_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (star z) = star (f z)) (z : ℂ) :
    analyticOrderAt f (star z) = analyticOrderAt f z := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.analyticAt _),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.analyticAt _)]
  simp only [iteratedDeriv_conj hf hconj, star_eq_zero]

theorem analyticOrderNatAt_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (star z) = star (f z)) (z : ℂ) :
    analyticOrderNatAt f (star z) = analyticOrderNatAt f z :=
  congrArg ENat.toNat (analyticOrderAt_conj hf hconj z)

/-- A nonzero value at the origin rules out infinite-order zeros everywhere. -/
theorem order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  apply AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ 0) (Set.mem_univ z)
  rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr h0]
  exact ENat.zero_ne_top

/-- Each zero occurs once for each natural label below its analytic multiplicity. -/
def Index (f : ℂ → ℂ) := {p : ℂ × ℕ // p.2 < analyticOrderNatAt f p.1}

def value {f : ℂ → ℂ} (i : Index f) : ℂ := i.val.1

theorem value_zero {f : ℂ → ℂ} (i : Index f) : f (value i) = 0 := by
  apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
  exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val.2) i.property)

theorem value_ne_zero {f : ℂ → ℂ} (h0 : f 0 ≠ 0) (i : Index f) : value i ≠ 0 := by
  intro hi
  exact h0 (hi ▸ value_zero i)

/-- The index contains a point precisely when it is a zero; infinite-order
junk values cannot delete a zero because the function is entire and nonzero. -/
theorem exists_value_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (z : ℂ) :
    (∃ i : Index f, value i = z) ↔ f z = 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    exact value_zero i
  · intro hz
    have hn : analyticOrderNatAt f z ≠ 0 := by
      intro hn
      have hc := Nat.cast_analyticOrderNatAt (order_ne_top hf h0 z)
      rw [hn, Nat.cast_zero] at hc
      exact ((hf.analyticAt z).analyticOrderAt_ne_zero.mpr hz) hc.symm
    exact ⟨⟨(z, 0), Nat.pos_of_ne_zero hn⟩, rfl⟩

/-- The fiber over z is exactly Fin of the analytic multiplicity, not an
arbitrary enumeration or an assumption of simple zeros. -/
def fiberEquiv (f : ℂ → ℂ) (z : ℂ) :
    {i : Index f // value i = z} ≃ Fin (analyticOrderNatAt f z) where
  toFun i := ⟨i.val.val.2, by
    have hi := i.val.property
    change i.val.val.2 < analyticOrderNatAt f (value i.val) at hi
    rwa [i.property] at hi⟩
  invFun n := ⟨⟨(z, n.val), n.isLt⟩, rfl⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext i.property.symm rfl
  right_inv n := by rfl

theorem fiber_card (f : ℂ → ℂ) (z : ℂ) :
    Nat.card {i : Index f // value i = z} = analyticOrderNatAt f z := by
  rw [Nat.card_congr (fiberEquiv f z), Nat.card_fin]

/-- Conjugation keeps the multiplicity label unchanged. -/
def conjugate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (star z) = star (f z)) (i : Index f) : Index f :=
  ⟨(star i.val.1, i.val.2), by rw [analyticOrderNatAt_conj hf hconj]; exact i.property⟩

theorem value_conjugate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (star z) = star (f z)) (i : Index f) :
    value (conjugate hf hconj i) = star (value i) := rfl

theorem conjugate_involutive {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f (star z) = star (f z)) :
    Function.Involutive (conjugate hf hconj) := by
  intro i
  apply Subtype.ext
  exact Prod.ext (star_star _) rfl

end Reinmann.CanonicalZeroIndex

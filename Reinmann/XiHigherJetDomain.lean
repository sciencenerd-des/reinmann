/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiJordanDomain
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Higher coherent jets in the arithmetic Xi domain

Creation is multiplication by z on coefficient sequences. The convergent
rows for successive Xi derivatives obey a creation identity. This puts
z^p exp(sz) in the actual Xi coefficient domain whenever derivatives through
order p vanish at s. No simplicity or critical-line premise is used.
This file does not assert the higher-jet kernel coupling or Fock norm bounds.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAnnihilator
open FockEigenvectors

def creationAction : Coeff →ₗ[ℂ] Coeff where
  toFun c
    | 0 => 0
    | n + 1 => c n
  map_add' := by intro c d; ext n; cases n <;> simp
  map_smul' := by intro a c; ext n; cases n <;> simp [smul_eq_mul]

@[simp] theorem creation_zero (c : Coeff) : creationAction c 0 = 0 := rfl
@[simp] theorem creation_succ (c : Coeff) (n : ℕ) : creationAction c (n + 1) = c n := rfl

theorem derivative_creation (c : Coeff) :
    derivativeAction (creationAction c) = creationAction (derivativeAction c) + c := by
  ext n
  cases n with
  | zero => simp [derivativeAction]
  | succ n =>
    simp only [derivativeAction, LinearMap.coe_mk, AddHom.coe_mk, creation_succ,
      Pi.add_apply, Nat.cast_add, Nat.cast_one]
    ring

theorem derivative_power_creation (c : Coeff) (m : ℕ) :
    (derivativeAction ^ (m + 1)) (creationAction c) =
      creationAction ((derivativeAction ^ (m + 1)) c) +
        (m + 1 : ℂ) • ((derivativeAction ^ m) c) := by
  induction m with
  | zero => simpa using derivative_creation c
  | succ m hm =>
    rw [pow_succ', Module.End.mul_apply, hm, map_add, map_smul, derivative_creation]
    simp only [pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one]
    module

def higherJet (s : ℂ) : ℕ → Coeff
  | 0 => coherent s
  | p + 1 => creationAction (higherJet s p)

@[simp] theorem higherJet_zero (s : ℂ) : higherJet s 0 = coherent s := rfl
@[simp] theorem higherJet_succ (s : ℂ) (p : ℕ) :
    higherJet s (p + 1) = creationAction (higherJet s p) := rfl

theorem higherJet_apply_add (s : ℂ) (p n : ℕ) : higherJet s p (n + p) = coherent s n := by
  induction p with
  | zero => simp
  | succ p hp => simpa [Nat.add_assoc] using hp

theorem higherJet_apply_lt (s : ℂ) {p n : ℕ} (hn : n < p) : higherJet s p n = 0 := by
  induction p generalizing n with
  | zero => omega
  | succ p hp =>
    cases n with
    | zero => simp
    | succ n => simpa using hp (by omega : n < p)

theorem higherJet_nonzero (s : ℂ) (p : ℕ) : higherJet s p ≠ 0 := by
  intro hz
  have h := higherJet_apply_add s p 0
  rw [hz] at h
  simpa [coherent] using h

theorem derivative_higherJet_succ (s : ℂ) (p : ℕ) :
    derivativeAction (higherJet s (p + 1)) =
      s • higherJet s (p + 1) + (p + 1 : ℂ) • higherJet s p := by
  induction p with
  | zero =>
    rw [higherJet_succ, derivative_creation, higherJet_zero, derivative_coherent, map_smul]
    simp
  | succ p hp =>
    rw [higherJet_succ, derivative_creation, hp, map_add, map_smul, map_smul]
    simp only [← higherJet_succ, Nat.cast_add, Nat.cast_one]
    module

theorem differentiable_iterated_xi (j : ℕ) : Differentiable ℂ (iteratedDeriv j xiCompleted) := by
  induction j with
  | zero => simpa using differentiable_xiCompleted
  | succ j hj =>
    rw [iteratedDeriv_succ]
    exact differentiableOn_univ.mp (hj.differentiableOn.deriv isOpen_univ)

def xiDerivativeTaylor (j k : ℕ) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedDeriv k (iteratedDeriv j xiCompleted) 0

@[simp] theorem xiDerivativeTaylor_zero (k : ℕ) : xiDerivativeTaylor 0 k = xiTaylor k := by
  simp [xiDerivativeTaylor, xiTaylor]

theorem xiDerivativeTaylor_succ (j k : ℕ) :
    xiDerivativeTaylor (j + 1) k = (k + 1 : ℂ) * xiDerivativeTaylor j (k + 1) := by
  unfold xiDerivativeTaylor
  rw [iteratedDeriv_succ, iteratedDeriv_succ']
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

theorem xiDerivativeTaylor_hasSum (j : ℕ) (s : ℂ) :
    HasSum (fun k => xiDerivativeTaylor j k * s ^ k) (iteratedDeriv j xiCompleted s) := by
  have ht := Complex.hasSum_taylorSeries_of_entire (differentiable_iterated_xi j) 0 s
  convert ht using 1
  ext k
  simp only [xiDerivativeTaylor, sub_zero, smul_eq_mul]
  ring

def derivativeRowTerm (j n : ℕ) (c : Coeff) (k : ℕ) : ℂ :=
  xiDerivativeTaylor j k * ((derivativeAction ^ (k + n)) c) 0

@[simp] theorem derivativeRowTerm_zero (n : ℕ) (c : Coeff) :
    derivativeRowTerm 0 n c = rowTerm n c := by
  ext k
  simp [derivativeRowTerm, rowTerm]

theorem coherent_derivative_row_hasSum (j n : ℕ) (s : ℂ) :
    HasSum (derivativeRowTerm j n (coherent s))
      (s ^ n * iteratedDeriv j xiCompleted s) := by
  convert (xiDerivativeTaylor_hasSum j s).mul_left (s ^ n) using 1
  ext k
  rw [derivativeRowTerm, derivative_power_coherent]
  simp only [Pi.smul_apply, smul_eq_mul, coherent, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one, pow_add]
  ring

theorem derivative_row_creation_zero (j : ℕ) (c : Coeff) :
    derivativeRowTerm j 0 (creationAction c) 0 = 0 := by
  simp [derivativeRowTerm]

theorem derivative_row_creation_shift (j k : ℕ) (c : Coeff) :
    derivativeRowTerm j 0 (creationAction c) (k + 1) = derivativeRowTerm (j + 1) 0 c k := by
  rw [derivativeRowTerm, Nat.add_zero, derivative_power_creation]
  simp only [Pi.add_apply, Pi.smul_apply, creation_zero, zero_add, smul_eq_mul]
  rw [derivativeRowTerm, Nat.add_zero, xiDerivativeTaylor_succ]
  simp only [Nat.add_zero]
  ring

theorem derivative_row_creation_split (j n k : ℕ) (c : Coeff) :
    derivativeRowTerm j (n + 1) (creationAction c) k -
        (n + 1 : ℂ) * derivativeRowTerm j n c k =
      if k = 0 then 0 else derivativeRowTerm (j + 1) (n + 1) c (k - 1) := by
  rw [derivativeRowTerm, show k + (n + 1) = (k + n) + 1 by omega,
    derivative_power_creation]
  simp only [Pi.add_apply, Pi.smul_apply, creation_zero, zero_add, smul_eq_mul,
    derivativeRowTerm]
  cases k with
  | zero => simp <;> ring
  | succ k =>
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one, xiDerivativeTaylor_succ,
      show k + (n + 1) = (k + 1) + n by omega, Nat.cast_add, Nat.cast_one]
    ring

theorem creation_rows_hasSum_zero (j : ℕ) (c : Coeff)
    (h0 : ∀ n, HasSum (derivativeRowTerm j n c) 0)
    (h1 : ∀ n, HasSum (derivativeRowTerm (j + 1) n c) 0) :
    ∀ n, HasSum (derivativeRowTerm j n (creationAction c)) 0 := by
  intro n
  cases n with
  | zero =>
    apply (hasSum_nat_add_iff' 1).mp
    simpa only [Finset.sum_range_one, derivative_row_creation_zero, sub_zero,
      derivative_row_creation_shift] using h1 0
  | succ n =>
    let g := fun k => derivativeRowTerm j (n + 1) (creationAction c) k -
      (n + 1 : ℂ) * derivativeRowTerm j n c k
    have hg0 : g 0 = 0 := by simpa [g] using derivative_row_creation_split j n 0 c
    have hgshift : HasSum (fun k => g (k + 1)) 0 := by
      convert h1 (n + 1) using 1
      ext k
      simp [g, derivative_row_creation_split]
    have hg : HasSum g 0 := by
      apply (hasSum_nat_add_iff' 1).mp
      simpa [hg0] using hgshift
    have h := hg.add ((h0 n).mul_left (n + 1 : ℂ))
    simpa only [g, sub_add_cancel, mul_zero, zero_add] using h

theorem higherJet_derivative_rows_zero (s : ℂ) (p j : ℕ)
    (hvan : ∀ l : ℕ, l ≤ p → iteratedDeriv (j + l) xiCompleted s = 0) :
    ∀ n, HasSum (derivativeRowTerm j n (higherJet s p)) 0 := by
  induction p generalizing j with
  | zero =>
    intro n
    have hz : iteratedDeriv j xiCompleted s = 0 := by simpa using hvan 0 (by omega)
    simpa [hz] using coherent_derivative_row_hasSum j n s
  | succ p hp =>
    apply creation_rows_hasSum_zero
    · apply hp
      intro l hl
      exact hvan l (by omega)
    · apply hp
      intro l hl
      convert hvan (l + 1) (by omega) using 1 <;> congr 1 <;> omega

theorem higherJet_mem_domain (s : ℂ) (p : ℕ)
    (hvan : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0) : higherJet s p ∈ domain := by
  intro n
  have h := higherJet_derivative_rows_zero s p 0 (by simpa using hvan) n
  rw [derivativeRowTerm_zero] at h
  exact ⟨h.summable, h.tsum_eq⟩

def higherJetState (s : ℂ) (p : ℕ)
    (hvan : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0) : domain :=
  ⟨higherJet s p, higherJet_mem_domain s p hvan⟩

theorem higherJetState_nonzero (s : ℂ) (p : ℕ)
    (hvan : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0) :
    higherJetState s p hvan ≠ 0 := by
  intro hz
  exact higherJet_nonzero s p (congrArg Subtype.val hz)

end Reinmann.XiAnnihilator

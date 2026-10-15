/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiAlgebraicJetForm

/-!
# Universal arithmetic Xi Gram recurrence

The parameters cover all complex numbers and all jet orders. Away from
reflected pairs a Green recurrence defines the Gram entries; at reflection
an explicit confluent formula supplies them. Hermitianization is performed
once on this universal matrix. No reality or simplicity premise enters.
This module does not identify all entries with mixed analytic derivatives.
-/

noncomputable section
open Complex
open scoped ComplexConjugate Classical

namespace Reinmann.XiGreenGram
open XiAlgebraicJetSpace XiDividedDifference

def delta (s t : ℂ) : ℂ := s + conj t - 1

def confluent (s : ℂ) (p q : ℕ) : ℂ :=
  I * (-1) ^ q * (p.factorial : ℂ) * (q.factorial : ℂ) /
    ((p + q + 1).factorial : ℂ) * iteratedDeriv (p + q + 1) xiCompleted s

theorem confluent_zero_left (s : ℂ) (q : ℕ) :
    confluent s 0 q = I * (-1) ^ q / (q + 1 : ℂ) * iteratedDeriv (q + 1) xiCompleted s := by
  simp only [confluent, Nat.zero_add, Nat.factorial_zero, Nat.cast_one,
    mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hf : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
  have hq : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  field_simp

theorem confluent_zero_right (s : ℂ) (p : ℕ) :
    confluent s p 0 = I / (p + 1 : ℂ) * iteratedDeriv (p + 1) xiCompleted s := by
  simp only [confluent, Nat.add_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hf : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hp : (p + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  field_simp

theorem confluent_interior_cancel (s : ℂ) (p q : ℕ) :
    (p + 1 : ℂ) * confluent s p (q + 1) +
      (q + 1 : ℂ) * confluent s (p + 1) q = 0 := by
  simp only [confluent, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, show p + (q + 1) + 1 = (p + 1) + q + 1 by omega]
  ring

def offGram (s t : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => I * (xiCompleted s - conj (xiCompleted t)) / delta s t
  | p + 1, 0 =>
      (I * iteratedDeriv (p + 1) xiCompleted s - (p + 1 : ℂ) * offGram s t p 0) /
        delta s t
  | 0, q + 1 =>
      (-I * conj (iteratedDeriv (q + 1) xiCompleted t) -
        (q + 1 : ℂ) * offGram s t 0 q) / delta s t
  | p + 1, q + 1 =>
      (-(p + 1 : ℂ) * offGram s t p (q + 1) -
        (q + 1 : ℂ) * offGram s t (p + 1) q) / delta s t
termination_by p q => p + q

def raw (s t : ℂ) (p q : ℕ) : ℂ :=
  if delta s t = 0 then confluent s p q else offGram s t p q

theorem reflected_derivative {s t : ℂ} (h : delta s t = 0) (q : ℕ) :
    conj (iteratedDeriv q xiCompleted t) = (-1) ^ q * iteratedDeriv q xiCompleted s := by
  have hc : conj t = 1 - s := by unfold delta at h; linear_combination h
  rw [← iteratedDeriv_xi_conj, hc, iteratedDeriv_xi_one_sub]

theorem raw_balance (s t : ℂ) (p q : ℕ) :
    delta s t * raw s t p q +
      (if p = 0 then 0 else (p : ℂ) * raw s t (p - 1) q) +
      (if q = 0 then 0 else (q : ℂ) * raw s t p (q - 1)) =
        I * ((if q = 0 then iteratedDeriv p xiCompleted s else 0) -
          (if p = 0 then conj (iteratedDeriv q xiCompleted t) else 0)) := by
  by_cases h : delta s t = 0
  · simp only [raw, h, if_true, zero_mul, zero_add]
    cases p with
    | zero =>
      cases q with
      | zero =>
        have hc : conj (xiCompleted t) = xiCompleted s := by
          simpa only [iteratedDeriv_zero, pow_zero, one_mul] using reflected_derivative h 0
        simp [hc]
      | succ q =>
        simp only [Nat.succ_ne_zero, if_false, if_true, Nat.cast_add, Nat.cast_one,
          Nat.add_sub_cancel, confluent_zero_left, reflected_derivative h, pow_succ]
        have hq : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
        field_simp
        ring
    | succ p =>
      cases q with
      | zero =>
        simp only [Nat.succ_ne_zero, if_false, if_true, Nat.cast_add, Nat.cast_one,
          Nat.add_sub_cancel, confluent_zero_right, sub_zero, add_zero]
        have hp : (p + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
        field_simp
      | succ q =>
        simpa only [Nat.succ_ne_zero, if_false, Nat.cast_add, Nat.cast_one,
          Nat.add_sub_cancel, sub_self, mul_zero] using confluent_interior_cancel s p q
  · simp only [raw, h, if_false]
    cases p <;> cases q <;>
      simp only [offGram, Nat.succ_ne_zero, if_false, if_true, iteratedDeriv_zero,
        Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] <;>
      field_simp <;> ring

def gram (a b : Label) : ℂ := (raw a.1 b.1 a.2 b.2 + conj (raw b.1 a.1 b.2 a.2)) / 2

theorem gram_hermitian (a b : Label) : conj (gram b a) = gram a b := by
  simp [gram, map_div₀, map_add, map_ofNat, add_comm]

theorem conj_delta (s t : ℂ) : conj (delta t s) = delta s t := by
  simp [delta, map_add, map_sub, add_comm]

theorem gram_balance (s t : ℂ) (p q : ℕ) :
    delta s t * gram ⟨s, p⟩ ⟨t, q⟩ +
      (if p = 0 then 0 else (p : ℂ) * gram ⟨s, p - 1⟩ ⟨t, q⟩) +
      (if q = 0 then 0 else (q : ℂ) * gram ⟨s, p⟩ ⟨t, q - 1⟩) =
        I * ((if q = 0 then iteratedDeriv p xiCompleted s else 0) -
          (if p = 0 then conj (iteratedDeriv q xiCompleted t) else 0)) := by
  have h := raw_balance s t p q
  have hc := congrArg (starRingEnd ℂ) (raw_balance t s q p)
  simp only [map_add, map_mul, map_sub, apply_ite, map_zero, map_natCast,
    conj_delta, Complex.conj_I, Complex.conj_conj] at hc
  by_cases hp : p = 0 <;> by_cases hq : q = 0 <;>
    simp only [hp, hq, if_true, if_false, map_mul, map_zero, map_natCast,
      Complex.conj_conj] at h hc ⊢ <;>
    simp only [gram] <;> linear_combination (h + hc) / 2

theorem raw_at_reflection (s : ℂ) (p q : ℕ) :
    raw s (1 - conj s) p q = confluent s p q := by
  simp [raw, delta, map_sub]

theorem gram_reflected_partner (s : ℂ) (p : ℕ) :
    gram ⟨s, 0⟩ ⟨1 - conj s, p⟩ = jetCoupling s p := by
  have hd : delta (1 - conj s) s = 0 := by simp [delta]
  have hf : delta s (1 - conj s) = 0 := by simp [delta, map_sub]
  have hc := reflected_derivative hf (p + 1)
  rw [gram, raw_at_reflection]
  simp only [raw, hd, if_true, confluent_zero_left, confluent_zero_right]
  rw [map_mul, map_div₀, Complex.conj_I]
  simp only [map_natCast, map_add, map_one]
  rw [hc, jetCoupling_eq]
  simp only [pow_succ]
  ring

end Reinmann.XiGreenGram

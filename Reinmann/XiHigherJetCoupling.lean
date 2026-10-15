/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiHigherJetDomain
import Reinmann.XiDividedDifference
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Higher-jet Xi kernel coupling at reflected nodes

The first nonzero derivative of Xi exists at every point because Xi is entire
and Xi(0)=1/2. At a zero its index is the finite multiplicity. Successive
parameter derivatives of the entire removable Xi kernel give the nonzero
coupling used by the packet mass construction. The coefficient jet belongs
to the arithmetic domain. Identifying this parameter derivative with the
full Fock-space form remains a separate analytic obligation.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAnnihilator
open FockEigenvectors

theorem higherJet_one_eq_coherentJet (s : ℂ) : higherJet s 1 = coherentJet s := by
  ext n
  cases n <;> rfl

theorem spectral_higherJet_succ (s : ℂ) (p : ℕ) :
    spectralAction (higherJet s (p + 1)) = spectralParam s • higherJet s (p + 1) -
      (I * (p + 1 : ℂ)) • higherJet s p := by
  ext n
  have hd := congrFun (derivative_higherJet_succ s p) n
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hd
  change -I * (derivativeAction (higherJet s (p + 1)) n -
    (1 / 2 : ℂ) * higherJet s (p + 1) n) =
      spectralParam s * higherJet s (p + 1) n - I * (p + 1 : ℂ) * higherJet s p n
  rw [hd]
  unfold spectralParam
  ring

theorem higherJetState_spectral_succ (s : ℂ) (p : ℕ)
    (hvan : ∀ j : ℕ, j ≤ p + 1 → iteratedDeriv j xiCompleted s = 0) :
    spectralOnDomain (higherJetState s (p + 1) hvan) =
      spectralParam s • higherJetState s (p + 1) hvan -
        (I * (p + 1 : ℂ)) • higherJetState s p
          (fun j hj => hvan j (Nat.le_succ_of_le hj)) := by
  apply Subtype.ext
  exact spectral_higherJet_succ s p

end Reinmann.XiAnnihilator

namespace Reinmann.XiDividedDifference
open XiAnnihilator FockEigenvectors

theorem iteratedDeriv_xi_one_sub (p : ℕ) (s : ℂ) :
    iteratedDeriv p xiCompleted (1 - s) = (-1 : ℂ) ^ p * iteratedDeriv p xiCompleted s := by
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv p f s)
    (show (fun z => xiCompleted (1 - z)) = xiCompleted from funext xi_one_sub)
  change iteratedDeriv p (fun z => xiCompleted (1 - z)) s = iteratedDeriv p xiCompleted s at h
  rw [iteratedDeriv_comp_const_sub] at h
  simp only [smul_eq_mul] at h
  calc
    _ = (-1 : ℂ) ^ p * ((-1 : ℂ) ^ p * iteratedDeriv p xiCompleted (1 - s)) := by
      rw [← mul_assoc, ← mul_pow]
      simp
    _ = _ := by rw [h]

theorem iteratedDeriv_xi_conj (p : ℕ) (s : ℂ) :
    iteratedDeriv p xiCompleted (conj s) = conj (iteratedDeriv p xiCompleted s) := by
  induction p generalizing s with
  | zero => simpa using xi_conj s
  | succ p hp =>
    rw [iteratedDeriv_succ]
    have hcc := ((differentiable_iterated_xi p (conj s)).hasDerivAt).conj_conj
    rw [Complex.conj_conj] at hcc
    have heq : iteratedDeriv p xiCompleted =ᶠ[nhds s]
        (⇑(starRingEnd ℂ) ∘ iteratedDeriv p xiCompleted ∘ ⇑(starRingEnd ℂ)) := by
      filter_upwards with z
      change iteratedDeriv p xiCompleted z = conj (iteratedDeriv p xiCompleted (conj z))
      rw [hp, Complex.conj_conj]
    have h := (hcc.congr_of_eventuallyEq heq).deriv
    have hc := congrArg (starRingEnd ℂ) h
    simpa using hc.symm

theorem exists_nonzero_xi_derivative (s : ℂ) : ∃ m : ℕ, iteratedDeriv m xiCompleted s ≠ 0 := by
  by_contra h
  push Not at h
  have ht := Complex.hasSum_taylorSeries_of_entire differentiable_xiCompleted s 0
  have heq := ht.tsum_eq
  simp only [h, smul_zero, tsum_zero, xiCompleted_zero] at heq
  norm_num at heq

theorem exists_finite_xi_multiplicity {s : ℂ} (hz : xiCompleted s = 0) :
    ∃ m : ℕ, 0 < m ∧ (∀ j : ℕ, j < m → iteratedDeriv j xiCompleted s = 0) ∧
      iteratedDeriv m xiCompleted s ≠ 0 := by
  let hex := exists_nonzero_xi_derivative s
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · by_contra hpos
    have hm : Nat.find hex = 0 := by omega
    have hd := Nat.find_spec hex
    simpa [hm, hz] using hd
  · intro j hj
    exact not_not.mp (Nat.find_min hex hj)

theorem iteratedDeriv_dslope_same {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (p : ℕ) :
    iteratedDeriv p (dslope f a) a = iteratedDeriv (p + 1) f a / (p + 1 : ℂ) := by
  have hp := hf.hasFPowerSeriesAt.has_fpower_series_dslope_fslope
  have heq := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hcoeff := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff p) heq
  simp only [FormalMultilinearSeries.coeff_fslope,
    FormalMultilinearSeries.coeff_ofScalars] at hcoeff
  have hf0 : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hp0 : (p + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcoeff
  field_simp at hcoeff ⊢
  linear_combination -hcoeff

def polarizedKernel (s u : ℂ) : ℂ := I * dslope xiCompleted (1 - u) s

theorem polarizedKernel_eq_kernel (s u : ℂ) : polarizedKernel s u = kernel s (conj u) := by
  simp [polarizedKernel, kernel]

theorem polarizedKernel_eq (s u : ℂ) :
    polarizedKernel s u = -I * dslope xiCompleted (1 - s) u := by
  by_cases h : s = 1 - u
  · have hu : u = 1 - s := by linear_combination h
    rw [polarizedKernel, ← h, dslope_same, hu, dslope_same, deriv_xi_one_sub]
    ring
  · have hu : u ≠ 1 - s := by intro hu; apply h; linear_combination hu
    rw [polarizedKernel, dslope_of_ne _ h, dslope_of_ne _ hu, slope_def_field,
      slope_def_field, xi_one_sub, xi_one_sub]
    field_simp
    ring

def jetCoupling (s : ℂ) (p : ℕ) : ℂ :=
  iteratedDeriv p (polarizedKernel s) (1 - s)

theorem jetCoupling_eq (s : ℂ) (p : ℕ) :
    jetCoupling s p = I * (-1 : ℂ) ^ p * iteratedDeriv (p + 1) xiCompleted s / (p + 1 : ℂ) := by
  have heq : polarizedKernel s = fun u => -I * dslope xiCompleted (1 - s) u :=
    funext (polarizedKernel_eq s)
  rw [jetCoupling, heq, iteratedDeriv_const_mul_field,
    iteratedDeriv_dslope_same (differentiable_xiCompleted.analyticAt (1 - s)),
    iteratedDeriv_xi_one_sub, pow_succ]
  ring

theorem jetCoupling_ne_zero (s : ℂ) (p : ℕ)
    (hd : iteratedDeriv (p + 1) xiCompleted s ≠ 0) : jetCoupling s p ≠ 0 := by
  rw [jetCoupling_eq]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero (pow_ne_zero _ (by norm_num))) hd)
    (by exact_mod_cast Nat.succ_ne_zero p)

/-- Every Xi zero has an actual-domain higher jet and a nonzero derivative
of the arithmetic kernel at the matching reflected node. Full Fock form
compatibility is not asserted by this coefficient-domain theorem. -/
theorem zero_has_domain_jet_and_nonzero_coupling {s : ℂ} (hz : xiCompleted s = 0) :
    ∃ p : ℕ, (∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0) ∧
      higherJet s p ∈ domain ∧ higherJet (1 - conj s) p ∈ domain ∧ jetCoupling s p ≠ 0 := by
  obtain ⟨m, hm, hvan, hd⟩ := exists_finite_xi_multiplicity hz
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hv : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0 := by
    intro j hj
    exact hvan j (by omega)
  have hvp : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted (1 - conj s) = 0 := by
    intro j hj
    rw [iteratedDeriv_xi_one_sub, iteratedDeriv_xi_conj, hv j hj, map_zero, mul_zero]
  exact ⟨p, hv, higherJet_mem_domain s p hv, higherJet_mem_domain (1 - conj s) p hvp,
    jetCoupling_ne_zero s p hd⟩

end Reinmann.XiDividedDifference

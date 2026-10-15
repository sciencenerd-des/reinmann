/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiAnnihilator
import Reinmann.PseudoHermitianJordan

/-!
# Actual Xi-domain Jordan states at multiple zeros

The derivative Taylor series and convergent Xi rows put the coherent jet in
the arithmetic domain exactly at multiple Xi zeros. Thus any globally
symmetric additive scalar form on this full domain gives zero mass to the
coherent eigenstate there. Excluding this obstruction would require a theorem
about Xi multiplicities or a different realization, not a choice of metric.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAnnihilator
open FockEigenvectors

theorem xiTaylor_derivative_hasSum (s : ℂ) :
    HasSum (fun k => xiTaylor k * (k : ℂ) * s ^ (k - 1)) (deriv xiCompleted s) := by
  have hd : Differentiable ℂ (deriv xiCompleted) :=
    differentiableOn_univ.mp (differentiable_xiCompleted.differentiableOn.deriv isOpen_univ)
  have ht := Complex.hasSum_taylorSeries_of_entire hd 0 s
  have hshift : HasSum (fun k => xiTaylor (k + 1) * (k + 1 : ℂ) * s ^ k)
      (deriv xiCompleted s) := by
    convert ht using 1
    ext k
    simp only [xiTaylor, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      iteratedDeriv_succ', sub_zero, smul_eq_mul]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  apply (hasSum_nat_add_iff' 1).mp
  simpa using hshift

theorem derivative_power_coherentJet (s : ℂ) (m : ℕ) :
    (derivativeAction ^ m) (coherentJet s) =
      s ^ m • coherentJet s + ((m : ℂ) * s ^ (m - 1)) • coherent s := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ', Module.End.mul_apply, hm, map_add, map_smul, map_smul,
      derivative_coherentJet, derivative_coherent]
    cases m with
    | zero => simp
    | succ m =>
      ext n
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem rowTerm_coherentJet (s : ℂ) (n k : ℕ) :
    rowTerm n (coherentJet s) k =
      s ^ n * (xiTaylor k * (k : ℂ) * s ^ (k - 1)) +
        ((n : ℂ) * s ^ (n - 1)) * (xiTaylor k * s ^ k) := by
  rw [rowTerm, derivative_power_coherentJet]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, coherentJet, coherent,
    pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, zero_add, mul_one]
  have hprod := (hasDerivAt_pow k s).mul (hasDerivAt_pow n s)
  change HasDerivAt (fun z : ℂ => z ^ k * z ^ n) _ s at hprod
  rw [show (fun z : ℂ => z ^ k * z ^ n) = (fun z => z ^ (k + n)) by
    funext z; exact (pow_add z k n).symm] at hprod
  have hp := (hasDerivAt_pow (k + n) s).unique hprod
  rw [hp]
  ring

theorem coherentJet_row_hasSum (s : ℂ) (n : ℕ) :
    HasSum (rowTerm n (coherentJet s))
      (s ^ n * deriv xiCompleted s + (n : ℂ) * s ^ (n - 1) * xiCompleted s) := by
  have h := ((xiTaylor_derivative_hasSum s).mul_left (s ^ n)).add
    ((xiTaylor_hasSum s).mul_left ((n : ℂ) * s ^ (n - 1)))
  convert h using 1
  ext k
  exact rowTerm_coherentJet s n k

theorem coherentJet_mem_domain_iff (s : ℂ) :
    coherentJet s ∈ domain ↔ xiCompleted s = 0 ∧ deriv xiCompleted s = 0 := by
  constructor
  · intro h
    have h0 := (coherentJet_row_hasSum s 0).tsum_eq
    rw [(h 0).2] at h0
    have hd : deriv xiCompleted s = 0 := by simpa using h0.symm
    have h1 := (coherentJet_row_hasSum s 1).tsum_eq
    rw [(h 1).2, hd] at h1
    exact ⟨by simpa using h1.symm, hd⟩
  · rintro ⟨hz, hd⟩ n
    exact ⟨(coherentJet_row_hasSum s n).summable, by
      rw [(coherentJet_row_hasSum s n).tsum_eq, hz, hd]; simp⟩

def jordanZeroState (s : ℂ) (hz : xiCompleted s = 0)
    (hd : deriv xiCompleted s = 0) : domain :=
  I • ⟨coherentJet s, (coherentJet_mem_domain_iff s).mpr ⟨hz, hd⟩⟩

theorem jordanZeroState_chain (s : ℂ) (hz : xiCompleted s = 0)
    (hd : deriv xiCompleted s = 0) :
    spectralOnDomain (jordanZeroState s hz hd) =
      spectralParam s • jordanZeroState s hz hd + zeroState s hz := by
  apply Subtype.ext
  exact spectral_coherentJordan s

/-- Global symmetry on the actual arithmetic domain cannot provide non-isotropy
at a multiple zero, regardless of whether that zero is critical. -/
theorem mass_zero_at_multiple_xi_zero (F : AdditiveScalarForm domain)
    (hsym : ∀ v w : domain, F.η (spectralOnDomain v) w = F.η v (spectralOnDomain w))
    (s : ℂ) (hz : xiCompleted s = 0) (hd : deriv xiCompleted s = 0) :
    F.η (zeroState s hz) (zeroState s hz) = 0 :=
  F.mass_zero_of_symmetric_jordan_chain spectralOnDomain (zeroState_eigen s hz)
    (jordanZeroState_chain s hz hd) (hsym _ _) (hsym _ _)

end Reinmann.XiAnnihilator

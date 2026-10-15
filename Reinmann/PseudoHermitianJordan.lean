/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FockEigenvectors

/-!
# Jordan-chain obstruction to selected-state mass

At a real eigenvalue, symmetry between a length-two Jordan chain and its
eigenvector forces the latter's diagonal mass to vanish. We also check the
explicit coherent-state parameter jet for the coefficient differentiation
action. The companion `XiJordanDomain` checks membership in the arithmetic
domain at multiple Xi zeros; that membership is not asserted by this file.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

theorem AdditiveScalarForm.mass_zero_of_real_jordan_chain
    (F : AdditiveScalarForm E) (T : E → E) {v w : E} {μ : ℂ}
    (heigen : T v = μ • v) (hchain : T w = μ • w + v)
    (hpaired : F.η (T w) v = F.η w (T v)) (hreal : conj μ = μ) :
    F.η v v = 0 := by
  rw [hchain, heigen, F.add_left, F.smul_left, F.smul_right, hreal] at hpaired
  linear_combination hpaired

theorem AdditiveScalarForm.mass_zero_of_symmetric_jordan_chain
    (F : AdditiveScalarForm E) (T : E → E) {v w : E} {μ : ℂ}
    (heigen : T v = μ • v) (hchain : T w = μ • w + v)
    (hdiagonal : F.η (T v) v = F.η v (T v))
    (hpaired : F.η (T w) v = F.η w (T v)) : F.η v v = 0 := by
  by_cases hreal : conj μ = μ
  · exact F.mass_zero_of_real_jordan_chain T heigen hchain hpaired hreal
  · exact F.toScalarHomogeneousForm.isotropic_of_nonreal heigen hdiagonal hreal

namespace FockEigenvectors

def coherentJet (s : ℂ) : Coeff
  | 0 => 0
  | n + 1 => coherent s n

theorem derivative_coherentJet (s : ℂ) :
    derivativeAction (coherentJet s) = s • coherentJet s + coherent s := by
  ext n
  cases n with
  | zero => simp [derivativeAction, coherentJet, coherent]
  | succ n =>
    have hd := congrFun (derivative_coherent s) n
    simp only [derivativeAction, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, smul_eq_mul] at hd
    simp only [derivativeAction, LinearMap.coe_mk, AddHom.coe_mk,
      coherentJet, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    linear_combination hd

theorem spectral_coherentJet (s : ℂ) :
    spectralAction (coherentJet s) =
      spectralParam s • coherentJet s - I • coherent s := by
  ext n
  have hd := congrFun (derivative_coherentJet s) n
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hd
  change -I * (derivativeAction (coherentJet s) n - (1 / 2 : ℂ) * coherentJet s n) =
    spectralParam s * coherentJet s n - I * coherent s n
  rw [hd]
  unfold spectralParam
  ring

def coherentJordan (s : ℂ) : Coeff := I • coherentJet s

theorem spectral_coherentJordan (s : ℂ) :
    spectralAction (coherentJordan s) =
      spectralParam s • coherentJordan s + coherent s := by
  rw [coherentJordan, map_smul, spectral_coherentJet]
  ext n
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  calc
    I * (spectralParam s * coherentJet s n - I * coherent s n) =
      spectralParam s * (I * coherentJet s n) - I ^ 2 * coherent s n := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem coherent_mass_zero_of_real_chain_symmetry (F : AdditiveScalarForm Coeff)
    {s : ℂ} (hs : s.re = 1 / 2)
    (hpaired : F.η (spectralAction (coherentJordan s)) (coherent s) =
      F.η (coherentJordan s) (spectralAction (coherent s))) :
    F.η (coherent s) (coherent s) = 0 := by
  apply F.mass_zero_of_real_jordan_chain spectralAction (spectral_coherent s)
    (spectral_coherentJordan s) hpaired
  exact Complex.conj_eq_iff_im.mpr ((spectralParam_real_iff s).mpr hs)

end FockEigenvectors
end Reinmann

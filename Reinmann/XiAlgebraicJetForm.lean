/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiAlgebraicJetSpace
import Reinmann.PseudoHermitianPacketMass
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# One fixed arithmetic Hermitian form on the algebraic jet space

A mixed-derivative kernel Gram matrix is Hermitianized once on all complex
parameters and all jet orders. Its finite-sum form is transported through the
injective coefficient realization. The coherent-to-jet entries agree with
the Xi kernel derivatives, giving nonzero arithmetic cross pairings at every
Xi zero. This is an algebraic form, not a claimed bounded Fock operator.
Operator-form symmetry and the relative paired budget remain separate.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAlgebraicJetForm
open XiAlgebraicJetSpace XiAnnihilator XiDividedDifference FockEigenvectors

def pairing (K : Label → Label → ℂ) (c d : Expansion) : ℂ :=
  c.sum fun a ca => d.sum fun b db => ca * conj db * K a b

def expansionForm (K : Label → Label → ℂ) : AdditiveScalarForm Expansion where
  η := pairing K
  smul_left := by
    intro a c d
    simp [pairing, Finsupp.sum_smul_index, Finsupp.mul_sum, mul_assoc]
  smul_right := by
    intro a c d
    simp [pairing, Finsupp.sum_smul_index, Finsupp.mul_sum, map_mul,
      mul_assoc, mul_left_comm, mul_comm]
  add_left := by
    intro c d e
    simp [pairing, Finsupp.sum_add_index, add_mul, Finsupp.sum_add]
  add_right := by
    intro c d e
    simp [pairing, Finsupp.sum_add_index', map_add, mul_add, add_mul, Finsupp.sum_add]

theorem pairing_hermitian {K : Label → Label → ℂ}
    (hK : ∀ a b, conj (K b a) = K a b) (c d : Expansion) :
    conj (pairing K d c) = pairing K c d := by
  classical
  simp only [pairing, Finsupp.sum, map_sum, map_mul, Complex.conj_conj, hK]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem pairing_single (K : Label → Label → ℂ) (a b : Label) :
    pairing K (Finsupp.single a 1) (Finsupp.single b 1) = K a b := by
  simp [pairing]

def rawGram (a b : Label) : ℂ :=
  iteratedDeriv a.2 (fun s => iteratedDeriv b.2 (polarizedKernel s) (conj b.1)) a.1

def gram (a b : Label) : ℂ := (rawGram a b + conj (rawGram b a)) / 2

theorem gram_hermitian (a b : Label) : conj (gram b a) = gram a b := by
  simp [gram, map_div₀, map_add, map_ofNat, Complex.conj_conj, add_comm]

theorem iteratedDeriv_conj_function (p : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv p (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv p f ∘ conj := by
  induction p with
  | zero => simp
  | succ p hp => rw [iteratedDeriv_succ, hp, deriv_conj_conj, iteratedDeriv_succ]

theorem rawGram_zero_left_conj (s t : ℂ) (p : ℕ) :
    conj (rawGram ⟨t, p⟩ ⟨s, 0⟩) = rawGram ⟨s, 0⟩ ⟨t, p⟩ := by
  have heq : (fun z => polarizedKernel z (conj s)) = conj ∘ polarizedKernel s ∘ conj := by
    funext z
    simpa [Function.comp, polarizedKernel_eq_kernel] using kernel_hermitian z s
  simp only [rawGram, iteratedDeriv_zero]
  rw [heq, iteratedDeriv_conj_function]
  simp [Function.comp]

theorem gram_zero_left (s t : ℂ) (p : ℕ) :
    gram ⟨s, 0⟩ ⟨t, p⟩ = iteratedDeriv p (polarizedKernel s) (conj t) := by
  rw [gram, rawGram_zero_left_conj]
  simp only [rawGram, iteratedDeriv_zero]
  ring

def pullbackForm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : AdditiveScalarForm Expansion) (L : V →ₗ[ℂ] Expansion) : AdditiveScalarForm V where
  η x y := F.η (L x) (L y)
  smul_left := by intro a x y; rw [map_smul, F.smul_left]
  smul_right := by intro a x y; rw [map_smul, F.smul_right]
  add_left := by intro x y z; rw [map_add, F.add_left]
  add_right := by intro x y z; rw [map_add, F.add_right]

def coreForm : AdditiveScalarForm core :=
  pullbackForm (expansionForm gram) coordinatesEquiv.symm.toLinearMap

def arithmeticForm : AdditiveScalarForm arithmeticDomain :=
  pullbackForm (expansionForm gram)
    (coordinatesEquiv.symm.toLinearMap.comp arithmeticDomain.subtype)

theorem arithmeticForm_hermitian (x y : arithmeticDomain) :
    conj (arithmeticForm.η y x) = arithmeticForm.η x y :=
  pairing_hermitian gram_hermitian _ _

theorem arithmeticForm_jets (s t : ℂ) (p q : ℕ)
    (hs : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0)
    (ht : ∀ j : ℕ, j ≤ q → iteratedDeriv j xiCompleted t = 0) :
    arithmeticForm.η (jetState s p hs) (jetState t q ht) = gram ⟨s, p⟩ ⟨t, q⟩ := by
  change pairing gram (coordinatesEquiv.symm (jetInCore s p))
    (coordinatesEquiv.symm (jetInCore t q)) = _
  rw [coordinates_jet, coordinates_jet, pairing_single]

def coherentState (s : ℂ) (hz : xiCompleted s = 0) : arithmeticDomain :=
  jetState s 0 (by
    intro j hj
    have he : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa using hz)

theorem coherentState_eigen (s : ℂ) (hz : xiCompleted s = 0) :
    arithmeticSpectral (coherentState s hz) = spectralParam s • coherentState s hz := by
  apply Subtype.ext
  apply Subtype.ext
  exact spectral_coherent s

theorem coherentState_mass (s : ℂ) (hz : xiCompleted s = 0) :
    arithmeticForm.η (coherentState s hz) (coherentState s hz) = kernel s s := by
  rw [coherentState, arithmeticForm_jets, gram_zero_left]
  simp [polarizedKernel_eq_kernel]

theorem coherent_jet_partner_pairing (s : ℂ) (hz : xiCompleted s = 0) (p : ℕ)
    (ht : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted (1 - conj s) = 0) :
    arithmeticForm.η (coherentState s hz) (jetState (1 - conj s) p ht) = jetCoupling s p := by
  rw [coherentState, arithmeticForm_jets, gram_zero_left]
  simp [jetCoupling, map_sub]

theorem zero_has_nonzero_arithmetic_cross_pairing {s : ℂ} (hz : xiCompleted s = 0) :
    ∃ w : arithmeticDomain, arithmeticForm.η (coherentState s hz) w ≠ 0 := by
  obtain ⟨m, hm, hvan, hd⟩ := exists_finite_xi_multiplicity hz
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have ht : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted (1 - conj s) = 0 := by
    intro j hj
    rw [iteratedDeriv_xi_one_sub, iteratedDeriv_xi_conj, hvan j (by omega), map_zero, mul_zero]
  refine ⟨jetState (1 - conj s) p ht, ?_⟩
  rw [coherent_jet_partner_pairing]
  exact jetCoupling_ne_zero s p hd

end Reinmann.XiAlgebraicJetForm

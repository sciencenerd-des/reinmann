/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.XiHigherJetCoupling
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The fixed algebraic span of all coherent jets

The labels range over all complex parameters and all natural jet orders,
before selecting zeros. Their coefficient realization is injective. The
operator is restricted from coefficient differentiation, and its arithmetic
domain is the pullback of the independently defined convergent Xi rows.
No Hilbert completion, metric positivity or reality of zeros is assumed.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAlgebraicJetSpace
open FockEigenvectors XiAnnihilator

abbrev Label := Σ _ : ℂ, ℕ
abbrev Expansion := Label →₀ ℂ

def jetFamily (a : Label) : Coeff := higherJet a.1 a.2

theorem higherJet_diagonal (s : ℂ) (p : ℕ) : higherJet s p p = 1 := by
  simpa [coherent] using higherJet_apply_add s p 0

theorem jets_at_parameter_linearIndependent (s : ℂ) : LinearIndependent ℂ (higherJet s) := by
  classical
  rw [linearIndependent_iff']
  intro S a h
  have hall : ∀ n : ℕ, n ∈ S → a n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have heval := congrFun h n
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
      have hsum : (∑ i ∈ S, a i * higherJet s i n) = a n := by
        calc
          _ = a n * higherJet s n n := by
            apply Finset.sum_eq_single_of_mem n hn
            intro i hi hine
            by_cases hil : i < n
            · rw [ih i hil hi, zero_mul]
            · rw [higherJet_apply_lt s (by omega : n < i), mul_zero]
          _ = _ := by rw [higherJet_diagonal, mul_one]
      rw [hsum] at heval
      exact heval
  exact hall

def shiftedAction (s : ℂ) : Coeff →ₗ[ℂ] Coeff := derivativeAction - s • LinearMap.id

theorem shifted_jet_zero (s : ℂ) : shiftedAction s (higherJet s 0) = 0 := by
  simp [shiftedAction, derivative_coherent]

theorem shifted_jet_succ (s : ℂ) (p : ℕ) :
    shiftedAction s (higherJet s (p + 1)) = (p + 1 : ℂ) • higherJet s p := by
  change derivativeAction (higherJet s (p + 1)) - s • higherJet s (p + 1) = _
  rw [derivative_higherJet_succ]
  abel

theorem shifted_power_kills_jet (s : ℂ) (p : ℕ) :
    (shiftedAction s ^ (p + 1)) (higherJet s p) = 0 := by
  induction p with
  | zero => simpa using shifted_jet_zero s
  | succ p hp =>
    rw [pow_succ, Module.End.mul_apply, shifted_jet_succ, map_smul, hp, smul_zero]

theorem jet_mem_maxGenEigenspace (s : ℂ) (p : ℕ) :
    higherJet s p ∈ Module.End.genEigenspace derivativeAction s ⊤ := by
  apply Module.End.mem_genEigenspace_top.mpr
  refine ⟨p + 1, ?_⟩
  simpa [shiftedAction, LinearMap.mem_ker] using shifted_power_kills_jet s p

theorem span_jets_le_maxGenEigenspace (s : ℂ) :
    Submodule.span ℂ (Set.range (higherJet s)) ≤
      Module.End.genEigenspace derivativeAction s ⊤ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact jet_mem_maxGenEigenspace s p

theorem parameter_spans_independent :
    iSupIndep (fun s : ℂ => Submodule.span ℂ (Set.range (higherJet s))) :=
  (Module.End.independent_genEigenspace derivativeAction ⊤).mono span_jets_le_maxGenEigenspace

theorem jetFamily_linearIndependent : LinearIndependent ℂ jetFamily := by
  apply linearIndependent_iUnion_finite jets_at_parameter_linearIndependent
  intro s t ht hnot
  have h := iSupIndep_def.mp parameter_spans_independent s
  apply h.mono_right
  apply iSup₂_le
  intro u hu
  have hus : u ≠ s := by intro heq; subst u; exact hnot hu
  exact le_iSup_of_le u (le_iSup_of_le hus le_rfl)

def realize : Expansion →ₗ[ℂ] Coeff := Finsupp.linearCombination ℂ jetFamily

theorem realize_injective : Function.Injective realize :=
  (linearIndependent_iff_injective_finsuppLinearCombination.mp jetFamily_linearIndependent)

theorem realize_single (s : ℂ) (p : ℕ) (a : ℂ) :
    realize (Finsupp.single ⟨s, p⟩ a) = a • higherJet s p := by
  simp [realize, jetFamily]

def core : Submodule ℂ Coeff := Submodule.span ℂ (Set.range jetFamily)

def coordinatesEquiv : Expansion ≃ₗ[ℂ] core :=
  jetFamily_linearIndependent.linearCombinationEquiv

theorem coordinatesEquiv_coe (c : Expansion) :
    (coordinatesEquiv c : Coeff) = realize c := rfl

theorem jet_mem_core (s : ℂ) (p : ℕ) : higherJet s p ∈ core :=
  Submodule.subset_span ⟨⟨s, p⟩, rfl⟩

def jetInCore (s : ℂ) (p : ℕ) : core := ⟨higherJet s p, jet_mem_core s p⟩

theorem coordinates_jet (s : ℂ) (p : ℕ) :
    coordinatesEquiv.symm (jetInCore s p) = Finsupp.single ⟨s, p⟩ 1 := by
  apply coordinatesEquiv.injective
  apply Subtype.ext
  simpa [coordinatesEquiv_coe, realize_single, jetInCore] using
    realize_single s p 1 |>.symm

theorem derivative_mem_core {c : Coeff} (hc : c ∈ core) : derivativeAction c ∈ core := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨⟨s, p⟩, rfl⟩
    cases p with
    | zero =>
      simpa [jetFamily, derivative_coherent] using core.smul_mem s (jet_mem_core s 0)
    | succ p =>
      rw [jetFamily, derivative_higherJet_succ]
      exact core.add_mem (core.smul_mem s (jet_mem_core s (p + 1)))
        (core.smul_mem (p + 1 : ℂ) (jet_mem_core s p))
  | zero => simpa using core.zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using core.add_mem hx' hy'
  | smul a x hx hx' => simpa only [map_smul] using core.smul_mem a hx'

def derivativeOnCore : core →ₗ[ℂ] core :=
  derivativeAction.restrict (fun _ hc => derivative_mem_core hc)

def arithmeticDomain : Submodule ℂ core := domain.comap core.subtype

theorem derivative_mem_arithmeticDomain {c : core} (hc : c ∈ arithmeticDomain) :
    derivativeOnCore c ∈ arithmeticDomain := derivative_mem_domain hc

def derivativeOnArithmeticDomain : arithmeticDomain →ₗ[ℂ] arithmeticDomain :=
  derivativeOnCore.restrict (fun _ hc => derivative_mem_arithmeticDomain hc)

def arithmeticSpectral : arithmeticDomain →ₗ[ℂ] arithmeticDomain :=
  (-I) • (derivativeOnArithmeticDomain - (1 / 2 : ℂ) • LinearMap.id)

def jetState (s : ℂ) (p : ℕ)
    (hvan : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0) : arithmeticDomain :=
  ⟨jetInCore s p, higherJet_mem_domain s p hvan⟩

theorem jetState_nonzero (s : ℂ) (p : ℕ)
    (hvan : ∀ j : ℕ, j ≤ p → iteratedDeriv j xiCompleted s = 0) : jetState s p hvan ≠ 0 := by
  intro hz
  exact higherJet_nonzero s p (congrArg (fun c : arithmeticDomain => ((c : core) : Coeff)) hz)

theorem coherent_state_eigen (s : ℂ) (hz : xiCompleted s = 0) :
    arithmeticSpectral (jetState s 0 (by simpa using hz)) =
      spectralParam s • jetState s 0 (by simpa using hz) := by
  apply Subtype.ext
  apply Subtype.ext
  exact spectral_coherent s

end Reinmann.XiAlgebraicJetSpace

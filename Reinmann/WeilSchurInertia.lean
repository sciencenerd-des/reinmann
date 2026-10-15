import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
Finite-dimensional Schur inertia after an explicitly supplied completion of
the square. No operator-domain assertion or positivity instance is supplied.
-/

noncomputable section
open QuadraticMap

namespace Reinmann.WeilSchurInertia

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module ℝ M] [Module ℝ N] [FiniteDimensional ℝ M] [FiniteDimensional ℝ N]

theorem sigNeg_le_of_injective_domination
    (Q : QuadraticForm ℝ M) (R : QuadraticForm ℝ N)
    (f : M →ₗ[ℝ] N) (hf : Function.Injective f)
    (hdom : ∀ x, R (f x) ≤ Q x) : sigNeg Q ≤ sigNeg R := by
  obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigNeg_and_negDef Q
  let g : V →ₗ[ℝ] N := f.comp V.subtype
  have hg : Function.Injective g := hf.comp V.subtype_injective
  have hneg : ((-R).restrict (LinearMap.range g)).PosDef := by
    intro w hw
    obtain ⟨v, hv⟩ := w.property
    have hv0 : v ≠ 0 := by
      intro h
      apply hw
      apply Subtype.ext
      simpa [h] using hv.symm
    have hp := hV v hv0
    change 0 < -Q (v : M) at hp
    change 0 < -R (w : N)
    rw [← hv]
    exact lt_of_lt_of_le hp (neg_le_neg (hdom (v : M)))
  have hle := le_sigNeg_of_negDef R hneg
  rw [LinearMap.finrank_range_of_inj hg, hdim] at hle
  exact hle

theorem sigNeg_prod_of_nonneg (S : QuadraticForm ℝ M) (D : QuadraticForm ℝ N)
    (hD : ∀ y, 0 ≤ D y) : sigNeg (S.prod D) = sigNeg S := by
  apply Nat.le_antisymm
  · obtain ⟨V, hdim, hV⟩ := exists_finrank_eq_sigNeg_and_negDef (S.prod D)
    let f : V →ₗ[ℝ] M := (LinearMap.fst ℝ M N).comp V.subtype
    have hf : Function.Injective f := by
      intro u v huv
      by_contra hne
      have hnonzero : u-v ≠ 0 := sub_ne_zero.mpr hne
      have hp := hV (u-v) hnonzero
      have hz : ((u-v : V) : M × N).1 = 0 := by
        change f (u-v) = 0
        simp [huv]
      change 0 < -(S (((u-v : V) : M × N).1) + D (((u-v : V) : M × N).2)) at hp
      rw [hz, map_zero, zero_add] at hp
      linarith [hD (((u-v : V) : M × N).2)]
    have hneg : ((-S).restrict (LinearMap.range f)).PosDef := by
      intro w hw
      obtain ⟨v, hv⟩ := w.property
      have hv0 : v ≠ 0 := by
        intro h
        apply hw
        apply Subtype.ext
        simpa [h] using hv.symm
      have hp := hV v hv0
      change 0 < -(S (v : M × N).1 + D (v : M × N).2) at hp
      change 0 < -S (w : M)
      rw [← hv]
      change 0 < -S (v : M × N).1
      linarith [hD (v : M × N).2]
    have hle := le_sigNeg_of_negDef S hneg
    rw [LinearMap.finrank_range_of_inj hf, hdim] at hle
    exact hle
  · apply sigNeg_le_of_injective_domination S (S.prod D) (LinearMap.inl ℝ M N)
    · intro x y h
      exact congrArg Prod.fst h
    · intro x
      simp

/-- The triangular change of variables used to complete the square. -/
def shear (T : M →ₗ[ℝ] N) : (M × N) ≃ₗ[ℝ] (M × N) where
  toFun v := (v.1, v.2 + T v.1)
  invFun v := (v.1, v.2 - T v.1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' u v := by ext <;> simp <;> abel
  map_smul' c v := by ext <;> simp [smul_add]

/-- Schur inertia: the coercive complementary square contributes no negative
directions. In a matrix application T = D⁻¹B and S = H - BᵀD⁻¹B. -/
theorem schur_inertia_of_completion
    (Q : QuadraticForm ℝ (M × N)) (S : QuadraticForm ℝ M)
    (D : QuadraticForm ℝ N) (T : M →ₗ[ℝ] N)
    (hD : ∀ y, 0 ≤ D y)
    (hcomplete : ∀ x y, Q (x,y) = S x + D (y + T x)) :
    sigNeg Q = sigNeg S := by
  let e : Q.IsometryEquiv (S.prod D) :=
    { shear T with map_app' := by intro v; exact (hcomplete v.1 v.2).symm }
  exact (QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩).trans (sigNeg_prod_of_nonneg S D hD)

end Reinmann.WeilSchurInertia

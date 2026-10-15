import Reinmann.PseudoHermitianLocal

/-! A concrete obstruction to replacing diagonal nonvanishing by ordinary
nondegeneracy of an indefinite form. The form is nondegenerate and the action
is symmetric for it, but the action has an eigenvalue `I` at an isotropic state.
This is a classical mechanism, included as a checked scope regression. -/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.PseudoHermitianIsotropy

abbrev E := ℂ × ℂ

def swapForm : AdditiveScalarForm E where
  η x y := x.1 * conj y.2 + x.2 * conj y.1
  smul_left := by
    intro c x y
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  smul_right := by
    intro c x y
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul]
    ring
  add_left := by
    intro x y z
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  add_right := by
    intro x y z
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

def action : E →ₗ[ℂ] E where
  toFun x := (I * x.1, -I * x.2)
  map_add' := by
    intro x y
    ext <;> simp [mul_add]
  map_smul' := by
    intro c x
    ext <;> simp [smul_eq_mul] <;> ring

theorem swapForm_hermitian (x y : E) : conj (swapForm.η y x) = swapForm.η x y := by
  simp [swapForm, map_add, map_mul]
  ring

/-- Ordinary left nondegeneracy: all pairings vanish only for the zero state. -/
theorem swapForm_nondegenerate (x : E) (h : ∀ y, swapForm.η x y = 0) : x = 0 := by
  have h1 := h (0, 1)
  have h2 := h (1, 0)
  apply Prod.ext
  · simpa [swapForm] using h1
  · simpa [swapForm] using h2

theorem action_form_symmetric (x y : E) :
    swapForm.η (action x) y = swapForm.η x (action y) := by
  simp [swapForm, action, map_mul]
  ring

theorem eigenvector_nonzero : ((1, 0) : E) ≠ 0 := by
  simp

theorem eigenvalue_I : action ((1, 0) : E) = I • ((1, 0) : E) := by
  simp [action]

theorem eigenvector_isotropic : swapForm.η ((1, 0) : E) ((1, 0) : E) = 0 := by
  simp [swapForm]

theorem eigenvalue_nonreal : conj I ≠ I := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

end Reinmann.PseudoHermitianIsotropy

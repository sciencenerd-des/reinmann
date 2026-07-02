/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HorizontalRepulsion
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Horizontal Critical-Point Route

The global convexity experiment in `HorizontalRepulsion` is too strong. This file
keeps the same same-height-zero goal but weakens the analytic input.

For a fixed height `γ`, consider the complex-valued horizontal slice

  `x ↦ ζ(x + iγ)`.

A Rolle-style principle says: if this slice has two zeros at `x < y`, then
there is an intermediate horizontal critical point. A separate repulsion
principle says such a critical point cannot lie between two same-height zeros.

Together these two analytic inputs rule out two critical-strip zeros at the same
height, hence prove RH via the already verified fiber-cardinality criterion.

For complex-valued slices, the common-critical-point Rolle statement is stronger
than ordinary scalar Rolle. The componentwise variant below is closer to what
standard real-variable Rolle can provide: the real and imaginary parts get
critical points, possibly at different locations. A viable proof can attack
either the stronger common-critical route or the weaker componentwise route.
-/

noncomputable section

open Complex

namespace Reinmann

/-- The horizontal zeta slice at height `γ`. -/
def horizontalZetaSlice (γ : ℝ) : ℝ → ℂ :=
  fun x => riemannZeta (x + I * γ : ℂ)

/-- Its real-direction derivative. -/
def horizontalZetaDeriv (γ x : ℝ) : ℂ :=
  deriv (horizontalZetaSlice γ) x

/-- Rolle-style analytic input for horizontal zeta slices: two same-height zeros
force an intermediate horizontal critical point. -/
def HorizontalRolleForZetaZeros : Prop :=
  ∀ γ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → x < y →
    horizontalZetaSlice γ x = 0 → horizontalZetaSlice γ y = 0 →
      ∃ c : ℝ, x < c ∧ c < y ∧ horizontalZetaDeriv γ c = 0

/-- Same-height critical-point exclusion: no horizontal critical point can lie
between two distinct same-height critical-strip zeros. -/
def NoHorizontalCriticalBetweenZetaZeros : Prop :=
  ∀ γ x y c : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → x < c → c < y →
    horizontalZetaSlice γ x = 0 → horizontalZetaSlice γ y = 0 →
      horizontalZetaDeriv γ c ≠ 0

private theorem horizontalZetaSlice_zero_of_fiber {γ : ℝ} {s : ℂ}
    (hzs : riemannZeta s = 0) (hsim : s.im = γ) :
    horizontalZetaSlice γ s.re = 0 := by
  unfold horizontalZetaSlice
  have hs_eq : (s.re + I * γ : ℂ) = s := by
    apply Complex.ext <;> simp [hsim]
  rw [hs_eq, hzs]

/-- The Rolle input plus critical-point exclusion imply every height-fiber has
at most one zero. -/
theorem all_fiber_card_le_one_of_horizontalCriticalExclusion
    (hrolle : HorizontalRolleForZetaZeros)
    (hcrit : NoHorizontalCriticalBetweenZetaZeros) :
    ∀ γ : ℝ, (fiberFinset γ).card ≤ 1 := by
  intro γ
  rw [Finset.card_le_one]
  intro s hs t ht
  rw [mem_fiberFinset] at hs ht
  obtain ⟨hzs, hspos, hslt, hsim⟩ := hs
  obtain ⟨hzt, htpos, htlt, htim⟩ := ht
  by_cases hre : s.re = t.re
  · apply Complex.ext
    · exact hre
    · rw [hsim, htim]
  · have hs_slice : horizontalZetaSlice γ s.re = 0 :=
      horizontalZetaSlice_zero_of_fiber hzs hsim
    have ht_slice : horizontalZetaSlice γ t.re = 0 :=
      horizontalZetaSlice_zero_of_fiber hzt htim
    rcases lt_or_gt_of_ne hre with hst | hts
    · rcases hrolle γ s.re t.re hspos hslt htpos htlt hst hs_slice ht_slice with
        ⟨c, hsc, hct, hc⟩
      exact False.elim
        ((hcrit γ s.re t.re c hspos hslt htpos htlt hsc hct hs_slice ht_slice) hc)
    · rcases hrolle γ t.re s.re htpos htlt hspos hslt hts ht_slice hs_slice with
        ⟨c, htc, hcs, hc⟩
      exact False.elim
        ((hcrit γ t.re s.re c htpos htlt hspos hslt htc hcs ht_slice hs_slice) hc)

/-- The horizontal critical-point route implies RH. -/
theorem riemannHypothesis_of_horizontalCriticalExclusion
    (hrolle : HorizontalRolleForZetaZeros)
    (hcrit : NoHorizontalCriticalBetweenZetaZeros) : RiemannHypothesis :=
  riemannHypothesis_of_all_fiber_card_le_one
    (all_fiber_card_le_one_of_horizontalCriticalExclusion hrolle hcrit)

/-! ### Componentwise Rolle route -/

/-- Real part of the horizontal zeta slice. -/
def horizontalZetaRe (γ : ℝ) : ℝ → ℝ :=
  fun x => (horizontalZetaSlice γ x).re

/-- Imaginary part of the horizontal zeta slice. -/
def horizontalZetaIm (γ : ℝ) : ℝ → ℝ :=
  fun x => (horizontalZetaSlice γ x).im

/-- Componentwise Rolle input: two same-height zeros force an intermediate
critical point for the real part and an intermediate critical point for the
imaginary part, not necessarily the same point. -/
def ComponentwiseRolleForZetaZeros : Prop :=
  ∀ γ x y : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → x < y →
    horizontalZetaSlice γ x = 0 → horizontalZetaSlice γ y = 0 →
      (∃ c_re : ℝ, x < c_re ∧ c_re < y ∧ deriv (horizontalZetaRe γ) c_re = 0) ∧
      (∃ c_im : ℝ, x < c_im ∧ c_im < y ∧ deriv (horizontalZetaIm γ) c_im = 0)

private theorem horizontalZetaRe_continuousOn_Icc {γ x y : ℝ}
    (hylt : y < 1) : ContinuousOn (horizontalZetaRe γ) (Set.Icc x y) := by
  intro u hu
  have hu_le : u ≤ y := hu.2
  have hu_ne : (u + I * γ : ℂ) ≠ 1 := by
    intro h
    have hre : u = (1 : ℂ).re := by
      calc
        u = (u + I * γ : ℂ).re := by simp
        _ = (1 : ℂ).re := by rw [h]
    simp at hre
    linarith
  have hslice : ContinuousAt (horizontalZetaSlice γ) u := by
    unfold horizontalZetaSlice
    exact ContinuousAt.comp
      ((differentiableAt_riemannZeta hu_ne).restrictScalars ℝ).continuousAt
      (show ContinuousAt (fun x : ℝ => (x : ℂ) + I * γ) u by fun_prop)
  unfold horizontalZetaRe
  exact (Complex.continuous_re.continuousAt.comp hslice).continuousWithinAt

private theorem horizontalZetaIm_continuousOn_Icc {γ x y : ℝ}
    (hylt : y < 1) : ContinuousOn (horizontalZetaIm γ) (Set.Icc x y) := by
  intro u hu
  have hu_le : u ≤ y := hu.2
  have hu_ne : (u + I * γ : ℂ) ≠ 1 := by
    intro h
    have hre : u = (1 : ℂ).re := by
      calc
        u = (u + I * γ : ℂ).re := by simp
        _ = (1 : ℂ).re := by rw [h]
    simp at hre
    linarith
  have hslice : ContinuousAt (horizontalZetaSlice γ) u := by
    unfold horizontalZetaSlice
    exact ContinuousAt.comp
      ((differentiableAt_riemannZeta hu_ne).restrictScalars ℝ).continuousAt
      (show ContinuousAt (fun x : ℝ => (x : ℂ) + I * γ) u by fun_prop)
  unfold horizontalZetaIm
  exact (Complex.continuous_im.continuousAt.comp hslice).continuousWithinAt

/-- The componentwise Rolle input is ordinary real-variable calculus, not the
zeta-specific RH-strength gap.  The endpoints are zeros of the complex slice, so
both real and imaginary parts agree at the two endpoints; Rolle's theorem then
produces one critical point for each scalar component. -/
theorem componentwiseRolleForZetaZeros_proved : ComponentwiseRolleForZetaZeros := by
  intro γ x y _hxpos _hxlt _hypos hylt hxy hxzero hyzero
  constructor
  · rcases exists_deriv_eq_zero hxy (horizontalZetaRe_continuousOn_Icc (γ := γ) hylt)
      (by simp [horizontalZetaRe, hxzero, hyzero]) with ⟨c, hcIoo, hcderiv⟩
    exact ⟨c, hcIoo.1, hcIoo.2, hcderiv⟩
  · rcases exists_deriv_eq_zero hxy (horizontalZetaIm_continuousOn_Icc (γ := γ) hylt)
      (by simp [horizontalZetaIm, hxzero, hyzero]) with ⟨c, hcIoo, hcderiv⟩
    exact ⟨c, hcIoo.1, hcIoo.2, hcderiv⟩

/-- Componentwise critical-pair exclusion: between two same-height zeros, it is
impossible to find both a real-part critical point and an imaginary-part
critical point in the interval. -/
def NoComponentwiseCriticalPairBetweenZetaZeros : Prop :=
  ∀ γ x y c_re c_im : ℝ, 0 < x → x < 1 → 0 < y → y < 1 →
    x < c_re → c_re < y → x < c_im → c_im < y →
    horizontalZetaSlice γ x = 0 → horizontalZetaSlice γ y = 0 →
      deriv (horizontalZetaRe γ) c_re ≠ 0 ∨ deriv (horizontalZetaIm γ) c_im ≠ 0

/-- The componentwise Rolle input plus componentwise critical-pair exclusion
rule out two critical-strip zeros at the same height. -/
theorem all_fiber_card_le_one_of_componentwiseCriticalExclusion
    (hrolle : ComponentwiseRolleForZetaZeros)
    (hcrit : NoComponentwiseCriticalPairBetweenZetaZeros) :
    ∀ γ : ℝ, (fiberFinset γ).card ≤ 1 := by
  intro γ
  rw [Finset.card_le_one]
  intro s hs t ht
  rw [mem_fiberFinset] at hs ht
  obtain ⟨hzs, hspos, hslt, hsim⟩ := hs
  obtain ⟨hzt, htpos, htlt, htim⟩ := ht
  by_cases hre : s.re = t.re
  · apply Complex.ext
    · exact hre
    · rw [hsim, htim]
  · have hs_slice : horizontalZetaSlice γ s.re = 0 :=
      horizontalZetaSlice_zero_of_fiber hzs hsim
    have ht_slice : horizontalZetaSlice γ t.re = 0 :=
      horizontalZetaSlice_zero_of_fiber hzt htim
    rcases lt_or_gt_of_ne hre with hst | hts
    · rcases hrolle γ s.re t.re hspos hslt htpos htlt hst hs_slice ht_slice with
        ⟨⟨cre, hscre, hcret, hrecrit⟩, ⟨cim, hscim, hcimt, himcrit⟩⟩
      rcases hcrit γ s.re t.re cre cim hspos hslt htpos htlt
          hscre hcret hscim hcimt hs_slice ht_slice with hbad | hbad
      · exact False.elim (hbad hrecrit)
      · exact False.elim (hbad himcrit)
    · rcases hrolle γ t.re s.re htpos htlt hspos hslt hts ht_slice hs_slice with
        ⟨⟨cre, htcre, hcre_s, hrecrit⟩, ⟨cim, htcim, hcim_s, himcrit⟩⟩
      rcases hcrit γ t.re s.re cre cim htpos htlt hspos hslt
          htcre hcre_s htcim hcim_s ht_slice hs_slice with hbad | hbad
      · exact False.elim (hbad hrecrit)
      · exact False.elim (hbad himcrit)

/-- The componentwise horizontal critical-pair route implies RH. -/
theorem riemannHypothesis_of_componentwiseCriticalExclusion
    (hrolle : ComponentwiseRolleForZetaZeros)
    (hcrit : NoComponentwiseCriticalPairBetweenZetaZeros) : RiemannHypothesis :=
  riemannHypothesis_of_all_fiber_card_le_one
    (all_fiber_card_le_one_of_componentwiseCriticalExclusion hrolle hcrit)

/-- After discharging the scalar Rolle step, the exact remaining local
same-height repulsion target is the zeta-specific componentwise critical-pair
exclusion.  Proving this exclusion would prove RH. -/
theorem riemannHypothesis_of_componentwiseCriticalPairExclusion
    (hcrit : NoComponentwiseCriticalPairBetweenZetaZeros) : RiemannHypothesis :=
  riemannHypothesis_of_componentwiseCriticalExclusion
    componentwiseRolleForZetaZeros_proved hcrit

end Reinmann

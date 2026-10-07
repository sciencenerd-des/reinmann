/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Named inputs for the computer-assisted compact Weil window

The analytic Weil functional is the explicit parameter `Q`, and its legal
test class is `Admissible`. Identifying these parameters with the genuine
explicit-formula functional and verifying its analytic/computational bounds
remain external inputs. No Arb interval or Weil explicit formula is asserted
as a Lean theorem. Named hypotheses are arguments, never global axioms.

What is proved: exact cutoff/prime arithmetic, the scalar block and Schur
inequalities, certificate assembly, restriction to smaller supports, and
passage from cofinal certified windows to all-window positivity. A single
finite certificate does not supply that cofinal family or prove RH.
-/
noncomputable section
namespace Reinmann.WeilWindow
open MeasureTheory

abbrev TestFunction := ℝ → ℂ

/-- Centered additive support of half-width `a`. -/
def Supported (a : ℝ) (f : TestFunction) : Prop :=
  ∀ x : ℝ, a < |x| → f x = 0

def energy (f : TestFunction) : ℝ := ∫ x : ℝ, ‖f x‖ ^ 2

theorem energy_nonneg (f : TestFunction) : 0 ≤ energy f :=
  integral_nonneg fun x => sq_nonneg ‖f x‖

theorem supported_mono {a b : ℝ} {f : TestFunction}
    (hab : a ≤ b) (hf : Supported a f) : Supported b f := by
  intro x hx
  exact hf x (lt_of_le_of_lt hab hx)

/-- External full-form certificate, including all complement and coupling terms. -/
def WindowBoundHypothesis (Q : TestFunction → ℝ) (Admissible : TestFunction → Prop)
    (a c : ℝ) : Prop :=
  ∀ f, Admissible f → Supported a f → c * energy f ≤ Q f

def cutoff : ℝ := Real.exp (6 / 5)
def finiteLower : ℝ := 1 / 10 ^ 12
def complementLower : ℝ := 1131 / 20000 - 9444 / 10 ^ 63
def couplingUpper : ℝ := 1431 / 10 ^ 31
def publicLower : ℝ := 9 / 10 ^ 13
def schurComplementLower : ℝ := 1131 / 20000 - 7843 / 10 ^ 22
def schurCouplingUpper : ℝ := 4124 / 10 ^ 11
def schurTarget : ℝ := 19 / (2 * 10 ^ 13)

/-- The October 7 certificate as a named input, not a theorem about zeta. -/
def CertifiedExpSixFifthsHypothesis (Q : TestFunction → ℝ)
    (Admissible : TestFunction → Prop) : Prop :=
  WindowBoundHypothesis Q Admissible (3 / 5) publicLower

theorem publicLower_pos : 0 < publicLower := by norm_num [publicLower]

theorem cutoff_support_dictionary : Real.exp (2 * (3 / 5)) = cutoff := by
  congr 1
  norm_num

theorem cutoff_between_three_four : 3 < cutoff ∧ cutoff < 4 := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (x := (6 / 5 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    dsimp [cutoff]
    linarith
  · have hsmall : Real.exp (1 / 5 : ℝ) ≤ 5 / 4 := by
      have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 5 : ℝ))
        (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h
    have hone := Real.exp_one_lt_three
    have hpos := Real.exp_pos (1 / 5 : ℝ)
    have heq : (6 / 5 : ℝ) = 1 + 1 / 5 := by norm_num
    rw [cutoff, heq, Real.exp_add]
    nlinarith

/-- Finite prime-power enumeration is checked by Lean's kernel. -/
theorem prime_powers_below_four :
    ∀ q ∈ Finset.range 4, IsPrimePow q ↔ q = 2 ∨ q = 3 := by
  decide +kernel

theorem active_prime_powers (q : ℕ) :
    (IsPrimePow q ∧ (q : ℝ) < cutoff) ↔ q = 2 ∨ q = 3 := by
  constructor
  · rintro ⟨hq, hcut⟩
    have hq4 : q < 4 := by
      exact_mod_cast (hcut.trans cutoff_between_three_four.2)
    exact (prime_powers_below_four q (Finset.mem_range.mpr hq4)).mp hq
  · intro hq
    rcases hq with rfl | rfl
    · exact ⟨by decide +kernel, by
        change (2 : ℝ) < cutoff
        linarith [cutoff_between_three_four.1]⟩
    · exact ⟨by decide +kernel, cutoff_between_three_four.1⟩

/-- Complete-square block lower bound. No sign assumption on the coordinates. -/
theorem linear_block_lower (x y ell d B ε R : ℝ)
    (hB : 0 ≤ B) (hell : ε ≤ ell - B) (hd : ε ≤ d - B)
    (hR : ell * x ^ 2 + d * y ^ 2 - 2 * B * x * y ≤ R) :
    ε * (x ^ 2 + y ^ 2) ≤ R := by
  have hmix := mul_nonneg hB (sq_nonneg (x - y))
  have hx := mul_nonneg (show 0 ≤ ell - B - ε by linarith) (sq_nonneg x)
  have hy := mul_nonneg (show 0 ≤ d - B - ε by linarith) (sq_nonneg y)
  nlinarith

/-- Schur estimate: the cross loss scales like B²/d rather than B.
This is a proved general inequality, not an instantiated larger Weil window. -/
theorem schur_block_lower (x y ell d B ε R : ℝ)
    (hell : ε < ell) (hdet : B ^ 2 ≤ (ell - ε) * (d - ε))
    (hR : ell * x ^ 2 + d * y ^ 2 - 2 * B * x * y ≤ R) :
    ε * (x ^ 2 + y ^ 2) ≤ R := by
  have h1 := mul_nonneg (show 0 ≤ ell - ε by linarith)
    (show 0 ≤ R - (ell * x ^ 2 + d * y ^ 2 - 2 * B * x * y) by linarith)
  have h2 := sq_nonneg ((ell - ε) * x - B * y)
  have h3 := mul_nonneg (show 0 ≤ (ell - ε) * (d - ε) - B ^ 2 by linarith)
    (sq_nonneg y)
  have hid :
      (ell - ε) * (R - ε * (x ^ 2 + y ^ 2)) =
      (ell - ε) * (R - (ell * x ^ 2 + d * y ^ 2 - 2 * B * x * y)) +
        ((ell - ε) * x - B * y) ^ 2 +
        ((ell - ε) * (d - ε) - B ^ 2) * y ^ 2 := by ring
  have hprod : 0 ≤ (ell - ε) * (R - ε * (x ^ 2 + y ^ 2)) := by
    rw [hid]
    exact add_nonneg (add_nonneg h1 h2) h3
  have := (mul_nonneg_iff_of_pos_left (show 0 < ell - ε by linarith)).mp hprod
  linarith

/-- Explicit example of the gain. These numbers are illustrative, not a
computed Weil eigenvalue or a new window certificate. -/
theorem schur_can_close_when_linear_allowance_fails :
    (1 / 10 ^ 21 : ℝ) ^ 2 ≤
      (1 / 10 ^ 40 - 1 / (2 * 10 ^ 40)) * (1 / 2 - 1 / (2 * 10 ^ 40)) ∧
    (1 / 10 ^ 40 - 1 / 10 ^ 21 : ℝ) < 0 := by
  norm_num

/-- External analytic and numerical inputs, separated by their actual role.
`retained` includes both parity blocks, `omitted` the whole complement, and
`cross` its full coupling. The arithmetic source normalization is an input
through `source_domination`, not silently identified with an arbitrary form. -/
structure WindowBlockHypotheses (Q : TestFunction → ℝ)
    (Admissible : TestFunction → Prop) (a ell d B : ℝ) where
  reduced : TestFunction → ℝ
  retained : TestFunction → ℝ
  omitted : TestFunction → ℝ
  cross : TestFunction → ℝ
  lowSize : TestFunction → ℝ
  tailSize : TestFunction → ℝ
  source_domination : ∀ f, Admissible f → Supported a f → reduced f ≤ Q f
  energy_split : ∀ f, Admissible f → Supported a f →
    energy f = lowSize f ^ 2 + tailSize f ^ 2
  form_assembly : ∀ f, Admissible f → Supported a f →
    reduced f = retained f + omitted f + 2 * cross f
  finite_compression : ∀ f, Admissible f → Supported a f →
    ell * lowSize f ^ 2 ≤ retained f
  infinite_complement : ∀ f, Admissible f → Supported a f →
    d * tailSize f ^ 2 ≤ omitted f
  full_coupling : ∀ f, Admissible f → Supported a f →
    -B * lowSize f * tailSize f ≤ cross f

theorem WindowBlockHypotheses.two_block {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} {a ell d B : ℝ}
    (h : WindowBlockHypotheses Q Admissible a ell d B)
    (f : TestFunction) (hf : Admissible f) (hs : Supported a f) :
    ell * h.lowSize f ^ 2 + d * h.tailSize f ^ 2 -
      2 * B * h.lowSize f * h.tailSize f ≤ h.reduced f := by
  rw [h.form_assembly f hf hs]
  linarith [h.finite_compression f hf hs, h.infinite_complement f hf hs,
    h.full_coupling f hf hs]

theorem WindowBlockHypotheses.bound {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} {a ell d B ε : ℝ}
    (h : WindowBlockHypotheses Q Admissible a ell d B)
    (hB : 0 ≤ B) (hell : ε ≤ ell - B) (hd : ε ≤ d - B) :
    WindowBoundHypothesis Q Admissible a ε := by
  intro f hf hs
  rw [h.energy_split f hf hs]
  exact (linear_block_lower _ _ _ _ _ _ _ hB hell hd (h.two_block f hf hs)).trans
    (h.source_domination f hf hs)

theorem WindowBlockHypotheses.schur_bound {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} {a ell d B ε : ℝ}
    (h : WindowBlockHypotheses Q Admissible a ell d B)
    (hell : ε < ell) (hdet : B ^ 2 ≤ (ell - ε) * (d - ε)) :
    WindowBoundHypothesis Q Admissible a ε := by
  intro f hf hs
  rw [h.energy_split f hf hs]
  exact (schur_block_lower _ _ _ _ _ _ _ hell hdet (h.two_block f hf hs)).trans
    (h.source_domination f hf hs)

theorem certificate_arithmetic :
    0 ≤ couplingUpper ∧ publicLower ≤ finiteLower - couplingUpper ∧
      publicLower ≤ complementLower - couplingUpper := by
  norm_num [couplingUpper, publicLower, finiteLower, complementLower]

theorem certified_exp_six_fifths_of_blocks {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop}
    (h : WindowBlockHypotheses Q Admissible (3 / 5)
      finiteLower complementLower couplingUpper) :
    CertifiedExpSixFifthsHypothesis Q Admissible :=
  h.bound certificate_arithmetic.1 certificate_arithmetic.2.1 certificate_arithmetic.2.2

/-- Named analytic/numerical input for the smaller 124-degree Schur run. -/
def Polynomial124SchurHypothesis (Q : TestFunction → ℝ)
    (Admissible : TestFunction → Prop) : Type :=
  WindowBlockHypotheses Q Admissible (3 / 5)
    finiteLower schurComplementLower schurCouplingUpper

theorem schur_certificate_arithmetic :
    schurTarget < finiteLower ∧
    schurCouplingUpper ^ 2 ≤
      (finiteLower - schurTarget) * (schurComplementLower - schurTarget) ∧
    finiteLower - schurCouplingUpper < 0 := by
  norm_num [finiteLower, schurTarget, schurCouplingUpper, schurComplementLower]

theorem window_bound_weaken {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} {a c d : ℝ}
    (h : WindowBoundHypothesis Q Admissible a d) (hcd : c ≤ d) :
    WindowBoundHypothesis Q Admissible a c := by
  intro f hf hs
  exact (mul_le_mul_of_nonneg_right hcd (energy_nonneg f)).trans (h f hf hs)

theorem certified_exp_six_fifths_of_schur_blocks {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} (h : Polynomial124SchurHypothesis Q Admissible) :
    CertifiedExpSixFifthsHypothesis Q Admissible := by
  exact window_bound_weaken
    (h.schur_bound schur_certificate_arithmetic.1 schur_certificate_arithmetic.2.1)
    (by norm_num [publicLower, schurTarget])

theorem window_bound_restrict {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} {a b c : ℝ}
    (h : WindowBoundHypothesis Q Admissible b c) (hab : a ≤ b) :
    WindowBoundHypothesis Q Admissible a c := by
  intro f hf hs
  exact h f hf (supported_mono hab hs)

theorem smaller_windows_of_certificate {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop}
    (h : CertifiedExpSixFifthsHypothesis Q Admissible) {a : ℝ} (ha : a ≤ 3 / 5) :
    WindowBoundHypothesis Q Admissible a publicLower :=
  window_bound_restrict h ha

theorem window_nonnegative_of_bound {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop} {a c : ℝ}
    (h : WindowBoundHypothesis Q Admissible a c) (hc : 0 ≤ c)
    {f : TestFunction} (hf : Admissible f) (hs : Supported a f) : 0 ≤ Q f :=
  (mul_nonneg hc (energy_nonneg f)).trans (h f hf hs)

/-- The genuinely unbounded research input: a cofinal supply of full-window
bounds. The single October certificate does not discharge this hypothesis. -/
def CofinalWindowBoundsHypothesis (Q : TestFunction → ℝ)
    (Admissible : TestFunction → Prop) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ b c : ℝ, a ≤ b ∧ 0 ≤ c ∧
    WindowBoundHypothesis Q Admissible b c

theorem all_windows_of_cofinal_bounds {Q : TestFunction → ℝ}
    {Admissible : TestFunction → Prop}
    (h : CofinalWindowBoundsHypothesis Q Admissible) :
    ∀ a : ℝ, 0 < a → ∀ f, Admissible f → Supported a f → 0 ≤ Q f := by
  intro a ha f hf hs
  obtain ⟨b, c, hab, hc, hb⟩ := h a ha
  exact window_nonnegative_of_bound (window_bound_restrict hb hab) hc hf hs

end Reinmann.WeilWindow

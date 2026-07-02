/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.ZeroFreeEngine
import Reinmann.Zeta341GlobalBridge
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic

/-!
# de la Vallée Poussin: verified deductive core, analytic inputs named

## Honest scope

The full zero-free region needs two analytic facts **absent from Mathlib**:
1. the logarithmic Euler series
   `log|ζ(σ+it)| = ∑_{p,k} k⁻¹ p^{-kσ} cos(kt log p)` (with summability), and
2. growth bounds on `ζ` near `Re = 1` (Borel–Carathéodory / Hadamard).

Formalizing those is a large project. We instead verify the two purely
*deductive* cores and expose the analytic facts as explicit hypotheses, so the
argument's skeleton is machine-checked and the gap is named, not hidden.

## The two cores

* **Positivity core** (`ZeroFreeEngine.cos_341_nonneg`): `3+4cosθ+cos2θ ≥ 0`,
  which yields `P(σ) := |ζ(σ)|³|ζ(σ+it)|⁴|ζ(σ+2it)| ≥ 1` once input (1) is known.
* **Order core** (`vdp_net_exponent_pos`): a boundary zero of order `m ≥ 1` makes
  `P(σ)` behave like `(σ-1)^{4m-3}`; since `4m - 3 ≥ 1 > 0`, `P(σ) → 0` as
  `σ → 1⁺`. This is input (2)'s consequence.

* **The contradiction** (`product_bound_contradiction`): a function that is `≥ 1`
  on `(1,∞)` cannot tend to `0` at `1⁺`. Fully proved here. Plugging in `P`
  contradicts a boundary zero — the de la Vallée Poussin conclusion.
-/

noncomputable section

open Filter Topology Complex

namespace Reinmann

/-! ### Order core (verified) -/

/-- **Net exponent of the 3-4-1 product.** Pole order `3` at `σ = 1` versus zero
order `4·m` from a boundary zero of order `m ≥ 1`: the net exponent `4m - 3` is
strictly positive, forcing the product to vanish at `1⁺`. -/
theorem vdp_net_exponent_pos {m : ℕ} (hm : 1 ≤ m) : 0 < 4 * (m : ℝ) - 3 := by
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-! ### The contradiction core (verified) -/

/-- **The deductive heart of de la Vallée Poussin's boundary argument.** If a real
function `P` satisfies `P σ ≥ 1` for all `σ > 1` yet tends to `0` as `σ → 1⁺`,
that is impossible. Applied to the 3-4-1 product `P`, a zero on `Re = 1` produces
exactly this contradiction. -/
theorem product_bound_contradiction
    (P : ℝ → ℝ)
    (hP0 : Tendsto P (𝓝[>] (1 : ℝ)) (𝓝 0))
    (hP1 : ∀ σ : ℝ, 1 < σ → (1 : ℝ) ≤ P σ) : False := by
  -- Near `1⁺`, `P σ < 1` (from tending to 0)…
  have hlt : ∀ᶠ σ in 𝓝[>] (1 : ℝ), P σ < 1 :=
    hP0 (Iio_mem_nhds (by norm_num))
  -- …but also `P σ ≥ 1` (from the hypothesis on `(1,∞)`).
  have hge : ∀ᶠ σ in 𝓝[>] (1 : ℝ), (1 : ℝ) ≤ P σ := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards with σ hσ
    exact hP1 σ hσ
  -- Contradiction on a nontrivial filter.
  have hfalse : ∀ᶠ _σ in 𝓝[>] (1 : ℝ), False := by
    filter_upwards [hlt, hge] with σ h1 h2
    linarith
  exact hfalse.exists.choose_spec

/-! ### The zeta 3-4-1 product plugged into the contradiction core -/

/-- The de la Vallée Poussin 3-4-1 product along the horizontal line with height
`t`, evaluated at real part `σ`. -/
def zeta341Product (t σ : ℝ) : ℝ :=
  ‖riemannZeta (σ : ℂ) ^ 3 * riemannZeta (σ + I * t) ^ 4 *
    riemannZeta (σ + 2 * I * t)‖

/-- The verified Euler-product lower bound for the zeta 3-4-1 product:
`P_t(σ) ≥ 1` for every `σ > 1`. -/
theorem zeta341Product_ge_one (t : ℝ) :
    ∀ σ : ℝ, 1 < σ → (1 : ℝ) ≤ zeta341Product t σ := by
  intro σ hσ
  exact zeta_341_modulus (σ := σ) (t := t) hσ

/-- If the zeta 3-4-1 product at height `t` tends to `0` as `σ → 1⁺`, then the
verified Euler-product lower bound gives a contradiction.

This is the fully formal boundary skeleton of the classical de la Vallée
Poussin argument. The remaining analytic input is precisely the limit hypothesis,
which would come from the local order of a hypothetical zero on `Re = 1` plus
growth control for the pole at `1`. -/
theorem zeta341Product_limit_zero_contradiction (t : ℝ)
    (hlim : Tendsto (zeta341Product t) (𝓝[>] (1 : ℝ)) (𝓝 0)) : False :=
  product_bound_contradiction (zeta341Product t) hlim (zeta341Product_ge_one t)

/-! ### The remaining analytic boundary input, stated explicitly -/

/-- The missing analytic input for the VDP boundary argument: a zero at `1 + it`
forces the 3-4-1 product at height `t` to tend to `0` as `σ → 1⁺`.

This packages the local-order/Laurent-expansion part of the classical proof as
a named target. It is intentionally a hypothesis, not an axiom in the active
proof tree. -/
def BoundaryZeroVDPLimit : Prop :=
  ∀ t : ℝ, riemannZeta (1 + I * t) = 0 →
    Tendsto (zeta341Product t) (𝓝[>] (1 : ℝ)) (𝓝 0)

/-- Under the named VDP boundary-limit input, `ζ(1+it)` has no zeros. -/
theorem no_zeta_zero_on_one_add_I_mul_of_vdp_limit
    (h : BoundaryZeroVDPLimit) (t : ℝ) : riemannZeta (1 + I * t) ≠ 0 := by
  intro hz
  exact zeta341Product_limit_zero_contradiction t (h t hz)

/-- Under the named VDP boundary-limit input, `ζ` has no zeros on the vertical
line `Re s = 1`. This is the VDP-specific conditional version of the boundary
zero-free theorem. -/
theorem no_zeta_zero_on_re_eq_one_of_vdp_limit
    (h : BoundaryZeroVDPLimit) {s : ℂ} (hs : s.re = 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hs_eq : s = 1 + I * s.im := by
    apply Complex.ext
    · simp [hs]
    · simp
  rw [hs_eq] at hz
  exact zeta341Product_limit_zero_contradiction s.im (h s.im hz)

/-! ### Boundary target audit -/

/-- Mathlib already proves the whole boundary half-plane nonvanishing
`riemannZeta_ne_zero_of_one_le_re`. Therefore the named VDP boundary-limit input
is true vacuously in the active formalization: the antecedent `ζ(1+it)=0` is
impossible.

This theorem is deliberately labeled as an audit result. It closes the boundary
line target, but it does **not** provide a method for pushing the zero-free
region into `1/2 < Re s < 1`. -/
theorem boundaryZeroVDPLimit_of_mathlib_nonvanishing : BoundaryZeroVDPLimit := by
  intro t hz
  have hne : riemannZeta (1 + I * t) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simp
  exact False.elim (hne hz)

/-- Direct audit form: Mathlib's boundary nonvanishing rules out every zero on
the vertical line `Re s = 1`. -/
theorem no_zeta_zero_on_re_eq_one_mathlib {s : ℂ} (hs : s.re = 1) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by linarith)

end Reinmann

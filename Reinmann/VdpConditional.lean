/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RiemannSpine
import Reinmann.ZeroFreeEngine
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

open Filter Topology

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

end Reinmann

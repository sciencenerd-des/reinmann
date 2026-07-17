/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.JensenProgram
import Reinmann.XiPlanePrincipalValue

/-!
# Limits of hyperbolic polynomials of bounded degree

The first proved leg of the Laguerre–Pólya closure bridge
(`XiLaguerrePolyaClosureBridge`).

## Main result

`polynomialHyperbolic_of_tendsto`: a pointwise limit of hyperbolic (real-rooted)
real polynomials of uniformly bounded degree is hyperbolic, unless it vanishes
identically.  This is the finite-dimensional Hurwitz-type statement that the
closure bridge consumes once the analytic legs supply hyperbolic bounded-degree
approximants to each Jensen polynomial of `Ξ`.

The proof is elementary — no complex analysis.  For a real-rooted polynomial
`p` and two points `z₁, z₂` on the same horizontal line `im = y ≠ 0`, each root
factor obeys

`‖z₂ - r‖² ≤ (2 + 2(re z₂ - re z₁)²/y²) · ‖z₁ - r‖²`,

so `‖p(z₂)‖² ≤ K^deg · ‖p(z₁)‖²`.  If the limit polynomial vanished at a
non-real `z₁`, the approximants would tend to zero along the whole horizontal
line through `z₁`, forcing the limit to vanish on an infinite set.

## Bridge decomposition

`xiLaguerrePolyaClosureBridge_of_jensenApproximation` reduces the closure
bridge to the named analytic condition `XiJensenApproximationBridge`: from the
scaled finite real-rooted approximants of `Ξ`, produce, for each degree and
shift, hyperbolic approximants of bounded degree converging to that Jensen
polynomial, which must also be nonzero.  The finite-degree algebraic part of
Cauchy coefficient convergence is proved in
`CauchyCoefficientConvergence`: Lagrange interpolation on `D + 1` real nodes
turns nodewise evaluation limits into coefficient limits.  The remaining
analytic work is supplying those nodewise limits from the chosen locally
uniform approximants, together with the Hermite–Poulain/Schur fact that Jensen
polynomials of real-rooted polynomials are real-rooted.  The exact coefficientwise
composition convention and its identification with `JensenPoly` are fixed in
`HermitePoulainComposition`; the general hyperbolicity-preservation proposition
there remains the open composition theorem.
RH is not proved here; this closes one of the three legs of one of the four
scaffolding bridges.
-/

noncomputable section

open Polynomial Filter Complex

namespace Reinmann

/-! ## The horizontal-line estimate -/

/-- Per-line product estimate for real-rooted factor collections: along a
horizontal line `im = y ≠ 0`, the squared modulus of the root-factor product
at one point controls it at every other point, at multiplicative cost
`K^(number of roots)` with `K = 2 + 2(Δre)²/y²`. -/
theorem prod_normSq_line_le (roots : Multiset ℂ) (hreal : ∀ r ∈ roots, r.im = 0)
    (z₁ z₂ : ℂ) (him : z₁.im = z₂.im) (hy : z₁.im ≠ 0) :
    (roots.map (fun r => Complex.normSq (z₂ - r))).prod ≤
      (2 + 2 * (z₂.re - z₁.re) ^ 2 / z₁.im ^ 2) ^ (Multiset.card roots) *
        (roots.map (fun r => Complex.normSq (z₁ - r))).prod := by
  set K : ℝ := 2 + 2 * (z₂.re - z₁.re) ^ 2 / z₁.im ^ 2 with hKdef
  have hy2 : 0 < z₁.im ^ 2 := by positivity
  have hK : K * z₁.im ^ 2 = 2 * z₁.im ^ 2 + 2 * (z₂.re - z₁.re) ^ 2 := by
    rw [hKdef]
    field_simp
  have hK2 : 2 ≤ K := by nlinarith [sq_nonneg (z₂.re - z₁.re)]
  have hfac : ∀ r : ℂ, r.im = 0 →
      Complex.normSq (z₂ - r) ≤ K * Complex.normSq (z₁ - r) := by
    intro r hr
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, hr, sub_zero, ← him]
    nlinarith [sq_nonneg ((z₂.re - z₁.re) - (z₁.re - r.re)),
      sq_nonneg (z₁.re - r.re), sq_nonneg (z₂.re - z₁.re)]
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      have hr : r.im = 0 := hreal r (Multiset.mem_cons_self r s)
      have hs : ∀ x ∈ s, x.im = 0 := fun x hx => hreal x (Multiset.mem_cons_of_mem hx)
      have hihs := ih hs
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      have hprod_nonneg : 0 ≤ (s.map (fun x => Complex.normSq (z₂ - x))).prod := by
        apply Multiset.prod_nonneg
        intro a ha
        rcases Multiset.mem_map.mp ha with ⟨x, _, rfl⟩
        exact Complex.normSq_nonneg _
      have hKg_nonneg : 0 ≤ K * Complex.normSq (z₁ - r) := by
        have := Complex.normSq_nonneg (z₁ - r)
        nlinarith
      calc Complex.normSq (z₂ - r) * (s.map (fun x => Complex.normSq (z₂ - x))).prod
          ≤ (K * Complex.normSq (z₁ - r)) *
              (K ^ (Multiset.card s) *
                (s.map (fun x => Complex.normSq (z₁ - x))).prod) :=
            mul_le_mul (hfac r hr) hihs hprod_nonneg hKg_nonneg
        _ = K ^ (Multiset.card s + 1) *
              (Complex.normSq (z₁ - r) *
                (s.map (fun x => Complex.normSq (z₁ - x))).prod) := by
            ring

/-! ## The bounded-degree hyperbolic limit theorem -/

/-- **Limits of hyperbolic polynomials.**  If real polynomials of degree at most
`D`, all hyperbolic, converge pointwise on `ℂ` to a nonzero polynomial, the
limit is hyperbolic.  Elementary finite-dimensional Hurwitz-type statement. -/
theorem polynomialHyperbolic_of_tendsto
    {D : ℕ} (p : ℕ → Polynomial ℝ) (f : Polynomial ℝ)
    (hdeg : ∀ j, (p j).natDegree ≤ D)
    (hhyp : ∀ j, PolynomialHyperbolic (p j))
    (hconv : ∀ z : ℂ,
      Tendsto (fun j => Polynomial.eval z ((p j).map (algebraMap ℝ ℂ))) atTop
        (nhds (Polynomial.eval z (f.map (algebraMap ℝ ℂ)))))
    (hf : f ≠ 0) :
    PolynomialHyperbolic f := by
  intro z hz
  by_contra him
  -- Every point on the horizontal line through `z` is a root of `f`.
  have hline : ∀ u : ℝ, Polynomial.eval (⟨u, z.im⟩ : ℂ) (f.map (algebraMap ℝ ℂ)) = 0 := by
    intro u
    set z₂ : ℂ := ⟨u, z.im⟩ with hz₂
    have him₂ : z.im = z₂.im := rfl
    set K : ℝ := 2 + 2 * (z₂.re - z.re) ^ 2 / z.im ^ 2 with hKdef
    have hy2 : 0 < z.im ^ 2 := by positivity
    have hK2 : 2 ≤ K := by
      have h0 : 0 ≤ 2 * (z₂.re - z.re) ^ 2 / z.im ^ 2 := by positivity
      linarith
    have hK1 : 1 ≤ K := by linarith
    -- uniform bound: ‖p_j(z₂)‖² ≤ K^D ‖p_j(z)‖²
    have hbound : ∀ j : ℕ,
        Complex.normSq (Polynomial.eval z₂ ((p j).map (algebraMap ℝ ℂ))) ≤
          K ^ D * Complex.normSq (Polynomial.eval z ((p j).map (algebraMap ℝ ℂ))) := by
      intro j
      set pC : Polynomial ℂ := (p j).map (algebraMap ℝ ℂ) with hpC
      have hsplit : pC.Splits := IsAlgClosed.splits pC
      have hfact := hsplit.eq_prod_roots
      have hreal : ∀ r ∈ pC.roots, r.im = 0 := by
        intro r hr
        have hroot := (Polynomial.mem_roots'.mp hr).2
        exact hhyp j r hroot
      have hcard : Multiset.card pC.roots ≤ D :=
        le_trans (Polynomial.card_roots' pC)
          (le_trans (Polynomial.natDegree_map_le) (hdeg j))
      have heval : ∀ w : ℂ, Complex.normSq (Polynomial.eval w pC) =
          Complex.normSq pC.leadingCoeff *
            (pC.roots.map (fun r => Complex.normSq (w - r))).prod := by
        intro w
        conv_lhs => rw [hfact]
        rw [Polynomial.eval_mul, Polynomial.eval_C, map_mul]
        congr 1
        rw [Polynomial.eval_multiset_prod, Multiset.map_map,
          map_multiset_prod Complex.normSq, Multiset.map_map]
        congr 1
        apply Multiset.map_congr rfl
        intro r _
        simp
      have hprod := prod_normSq_line_le pC.roots hreal z z₂ him₂ him
      have hKpow : K ^ (Multiset.card pC.roots) ≤ K ^ D :=
        pow_le_pow_right₀ hK1 hcard
      have hprodP_nonneg :
          0 ≤ (pC.roots.map (fun r => Complex.normSq (z - r))).prod := by
        apply Multiset.prod_nonneg
        intro a ha
        rcases Multiset.mem_map.mp ha with ⟨x, _, rfl⟩
        exact Complex.normSq_nonneg _
      have hlead := Complex.normSq_nonneg pC.leadingCoeff
      rw [heval z₂, heval z]
      calc Complex.normSq pC.leadingCoeff *
              (pC.roots.map (fun r => Complex.normSq (z₂ - r))).prod
          ≤ Complex.normSq pC.leadingCoeff *
              (K ^ (Multiset.card pC.roots) *
                (pC.roots.map (fun r => Complex.normSq (z - r))).prod) :=
            mul_le_mul_of_nonneg_left hprod hlead
        _ ≤ Complex.normSq pC.leadingCoeff *
              (K ^ D * (pC.roots.map (fun r => Complex.normSq (z - r))).prod) := by
            apply mul_le_mul_of_nonneg_left _ hlead
            exact mul_le_mul_of_nonneg_right hKpow hprodP_nonneg
        _ = K ^ D * (Complex.normSq pC.leadingCoeff *
              (pC.roots.map (fun r => Complex.normSq (z - r))).prod) := by ring
    -- pass to the limit
    have h₀ : Tendsto
        (fun j => Complex.normSq (Polynomial.eval z ((p j).map (algebraMap ℝ ℂ))))
        atTop (nhds 0) := by
      have := (Complex.continuous_normSq.tendsto _).comp (hconv z)
      rwa [hz, map_zero] at this
    have h₂ : Tendsto
        (fun j => Complex.normSq (Polynomial.eval z₂ ((p j).map (algebraMap ℝ ℂ))))
        atTop (nhds (Complex.normSq (Polynomial.eval z₂ (f.map (algebraMap ℝ ℂ))))) :=
      (Complex.continuous_normSq.tendsto _).comp (hconv z₂)
    have hKD : Tendsto
        (fun j => K ^ D *
          Complex.normSq (Polynomial.eval z ((p j).map (algebraMap ℝ ℂ))))
        atTop (nhds (K ^ D * 0)) := h₀.const_mul _
    have hle : Complex.normSq (Polynomial.eval z₂ (f.map (algebraMap ℝ ℂ))) ≤ K ^ D * 0 :=
      le_of_tendsto_of_tendsto' h₂ hKD hbound
    have : Complex.normSq (Polynomial.eval z₂ (f.map (algebraMap ℝ ℂ))) = 0 := by
      have := Complex.normSq_nonneg (Polynomial.eval z₂ (f.map (algebraMap ℝ ℂ)))
      linarith
    exact Complex.normSq_eq_zero.mp this
  -- infinitely many roots force `f = 0`
  have hfC : f.map (algebraMap ℝ ℂ) ≠ 0 := by
    intro h0
    exact hf (Polynomial.map_injective _ (algebraMap ℝ ℂ).injective (by simpa using h0))
  have hinj : Function.Injective (fun u : ℝ => (⟨u, z.im⟩ : ℂ)) := by
    intro u v huv
    exact congrArg Complex.re huv
  have hsub : Set.range (fun u : ℝ => (⟨u, z.im⟩ : ℂ)) ⊆
      {w | Polynomial.IsRoot (f.map (algebraMap ℝ ℂ)) w} := by
    rintro w ⟨u, rfl⟩
    exact hline u
  have hinf : Set.Infinite {w | Polynomial.IsRoot (f.map (algebraMap ℝ ℂ)) w} :=
    Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)
  exact hfC (Polynomial.eq_zero_of_infinite_isRoot _ hinf)

/-! ## Decomposition of the Laguerre–Pólya closure bridge -/

/-- **The remaining analytic legs of the closure bridge, named.**  From the
scaled finite real-rooted approximants of `Ξ`, produce, for each degree `d`
and shift `n`, hyperbolic real polynomials of degree at most `d` converging
pointwise (over `ℂ`) to the Jensen polynomial `J_{d,n}` of `Ξ`, which must in
particular be nonzero.

Classical content: (i) locally uniform convergence upgrades pointwise
convergence of the approximants to convergence of their Taylor coefficients
(Cauchy estimates); (ii) Jensen polynomials of real-rooted polynomials are
real-rooted (Hermite–Poulain/Schur composition theorems); (iii) nonvanishing
of the limit Jensen polynomials (positivity of the `Ξ` moments).  None of this
is RH-strength. -/
def XiJensenApproximationBridge : Prop :=
  XiLaguerrePolyaScaledFiniteTarget →
    ∀ d n : ℕ, JensenPoly d n ≠ 0 ∧
      ∃ q : ℕ → Polynomial ℝ,
        (∀ j, (q j).natDegree ≤ d) ∧
        (∀ j, PolynomialHyperbolic (q j)) ∧
        (∀ z : ℂ,
          Tendsto (fun j => Polynomial.eval z ((q j).map (algebraMap ℝ ℂ))) atTop
            (nhds (Polynomial.eval z ((JensenPoly d n).map (algebraMap ℝ ℂ)))))

/-- **The closure bridge, reduced.**  Given the Jensen approximation legs, the
Laguerre–Pólya closure bridge follows from the proved bounded-degree
hyperbolic-limit theorem.  One of the four scaffolding bridges is thereby
reduced to sharper classical conditions. -/
theorem xiLaguerrePolyaClosureBridge_of_jensenApproximation
    (h : XiJensenApproximationBridge) : XiLaguerrePolyaClosureBridge := by
  intro hfinite d n
  obtain ⟨hne, q, hdeg, hhyp, hconv⟩ := h hfinite d n
  exact polynomialHyperbolic_of_tendsto q (JensenPoly d n) hdeg hhyp hconv hne

end Reinmann

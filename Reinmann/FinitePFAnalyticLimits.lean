/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FinitePFLimits
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Analytic limits of finite Pólya-frequency sequences

Locally uniform convergence of holomorphic functions gives convergence of their
ordinary Taylor coefficients, including the factorial normalization. Together
with finite-PF closure this supplies the analytic limit step of the polynomial
sector route. Neither the polynomial sector theorem nor folded Xi's canonical
product is assumed to have been proved here.
-/
noncomputable section
namespace Reinmann.FinitePFAnalyticLimits
open Filter
open scoped Topology

private theorem differentiableOn_iteratedDeriv {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

/-- Holomorphic locally uniform limits commute with every iterated derivative.
Only eventual holomorphy of the approximating family is required. -/
theorem iteratedDeriv_locallyUniformly {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ t in l, DifferentiableOn ℂ (F t) U) (hU : IsOpen U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun t => iteratedDeriv n (F t))
      (iteratedDeriv n f) l U := by
  induction n with
  | zero => simpa using hlim
  | succ n ih =>
    have hFn : ∀ᶠ t in l, DifferentiableOn ℂ (iteratedDeriv n (F t)) U :=
      hF.mono (fun t ht => differentiableOn_iteratedDeriv ht hU n)
    simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv hFn hU

/-- Ordinary Taylor coefficients, rather than Jensen coefficients, converge at
every centre in the open domain. -/
theorem ordinaryCoeff_tendsto {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ t in l, DifferentiableOn ℂ (F t) U) (hU : IsOpen U)
    (hc : c ∈ U) (n : ℕ) :
    Tendsto (fun t => iteratedDeriv n (F t) c / (n.factorial : ℂ)) l
      (𝓝 (iteratedDeriv n f c / (n.factorial : ℂ))) :=
  ((iteratedDeriv_locallyUniformly hlim hF hU n).tendsto_at hc).div_const _

/-- Finite PF passes to the real parts of the ordinary coefficients of an
analytic limit. Real-valuedness of the complex coefficients is not inferred
from this statement; applications identify the resulting real sequence. -/
theorem finitePF_of_locallyUniformly {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℕ}
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ t in l, DifferentiableOn ℂ (F t) U) (hU : IsOpen U) (hc : c ∈ U)
    (hpf : ∀ᶠ t in l, FinitePF
      (fun n => (iteratedDeriv n (F t) c / (n.factorial : ℂ)).re) r) :
    FinitePF (fun n => (iteratedDeriv n f c / (n.factorial : ℂ)).re) r := by
  apply finitePF_of_tendsto (hpf := hpf)
  intro n
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (ordinaryCoeff_tendsto hlim hF hU hc n)

private theorem iteratedDeriv_polynomial (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) =
      fun z => (Polynomial.derivative^[n] p).eval z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    simp only [Polynomial.deriv, Function.iterate_succ_apply']

/-- The analytic ordinary coefficients at zero are exactly the polynomial
coefficients, including above the polynomial's degree. -/
theorem polynomial_ordinaryCoeff (p : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => p.eval z) 0 / (n.factorial : ℂ) = p.coeff n := by
  rw [iteratedDeriv_polynomial]
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)

/-- Real polynomial coefficients inherit finite PF in an analytic limit.
The approximants are genuine real polynomials, evaluated over the complex
numbers, so no separate Taylor-coefficient identity is an application premise. -/
theorem finitePF_of_polynomial_locallyUniformly {ι : Type*} {l : Filter ι} [l.NeBot]
    {p : ι → Polynomial ℝ} {f : ℂ → ℂ} {U : Set ℂ} {r : ℕ}
    (hlim : TendstoLocallyUniformlyOn
      (fun t z => ((p t).map (algebraMap ℝ ℂ)).eval z) f l U)
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hpf : ∀ᶠ t in l, FinitePF (fun n => (p t).coeff n) r) :
    FinitePF (fun n => (iteratedDeriv n f 0 / (n.factorial : ℂ)).re) r := by
  have hp : ∀ᶠ t in l, DifferentiableOn ℂ
      (fun z => ((p t).map (algebraMap ℝ ℂ)).eval z) U :=
    Filter.Eventually.of_forall (fun t =>
      ((p t).map (algebraMap ℝ ℂ)).differentiable.differentiableOn)
  apply finitePF_of_locallyUniformly hlim hp hU h0
  simpa only [polynomial_ordinaryCoeff, Polynomial.coeff_map,
    RCLike.algebraMap_eq_ofReal, Complex.ofReal_re] using hpf

end Reinmann.FinitePFAnalyticLimits

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzFullPF
import Reinmann.HermitePoulainComposition
import Reinmann.Order3Certificate

/-!
# Effective assembly: where new mathematics plugs into the RH reduction

This module contains conditional assembly theorems. Its legacy certificate
names do not themselves encode computability or an explicit error estimate.
Additional analytic and certificate-checking work remains at those boundaries.

## Ladder route (logical prefix/tail split)

`KernelEffectiveCertificates M` is equivalent to `KernelLadderStrict M`, as
proved below: choosing cutoff zero makes the prefix empty. It records no
computable cutoff or remainder bound. The end-to-end implication remains a
valid conditional theorem, not an independent positivity mechanism.

The strict transfer `xiToeplitzContigMinor_pos_iff_moment_of_kernelRep`
(from the `2^k`-scaling identity) moves kernel-side certificates to the
coefficient-side strict ladder consumed by the Fekete/PF machinery of
`Reinmann/ToeplitzFullPF.lean`.  This is the **all-order positivity
propagation**: order-local certificates propagate to full PF positivity and
hence, with the classical scaffolding, to RH.  Compatibility with the order-3
program is `order3TailGap_of_kernelTailStrict`.

## Jensen route (Schur–Szegő receptor)

The HPSS per-window hypothesis already contains legacy Jensen hyperbolicity.
Its retained RH implication requires `DiagnosticJensenRHBridge`, not the
classical factorial-normalized Pólya--Jensen theorem. The primary classical
route uses `ClassicalJensenPoly` through `JensenUniformHyperbolicityWitness`.
All statements remain conditional and no custom axioms are introduced.
-/

noncomputable section

open Polynomial

namespace Reinmann

/-! ## Strict kernel-to-coefficient transfer -/

/-- Strict form of the `2^k`-scaling transfer: kernel-side and
coefficient-side contiguous minors are simultaneously strictly positive. -/
theorem xiToeplitzContigMinor_pos_iff_moment_of_kernelRep {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (k m : ℕ) :
    0 < XiToeplitzContigMinor k m ↔ 0 < momentToeplitzContigMinor M k m := by
  rw [xiToeplitzContigMinor_eq_of_kernelRep hM]
  exact mul_pos_iff_of_pos_left (by positivity)

/-! ## Per-order effective certificates and the all-order propagation -/

/-- Kernel-side strict contiguous ladder: every factorial-weighted moment
Toeplitz minor is strictly positive. -/
def KernelLadderStrict (M : ℕ → ℝ) : Prop :=
  ∀ k m : ℕ, 0 < momentToeplitzContigMinor M k m

/-- Certified strict prefix at order `k` up to cutoff `N`.  For rational
moment enclosures this is dischargeable by `norm_num`, offset by offset. -/
def KernelMinorPrefixStrict (M : ℕ → ℝ) (k N : ℕ) : Prop :=
  ∀ m : ℕ, m < N → 0 < momentToeplitzContigMinor M k m

/-- Strict tail proposition at order `k` beyond cutoff `N`.
It does not encode a quantitative remainder bound. -/
def KernelMinorTailStrict (M : ℕ → ℝ) (k N : ℕ) : Prop :=
  ∀ m : ℕ, N ≤ m → 0 < momentToeplitzContigMinor M k m

/-- Legacy name for a purely logical prefix/tail split, equivalent to the
strict ladder. No computable cutoff or quantitative bound is encoded. -/
def KernelEffectiveCertificates (M : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, KernelMinorPrefixStrict M k N ∧ KernelMinorTailStrict M k N

/-- Prefix and tail assemble each rung; all rungs assemble the strict
kernel ladder. -/
theorem kernelLadderStrict_of_certificates {M : ℕ → ℝ}
    (h : KernelEffectiveCertificates M) : KernelLadderStrict M := by
  intro k m
  obtain ⟨N, hpre, htail⟩ := h k
  rcases lt_or_ge m N with hm | hm
  · exact hpre m hm
  · exact htail m hm

/-- Choosing cutoff zero proves that the legacy certificate predicate carries
exactly the strict-ladder obligation, with no additional effectiveness. -/
theorem kernelEffectiveCertificates_iff_ladder (M : ℕ → ℝ) :
    KernelEffectiveCertificates M ↔ KernelLadderStrict M := by
  constructor
  · exact kernelLadderStrict_of_certificates
  · intro h k
    refine ⟨0, ?_, ?_⟩
    · intro m hm
      omega
    · intro m _
      exact h k m

/-- **All-order propagation.**  The kernel-side strict ladder transfers to the
coefficient-side strict ladder — the single positivity input of the
Fekete/full-PF machinery. -/
theorem xiContigToeplitzStrictPositive_of_kernelLadder {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (h : KernelLadderStrict M) : XiContigToeplitzStrictPositive :=
  fun k m => (xiToeplitzContigMinor_pos_iff_moment_of_kernelRep hM k m).mpr (h k m)

/-- Conditional RH reduction from scaffolding, kernel representation and the
strict ladder expressed as a prefix/tail split. No effective bound is proved. -/
theorem riemannHypothesis_of_effectiveCertificates
    (S : ClassicalToeplitzScaffolding)
    (M : ℕ → ℝ)
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (h : KernelEffectiveCertificates M) :
    RiemannHypothesis :=
  riemannHypothesis_of_strictLadder S
    (xiContigToeplitzStrictPositive_of_kernelLadder hM
      (kernelLadderStrict_of_certificates h))

/-- Compatibility: a strict order-3 tail certificate supplies the earlier
nonnegative order-3 tail gap of the kernel program. -/
theorem order3TailGap_of_kernelTailStrict {M : ℕ → ℝ} {N : ℕ}
    (h : KernelMinorTailStrict M 3 (N + 2)) : Order3TailGap M N :=
  fun n hn => le_of_lt (h (n + 2) (by omega))

/-! ## The Schur–Szegő receptor for the Jensen route -/

/-- The Jensen factor `(1 + X)^d` has degree `d`. -/
theorem one_add_X_pow_natDegree (d : ℕ) :
    ((1 + X : ℝ[X]) ^ d).natDegree = d := by
  have h1 : (1 + X : ℝ[X]) = X + C 1 := by
    rw [Polynomial.C_1]
    ring
  rw [Polynomial.natDegree_pow, h1, Polynomial.natDegree_X_add_C, mul_one]

/-- The Jensen factor `(1 + X)^d` is hyperbolic: its only complex root is
`-1`. -/
theorem polynomialHyperbolic_one_add_X_pow (d : ℕ) :
    PolynomialHyperbolic ((1 + X : ℝ[X]) ^ d) := by
  intro z hz
  rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] at hz
  rcases Nat.eq_zero_or_pos d with hd | hd
  · rw [hd, pow_zero] at hz
    exact absurd hz one_ne_zero
  · have hz1 : (1 : ℂ) + z = 0 := (pow_eq_zero_iff (by omega : d ≠ 0)).mp hz
    have := congrArg Complex.im hz1
    simpa using this

/-- **The Schur–Szegő receptor.**  Once the general same-sign composition
theorem is proved, each Jensen polynomial whose coefficient window is
hyperbolic of full degree is itself hyperbolic.  The Jensen-factor side
conditions are discharged here once and for all. -/
theorem jensenPoly_hyperbolic_of_hpss
    (hHPSS : HermitePoulainSchurSzegoTheorem) (d n : ℕ)
    (hdeg : (jensenCoeffPoly d n).natDegree = d)
    (hcoeff : PolynomialHyperbolic (jensenCoeffPoly d n)) :
    PolynomialHyperbolic (JensenPoly d n) := by
  rw [JensenPoly_eq_schurSzego_one_add_X_pow]
  exact hHPSS d (jensenCoeffPoly d n) ((1 + X) ^ d) hdeg
    (one_add_X_pow_natDegree d) hcoeff
    (polynomialHyperbolic_one_add_X_pow d)
    (polynomialRootsSameSign_one_add_X_pow d)

/-- The per-window analytic input of the Jensen route: every coefficient
window polynomial of the xi sequence is hyperbolic of full degree.  This is
a stronger form of the legacy output itself, since `jensenCoeffPoly` is
definitionally `JensenPoly`. It is not an independent mechanism for proving it. -/
def XiJensenCoeffHyperbolic : Prop :=
  ∀ d n : ℕ, (jensenCoeffPoly d n).natDegree = d ∧
    PolynomialHyperbolic (jensenCoeffPoly d n)

/-- The HPSS payload already contains the requested legacy hyperbolicity.
Composition with `(1+X)^d` supplies no additional real-rootedness. -/
theorem allJensenHyperbolic_of_coeffHyperbolic
    (hcoeff : XiJensenCoeffHyperbolic) : AllJensenHyperbolic := by
  intro d n
  exact (hcoeff d n).2

/-- The general composition theorem plus the per-window input yield the full
Jensen hyperbolicity target. -/
theorem allJensenHyperbolic_of_hpss
    (hHPSS : HermitePoulainSchurSzegoTheorem)
    (hcoeff : XiJensenCoeffHyperbolic) : AllJensenHyperbolic := by
  intro d n
  obtain ⟨hdeg, hhyp⟩ := hcoeff d n
  exact jensenPoly_hyperbolic_of_hpss hHPSS d n hdeg hhyp

/-- Legacy diagnostic conditional reduction only. Its unestablished
`DiagnosticJensenRHBridge` is not the classical Pólya--Jensen theorem, and the
per-window input already contains the output. Retained for compatibility. -/
theorem riemannHypothesis_of_hpss_route
    (hPJ : DiagnosticJensenRHBridge)
    (hHPSS : HermitePoulainSchurSzegoTheorem)
    (hcoeff : XiJensenCoeffHyperbolic) :
    RiemannHypothesis :=
  hPJ.mpr (allJensenHyperbolic_of_hpss hHPSS hcoeff)

end Reinmann

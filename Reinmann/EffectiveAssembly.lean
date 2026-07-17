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

This module is the *receptor architecture* for the remaining open mathematics.
It proves the glue theorems so that each future ingredient — an explicit
remainder bound, a certified prefix, the general Schur–Szegő composition
theorem — plugs into the machine-checked reduction with **no further Lean work
at the interfaces**.

## Ladder route (per-order effective certificates)

`KernelEffectiveCertificates M` asks, for each order `k`, for a cutoff `N`
with a strict certified prefix (`KernelMinorPrefixStrict`, dischargeable by
`norm_num` on rational moment enclosures) and a strict analytic tail
(`KernelMinorTailStrict`, the *explicit remainder bound* target).  The
assembly proves:

`riemannHypothesis_of_effectiveCertificates`:
scaffolding + kernel representation + per-order certificates ⟹ RH.

The strict transfer `xiToeplitzContigMinor_pos_iff_moment_of_kernelRep`
(from the `2^k`-scaling identity) moves kernel-side certificates to the
coefficient-side strict ladder consumed by the Fekete/PF machinery of
`Reinmann/ToeplitzFullPF.lean`.  This is the **all-order positivity
propagation**: order-local certificates propagate to full PF positivity and
hence, with the classical scaffolding, to RH.  Compatibility with the order-3
program is `order3TailGap_of_kernelTailStrict`.

## Jensen route (Schur–Szegő receptor)

`jensenPoly_hyperbolic_of_hpss` instantiates the named general same-sign
Schur–Szegő target `HermitePoulainSchurSzegoTheorem` at the Jensen factor
`(1 + X)^d` — whose degree, hyperbolicity, and same-sign root location are
proved here — so that the general composition theorem, once proved, converts
per-window coefficient data (`XiJensenCoeffHyperbolic`) into
`AllJensenHyperbolic`, and with the Pólya–Jensen bridge into RH
(`riemannHypothesis_of_hpss_route`).

Every hypothesis below is a named `Prop`, never an axiom.  RH remains
unproved; this module guarantees that the day any input is proved — here or
in a future Mathlib — the reduction closes by `exact`.
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

/-- Strict analytic tail at order `k` beyond cutoff `N`: the **explicit
remainder bound** target.  This is what an effective-asymptotics theorem for
the xi moments must supply, one order at a time. -/
def KernelMinorTailStrict (M : ℕ → ℝ) (k N : ℕ) : Prop :=
  ∀ m : ℕ, N ≤ m → 0 < momentToeplitzContigMinor M k m

/-- The complete effective input: for every order, some cutoff splits the
ladder rung into a certified prefix and a bounded tail. -/
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

/-- **All-order propagation.**  The kernel-side strict ladder transfers to the
coefficient-side strict ladder — the single positivity input of the
Fekete/full-PF machinery. -/
theorem xiContigToeplitzStrictPositive_of_kernelLadder {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (h : KernelLadderStrict M) : XiContigToeplitzStrictPositive :=
  fun k m => (xiToeplitzContigMinor_pos_iff_moment_of_kernelRep hM k m).mpr (h k m)

/-- **The effective end-to-end reduction.**  RH follows from: the classical
scaffolding, Pólya's kernel representation data, and per-order effective
certificates (certified prefix + explicit remainder bound at every order).
Still conditional — the certificates are the open mathematics — but every
interface is now a proved theorem. -/
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
where xi-specific analysis (moment positivity, window real-rootedness) must
enter; it is not RH-strength by itself. -/
def XiJensenCoeffHyperbolic : Prop :=
  ∀ d n : ℕ, (jensenCoeffPoly d n).natDegree = d ∧
    PolynomialHyperbolic (jensenCoeffPoly d n)

/-- The general composition theorem plus the per-window input yield the full
Jensen hyperbolicity target. -/
theorem allJensenHyperbolic_of_hpss
    (hHPSS : HermitePoulainSchurSzegoTheorem)
    (hcoeff : XiJensenCoeffHyperbolic) : AllJensenHyperbolic := by
  intro d n
  obtain ⟨hdeg, hhyp⟩ := hcoeff d n
  exact jensenPoly_hyperbolic_of_hpss hHPSS d n hdeg hhyp

/-- **The Jensen-route end-to-end reduction.**  RH follows from: the
Pólya–Jensen bridge, the general same-sign Schur–Szegő theorem, and the
per-window hyperbolicity input.  Conditional, with every interface proved. -/
theorem riemannHypothesis_of_hpss_route
    (hPJ : PolyaJensenBridge)
    (hHPSS : HermitePoulainSchurSzegoTheorem)
    (hcoeff : XiJensenCoeffHyperbolic) :
    RiemannHypothesis :=
  hPJ.mpr (allJensenHyperbolic_of_hpss hHPSS hcoeff)

end Reinmann

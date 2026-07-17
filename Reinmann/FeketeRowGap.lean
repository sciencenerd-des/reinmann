/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.RHTheoremTargets
import Reinmann.InitialColumnThree

/-!
# Arbitrary row-gap positivity via Fekete's gap-shrinking induction

This module attacks the arbitrary-row initial-column frontier — the named open
targets `XiInitialColumnMinorThreeFromContig` and the first `k = 4` rung of
`XiInitialColumnMinorGeFourFromContig` — with the classical Fekete gap-shrinking
induction (Fekete 1912; Gantmacher–Krein, *Oscillation Matrices*, Ch. II).

## The engine

For four rows `w₀, w₁, w₂, w₃` of a matrix with three columns, the four maximal
`3 × 3` minors `Mᵢ` (delete row `i`) satisfy the Grassmann syzygy
`M₀w₀ - M₁w₁ + M₂w₂ - M₃w₃ = 0`.  Pairing the syzygy with one of the rows and a
column pair yields exact *three-term identities* between minors.  Inserting an
auxiliary row `s` inside a row gap and choosing the identity whose two
right-hand minors both omit an extreme row shrinks the row dispersion by at
least one.  Induction on the dispersion then reduces every arbitrary-row
initial-column minor to the contiguous ladder.

The division step consumes one strictness input that the nonnegative contiguous
ladder cannot supply: **strict** Turán/log-concavity of the signed xi moment
coefficients (`XiMomentStrictTuran`).  For the Riemann xi coefficients this is
the classical Csordas–Norfolk–Varga strict Turán theorem (1986) — a proved
classical result, **not** RH-strength — kept as a named hypothesis exactly like
`XiMomentKernelRep`.

## Main results

* `xiInitialColumnMinorThreeFromContig_of_strictTuran` — the previously open
  order-`3` arbitrary-row initial-column target holds, given strict positivity
  and strict Turán.  This closes `XiInitialColumnMinorThreeFromContig` modulo
  one classical strictness input.
* `xiInitialMinor3_pos` — the strict variant, from the strict order-`3`
  contiguous rung; this is exactly the divisor the `k = 4` step consumes.
* `xiInitialColumnMinorFourFromContig_of_strictTuran` — the `k = 4` rung of
  the arbitrary-row program, from strict Turán plus the strict order-`3`
  contiguous rung.
* `xiInitialColumnMinorGeFourFromContig_of_four_and_geFive` — splits the
  remaining tail: only `k ≥ 5` is left open.
* `kernelContigToPFInitialColumnGeFourTheorem_of_strictTuran_and_geFive` —
  rebuilds the capstone input with the order-`3` and order-`4` fields
  discharged, shrinking its open surface to `k ≥ 5` + Cryer's criterion +
  the contiguous ladder itself.

## What this does *not* do

RH remains unproved.  Open named inputs after this module: the contiguous
ladder (`XiContigToeplitzTotalPositive`, RH-adjacent), its strict order-`3`
and order-`4` contiguous rungs, strict Turán (classical, unformalized), the
`k ≥ 5` arbitrary-row tail, Cryer's initial-column criterion, and Pólya's
kernel representation (classical, unformalized).  The `k ≥ 5` tail should
follow by iterating the same induction once a generic (all-`k`) Grassmann
syzygy is formalized; each order `k` consumes the strict order-`(k-1)`
arbitrary-row result as its divisor.
-/

noncomputable section

open Matrix

namespace Reinmann

/-! ## Scalar forms of the initial-column minors -/

/-- Scalar form of the arbitrary-row initial-column `2 × 2` Toeplitz minor with
columns `0, 1`. -/
def XiInitialMinor2 (x y : ℕ) : ℝ :=
  XiToeplitzEntry x 0 * XiToeplitzEntry y 1 - XiToeplitzEntry x 1 * XiToeplitzEntry y 0

/-- Scalar form of the arbitrary-row initial-column `3 × 3` Toeplitz minor with
columns `0, 1, 2`. -/
def XiInitialMinor3 (r0 r1 r2 : ℕ) : ℝ :=
  XiToeplitzEntry r0 0 *
      (XiToeplitzEntry r1 1 * XiToeplitzEntry r2 2 -
        XiToeplitzEntry r1 2 * XiToeplitzEntry r2 1) -
    XiToeplitzEntry r0 1 *
      (XiToeplitzEntry r1 0 * XiToeplitzEntry r2 2 -
        XiToeplitzEntry r1 2 * XiToeplitzEntry r2 0) +
    XiToeplitzEntry r0 2 *
      (XiToeplitzEntry r1 0 * XiToeplitzEntry r2 1 -
        XiToeplitzEntry r1 1 * XiToeplitzEntry r2 0)

/-- The scalar `3 × 3` form agrees with the determinant used by the named
initial-column targets. -/
theorem xiInitialMinor3_eq_det (rows : Fin 3 → ℕ) :
    (Matrix.of (fun i j : Fin 3 => XiToeplitzEntry (rows i) j.val)).det =
      XiInitialMinor3 (rows 0) (rows 1) (rows 2) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two]
  unfold XiInitialMinor3
  ring

/-- The contiguous specialization of the scalar `3 × 3` minor is the ladder
minor. -/
theorem xiInitialMinor3_contig (m : ℕ) :
    XiInitialMinor3 m (m + 1) (m + 2) = XiToeplitzContigMinor 3 m := by
  unfold XiToeplitzContigMinor
  rw [xiInitialMinor3_eq_det (fun i : Fin 3 => m + i.val)]
  simp

/-! ## The Grassmann–Plücker three-term identities

Pure polynomial identities: no monotonicity or support assumptions.  They are
the two components of the four-row syzygy needed to shrink a gap in the first
and in the second row slot respectively. -/

/-- Gap-shrinking identity, gap in the **first** slot.  For any indices
(read `r0 < s < r1 < r2` in the application):
`D(r0,r1,r2)·m(s,r1) = D(s,r1,r2)·m(r0,r1) + D(r0,s,r1)·m(r1,r2)`. -/
theorem xiInitialMinor3_gap_first (r0 s r1 r2 : ℕ) :
    XiInitialMinor3 r0 r1 r2 * XiInitialMinor2 s r1 =
      XiInitialMinor3 s r1 r2 * XiInitialMinor2 r0 r1 +
        XiInitialMinor3 r0 s r1 * XiInitialMinor2 r1 r2 := by
  unfold XiInitialMinor3 XiInitialMinor2
  ring

/-- Gap-shrinking identity, gap in the **second** slot.  For any indices
(read `r0 < r1 < s < r2` in the application):
`D(r0,r1,r2)·m(r1,s) = D(r1,s,r2)·m(r0,r1) + D(r0,r1,s)·m(r1,r2)`. -/
theorem xiInitialMinor3_gap_second (r0 r1 s r2 : ℕ) :
    XiInitialMinor3 r0 r1 r2 * XiInitialMinor2 r1 s =
      XiInitialMinor3 r1 s r2 * XiInitialMinor2 r0 r1 +
        XiInitialMinor3 r0 r1 s * XiInitialMinor2 r1 r2 := by
  unfold XiInitialMinor3 XiInitialMinor2
  ring

/-! ## Strict Turán input and strict TP₂ propagation -/

/-- **Strict Turán / strict log-concavity of the signed xi moment
coefficients**: `μₙ μ_{n+2} < μ_{n+1}²`.

For the Riemann xi coefficients this is the Csordas–Norfolk–Varga theorem
(1986): a proved classical result, **not** RH-strength.  It is kept as a named
hypothesis (like `XiMomentKernelRep`) because its analytic proof is not yet
formalized.  It strictly refines the nonnegative Turán ladder fragment
`XiTuran2All`. -/
def XiMomentStrictTuran : Prop :=
  ∀ n : ℕ,
    XiMomentCoeff n * XiMomentCoeff (n + 2) <
      XiMomentCoeff (n + 1) * XiMomentCoeff (n + 1)

/-- The strict Turán condition in raw `XiCoeff` form: the signs cancel in both
products. -/
theorem xiMomentStrictTuran_iff_coeff :
    XiMomentStrictTuran ↔
      ∀ n : ℕ, XiCoeff n * XiCoeff (n + 2) < XiCoeff (n + 1) ^ 2 := by
  unfold XiMomentStrictTuran XiMomentCoeff
  have key : ∀ n : ℕ,
      ((-1 : ℝ) ^ n * XiCoeff n) * ((-1) ^ (n + 2) * XiCoeff (n + 2)) =
        XiCoeff n * XiCoeff (n + 2) := by
    intro n
    have h1 : ((-1 : ℝ)) ^ n * (-1) ^ (n + 2) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n + 1, by ring⟩
    calc ((-1 : ℝ) ^ n * XiCoeff n) * ((-1) ^ (n + 2) * XiCoeff (n + 2))
        = ((-1 : ℝ) ^ n * (-1) ^ (n + 2)) * (XiCoeff n * XiCoeff (n + 2)) := by ring
      _ = XiCoeff n * XiCoeff (n + 2) := by rw [h1, one_mul]
  have key2 : ∀ n : ℕ,
      ((-1 : ℝ) ^ (n + 1) * XiCoeff (n + 1)) * ((-1) ^ (n + 1) * XiCoeff (n + 1)) =
        XiCoeff (n + 1) ^ 2 := by
    intro n
    have h2 : ((-1 : ℝ)) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨n + 1, by ring⟩
    calc ((-1 : ℝ) ^ (n + 1) * XiCoeff (n + 1)) * ((-1) ^ (n + 1) * XiCoeff (n + 1))
        = ((-1 : ℝ) ^ (n + 1) * (-1) ^ (n + 1)) * (XiCoeff (n + 1) * XiCoeff (n + 1)) := by
          ring
      _ = XiCoeff (n + 1) ^ 2 := by rw [h2, one_mul]; ring
  constructor
  · intro h n
    have := h n
    rw [key n, key2 n] at this
    exact this
  · intro h n
    rw [key n, key2 n]
    exact h n

/-- Strict Turán supplies the classical nonstrict Turán ladder fragment. -/
theorem xiTuran2All_of_strictTuran (h : XiMomentStrictTuran) : XiTuran2All := by
  intro n
  unfold XiTuran2
  exact le_of_lt ((xiMomentStrictTuran_iff_coeff.mp h) n)

/-- Strict TP₂ propagation: strict positivity plus strict Turán yield strict
unit-column log-concavity across any base gap, `μ_a μ_{b+1} < μ_{a+1} μ_b`
for `a < b`.  This is the chained form of "the ratio `μ_{n+1}/μ_n` strictly
decreases". -/
theorem xiMomentCoeff_strict_tp2
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran)
    {a b : ℕ} (hab : a < b) :
    XiMomentCoeff a * XiMomentCoeff (b + 1) <
      XiMomentCoeff (a + 1) * XiMomentCoeff b := by
  induction b, hab using Nat.le_induction with
  | base => exact hTuran a
  | succ b hb ih =>
      have h2 := hTuran b
      have hW : 0 < XiMomentCoeff b * XiMomentCoeff (b + 1) :=
        mul_pos (hPos b) (hPos (b + 1))
      have hmul :
          (XiMomentCoeff a * XiMomentCoeff (b + 1)) *
              (XiMomentCoeff b * XiMomentCoeff (b + 2)) <
            (XiMomentCoeff (a + 1) * XiMomentCoeff b) *
              (XiMomentCoeff (b + 1) * XiMomentCoeff (b + 1)) :=
        mul_lt_mul'' ih h2
          (le_of_lt (mul_pos (hPos a) (hPos (b + 1))))
          (le_of_lt (mul_pos (hPos b) (hPos (b + 2))))
      have hkey :
          (XiMomentCoeff a * XiMomentCoeff (b + 2)) *
              (XiMomentCoeff b * XiMomentCoeff (b + 1)) <
            (XiMomentCoeff (a + 1) * XiMomentCoeff (b + 1)) *
              (XiMomentCoeff b * XiMomentCoeff (b + 1)) := by
        calc (XiMomentCoeff a * XiMomentCoeff (b + 2)) *
                (XiMomentCoeff b * XiMomentCoeff (b + 1))
            = (XiMomentCoeff a * XiMomentCoeff (b + 1)) *
                (XiMomentCoeff b * XiMomentCoeff (b + 2)) := by ring
          _ < (XiMomentCoeff (a + 1) * XiMomentCoeff b) *
                (XiMomentCoeff (b + 1) * XiMomentCoeff (b + 1)) := hmul
          _ = (XiMomentCoeff (a + 1) * XiMomentCoeff (b + 1)) *
                (XiMomentCoeff b * XiMomentCoeff (b + 1)) := by ring
      exact lt_of_mul_lt_mul_right hkey (le_of_lt hW)

/-- **Every arbitrary-row initial-column `2 × 2` minor is strictly positive**
under strict positivity and strict Turán.  The `x = 0` boundary row is a
product of positive coefficients; the supported case is strict TP₂. -/
theorem xiInitialMinor2_pos
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran)
    {x y : ℕ} (hxy : x < y) :
    0 < XiInitialMinor2 x y := by
  unfold XiInitialMinor2
  by_cases hx : 1 ≤ x
  · rw [xiToeplitzEntry_sub x 0 (Nat.zero_le _),
        xiToeplitzEntry_sub y 1 (by omega),
        xiToeplitzEntry_sub x 1 hx,
        xiToeplitzEntry_sub y 0 (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    have h := xiMomentCoeff_strict_tp2 hPos hTuran
      (a := x - 1) (b := y - 1) (by omega)
    have hx1 : x - 1 + 1 = x := by omega
    have hy1 : y - 1 + 1 = y := by omega
    rw [hx1, hy1] at h
    linarith
  · have hx0 : x = 0 := by omega
    subst hx0
    have h01 : XiToeplitzEntry 0 1 = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (by omega)]
    rw [h01, xiToeplitzEntry_sub 0 0 le_rfl,
        xiToeplitzEntry_sub y 1 (by omega)]
    simp only [Nat.sub_zero, zero_mul, sub_zero]
    exact mul_pos (hPos 0) (hPos (y - 1))

/-! ## The order-3 Fekete induction -/

/-- **Fekete gap-shrinking induction at order three.**  The contiguous ladder
plus strict positivity and strict Turán force every arbitrary-row
initial-column `3 × 3` minor to be nonnegative.  Strong induction on the row
dispersion `r2 - r0 - 2`, shrinking one gap per step via the three-term
identities. -/
theorem xiInitialMinor3_nonneg
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran)
    (hContig : XiContigToeplitzTotalPositive) :
    ∀ d r0 r1 r2 : ℕ, r0 < r1 → r1 < r2 → r2 - r0 - 2 ≤ d →
      0 ≤ XiInitialMinor3 r0 r1 r2 := by
  intro d
  induction d with
  | zero =>
      intro r0 r1 r2 h01 h12 hd
      have h1 : r1 = r0 + 1 := by omega
      have h2 : r2 = r0 + 2 := by omega
      subst h1
      subst h2
      rw [xiInitialMinor3_contig]
      exact hContig 3 r0
  | succ d ih =>
      intro r0 r1 r2 h01 h12 hd
      by_cases hdle : r2 - r0 - 2 ≤ d
      · exact ih r0 r1 r2 h01 h12 hdle
      have hdisp : r2 - r0 - 2 = d + 1 := by omega
      by_cases hgap : r0 + 1 < r1
      · -- gap in the first slot: insert s = r0 + 1
        have hkey := xiInitialMinor3_gap_first r0 (r0 + 1) r1 r2
        have hP : 0 < XiInitialMinor2 (r0 + 1) r1 :=
          xiInitialMinor2_pos hPos hTuran hgap
        have hA : 0 ≤ XiInitialMinor3 (r0 + 1) r1 r2 :=
          ih (r0 + 1) r1 r2 hgap h12 (by omega)
        have hB : 0 ≤ XiInitialMinor3 r0 (r0 + 1) r1 :=
          ih r0 (r0 + 1) r1 (by omega) hgap (by omega)
        have hQ : 0 ≤ XiInitialMinor2 r0 r1 :=
          le_of_lt (xiInitialMinor2_pos hPos hTuran h01)
        have hR : 0 ≤ XiInitialMinor2 r1 r2 :=
          le_of_lt (xiInitialMinor2_pos hPos hTuran h12)
        nlinarith [hkey, hP, mul_nonneg hA hQ, mul_nonneg hB hR]
      · -- no first gap: r1 = r0 + 1, so the gap is in the second slot
        have hr1 : r1 = r0 + 1 := by omega
        have hgap2 : r1 + 1 < r2 := by omega
        have hkey := xiInitialMinor3_gap_second r0 r1 (r1 + 1) r2
        have hP : 0 < XiInitialMinor2 r1 (r1 + 1) :=
          xiInitialMinor2_pos hPos hTuran (by omega)
        have hA : 0 ≤ XiInitialMinor3 r1 (r1 + 1) r2 :=
          ih r1 (r1 + 1) r2 (by omega) hgap2 (by omega)
        have hB : 0 ≤ XiInitialMinor3 r0 r1 (r1 + 1) :=
          ih r0 r1 (r1 + 1) h01 (by omega) (by omega)
        have hQ : 0 ≤ XiInitialMinor2 r0 r1 :=
          le_of_lt (xiInitialMinor2_pos hPos hTuran h01)
        have hR : 0 ≤ XiInitialMinor2 r1 r2 :=
          le_of_lt (xiInitialMinor2_pos hPos hTuran h12)
        nlinarith [hkey, hP, mul_nonneg hA hQ, mul_nonneg hB hR]

/-- **The order-three arbitrary-row initial-column target, closed modulo strict
Turán.**  This was the first named open rung of the row-gap program
(`XiInitialColumnMinorThreeFromContig`); it now follows from the contiguous
ladder, strict positivity, and the classical strict Turán inequality. -/
theorem xiInitialColumnMinorThreeFromContig_of_strictTuran
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran) :
    XiInitialColumnMinorThreeFromContig := by
  intro rows hRows hContig
  have h01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 3) < 1)
  have h12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 3) < 2)
  rw [xiInitialMinor3_eq_det rows]
  exact xiInitialMinor3_nonneg hPos hTuran hContig
    (rows 2 - rows 0 - 2) (rows 0) (rows 1) (rows 2) h01 h12 le_rfl

/-- Pólya's kernel representation supplies the strict-positivity input, so the
order-three target needs only strict Turán beyond the classical kernel. -/
theorem xiInitialColumnMinorThreeFromContig_of_kernelRep_strictTuran
    (hRep : XiMomentKernelRep) (hTuran : XiMomentStrictTuran) :
    XiInitialColumnMinorThreeFromContig :=
  xiInitialColumnMinorThreeFromContig_of_strictTuran
    (xiMomentCoeffPositive_of_kernelRep hRep) hTuran

/-! ## Strict contiguous rungs and the strict order-3 result -/

/-- Strict positivity of the order-`k` contiguous rung of the Toeplitz ladder.
For each fixed `k` this is a strict refinement of the corresponding slice of
`XiContigToeplitzTotalPositive`; the interval scans support it (the tightest
observed normalized order-`3` contiguous minor is ≈ 4.2e-6 at offset 116). -/
def XiContigMinorStrictPositiveAt (k : ℕ) : Prop :=
  ∀ m : ℕ, 0 < XiToeplitzContigMinor k m

/-- The strict order-3 Fekete induction: with the strict order-`3` contiguous
rung as base case, every arbitrary-row initial-column `3 × 3` minor is
**strictly** positive.  This strict output is exactly the divisor consumed by
the order-`4` step. -/
theorem xiInitialMinor3_pos
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran)
    (hStrict3 : XiContigMinorStrictPositiveAt 3) :
    ∀ d r0 r1 r2 : ℕ, r0 < r1 → r1 < r2 → r2 - r0 - 2 ≤ d →
      0 < XiInitialMinor3 r0 r1 r2 := by
  intro d
  induction d with
  | zero =>
      intro r0 r1 r2 h01 h12 hd
      have h1 : r1 = r0 + 1 := by omega
      have h2 : r2 = r0 + 2 := by omega
      subst h1
      subst h2
      rw [xiInitialMinor3_contig]
      exact hStrict3 r0
  | succ d ih =>
      intro r0 r1 r2 h01 h12 hd
      by_cases hdle : r2 - r0 - 2 ≤ d
      · exact ih r0 r1 r2 h01 h12 hdle
      have hdisp : r2 - r0 - 2 = d + 1 := by omega
      by_cases hgap : r0 + 1 < r1
      · have hkey := xiInitialMinor3_gap_first r0 (r0 + 1) r1 r2
        have hP : 0 < XiInitialMinor2 (r0 + 1) r1 :=
          xiInitialMinor2_pos hPos hTuran hgap
        have hA : 0 < XiInitialMinor3 (r0 + 1) r1 r2 :=
          ih (r0 + 1) r1 r2 hgap h12 (by omega)
        have hB : 0 < XiInitialMinor3 r0 (r0 + 1) r1 :=
          ih r0 (r0 + 1) r1 (by omega) hgap (by omega)
        have hQ : 0 < XiInitialMinor2 r0 r1 := xiInitialMinor2_pos hPos hTuran h01
        have hR : 0 < XiInitialMinor2 r1 r2 := xiInitialMinor2_pos hPos hTuran h12
        nlinarith [hkey, hP, mul_pos hA hQ, mul_pos hB hR]
      · have hr1 : r1 = r0 + 1 := by omega
        have hgap2 : r1 + 1 < r2 := by omega
        have hkey := xiInitialMinor3_gap_second r0 r1 (r1 + 1) r2
        have hP : 0 < XiInitialMinor2 r1 (r1 + 1) :=
          xiInitialMinor2_pos hPos hTuran (by omega)
        have hA : 0 < XiInitialMinor3 r1 (r1 + 1) r2 :=
          ih r1 (r1 + 1) r2 (by omega) hgap2 (by omega)
        have hB : 0 < XiInitialMinor3 r0 r1 (r1 + 1) :=
          ih r0 r1 (r1 + 1) h01 (by omega) (by omega)
        have hQ : 0 < XiInitialMinor2 r0 r1 := xiInitialMinor2_pos hPos hTuran h01
        have hR : 0 < XiInitialMinor2 r1 r2 := xiInitialMinor2_pos hPos hTuran h12
        nlinarith [hkey, hP, mul_pos hA hQ, mul_pos hB hR]

/-! ## The order-4 layer -/

/-- `3 × 3` Toeplitz minor at explicit rows and an explicit column triple.
Used for the cofactors of the first-row Laplace expansion at order four. -/
def XiMinor3Cols (x y z c0 c1 c2 : ℕ) : ℝ :=
  XiToeplitzEntry x c0 *
      (XiToeplitzEntry y c1 * XiToeplitzEntry z c2 -
        XiToeplitzEntry y c2 * XiToeplitzEntry z c1) -
    XiToeplitzEntry x c1 *
      (XiToeplitzEntry y c0 * XiToeplitzEntry z c2 -
        XiToeplitzEntry y c2 * XiToeplitzEntry z c0) +
    XiToeplitzEntry x c2 *
      (XiToeplitzEntry y c0 * XiToeplitzEntry z c1 -
        XiToeplitzEntry y c1 * XiToeplitzEntry z c0)

/-- Scalar form of the arbitrary-row initial-column `4 × 4` Toeplitz minor
(first-row Laplace expansion). -/
def XiInitialMinor4 (r0 r1 r2 r3 : ℕ) : ℝ :=
  XiToeplitzEntry r0 0 * XiMinor3Cols r1 r2 r3 1 2 3 -
    XiToeplitzEntry r0 1 * XiMinor3Cols r1 r2 r3 0 2 3 +
    XiToeplitzEntry r0 2 * XiMinor3Cols r1 r2 r3 0 1 3 -
    XiToeplitzEntry r0 3 * XiMinor3Cols r1 r2 r3 0 1 2

set_option linter.flexible false in
/-- The scalar `4 × 4` form agrees with the determinant used by the named
initial-column targets. -/
theorem xiInitialMinor4_eq_det (rows : Fin 4 → ℕ) :
    (Matrix.of (fun i j : Fin 4 => XiToeplitzEntry (rows i) j.val)).det =
      XiInitialMinor4 (rows 0) (rows 1) (rows 2) (rows 3) := by
  have hM : (Matrix.of (fun i j : Fin 4 => XiToeplitzEntry (rows i) j.val)) =
      !![XiToeplitzEntry (rows 0) 0, XiToeplitzEntry (rows 0) 1,
           XiToeplitzEntry (rows 0) 2, XiToeplitzEntry (rows 0) 3;
         XiToeplitzEntry (rows 1) 0, XiToeplitzEntry (rows 1) 1,
           XiToeplitzEntry (rows 1) 2, XiToeplitzEntry (rows 1) 3;
         XiToeplitzEntry (rows 2) 0, XiToeplitzEntry (rows 2) 1,
           XiToeplitzEntry (rows 2) 2, XiToeplitzEntry (rows 2) 3;
         XiToeplitzEntry (rows 3) 0, XiToeplitzEntry (rows 3) 1,
           XiToeplitzEntry (rows 3) 2, XiToeplitzEntry (rows 3) 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hM]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove, Fin.lt_def]
  unfold XiInitialMinor4 XiMinor3Cols
  ring

/-- The contiguous specialization of the scalar `4 × 4` minor is the ladder
minor. -/
theorem xiInitialMinor4_contig (m : ℕ) :
    XiInitialMinor4 m (m + 1) (m + 2) (m + 3) = XiToeplitzContigMinor 4 m := by
  unfold XiToeplitzContigMinor
  rw [xiInitialMinor4_eq_det (fun i : Fin 4 => m + i.val)]
  simp

/-- Order-4 gap-shrinking identity, gap in the **first** slot
(read `r0 < s < r1 < r2 < r3`). -/
theorem xiInitialMinor4_gap_first (r0 s r1 r2 r3 : ℕ) :
    XiInitialMinor4 r0 r1 r2 r3 * XiInitialMinor3 s r1 r2 =
      XiInitialMinor4 s r1 r2 r3 * XiInitialMinor3 r0 r1 r2 +
        XiInitialMinor4 r0 s r1 r2 * XiInitialMinor3 r1 r2 r3 := by
  unfold XiInitialMinor4 XiMinor3Cols XiInitialMinor3
  ring

/-- Order-4 gap-shrinking identity, gap in the **second** slot
(read `r0 < r1 < s < r2 < r3`). -/
theorem xiInitialMinor4_gap_second (r0 r1 s r2 r3 : ℕ) :
    XiInitialMinor4 r0 r1 r2 r3 * XiInitialMinor3 r1 s r2 =
      XiInitialMinor4 r1 s r2 r3 * XiInitialMinor3 r0 r1 r2 +
        XiInitialMinor4 r0 r1 s r2 * XiInitialMinor3 r1 r2 r3 := by
  unfold XiInitialMinor4 XiMinor3Cols XiInitialMinor3
  ring

/-- Order-4 gap-shrinking identity, gap in the **third** slot
(read `r0 < r1 < r2 < s < r3`). -/
theorem xiInitialMinor4_gap_third (r0 r1 r2 s r3 : ℕ) :
    XiInitialMinor4 r0 r1 r2 r3 * XiInitialMinor3 r1 r2 s =
      XiInitialMinor4 r1 r2 s r3 * XiInitialMinor3 r0 r1 r2 +
        XiInitialMinor4 r0 r1 r2 s * XiInitialMinor3 r1 r2 r3 := by
  unfold XiInitialMinor4 XiMinor3Cols XiInitialMinor3
  ring

/-- **Fekete gap-shrinking induction at order four.**  The contiguous ladder,
strict positivity, strict Turán, and the strict order-`3` contiguous rung force
every arbitrary-row initial-column `4 × 4` minor to be nonnegative.  The
divisor of each reduction step is a strict arbitrary-row `3 × 3` minor supplied
by `xiInitialMinor3_pos`. -/
theorem xiInitialMinor4_nonneg
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran)
    (hStrict3 : XiContigMinorStrictPositiveAt 3)
    (hContig : XiContigToeplitzTotalPositive) :
    ∀ d r0 r1 r2 r3 : ℕ, r0 < r1 → r1 < r2 → r2 < r3 → r3 - r0 - 3 ≤ d →
      0 ≤ XiInitialMinor4 r0 r1 r2 r3 := by
  have hD3 : ∀ x y z : ℕ, x < y → y < z → 0 < XiInitialMinor3 x y z := by
    intro x y z hxy hyz
    exact xiInitialMinor3_pos hPos hTuran hStrict3 (z - x - 2) x y z hxy hyz le_rfl
  intro d
  induction d with
  | zero =>
      intro r0 r1 r2 r3 h01 h12 h23 hd
      have h1 : r1 = r0 + 1 := by omega
      have h2 : r2 = r0 + 2 := by omega
      have h3 : r3 = r0 + 3 := by omega
      subst h1
      subst h2
      subst h3
      rw [xiInitialMinor4_contig]
      exact hContig 4 r0
  | succ d ih =>
      intro r0 r1 r2 r3 h01 h12 h23 hd
      by_cases hdle : r3 - r0 - 3 ≤ d
      · exact ih r0 r1 r2 r3 h01 h12 h23 hdle
      have hdisp : r3 - r0 - 3 = d + 1 := by omega
      by_cases hgap1 : r0 + 1 < r1
      · -- gap in the first slot: insert s = r0 + 1
        have hkey := xiInitialMinor4_gap_first r0 (r0 + 1) r1 r2 r3
        have hP : 0 < XiInitialMinor3 (r0 + 1) r1 r2 := hD3 _ _ _ hgap1 h12
        have hA : 0 ≤ XiInitialMinor4 (r0 + 1) r1 r2 r3 :=
          ih (r0 + 1) r1 r2 r3 hgap1 h12 h23 (by omega)
        have hB : 0 ≤ XiInitialMinor4 r0 (r0 + 1) r1 r2 :=
          ih r0 (r0 + 1) r1 r2 (by omega) hgap1 h12 (by omega)
        have hQ : 0 ≤ XiInitialMinor3 r0 r1 r2 := le_of_lt (hD3 _ _ _ h01 h12)
        have hR : 0 ≤ XiInitialMinor3 r1 r2 r3 := le_of_lt (hD3 _ _ _ h12 h23)
        nlinarith [hkey, hP, mul_nonneg hA hQ, mul_nonneg hB hR]
      by_cases hgap2 : r1 + 1 < r2
      · -- r1 = r0 + 1; gap in the second slot: insert s = r1 + 1
        have hkey := xiInitialMinor4_gap_second r0 r1 (r1 + 1) r2 r3
        have hP : 0 < XiInitialMinor3 r1 (r1 + 1) r2 := hD3 _ _ _ (by omega) hgap2
        have hA : 0 ≤ XiInitialMinor4 r1 (r1 + 1) r2 r3 :=
          ih r1 (r1 + 1) r2 r3 (by omega) hgap2 h23 (by omega)
        have hB : 0 ≤ XiInitialMinor4 r0 r1 (r1 + 1) r2 :=
          ih r0 r1 (r1 + 1) r2 h01 (by omega) hgap2 (by omega)
        have hQ : 0 ≤ XiInitialMinor3 r0 r1 r2 := le_of_lt (hD3 _ _ _ h01 h12)
        have hR : 0 ≤ XiInitialMinor3 r1 r2 r3 := le_of_lt (hD3 _ _ _ h12 h23)
        nlinarith [hkey, hP, mul_nonneg hA hQ, mul_nonneg hB hR]
      · -- r1 = r0 + 1, r2 = r1 + 1; the gap is before r3: insert s = r2 + 1
        have hgap3 : r2 + 1 < r3 := by omega
        have hkey := xiInitialMinor4_gap_third r0 r1 r2 (r2 + 1) r3
        have hP : 0 < XiInitialMinor3 r1 r2 (r2 + 1) := hD3 _ _ _ h12 (by omega)
        have hA : 0 ≤ XiInitialMinor4 r1 r2 (r2 + 1) r3 :=
          ih r1 r2 (r2 + 1) r3 h12 (by omega) hgap3 (by omega)
        have hB : 0 ≤ XiInitialMinor4 r0 r1 r2 (r2 + 1) :=
          ih r0 r1 r2 (r2 + 1) h01 h12 (by omega) (by omega)
        have hQ : 0 ≤ XiInitialMinor3 r0 r1 r2 := le_of_lt (hD3 _ _ _ h01 h12)
        have hR : 0 ≤ XiInitialMinor3 r1 r2 r3 := le_of_lt (hD3 _ _ _ h12 h23)
        nlinarith [hkey, hP, mul_nonneg hA hQ, mul_nonneg hB hR]

/-! ## Named targets: the `k = 4` rung and the `k ≥ 5` tail -/

/-- The `k = 4` rung of the arbitrary-row initial-column program, in the same
style as the named order-two and order-three targets. -/
def XiInitialColumnMinorFourFromContig : Prop :=
  ∀ (rows : Fin 4 → ℕ),
    StrictMono rows →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun i j : Fin 4 => XiToeplitzEntry (rows i) j.val)).det

/-- **The `k = 4` rung holds** from strict positivity, strict Turán, and the
strict order-`3` contiguous rung. -/
theorem xiInitialColumnMinorFourFromContig_of_strictTuran
    (hPos : XiMomentCoeffPositive) (hTuran : XiMomentStrictTuran)
    (hStrict3 : XiContigMinorStrictPositiveAt 3) :
    XiInitialColumnMinorFourFromContig := by
  intro rows hRows hContig
  have h01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 4) < 1)
  have h12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 4) < 2)
  have h23 : rows 2 < rows 3 := hRows (by decide : (2 : Fin 4) < 3)
  rw [xiInitialMinor4_eq_det rows]
  exact xiInitialMinor4_nonneg hPos hTuran hStrict3 hContig
    (rows 3 - rows 0 - 3) (rows 0) (rows 1) (rows 2) (rows 3) h01 h12 h23 le_rfl

/-- The remaining arbitrary-row initial-column tail after orders up to four. -/
def XiInitialColumnMinorGeFiveFromContig : Prop :=
  ∀ (k : ℕ), 5 ≤ k →
    ∀ (rows : Fin k → ℕ),
      StrictMono rows →
      XiContigToeplitzTotalPositive →
        0 ≤ (Matrix.of (fun i j : Fin k => XiToeplitzEntry (rows i) j.val)).det

/-- The order-four rung and the `k ≥ 5` tail assemble the previously named
`k ≥ 4` condition. -/
theorem xiInitialColumnMinorGeFourFromContig_of_four_and_geFive
    (hFour : XiInitialColumnMinorFourFromContig)
    (hGeFive : XiInitialColumnMinorGeFiveFromContig) :
    XiInitialColumnMinorGeFourFromContig := by
  intro k hk rows hRows hContig
  by_cases hk4 : k = 4
  · subst hk4
    exact hFour rows hRows hContig
  · exact hGeFive k (by omega) rows hRows hContig

/-! ## Capstone wiring -/

/-- Rebuild the capstone input `KernelContigToPFInitialColumnGeFourTheorem`
with the order-`3` field discharged by the Fekete row-gap theorem and the
order-`4` rung split off the tail.  The remaining open surface is: contiguous
kernel positivity, strict Turán, the strict order-`3` contiguous rung, the
`k ≥ 5` arbitrary-row tail, and Cryer's initial-column criterion. -/
def kernelContigToPFInitialColumnGeFourTheorem_of_strictTuran_and_geFive
    (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (hContig : KernelContigTotalPositive M)
    (hTuran : XiMomentStrictTuran)
    (hStrict3 : XiContigMinorStrictPositiveAt 3)
    (hGeFive : XiInitialColumnMinorGeFiveFromContig)
    (hCriterion : XiInitialColumnMinorToFullPFBridge) :
    KernelContigToPFInitialColumnGeFourTheorem where
  M := M
  positive := hMpos
  kernelRep := hM
  contig := hContig
  initialColumnsThree :=
    xiInitialColumnMinorThreeFromContig_of_kernelRep_strictTuran ⟨M, hMpos, hM⟩ hTuran
  initialColumnsGeFour :=
    xiInitialColumnMinorGeFourFromContig_of_four_and_geFive
      (xiInitialColumnMinorFourFromContig_of_strictTuran
        (xiMomentCoeffPositive_of_kernelRep ⟨M, hMpos, hM⟩) hTuran hStrict3)
      hGeFive
  initialColumnsToPF := hCriterion

end Reinmann

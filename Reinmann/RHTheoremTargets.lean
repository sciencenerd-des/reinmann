/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.CrossFieldBridges
import Reinmann.RHReductionCapstone

/-!
# Theorem Targets for a Full RH Attack

This module turns the accumulated research routes into auditable theorem
targets.  It does not prove RH.  Its purpose is to separate three levels of
mathematical progress:

1. `Order3FrontierTheorem`: the first open Toeplitz/PF rung beyond Turán.
2. `KernelContigTotalPositive`: all contiguous factorial-weighted kernel
   Toeplitz determinants.
3. `XiToeplitzTotalPositive`: full arbitrary-minor Pólya-frequency positivity,
   which is the RH-equivalent capstone input.

The cross-field routes are only useful if they deliver one of these concrete
positivity payloads.  The final theorem in this file records the exact success
condition: a full PF witness plus the classical scaffolding proves RH.
-/

noncomputable section

namespace Reinmann

/-! ## Level 1: the first frontier theorem -/

/-- The immediate next theorem to prove analytically: Pólya's xi-kernel moment
representation plus an independent order-`3` positivity proof. -/
structure Order3FrontierTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  order3 : MomentToeplitzOrder3Positive M

/-- The order-`3` frontier theorem transfers to the coefficient-side Toeplitz
order-`3` target.  This is real progress, but still only one rung, not RH. -/
theorem xiToeplitzOrder3Positive_of_order3Frontier
    (T : Order3FrontierTheorem) : XiToeplitzOrder3Positive :=
  (xiToeplitzOrder3Positive_iff_moment_of_kernelRep T.kernelRep).mpr T.order3

/-- Any cross-field order-`3` witness supplies the order-`3` frontier theorem. -/
theorem xiToeplitzOrder3Positive_of_order3CrossField
    {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (w : CrossFieldOrder3Witness M) :
    XiToeplitzOrder3Positive :=
  xiToeplitzOrder3Positive_of_crossFieldWitness hM w

/-! ## Level 2: contiguous all-order kernel positivity -/

/-- Contiguous all-order Toeplitz positivity for the signed xi coefficients.
This is stronger than the order-`3` frontier, but still weaker than the full
arbitrary-minor PF condition used by Edrei-ASW. -/
def XiContigToeplitzTotalPositive : Prop :=
  ∀ k m : ℕ, 0 ≤ XiToeplitzContigMinor k m

/-- Contiguous all-order positivity for the factorial-weighted kernel moments. -/
def KernelContigTotalPositive (M : ℕ → ℝ) : Prop :=
  ∀ k m : ℕ, 0 ≤ momentToeplitzContigMinor M k m

/-- Full Pólya-frequency positivity includes all contiguous Toeplitz minors. -/
theorem xiContigToeplitzTotalPositive_of_toeplitzTP
    (h : XiToeplitzTotalPositive) : XiContigToeplitzTotalPositive := by
  intro k m
  exact xiToeplitzContigMinor_nonneg_of_toeplitzTP h k m

/-- Under Pólya's kernel representation, kernel-side contiguous positivity is
equivalent to coefficient-side contiguous positivity. -/
theorem xiContigToeplitzTotalPositive_iff_kernelContig
    {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))) :
    XiContigToeplitzTotalPositive ↔ KernelContigTotalPositive M := by
  unfold XiContigToeplitzTotalPositive KernelContigTotalPositive
  constructor
  · intro h k m
    exact (xiToeplitzContigMinor_nonneg_iff_moment_of_kernelRep hM k m).mp (h k m)
  · intro h k m
    exact (xiToeplitzContigMinor_nonneg_iff_moment_of_kernelRep hM k m).mpr (h k m)

/-- A second-level theorem target: prove all contiguous kernel Toeplitz minors
from an external mathematical model. -/
structure KernelContigWitness (M : ℕ → ℝ) where
  model : Prop
  proof : model
  contig : model → KernelContigTotalPositive M

/-- A kernel contiguous witness transfers to all contiguous coefficient-side
Toeplitz minors. -/
theorem xiContigToeplitzTotalPositive_of_kernelContigWitness
    {M : ℕ → ℝ}
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (w : KernelContigWitness M) :
    XiContigToeplitzTotalPositive :=
  (xiContigToeplitzTotalPositive_iff_kernelContig hM).mpr (w.contig w.proof)

/-! ## Level 2.5: the contiguous-to-arbitrary-minor upgrade -/

/-- The exact bridge missing after all contiguous minors are proved.

For a general sequence this is false or at least far too strong to assume
silently.  For the xi signed coefficients it is the next named condition: a
mathematical theorem that upgrades the concrete contiguous ladder to the full
arbitrary-minor Pólya-frequency condition. -/
def XiContigToFullPFBridge : Prop :=
  XiContigToeplitzTotalPositive → XiToeplitzTotalPositive

/-- Local form of the contiguous-to-full bridge.

Instead of asking for the full upgrade in one black box, this asks for a
uniform reduction of each arbitrary Toeplitz minor to the contiguous positivity
ladder.  This is the better proof-search target: one can try to build
Cauchy-Binet, planar-network, or variation-diminishing certificates for
individual row/column patterns and then generalize. -/
def XiArbitraryMinorReductionToContig : Prop :=
  ∀ (k : ℕ) (rows cols : Fin k → ℕ),
    StrictMono rows → StrictMono cols →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- A certificate for one arbitrary Toeplitz minor.

The `certificate` field is deliberately a proposition rather than a data format
for now.  Future refinements can replace it with a concrete Cauchy-Binet sum,
planar-network model, or variation-diminishing factorization.  The crucial
point is that the certificate proves this *specific* minor from the contiguous
positivity ladder. -/
structure XiMinorContigCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols) where
  certificate : Prop
  proof : certificate
  nonneg :
    certificate →
      XiContigToeplitzTotalPositive →
        0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- A uniform supply of local certificates for every arbitrary minor pattern. -/
def XiAllMinorContigCertificates : Prop :=
  ∀ (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      Nonempty (XiMinorContigCertificate k rows cols hRows hCols)

/-- Contiguous `1 × 1` positivity makes every lower-triangular Toeplitz entry
nonnegative; entries above the support are zero. -/
theorem xiToeplitzEntry_nonneg_of_contig
    (h : XiContigToeplitzTotalPositive) (i j : ℕ) :
    0 ≤ XiToeplitzEntry i j := by
  by_cases hj : j ≤ i
  · have hminor := h 1 (i - j)
    unfold XiToeplitzContigMinor at hminor
    rw [Matrix.det_fin_one] at hminor
    simp only [Matrix.of_apply, Fin.val_zero] at hminor
    rw [Nat.add_zero] at hminor
    rw [xiToeplitzEntry_sub (i - j) 0 (Nat.zero_le _), Nat.sub_zero] at hminor
    rw [xiToeplitzEntry_sub i j hj]
    exact hminor
  · unfold XiToeplitzEntry
    rw [if_neg hj]

/-- Sequence-level nonnegativity supplied by contiguous `1 × 1` minors. -/
def XiMomentCoeffNonnegativeFromContig : Prop :=
  ∀ n : ℕ, XiContigToeplitzTotalPositive → 0 ≤ XiMomentCoeff n

/-- Sequence-level strict positivity, kept separate from contiguous positivity.
It is supplied by Pólya's positive kernel representation, not by nonnegative
Toeplitz minors alone. -/
def XiMomentCoeffPositive : Prop :=
  ∀ n : ℕ, 0 < XiMomentCoeff n

/-- Contiguous positivity proves nonnegativity of every signed xi moment
coefficient. -/
theorem xiMomentCoeffNonnegative_of_contig :
    XiMomentCoeffNonnegativeFromContig := by
  intro n hContig
  simpa [XiToeplitzEntry, Nat.sub_zero] using
    xiToeplitzEntry_nonneg_of_contig hContig n 0

/-- Pólya's positive kernel representation supplies strict positivity of the
signed xi moment coefficients. -/
theorem xiMomentCoeffPositive_of_kernelRep (hRep : XiMomentKernelRep) :
    XiMomentCoeffPositive := by
  rcases hRep with ⟨M, hMpos, hM⟩
  intro n
  exact xiMomentCoeff_pos_of_kernelRep hMpos hM n

/-- The empty arbitrary minor is nonnegative.  This closes the size-`0`
certificate case in the arbitrary-minor program. -/
def xiMinorZeroContigCertificate
    (rows cols : Fin 0 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols) :
    XiMinorContigCertificate 0 rows cols hRows hCols where
  certificate := True
  proof := trivial
  nonneg := by
    intro _ _
    simp

/-- Every arbitrary `0 × 0` row/column pattern has a local certificate. -/
theorem exists_xiMinorZeroContigCertificate
    (rows cols : Fin 0 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols) :
    Nonempty (XiMinorContigCertificate 0 rows cols hRows hCols) :=
  ⟨xiMinorZeroContigCertificate rows cols hRows hCols⟩

/-- Base-case certificate family: a contiguous minor certifies itself from the
contiguous positivity ladder.  This is not the hard bridge, but it anchors the
certificate program with the exact row/column pattern already controlled by
`XiContigToeplitzTotalPositive`. -/
def xiContiguousMinorSelfCertificate (k m : ℕ) :
    XiMinorContigCertificate k
      (fun i : Fin k => m + i.val)
      (fun j : Fin k => j.val)
      (strictMono_addLeft_val m k)
      (strictMono_fin_val k) where
  certificate := True
  proof := trivial
  nonneg := by
    intro _ hContig
    exact hContig k m

/-- The contiguous row/column patterns have local certificates.  The remaining
work is to extend this from interval row/column patterns to arbitrary strictly
monotone patterns. -/
theorem exists_contiguousMinorSelfCertificate (k m : ℕ) :
    Nonempty
      (XiMinorContigCertificate k
        (fun i : Fin k => m + i.val)
        (fun j : Fin k => j.val)
        (strictMono_addLeft_val m k)
        (strictMono_fin_val k)) :=
  ⟨xiContiguousMinorSelfCertificate k m⟩

/-- All arbitrary `1 × 1` Toeplitz minors have certificates from the contiguous
ladder.  If the column is above the row, the lower-triangular Toeplitz entry is
`0`; otherwise it is exactly the contiguous `1 × 1` minor at offset `row - col`.
-/
def xiMinorOneContigCertificate
    (rows cols : Fin 1 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols) :
    XiMinorContigCertificate 1 rows cols hRows hCols where
  certificate := True
  proof := trivial
  nonneg := by
    intro _ hContig
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply]
    by_cases hc : cols 0 ≤ rows 0
    · have h := hContig 1 (rows 0 - cols 0)
      unfold XiToeplitzContigMinor at h
      rw [Matrix.det_fin_one] at h
      simp only [Matrix.of_apply, Fin.val_zero] at h
      rw [Nat.add_zero] at h
      rw [xiToeplitzEntry_sub (rows 0 - cols 0) 0 (Nat.zero_le _), Nat.sub_zero] at h
      rw [xiToeplitzEntry_sub (rows 0) (cols 0) hc]
      exact h
    · unfold XiToeplitzEntry
      rw [if_neg hc]

/-- Every arbitrary `1 × 1` row/column pattern has a local contiguous-minor
certificate.  This is the first non-interval certificate family in the loop. -/
theorem exists_xiMinorOneContigCertificate
    (rows cols : Fin 1 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols) :
    Nonempty (XiMinorContigCertificate 1 rows cols hRows hCols) :=
  ⟨xiMinorOneContigCertificate rows cols hRows hCols⟩

/-- Certificate family for minors completely above the lower-triangular support.
If every selected column index is larger than every selected row index, every
Toeplitz entry is zero, so the determinant is zero and hence nonnegative. -/
def xiZeroSupportMinorCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin k, rows a < cols b) :
    XiMinorContigCertificate k rows cols hRows hCols where
  certificate := ∀ a b : Fin k, rows a < cols b
  proof := hSupport
  nonneg := by
    intro hZero _
    have hmat :
        (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b)))
          = (0 : Matrix (Fin k) (Fin k) ℝ) := by
      ext a b
      change XiToeplitzEntry (rows a) (cols b) = 0
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt (hZero a b))]
    rw [hmat]
    by_cases hk : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hnonempty : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
      rw [Matrix.det_zero hnonempty]

/-- Any minor completely above the lower-triangular Toeplitz support has a
local contiguous-minor certificate.  This closes an arbitrary-size degenerate
family before the genuinely mixed-support `2 × 2` cases. -/
theorem exists_xiZeroSupportMinorCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin k, rows a < cols b) :
    Nonempty (XiMinorContigCertificate k rows cols hRows hCols) :=
  ⟨xiZeroSupportMinorCertificate k rows cols hRows hCols hSupport⟩

/-- Certificate family for any arbitrary minor with one zero row.  If some
selected row lies strictly below every selected column, every entry in that row
is above the lower-triangular support.  The determinant is then zero. -/
def xiZeroRowMinorCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hZeroRow : ∃ a : Fin k, ∀ b : Fin k, rows a < cols b) :
    XiMinorContigCertificate k rows cols hRows hCols where
  certificate := ∃ a : Fin k, ∀ b : Fin k, rows a < cols b
  proof := hZeroRow
  nonneg := by
    intro hRow _
    rcases hRow with ⟨a0, ha0⟩
    have hdet :
        (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero a0
      intro b
      change XiToeplitzEntry (rows a0) (cols b) = 0
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt (ha0 b))]
    rw [hdet]

/-- Any arbitrary minor with one row above the lower-triangular support has a
local contiguous-minor certificate.  This strictly generalizes the
all-zero-support family. -/
theorem exists_xiZeroRowMinorCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hZeroRow : ∃ a : Fin k, ∀ b : Fin k, rows a < cols b) :
    Nonempty (XiMinorContigCertificate k rows cols hRows hCols) :=
  ⟨xiZeroRowMinorCertificate k rows cols hRows hCols hZeroRow⟩

/-- Certificate family for any arbitrary minor with one zero column.  If some
selected column lies strictly above every selected row, every entry in that
column is above the lower-triangular support.  The determinant is then zero. -/
def xiZeroColumnMinorCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hZeroCol : ∃ b : Fin k, ∀ a : Fin k, rows a < cols b) :
    XiMinorContigCertificate k rows cols hRows hCols where
  certificate := ∃ b : Fin k, ∀ a : Fin k, rows a < cols b
  proof := hZeroCol
  nonneg := by
    intro hCol _
    rcases hCol with ⟨b0, hb0⟩
    have hdet :
        (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero b0
      intro a
      change XiToeplitzEntry (rows a) (cols b0) = 0
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt (hb0 a))]
    rw [hdet]

/-- Any arbitrary minor with one column above the lower-triangular support has a
local contiguous-minor certificate. -/
theorem exists_xiZeroColumnMinorCertificate
    (k : ℕ) (rows cols : Fin k → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hZeroCol : ∃ b : Fin k, ∀ a : Fin k, rows a < cols b) :
    Nonempty (XiMinorContigCertificate k rows cols hRows hCols) :=
  ⟨xiZeroColumnMinorCertificate k rows cols hRows hCols hZeroCol⟩

/-- First mixed-support `2 × 2` certificate family.  If the upper-right entry is
above the lower-triangular Toeplitz support, the determinant is the product of
the two diagonal entries.  Contiguous `1 × 1` positivity makes those entries
nonnegative. -/
def xiMinorTwoUpperRightZeroCertificate
    (rows cols : Fin 2 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hUpperRight : rows 0 < cols 1) :
    XiMinorContigCertificate 2 rows cols hRows hCols where
  certificate := rows 0 < cols 1
  proof := hUpperRight
  nonneg := by
    intro hUR hContig
    have h00 := xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
    have h11 := xiToeplitzEntry_nonneg_of_contig hContig (rows 1) (cols 1)
    have h01 : XiToeplitzEntry (rows 0) (cols 1) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt hUR)]
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [h01, zero_mul, sub_zero]
    exact mul_nonneg h00 h11

/-- Any `2 × 2` arbitrary minor with zero upper-right Toeplitz entry has a local
contiguous-minor certificate.  This is the first genuinely mixed-support
non-contiguous certificate family. -/
theorem exists_xiMinorTwoUpperRightZeroCertificate
    (rows cols : Fin 2 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hUpperRight : rows 0 < cols 1) :
    Nonempty (XiMinorContigCertificate 2 rows cols hRows hCols) :=
  ⟨xiMinorTwoUpperRightZeroCertificate rows cols hRows hCols hUpperRight⟩

/-- The remaining full-support `2 × 2` Toeplitz certificate target.

All degenerate `2 × 2` cases above are now covered by zero-row/zero-column or
upper-right-zero certificates.  This condition isolates the first genuinely
nontrivial mixed-support problem: when all four entries are inside the
lower-triangular support, contiguous positivity must imply the arbitrary
`2 × 2` determinant is nonnegative. -/
def XiMinorTwoFullSupportFromContig : Prop :=
  ∀ (rows cols : Fin 2 → ℕ),
    StrictMono rows → StrictMono cols →
    (∀ a b : Fin 2, cols b ≤ rows a) →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- Explicit four-index form of the full-support `2 × 2` frontier.

For rows `r₀ < r₁` and columns `c₀ < c₁`, full support means `c₁ ≤ r₀`.
The arbitrary Toeplitz determinant is then exactly

`μ(r₀-c₀) μ(r₁-c₁) - μ(r₀-c₁) μ(r₁-c₀)`.

This is the first nontrivial Monge/log-submodularity-type inequality that the
contiguous ladder does not currently prove. -/
def XiMinorTwoGapInequalityFromContig : Prop :=
  ∀ (r0 r1 c0 c1 : ℕ),
    r0 < r1 → c0 < c1 → c1 ≤ r0 →
    XiContigToeplitzTotalPositive →
      XiMomentCoeff (r0 - c1) * XiMomentCoeff (r1 - c0) ≤
        XiMomentCoeff (r0 - c0) * XiMomentCoeff (r1 - c1)

/-- A ratio-Monge form of the same `2 × 2` frontier.

For every positive gap `d`, the adjacent ratio
`μ(n+d) / μ(n)` should decrease as `n` increases.  It is written without
division:

`μ(a) μ(b+d) ≤ μ(a+d) μ(b)` for `a ≤ b`.

This is the clean sequence-level condition to attack next. -/
def XiMomentRatioMongeFromContig : Prop :=
  ∀ (a b d : ℕ),
    a ≤ b → 0 < d →
    XiContigToeplitzTotalPositive →
      XiMomentCoeff a * XiMomentCoeff (b + d) ≤
        XiMomentCoeff (a + d) * XiMomentCoeff b

/-- Adjacent-step form of ratio monotonicity.

For every positive gap `d`, the cross-multiplied ratio inequality is required
only between adjacent bases `n` and `n+1`. -/
def XiMomentAdjacentRatioMongeFromContig : Prop :=
  ∀ (n d : ℕ),
    0 < d →
    XiContigToeplitzTotalPositive →
      XiMomentCoeff n * XiMomentCoeff (n + 1 + d) ≤
        XiMomentCoeff (n + d) * XiMomentCoeff (n + 1)

/-- Unit-gap adjacent ratio monotonicity.  This is the `d = 1` adjacent case,
equivalently the usual contiguous `2 × 2` Toeplitz/Turán inequality. -/
def XiMomentUnitRatioMongeFromContig : Prop :=
  ∀ n : ℕ,
    XiContigToeplitzTotalPositive →
      XiMomentCoeff n * XiMomentCoeff (n + 2) ≤
        XiMomentCoeff (n + 1) * XiMomentCoeff (n + 1)

/-- The unit-gap ratio condition is already proved by the contiguous `2 × 2`
minor in the ladder. -/
theorem xiMomentUnitRatioMonge_of_contig :
    XiMomentUnitRatioMongeFromContig := by
  intro n hContig
  have hminor := hContig 2 (n + 1)
  rw [← xiToeplitzMinor2_eq_contig n] at hminor
  unfold XiToeplitzMinor2 at hminor
  nlinarith

/-- Algebraic cancellation step for propagating adjacent ratio gaps.

If `A B ≤ C D` and `C E ≤ B²`, with the middle coefficients positive, then
`A E ≤ B D`.  This is the no-division form of multiplying consecutive quotient
inequalities. -/
theorem two_step_ratio_cancel
    {A B C D E : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 < C)
    (hAB : A * B ≤ C * D) (hCE : C * E ≤ B * B) :
    A * E ≤ B * D := by
  have hCnonneg : 0 ≤ C := le_of_lt hC
  have hCEA : A * (C * E) ≤ A * (B * B) :=
    mul_le_mul_of_nonneg_left hCE hA
  have hABB : (A * B) * B ≤ (C * D) * B :=
    mul_le_mul_of_nonneg_right hAB hB
  nlinarith

/-- General two-step cancellation for chaining ratio inequalities without
division. -/
theorem two_step_ratio_cancel_general
    {A B C D E F : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hAB : A * B ≤ C * D) (hCE : C * E ≤ B * F) :
    A * E ≤ D * F := by
  have hBnonneg : 0 ≤ B := le_of_lt hB
  have hCnonneg : 0 ≤ C := le_of_lt hC
  have hCE_nonneg : 0 ≤ C * E := mul_nonneg hCnonneg hE
  have hCD_nonneg : 0 ≤ C * D := mul_nonneg hCnonneg hD
  have hprod : (A * B) * (C * E) ≤ (C * D) * (B * F) :=
    mul_le_mul hAB hCE hCE_nonneg hCD_nonneg
  nlinarith [hprod, hB, hC]

/-- Fixed-gap adjacent ratio monotonicity.

This packages the `d`-th adjacent ratio inequality as a standalone target so
the unit-to-all-gaps propagation can be attacked by induction on `d`. -/
def XiMomentAdjacentRatioGap (d : ℕ) : Prop :=
  ∀ n : ℕ,
    XiContigToeplitzTotalPositive →
      XiMomentCoeff n * XiMomentCoeff (n + 1 + d) ≤
        XiMomentCoeff (n + d) * XiMomentCoeff (n + 1)

/-- The fixed-gap target at gap `1` is exactly the contiguous `2 × 2`
Toeplitz/Turán inequality already proved from the contiguous ladder. -/
theorem xiMomentAdjacentRatioGap_one_of_contig :
    XiMomentAdjacentRatioGap 1 := by
  intro n hContig
  simpa [XiMomentAdjacentRatioGap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    xiMomentUnitRatioMonge_of_contig n hContig

/-- Successor-step target for gap propagation.

Once this is proved, the already-verified `d = 1` case inductively gives all
positive gaps and therefore the adjacent-ratio Monge target. -/
def XiMomentAdjacentRatioGapSuccBridge : Prop :=
  ∀ d : ℕ, 0 < d →
    XiMomentAdjacentRatioGap d → XiMomentAdjacentRatioGap (d + 1)

/-- Strict positivity plus the unit-gap Turán inequality proves the
gap-successor bridge.

The induction step combines the already-known gap-`d` inequality at base `n`
with the unit-gap inequality at base `n + d`, then cancels the shared positive
middle coefficient using `two_step_ratio_cancel`. -/
theorem xiMomentAdjacentRatioGapSuccBridge_of_strictPositivity
    (hPos : XiMomentCoeffPositive)
    (hUnit : XiMomentUnitRatioMongeFromContig) :
    XiMomentAdjacentRatioGapSuccBridge := by
  intro d hd hGap n hContig
  have hA : 0 ≤ XiMomentCoeff n := le_of_lt (hPos n)
  have hB : 0 ≤ XiMomentCoeff (n + d + 1) := le_of_lt (hPos (n + d + 1))
  have hC : 0 < XiMomentCoeff (n + d) := hPos (n + d)
  have hAB : XiMomentCoeff n * XiMomentCoeff (n + d + 1) ≤
      XiMomentCoeff (n + d) * XiMomentCoeff (n + 1) := by
    have h := hGap n hContig
    simpa [XiMomentAdjacentRatioGap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hCE : XiMomentCoeff (n + d) * XiMomentCoeff (n + d + 2) ≤
      XiMomentCoeff (n + d + 1) * XiMomentCoeff (n + d + 1) := by
    have h := hUnit (n + d) hContig
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have h := two_step_ratio_cancel hA hB hC hAB hCE
  simpa [XiMomentAdjacentRatioGap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A gap-successor bridge reduces arbitrary positive adjacent-ratio gaps to the
verified unit-gap contiguous `2 × 2` inequality. -/
theorem xiMomentAdjacentRatioMonge_of_gapSuccBridge
    (hBridge : XiMomentAdjacentRatioGapSuccBridge) :
    XiMomentAdjacentRatioMongeFromContig := by
  intro n d hd hContig
  cases d with
  | zero =>
      omega
  | succ d =>
      have hAllGaps : ∀ e : ℕ, XiMomentAdjacentRatioGap (e + 1) := by
        intro e
        induction e with
        | zero =>
            simpa using xiMomentAdjacentRatioGap_one_of_contig
        | succ e ih =>
            exact hBridge (e + 1) (Nat.succ_pos e) ih
      have hGap : XiMomentAdjacentRatioGap (Nat.succ d) := by
        simpa [Nat.succ_eq_add_one] using hAllGaps d
      exact hGap n hContig

/-- Propagation target: the proved unit-gap inequality should imply adjacent
ratio monotonicity for every positive gap.  This is the next nontrivial
sequence-theoretic step. -/
def XiUnitRatioToAdjacentRatioBridge : Prop :=
  XiMomentUnitRatioMongeFromContig → XiMomentAdjacentRatioMongeFromContig

/-- Positivity-aware propagation target from unit-gap ratio monotonicity to
arbitrary-gap adjacent ratio monotonicity.  This names the real algebraic
payload: unit log-concavity plus nonnegative coefficients should propagate to
all gap lengths. -/
def XiUnitRatioToAdjacentRatioWithPositivityBridge : Prop :=
  XiMomentCoeffNonnegativeFromContig →
    XiMomentUnitRatioMongeFromContig →
      XiMomentAdjacentRatioMongeFromContig

/-- Strict-positivity propagation target.  This is the cleaner analytic route:
Pólya's kernel gives strict positivity of every coefficient, and unit-gap
log-concavity should then propagate to all positive gaps. -/
def XiUnitRatioToAdjacentRatioWithStrictPositivityBridge : Prop :=
  XiMomentCoeffPositive →
    XiMomentUnitRatioMongeFromContig →
      XiMomentAdjacentRatioMongeFromContig

/-- The strict-positivity route is closed at the sequence-algebra level:
positive coefficients plus the unit-gap contiguous `2 × 2` inequality propagate
to all positive adjacent gaps. -/
theorem xiUnitRatioToAdjacentRatioWithStrictPositivityBridge_of_gapInduction :
    XiUnitRatioToAdjacentRatioWithStrictPositivityBridge := by
  intro hPos hUnit
  exact xiMomentAdjacentRatioMonge_of_gapSuccBridge
    (xiMomentAdjacentRatioGapSuccBridge_of_strictPositivity hPos hUnit)

/-- A strict-positivity propagation theorem plus Pólya's kernel representation
implies the unit-to-adjacent bridge. -/
theorem xiUnitRatioToAdjacentRatioBridge_of_strictPositivity
    (hRep : XiMomentKernelRep)
    (hBridge : XiUnitRatioToAdjacentRatioWithStrictPositivityBridge) :
    XiUnitRatioToAdjacentRatioBridge := by
  intro hUnit
  exact hBridge (xiMomentCoeffPositive_of_kernelRep hRep) hUnit

/-- Pólya's positive-kernel representation supplies the proved unit-to-adjacent
bridge without any additional propagation hypothesis. -/
theorem xiUnitRatioToAdjacentRatioBridge_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiUnitRatioToAdjacentRatioBridge := by
  intro hUnit
  exact xiUnitRatioToAdjacentRatioWithStrictPositivityBridge_of_gapInduction
    (xiMomentCoeffPositive_of_kernelRep hRep) hUnit

/-- The positivity-aware propagation theorem implies the earlier unit-to-adjacent
bridge because coefficient nonnegativity is already supplied by contiguous
`1 × 1` minors. -/
theorem xiUnitRatioToAdjacentRatioBridge_of_withPositivity
    (hBridge : XiUnitRatioToAdjacentRatioWithPositivityBridge) :
    XiUnitRatioToAdjacentRatioBridge := by
  intro hUnit
  exact hBridge xiMomentCoeffNonnegative_of_contig hUnit

/-- Unit-gap control plus its propagation bridge gives the adjacent-ratio
condition. -/
theorem xiMomentAdjacentRatioMonge_of_unitBridge
    (hUnit : XiMomentUnitRatioMongeFromContig)
    (hBridge : XiUnitRatioToAdjacentRatioBridge) :
    XiMomentAdjacentRatioMongeFromContig :=
  hBridge hUnit

/-- Kernel positivity plus contiguous `2 × 2` positivity gives all positive
adjacent ratio gaps.  The remaining sequence-level frontier after this theorem
is the adjacent-to-global ratio-Monge propagation. -/
theorem xiMomentAdjacentRatioMonge_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiMomentAdjacentRatioMongeFromContig :=
  xiMomentAdjacentRatioMonge_of_unitBridge
    xiMomentUnitRatioMonge_of_contig
    (xiUnitRatioToAdjacentRatioBridge_of_kernelRep hRep)

/-- Bundled unit-gap route to adjacent ratio monotonicity. -/
structure XiUnitRatioRoute where
  unit : XiMomentUnitRatioMongeFromContig
  propagate : XiUnitRatioToAdjacentRatioBridge

/-- The unit-gap route implies adjacent ratio monotonicity. -/
theorem xiMomentAdjacentRatioMonge_of_unitRoute
    (R : XiUnitRatioRoute) : XiMomentAdjacentRatioMongeFromContig :=
  xiMomentAdjacentRatioMonge_of_unitBridge R.unit R.propagate

/-- Propagation target: adjacent ratio monotonicity should imply the full
ratio-Monge inequality for all `a ≤ b`.  This is separated because chaining the
cross-multiplied inequalities requires positivity/control of intermediate
coefficients. -/
def XiAdjacentRatioToGlobalRatioBridge : Prop :=
  XiMomentAdjacentRatioMongeFromContig → XiMomentRatioMongeFromContig

/-- Fixed-distance form of the global ratio-Monge condition.

The distance `k` is `b - a`.  This turns the adjacent-to-global bridge into an
ordinary induction over the base-point distance. -/
def XiMomentRatioDistanceFromAdjacent (k : ℕ) : Prop :=
  ∀ (a d : ℕ),
    0 < d →
    XiContigToeplitzTotalPositive →
      XiMomentCoeff a * XiMomentCoeff (a + k + d) ≤
        XiMomentCoeff (a + d) * XiMomentCoeff (a + k)

/-- Distance `0` is immediate. -/
theorem xiMomentRatioDistance_zero :
    XiMomentRatioDistanceFromAdjacent 0 := by
  intro a d hd hContig
  simp [mul_comm]

/-- Adjacent ratio monotonicity plus strict positivity propagates the
distance-indexed ratio-Monge inequality from distance `k` to `k + 1`. -/
theorem xiMomentRatioDistance_succ_of_adjacent_strictPositivity
    (hPos : XiMomentCoeffPositive)
    (hAdj : XiMomentAdjacentRatioMongeFromContig)
    {k : ℕ}
    (hDist : XiMomentRatioDistanceFromAdjacent k) :
    XiMomentRatioDistanceFromAdjacent (k + 1) := by
  intro a d hd hContig
  have hB : 0 < XiMomentCoeff (a + 1 + d) := hPos (a + 1 + d)
  have hC : 0 < XiMomentCoeff (a + 1) := hPos (a + 1)
  have hD : 0 ≤ XiMomentCoeff (a + d) := le_of_lt (hPos (a + d))
  have hE : 0 ≤ XiMomentCoeff (a + k + 1 + d) :=
    le_of_lt (hPos (a + k + 1 + d))
  have hAB : XiMomentCoeff a * XiMomentCoeff (a + 1 + d) ≤
      XiMomentCoeff (a + 1) * XiMomentCoeff (a + d) := by
    have h := hAdj a d hd hContig
    nlinarith
  have hCE : XiMomentCoeff (a + 1) * XiMomentCoeff (a + k + 1 + d) ≤
      XiMomentCoeff (a + 1 + d) * XiMomentCoeff (a + k + 1) := by
    have h := hDist (a + 1) d hd hContig
    simpa [XiMomentRatioDistanceFromAdjacent, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  have h := two_step_ratio_cancel_general hB hC hD hE hAB hCE
  simpa [XiMomentRatioDistanceFromAdjacent, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

/-- Strict positivity closes the adjacent-to-global ratio-Monge bridge by
induction over the distance between the two bases. -/
theorem xiMomentRatioMonge_of_adjacentRatio_strictPositivity
    (hPos : XiMomentCoeffPositive)
    (hAdj : XiMomentAdjacentRatioMongeFromContig) :
    XiMomentRatioMongeFromContig := by
  intro a b d hab hd hContig
  have hAllDistances : ∀ k : ℕ, XiMomentRatioDistanceFromAdjacent k := by
    intro k
    induction k with
    | zero =>
        exact xiMomentRatioDistance_zero
    | succ k ih =>
        simpa [Nat.succ_eq_add_one] using
          xiMomentRatioDistance_succ_of_adjacent_strictPositivity hPos hAdj ih
  have hDist := hAllDistances (b - a) a d hd hContig
  have hb : a + (b - a) = b := Nat.add_sub_of_le hab
  simpa [XiMomentRatioDistanceFromAdjacent, hb, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hDist

/-- Positivity-aware form of the adjacent-to-global bridge. -/
def XiAdjacentRatioToGlobalRatioWithStrictPositivityBridge : Prop :=
  XiMomentCoeffPositive →
    XiMomentAdjacentRatioMongeFromContig →
      XiMomentRatioMongeFromContig

/-- The strict-positivity adjacent-to-global bridge is proved by distance
induction. -/
theorem xiAdjacentRatioToGlobalRatioWithStrictPositivityBridge_of_distanceInduction :
    XiAdjacentRatioToGlobalRatioWithStrictPositivityBridge :=
  xiMomentRatioMonge_of_adjacentRatio_strictPositivity

/-- Pólya's positive-kernel representation supplies the adjacent-to-global
bridge for the xi signed moment coefficients. -/
theorem xiAdjacentRatioToGlobalRatioBridge_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiAdjacentRatioToGlobalRatioBridge := by
  intro hAdj
  exact xiMomentRatioMonge_of_adjacentRatio_strictPositivity
    (xiMomentCoeffPositive_of_kernelRep hRep) hAdj

/-- Adjacent ratio monotonicity plus its propagation bridge gives the full
ratio-Monge target. -/
theorem xiMomentRatioMonge_of_adjacentRatioBridge
    (hAdj : XiMomentAdjacentRatioMongeFromContig)
    (hBridge : XiAdjacentRatioToGlobalRatioBridge) :
    XiMomentRatioMongeFromContig :=
  hBridge hAdj

/-- Pólya's positive-kernel representation and contiguous `2 × 2` positivity
give the full ratio-Monge condition for xi signed moments. -/
theorem xiMomentRatioMonge_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiMomentRatioMongeFromContig :=
  xiMomentRatioMonge_of_adjacentRatioBridge
    (xiMomentAdjacentRatioMonge_of_kernelRep hRep)
    (xiAdjacentRatioToGlobalRatioBridge_of_kernelRep hRep)

/-- Bundled adjacent-ratio route to the `2 × 2` full-support frontier. -/
structure XiAdjacentRatioRoute where
  adjacent : XiMomentAdjacentRatioMongeFromContig
  propagate : XiAdjacentRatioToGlobalRatioBridge

/-- The adjacent-ratio route implies the ratio-Monge condition. -/
theorem xiMomentRatioMonge_of_adjacentRatioRoute
    (R : XiAdjacentRatioRoute) : XiMomentRatioMongeFromContig :=
  xiMomentRatioMonge_of_adjacentRatioBridge R.adjacent R.propagate

/-- The ratio-Monge condition implies the four-index full-support `2 × 2`
gap inequality. -/
theorem xiMinorTwoGapInequalityFromContig_of_ratioMonge
    (hRatio : XiMomentRatioMongeFromContig) :
    XiMinorTwoGapInequalityFromContig := by
  intro r0 r1 c0 c1 hr hc hfull hContig
  let a := r0 - c1
  let b := r1 - c1
  let d := c1 - c0
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hab : a ≤ b := by
    dsimp [a, b]
    omega
  have h := hRatio a b d hab hd hContig
  have haD : a + d = r0 - c0 := by
    dsimp [a, d]
    omega
  have hbD : b + d = r1 - c0 := by
    dsimp [b, d]
    omega
  dsimp [a, b] at h
  rw [haD, hbD] at h
  exact h

/-- Pólya's positive-kernel representation supplies the four-index
full-support `2 × 2` gap inequality. -/
theorem xiMinorTwoGapInequalityFromContig_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiMinorTwoGapInequalityFromContig :=
  xiMinorTwoGapInequalityFromContig_of_ratioMonge
    (xiMomentRatioMonge_of_kernelRep hRep)

/-- The explicit four-index inequality implies the determinant-form
full-support `2 × 2` target. -/
theorem xiMinorTwoFullSupportFromContig_of_gapInequality
    (hGap : XiMinorTwoGapInequalityFromContig) :
    XiMinorTwoFullSupportFromContig := by
  intro rows cols hRows hCols hSupport hContig
  have hr : rows 0 < rows 1 := hRows (by decide : (0 : Fin 2) < 1)
  have hc : cols 0 < cols 1 := hCols (by decide : (0 : Fin 2) < 1)
  have hfull : cols 1 ≤ rows 0 := hSupport 0 1
  have hineq := hGap (rows 0) (rows 1) (cols 0) (cols 1) hr hc hfull hContig
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  rw [xiToeplitzEntry_sub (rows 0) (cols 0) (hSupport 0 0),
      xiToeplitzEntry_sub (rows 1) (cols 1) (hSupport 1 1),
      xiToeplitzEntry_sub (rows 0) (cols 1) (hSupport 0 1),
      xiToeplitzEntry_sub (rows 1) (cols 0) (hSupport 1 0)]
  linarith

/-- Pólya's positive-kernel representation supplies the full-support `2 × 2`
certificate target. -/
theorem xiMinorTwoFullSupportFromContig_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiMinorTwoFullSupportFromContig :=
  xiMinorTwoFullSupportFromContig_of_gapInequality
    (xiMinorTwoGapInequalityFromContig_of_kernelRep hRep)

/-- A full-support `2 × 2` theorem target supplies local certificates for every
full-support `2 × 2` arbitrary minor. -/
def xiMinorTwoFullSupportCertificate
    (hFull : XiMinorTwoFullSupportFromContig)
    (rows cols : Fin 2 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin 2, cols b ≤ rows a) :
    XiMinorContigCertificate 2 rows cols hRows hCols where
  certificate := ∀ a b : Fin 2, cols b ≤ rows a
  proof := hSupport
  nonneg := by
    intro hSupp hContig
    exact hFull rows cols hRows hCols hSupp hContig

/-- The full-support `2 × 2` target gives certificates for every full-support
`2 × 2` pattern.  Proving `XiMinorTwoFullSupportFromContig` is therefore the
next named condition in the certificate loop. -/
theorem exists_xiMinorTwoFullSupportCertificate
    (hFull : XiMinorTwoFullSupportFromContig)
    (rows cols : Fin 2 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin 2, cols b ≤ rows a) :
    Nonempty (XiMinorContigCertificate 2 rows cols hRows hCols) :=
  ⟨xiMinorTwoFullSupportCertificate hFull rows cols hRows hCols hSupport⟩

/-- Pólya's positive-kernel representation supplies certificates for every
arbitrary `2 × 2` Toeplitz minor.

There are only two cases.  If the upper-right entry is above support, use the
upper-right-zero certificate.  Otherwise `cols 1 ≤ rows 0`; by strict row and
column monotonicity this implies full lower-triangular support for all four
entries, and the kernel-backed full-support theorem applies. -/
theorem exists_xiMinorTwoContigCertificate_of_kernelRep
    (hRep : XiMomentKernelRep)
    (rows cols : Fin 2 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols) :
    Nonempty (XiMinorContigCertificate 2 rows cols hRows hCols) := by
  by_cases hUR : rows 0 < cols 1
  · exact exists_xiMinorTwoUpperRightZeroCertificate rows cols hRows hCols hUR
  · have hSupport : ∀ a b : Fin 2, cols b ≤ rows a := by
      intro a b
      have hc : cols 0 < cols 1 := hCols (by decide : (0 : Fin 2) < 1)
      have hr : rows 0 < rows 1 := hRows (by decide : (0 : Fin 2) < 1)
      have h10 : cols 1 ≤ rows 0 := by omega
      fin_cases a
      · fin_cases b
        · exact le_trans (le_of_lt hc) h10
        · exact h10
      · fin_cases b
        · exact le_trans (le_trans (le_of_lt hc) h10) (le_of_lt hr)
        · exact le_trans h10 (le_of_lt hr)
    exact exists_xiMinorTwoFullSupportCertificate
      (xiMinorTwoFullSupportFromContig_of_kernelRep hRep)
      rows cols hRows hCols hSupport

/-- The exact remaining arbitrary-minor certificate frontier after sizes
`0`, `1`, and `2` have been closed.

This is now the right loop target for the full PF upgrade: prove certificates
only for minors of size at least `3`. -/
def XiAllMinorGeThreeContigCertificates : Prop :=
  ∀ (k : ℕ), 3 ≤ k →
    ∀ (rows cols : Fin k → ℕ)
      (hRows : StrictMono rows) (hCols : StrictMono cols),
        Nonempty (XiMinorContigCertificate k rows cols hRows hCols)

/-- The first remaining arbitrary-minor frontier after sizes `0`, `1`, and `2`
have been closed: all `3 × 3` certificates. -/
def XiMinorThreeContigCertificates : Prop :=
  ∀ (rows cols : Fin 3 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      Nonempty (XiMinorContigCertificate 3 rows cols hRows hCols)

/-- The tail frontier after the first unsolved `3 × 3` rung. -/
def XiAllMinorGeFourContigCertificates : Prop :=
  ∀ (k : ℕ), 4 ≤ k →
    ∀ (rows cols : Fin k → ℕ)
      (hRows : StrictMono rows) (hCols : StrictMono cols),
        Nonempty (XiMinorContigCertificate k rows cols hRows hCols)

/-- A solved `3 × 3` certificate theory plus the `k ≥ 4` tail is exactly enough
to recover the previous `k ≥ 3` frontier. -/
theorem xiAllMinorGeThree_of_three_and_geFour
    (hThree : XiMinorThreeContigCertificates)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiAllMinorGeThreeContigCertificates := by
  intro k hk rows cols hRows hCols
  by_cases hk3 : k = 3
  · subst k
    exact hThree rows cols hRows hCols
  have hk4 : 4 ≤ k := by omega
  exact hGeFour k hk4 rows cols hRows hCols

/-- Kernel representation plus the size-`≥ 3` certificate theorem supplies the
uniform certificate family for all arbitrary minors. -/
theorem xiAllMinorContigCertificates_of_kernelRep_and_geThree
    (hRep : XiMomentKernelRep)
    (hGeThree : XiAllMinorGeThreeContigCertificates) :
    XiAllMinorContigCertificates := by
  intro k rows cols hRows hCols
  by_cases hk0 : k = 0
  · subst k
    exact exists_xiMinorZeroContigCertificate rows cols hRows hCols
  by_cases hk1 : k = 1
  · subst k
    exact exists_xiMinorOneContigCertificate rows cols hRows hCols
  by_cases hk2 : k = 2
  · subst k
    exact exists_xiMinorTwoContigCertificate_of_kernelRep hRep rows cols hRows hCols
  have hk3 : 3 ≤ k := by omega
  exact hGeThree k hk3 rows cols hRows hCols

/-- Local certificates imply the arbitrary-minor reduction condition. -/
theorem arbitraryMinorReduction_of_allMinorContigCertificates
    (h : XiAllMinorContigCertificates) : XiArbitraryMinorReductionToContig := by
  intro k rows cols hRows hCols hContig
  rcases h k rows cols hRows hCols with ⟨cert⟩
  exact cert.nonneg cert.proof hContig

/-- The local arbitrary-minor reduction is exactly enough to produce the global
contiguous-to-full PF bridge. -/
theorem xiContigToFullPFBridge_of_arbitraryMinorReduction
    (h : XiArbitraryMinorReductionToContig) : XiContigToFullPFBridge := by
  intro hContig k rows cols hRows hCols
  exact h k rows cols hRows hCols hContig

/-- Therefore, a uniform certificate theory also gives the global
contiguous-to-full PF bridge. -/
theorem xiContigToFullPFBridge_of_allMinorContigCertificates
    (h : XiAllMinorContigCertificates) : XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_arbitraryMinorReduction
    (arbitraryMinorReduction_of_allMinorContigCertificates h)

/-- Kernel representation plus certificates for only sizes `≥ 3` is enough to
produce the full contiguous-to-arbitrary PF bridge, because sizes `0`, `1`, and
`2` are now covered separately. -/
theorem xiContigToFullPFBridge_of_kernelRep_and_geThree
    (hRep : XiMomentKernelRep)
    (hGeThree : XiAllMinorGeThreeContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_allMinorContigCertificates
    (xiAllMinorContigCertificates_of_kernelRep_and_geThree hRep hGeThree)

/-- Kernel representation plus the split `3 × 3` and `k ≥ 4` certificate
frontiers is enough to produce the full contiguous-to-arbitrary PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_three_and_geFour
    (hRep : XiMomentKernelRep)
    (hThree : XiMinorThreeContigCertificates)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_and_geThree hRep
    (xiAllMinorGeThree_of_three_and_geFour hThree hGeFour)

/-- Conversely, a global contiguous-to-full bridge supplies the local reduction
for every arbitrary minor. -/
theorem arbitraryMinorReduction_of_xiContigToFullPFBridge
    (h : XiContigToFullPFBridge) : XiArbitraryMinorReductionToContig := by
  intro k rows cols hRows hCols hContig
  exact h hContig k rows cols hRows hCols

/-- The global bridge and the local arbitrary-minor reduction are equivalent
ways to state the same missing proof step. -/
theorem xiContigToFullPFBridge_iff_arbitraryMinorReduction :
    XiContigToFullPFBridge ↔ XiArbitraryMinorReductionToContig :=
  ⟨arbitraryMinorReduction_of_xiContigToFullPFBridge,
    xiContigToFullPFBridge_of_arbitraryMinorReduction⟩

/-- A bundled theorem target for the combinatorial/planar-network route:
prove every contiguous kernel determinant and prove the xi-specific upgrade
from contiguous minors to arbitrary minors. -/
structure KernelContigToPFTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  upgrade : XiContigToFullPFBridge

/-- Sharper bundled theorem target after closing all arbitrary minors of size
at most `2`: prove contiguous kernel positivity and only the `k ≥ 3`
certificate frontier. -/
structure KernelContigToPFGeThreeTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  geThree : XiAllMinorGeThreeContigCertificates

/-- Even sharper theorem target: prove the first remaining `3 × 3` rung and
the `k ≥ 4` tail separately. -/
structure KernelContigToPFThreeAndGeFourTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  three : XiMinorThreeContigCertificates
  geFour : XiAllMinorGeFourContigCertificates

/-- The sharper `k ≥ 3` theorem target produces the older level-2.5 target. -/
def kernelContigToPF_of_geThree
    (T : KernelContigToPFGeThreeTheorem) : KernelContigToPFTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  upgrade :=
    xiContigToFullPFBridge_of_kernelRep_and_geThree
      ⟨T.M, T.positive, T.kernelRep⟩ T.geThree

/-- The split `3 × 3` plus `k ≥ 4` target produces the `k ≥ 3` target. -/
def kernelContigToPFGeThree_of_three_and_geFour
    (T : KernelContigToPFThreeAndGeFourTheorem) :
    KernelContigToPFGeThreeTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  geThree := xiAllMinorGeThree_of_three_and_geFour T.three T.geFour

/-- The level-2.5 theorem target produces the full PF condition. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPF
    (T : KernelContigToPFTheorem) : XiToeplitzTotalPositive :=
  T.upgrade ((xiContigToeplitzTotalPositive_iff_kernelContig T.kernelRep).mpr T.contig)

/-- The sharper `k ≥ 3` target also produces the full PF condition. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFGeThree
    (T : KernelContigToPFGeThreeTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPF
    (kernelContigToPF_of_geThree T)

/-- The split `3 × 3` plus `k ≥ 4` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour
    (T : KernelContigToPFThreeAndGeFourTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFGeThree
    (kernelContigToPFGeThree_of_three_and_geFour T)

/-- Kernel-contiguous positivity plus the contiguous-to-full upgrade closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPF
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPF T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the `k ≥ 3` certificate frontier closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFGeThree
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFGeThreeTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFGeThree T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the split `3 × 3` and `k ≥ 4`
certificate frontiers closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeAndGeFour
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeAndGeFourTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour T)
    S.asw S.lp S.polyaJensen

/-! ## Level 3: full arbitrary-minor PF positivity, the RH-closing target -/

/-- Algebraic-geometry / Weil-Hodge route to the full PF condition. -/
structure WeilHodgePFWitness where
  model : Prop
  proof : model
  pf : model → XiToeplitzTotalPositive

/-- Combinatorial Hodge / Lorentzian / lattice-path route to full PF. -/
structure CombinatorialPFWitness where
  model : Prop
  proof : model
  pf : model → XiToeplitzTotalPositive

/-- Euclidean convexity route to full PF. -/
structure EuclideanConvexityPFWitness where
  model : Prop
  proof : model
  pf : model → XiToeplitzTotalPositive

/-- Hyperbolic / non-Euclidean spectral route to full PF. -/
structure HyperbolicSpectralPFWitness where
  model : Prop
  proof : model
  pf : model → XiToeplitzTotalPositive

/-- Any successful full-strength cross-field theory must produce the same
arbitrary-minor Pólya-frequency condition for the signed xi coefficients. -/
def CrossFieldPFWitness : Prop :=
  Nonempty WeilHodgePFWitness ∨
  Nonempty CombinatorialPFWitness ∨
  Nonempty EuclideanConvexityPFWitness ∨
  Nonempty HyperbolicSpectralPFWitness

/-- Extract full PF positivity from any full-strength cross-field witness. -/
theorem xiToeplitzTotalPositive_of_crossFieldPFWitness
    (w : CrossFieldPFWitness) : XiToeplitzTotalPositive := by
  rcases w with hW | hC | hE | hH
  · rcases hW with ⟨wW⟩
    exact wW.pf wW.proof
  · rcases hC with ⟨wC⟩
    exact wC.pf wC.proof
  · rcases hE with ⟨wE⟩
    exact wE.pf wE.proof
  · rcases hH with ⟨wH⟩
    exact wH.pf wH.proof

/-- The exact success theorem for the current program.  Once a cross-field
theory proves full PF positivity, the existing classical Toeplitz scaffolding
closes RH. -/
theorem riemannHypothesis_of_crossFieldPFWitness
    (S : ClassicalToeplitzScaffolding)
    (w : CrossFieldPFWitness) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_crossFieldPFWitness w)
    S.asw S.lp S.polyaJensen

/-- Conversely, under the same classical scaffolding, a full cross-field PF
witness is exactly an RH-strength object: it supplies a condition equivalent in
strength to `RiemannHypothesis`. -/
theorem crossFieldPFWitness_implies_rh_equiv_target
    (S : ClassicalToeplitzScaffolding)
    (w : CrossFieldPFWitness) :
    RiemannHypothesis :=
  (riemannHypothesis_iff_pf_of_scaffolding S).mpr
    (xiToeplitzTotalPositive_of_crossFieldPFWitness w)

end Reinmann

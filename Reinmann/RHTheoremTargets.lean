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

/-- A subtraction-free certificate in contiguous Toeplitz minors.

Each summand has a natural-number coefficient times a finite product of
contiguous minors. This is the concrete output expected from a Cauchy-Binet or
planar-network derivation, and is stronger than merely asserting the target
quantity is nonnegative. -/
def XiContigMinorPositivePolynomial (x : ℝ) : Prop :=
  ∃ (N : ℕ) (coeff : Fin N → ℕ) (factors : Fin N → List (ℕ × ℕ)),
    x = ∑ i, (coeff i : ℝ) *
      ((factors i).map (fun km => XiToeplitzContigMinor km.1 km.2)).prod

/-- Every subtraction-free polynomial in contiguous minors is nonnegative
under the contiguous positivity ladder. -/
theorem xiContigMinorPositivePolynomial_nonneg
    (hContig : XiContigToeplitzTotalPositive) {x : ℝ}
    (hPolynomial : XiContigMinorPositivePolynomial x) :
    0 ≤ x := by
  rcases hPolynomial with ⟨N, coeff, factors, hEq⟩
  rw [hEq]
  refine Finset.sum_nonneg ?_
  intro i hi
  apply mul_nonneg (Nat.cast_nonneg _)
  apply List.prod_nonneg
  intro y hy
  rcases List.mem_map.mp hy with ⟨km, hkm, rfl⟩
  exact hContig km.1 km.2

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

/-- Toeplitz entries are invariant under a common translation of row and
column indices. -/
theorem xiToeplitzEntry_add_left (q i j : ℕ) :
    XiToeplitzEntry (q + i) (q + j) = XiToeplitzEntry i j := by
  by_cases hij : j ≤ i
  · rw [xiToeplitzEntry_sub (q + i) (q + j) (by omega),
      xiToeplitzEntry_sub i j hij]
    simp only [Nat.add_sub_add_left]
  · unfold XiToeplitzEntry
    rw [if_neg hij, if_neg (by omega)]

/-- Sequence-level nonnegativity supplied by contiguous `1 × 1` minors. -/
def XiMomentCoeffNonnegativeFromContig : Prop :=
  ∀ n : ℕ, XiContigToeplitzTotalPositive → 0 ≤ XiMomentCoeff n

/-- Sequence-level strict positivity, kept separate from contiguous positivity.
It is supplied by Pólya's positive kernel representation, not by nonnegative
Toeplitz minors alone. -/
def XiMomentCoeffPositive : Prop :=
  ∀ n : ℕ, 0 < XiMomentCoeff n

/-- Total nonnegativity of all Toeplitz minors whose columns are the initial
consecutive interval `0, ..., k - 1`; only the rows remain arbitrary. -/
def XiInitialColumnMinorTotalPositive : Prop :=
  ∀ (k : ℕ) (rows : Fin k → ℕ),
    StrictMono rows →
      0 ≤ (Matrix.of (fun i j : Fin k => XiToeplitzEntry (rows i) j.val)).det

/-- The Xi-specific bridge from the contiguous ladder to arbitrary-row,
initial-column minors. This is strictly more focused than the old
contiguous-to-all-minors bridge. -/
def XiContigToInitialColumnMinorBridge : Prop :=
  XiContigToeplitzTotalPositive → XiInitialColumnMinorTotalPositive

/-- The order-two part of the initial-column lift: arbitrary increasing rows,
with the fixed columns `0, 1`. -/
def XiInitialColumnMinorTwoFromContig : Prop :=
  ∀ (rows : Fin 2 → ℕ),
    StrictMono rows →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun i j : Fin 2 => XiToeplitzEntry (rows i) j.val)).det

/-- The remaining initial-column lift after the solved orders zero, one, and
two: arbitrary increasing rows at every order `k >= 3`. -/
def XiInitialColumnMinorGeThreeFromContig : Prop :=
  ∀ (k : ℕ), 3 ≤ k →
    ∀ (rows : Fin k → ℕ),
      StrictMono rows →
      XiContigToeplitzTotalPositive →
        0 ≤ (Matrix.of (fun i j : Fin k => XiToeplitzEntry (rows i) j.val)).det

/-- The order-three part of the initial-column lift: arbitrary increasing rows,
with the fixed columns `0, 1, 2`. -/
def XiInitialColumnMinorThreeFromContig : Prop :=
  ∀ (rows : Fin 3 → ℕ),
    StrictMono rows →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun i j : Fin 3 => XiToeplitzEntry (rows i) j.val)).det

/-- The higher initial-column lift after orders at most three are discharged. -/
def XiInitialColumnMinorGeFourFromContig : Prop :=
  ∀ (k : ℕ), 4 ≤ k →
    ∀ (rows : Fin k → ℕ),
      StrictMono rows →
      XiContigToeplitzTotalPositive →
        0 ≤ (Matrix.of (fun i j : Fin k => XiToeplitzEntry (rows i) j.val)).det

/-- Lower-triangular initial-column criterion as an explicit bridge contract.

For a positive-diagonal lower-triangular matrix, Cryer's criterion reduces total
nonnegativity to minors with consecutive initial columns. Formalizing that
finite-dimensional theorem and applying it to all truncations would discharge
this contract. -/
def XiInitialColumnMinorToFullPFBridge : Prop :=
  XiMomentCoeffPositive →
    XiInitialColumnMinorTotalPositive → XiToeplitzTotalPositive

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

/-- The initial-column bridge and lower-triangular criterion compose to the
existing contiguous-to-full PF bridge. -/
theorem xiContigToFullPFBridge_of_initialColumn
    (hInitial : XiContigToInitialColumnMinorBridge)
    (hCriterion : XiInitialColumnMinorToFullPFBridge)
    (hPos : XiMomentCoeffPositive) :
    XiContigToFullPFBridge := by
  intro hContig
  exact hCriterion hPos (hInitial hContig)

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

/-- Pólya's positive-kernel representation closes the order-two
initial-column lift for arbitrary increasing rows. -/
theorem xiInitialColumnMinorTwoFromContig_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiInitialColumnMinorTwoFromContig := by
  intro rows hRows hContig
  let cols : Fin 2 → ℕ := fun j => j.val
  have hCols : StrictMono cols := strictMono_fin_val 2
  rcases exists_xiMinorTwoContigCertificate_of_kernelRep hRep rows cols hRows hCols with
    ⟨certificate⟩
  simpa [cols] using certificate.nonneg certificate.proof hContig

/-- Orders zero and one, together with the order-two initial-column base,
reduce the whole initial-column lift to the `k >= 3` condition. -/
theorem xiContigToInitialColumnMinorBridge_of_two_and_geThree
    (hTwo : XiInitialColumnMinorTwoFromContig)
    (hGeThree : XiInitialColumnMinorGeThreeFromContig) :
    XiContigToInitialColumnMinorBridge := by
  intro hContig k rows hRows
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk1 : k = 1
  · subst k
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply, Fin.val_zero]
    exact xiToeplitzEntry_nonneg_of_contig hContig (rows 0) 0
  by_cases hk2 : k = 2
  · subst k
    exact hTwo rows hRows hContig
  have hk3 : 3 ≤ k := by omega
  exact hGeThree k hk3 rows hRows hContig

/-- With Pólya's positive kernel, the initial-column bridge has only the
order-`k >= 3` arbitrary-row payload left to prove. -/
theorem xiContigToInitialColumnMinorBridge_of_kernelRep_and_geThree
    (hRep : XiMomentKernelRep)
    (hGeThree : XiInitialColumnMinorGeThreeFromContig) :
    XiContigToInitialColumnMinorBridge :=
  xiContigToInitialColumnMinorBridge_of_two_and_geThree
    (xiInitialColumnMinorTwoFromContig_of_kernelRep hRep) hGeThree

/-- The full-support `3 × 3` Toeplitz certificate target.

This isolates the first genuinely new determinant problem after the `2 × 2`
case: every selected column is inside lower-triangular support for every
selected row, so no row/column vanishing argument applies. -/
def XiMinorThreeFullSupportFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    (∀ a b : Fin 3, cols b ≤ rows a) →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- Moment-index form of the full-support `3 × 3` target.

Under full lower-triangular support, every Toeplitz entry is exactly the signed
xi moment coefficient at gap `row - col`.  This names the cleaner algebraic
payload, separated from support bookkeeping. -/
def XiMinorThreeFullSupportMomentFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    (∀ a b : Fin 3, cols b ≤ rows a) →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiMomentCoeff (rows a - cols b))).det

/-- The moment-index full-support target implies the Toeplitz-entry
full-support target. -/
theorem xiMinorThreeFullSupportFromContig_of_moment
    (hMoment : XiMinorThreeFullSupportMomentFromContig) :
    XiMinorThreeFullSupportFromContig := by
  intro rows cols hRows hCols hSupport hContig
  have h := hMoment rows cols hRows hCols hSupport hContig
  rw [Matrix.det_fin_three]
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply] at h ⊢
  rw [xiToeplitzEntry_sub (rows 0) (cols 0) (hSupport 0 0),
      xiToeplitzEntry_sub (rows 0) (cols 1) (hSupport 0 1),
      xiToeplitzEntry_sub (rows 0) (cols 2) (hSupport 0 2),
      xiToeplitzEntry_sub (rows 1) (cols 0) (hSupport 1 0),
      xiToeplitzEntry_sub (rows 1) (cols 1) (hSupport 1 1),
      xiToeplitzEntry_sub (rows 1) (cols 2) (hSupport 1 2),
      xiToeplitzEntry_sub (rows 2) (cols 0) (hSupport 2 0),
      xiToeplitzEntry_sub (rows 2) (cols 1) (hSupport 2 1),
      xiToeplitzEntry_sub (rows 2) (cols 2) (hSupport 2 2)]
  exact h

/-- A full-support `3 × 3` theorem target supplies local certificates for every
full-support `3 × 3` arbitrary minor. -/
def xiMinorThreeFullSupportCertificate
    (hFull : XiMinorThreeFullSupportFromContig)
    (rows cols : Fin 3 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin 3, cols b ≤ rows a) :
    XiMinorContigCertificate 3 rows cols hRows hCols where
  certificate := ∀ a b : Fin 3, cols b ≤ rows a
  proof := hSupport
  nonneg := by
    intro hSupp hContig
    exact hFull rows cols hRows hCols hSupp hContig

/-- The full-support `3 × 3` target gives certificates for every full-support
`3 × 3` pattern. -/
theorem exists_xiMinorThreeFullSupportCertificate
    (hFull : XiMinorThreeFullSupportFromContig)
    (rows cols : Fin 3 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin 3, cols b ≤ rows a) :
    Nonempty (XiMinorContigCertificate 3 rows cols hRows hCols) :=
  ⟨xiMinorThreeFullSupportCertificate hFull rows cols hRows hCols hSupport⟩

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

/-- The remaining mixed-support `3 × 3` frontier.

This covers `3 × 3` patterns that are not full-support but also do not have an
immediate zero row or zero column.  It is separated from full support because
the proof mechanism should be more combinatorial/sparse: expansion,
block-triangular reduction, or Cauchy-Binet certificates. -/
def XiMinorThreeMixedSupportCertificates : Prop :=
  ∀ (rows cols : Fin 3 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      (¬ ∃ a : Fin 3, ∀ b : Fin 3, rows a < cols b) →
      (¬ ∃ b : Fin 3, ∀ a : Fin 3, rows a < cols b) →
      (¬ ∀ a b : Fin 3, cols b ≤ rows a) →
        Nonempty (XiMinorContigCertificate 3 rows cols hRows hCols)

/-- Banded mixed-support `3 × 3` frontier.

For strictly monotone `3 × 3` row/column patterns, the mixed-support case with
no zero row and no zero column reduces to this band condition:

* the lower-left edge is supported: `cols 0 ≤ rows 0`;
* the upper-right entry is missing: `rows 0 < cols 2`;
* the lower-right edge is supported: `cols 2 ≤ rows 2`.

This is the first sparse `3 × 3` pattern class to attack directly. -/
def XiMinorThreeBandedMixedSupportCertificates : Prop :=
  ∀ (rows cols : Fin 3 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      cols 0 ≤ rows 0 →
      rows 0 < cols 2 →
      cols 2 ≤ rows 2 →
        Nonempty (XiMinorContigCertificate 3 rows cols hRows hCols)

/-- Determinant inequality form of the banded mixed-support `3 × 3` frontier.

This removes the certificate wrapper and exposes the exact sparse determinant
nonnegativity statement that remains to prove from the contiguous ladder. -/
def XiMinorThreeBandedDetInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- Expanded sparse determinant form of the banded mixed-support `3 × 3`
frontier.

The band condition forces the upper-right entry `T(rows 0, cols 2)` to vanish,
so the `3 × 3` determinant reduces to the four-term expression below.  This is
the next algebraic condition to attack before translating everything into
moment-index inequalities. -/
def XiMinorThreeBandedExpandedInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 0) (cols 0) *
          (XiToeplitzEntry (rows 1) (cols 1) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 1))
        - XiToeplitzEntry (rows 0) (cols 1) *
          (XiToeplitzEntry (rows 1) (cols 0) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 0))

/-- Middle-supported moment-index form of the banded mixed-support `3 × 3`
frontier.

The general banded pattern only forces `T00`, `T22`, and `T02 = 0`; some middle
entries can still vanish.  This condition isolates the dense part of the band
where `T01` and `T12` are also supported, so every surviving entry rewrites to a
signed xi moment coefficient. -/
def XiMinorThreeBandedMiddleMomentInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 1 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiMomentCoeff (rows 0 - cols 0) *
          (XiMomentCoeff (rows 1 - cols 1) *
              XiMomentCoeff (rows 2 - cols 2)
            - XiMomentCoeff (rows 1 - cols 2) *
              XiMomentCoeff (rows 2 - cols 1))
        - XiMomentCoeff (rows 0 - cols 1) *
          (XiMomentCoeff (rows 1 - cols 0) *
              XiMomentCoeff (rows 2 - cols 2)
            - XiMomentCoeff (rows 1 - cols 2) *
              XiMomentCoeff (rows 2 - cols 0))

/-- Compound-ratio form of the middle-supported banded `3 × 3` moment target.

This isolates the real next algebraic payload: the left column ratio
`μ(r₀-c₁) / μ(r₀-c₀)` should be dominated by the corresponding ratio of
adjacent `2 × 2` compound minors.  Written without division, it is exactly the
cross-product inequality below. -/
def XiMinorThreeBandedMiddleCompoundRatioFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 1 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      XiMomentCoeff (rows 0 - cols 1) *
          (XiMomentCoeff (rows 1 - cols 0) *
              XiMomentCoeff (rows 2 - cols 2)
            - XiMomentCoeff (rows 1 - cols 2) *
              XiMomentCoeff (rows 2 - cols 0))
        ≤
        XiMomentCoeff (rows 0 - cols 0) *
          (XiMomentCoeff (rows 1 - cols 1) *
              XiMomentCoeff (rows 2 - cols 2)
            - XiMomentCoeff (rows 1 - cols 2) *
              XiMomentCoeff (rows 2 - cols 1))

/-- Unified moment-index `3 × 3` payload.

This packages the two remaining explicit `3 × 3` moment conditions into one
target: full-support moment determinant positivity and the banded middle
compound-ratio inequality. -/
def XiMinorThreeMomentPayloadFromContig : Prop :=
  XiMinorThreeFullSupportMomentFromContig ∧
    XiMinorThreeBandedMiddleCompoundRatioFromContig

/-- The unified moment payload supplies the full-support moment target. -/
theorem xiMinorThreeFullSupportMoment_of_momentPayload
    (hPayload : XiMinorThreeMomentPayloadFromContig) :
    XiMinorThreeFullSupportMomentFromContig :=
  hPayload.1

/-- The unified moment payload supplies the middle compound-ratio target. -/
theorem xiMinorThreeBandedMiddleCompoundRatio_of_momentPayload
    (hPayload : XiMinorThreeMomentPayloadFromContig) :
    XiMinorThreeBandedMiddleCompoundRatioFromContig :=
  hPayload.2

/-- The compound-ratio target is exactly strong enough to imply the
middle-supported banded moment inequality. -/
theorem xiMinorThreeBandedMiddleMoment_of_compoundRatio
    (hCompound : XiMinorThreeBandedMiddleCompoundRatioFromContig) :
    XiMinorThreeBandedMiddleMomentInequalityFromContig := by
  intro rows cols hRows hCols hLeft h01 hGap h12 hRight hContig
  have h := hCompound rows cols hRows hCols hLeft h01 hGap h12 hRight hContig
  linarith

/-- The middle-supported moment-index banded inequality implies the expanded
Toeplitz-entry banded inequality on that support class. -/
theorem xiMinorThreeBandedExpandedInequality_of_middleMoment
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig) :
    ∀ (rows cols : Fin 3 → ℕ),
      StrictMono rows → StrictMono cols →
      cols 0 ≤ rows 0 →
      cols 1 ≤ rows 0 →
      rows 0 < cols 2 →
      cols 2 ≤ rows 1 →
      cols 2 ≤ rows 2 →
      XiContigToeplitzTotalPositive →
        0 ≤
          XiToeplitzEntry (rows 0) (cols 0) *
            (XiToeplitzEntry (rows 1) (cols 1) *
                XiToeplitzEntry (rows 2) (cols 2)
              - XiToeplitzEntry (rows 1) (cols 2) *
                XiToeplitzEntry (rows 2) (cols 1))
          - XiToeplitzEntry (rows 0) (cols 1) *
            (XiToeplitzEntry (rows 1) (cols 0) *
                XiToeplitzEntry (rows 2) (cols 2)
              - XiToeplitzEntry (rows 1) (cols 2) *
                XiToeplitzEntry (rows 2) (cols 0)) := by
  intro rows cols hRows hCols hLeft h01 hGap h12 hRight hContig
  have hRows01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 3) < 1)
  have hRows12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 3) < 2)
  have h11 : cols 1 ≤ rows 1 := le_trans h01 (le_of_lt hRows01)
  have h20 : cols 0 ≤ rows 2 :=
    le_trans hLeft (le_of_lt (lt_trans hRows01 hRows12))
  have h21 : cols 1 ≤ rows 2 :=
    le_trans h11 (le_of_lt hRows12)
  have h10 : cols 0 ≤ rows 1 := le_trans hLeft (le_of_lt hRows01)
  have h := hMoment rows cols hRows hCols hLeft h01 hGap h12 hRight hContig
  rw [xiToeplitzEntry_sub (rows 0) (cols 0) hLeft,
      xiToeplitzEntry_sub (rows 1) (cols 1) h11,
      xiToeplitzEntry_sub (rows 2) (cols 2) hRight,
      xiToeplitzEntry_sub (rows 1) (cols 2) h12,
      xiToeplitzEntry_sub (rows 2) (cols 1) h21,
      xiToeplitzEntry_sub (rows 0) (cols 1) h01,
      xiToeplitzEntry_sub (rows 1) (cols 0) h10,
      xiToeplitzEntry_sub (rows 2) (cols 0) h20]
  exact h

/-- Edge case where the `T01` entry vanishes in the banded `3 × 3` determinant:
`rows 0 < cols 1`. -/
def XiMinorThreeBandedT01ZeroInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 1 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 0) (cols 0) *
          (XiToeplitzEntry (rows 1) (cols 1) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 1))
        - XiToeplitzEntry (rows 0) (cols 1) *
          (XiToeplitzEntry (rows 1) (cols 0) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 0))

/-- Edge case where the `T12` entry vanishes in the banded `3 × 3` determinant:
`rows 1 < cols 2`, while `T01` is still supported. -/
def XiMinorThreeBandedT12ZeroInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    rows 1 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 0) (cols 0) *
          (XiToeplitzEntry (rows 1) (cols 1) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 1))
        - XiToeplitzEntry (rows 0) (cols 1) *
          (XiToeplitzEntry (rows 1) (cols 0) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 0))

/-- Simplified form of the `T01 = 0` edge case.  Since the second large term is
multiplied by the vanished `T01`, only the leading product remains. -/
def XiMinorThreeBandedT01ZeroSimplifiedFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 1 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 0) (cols 0) *
          (XiToeplitzEntry (rows 1) (cols 1) *
              XiToeplitzEntry (rows 2) (cols 2)
            - XiToeplitzEntry (rows 1) (cols 2) *
              XiToeplitzEntry (rows 2) (cols 1))

/-- Simplified form of the `T12 = 0` edge case.  The products involving `T12`
vanish, leaving one two-product difference multiplied by `T22`. -/
def XiMinorThreeBandedT12ZeroSimplifiedFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    rows 1 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 2) (cols 2) *
          (XiToeplitzEntry (rows 0) (cols 0) *
              XiToeplitzEntry (rows 1) (cols 1)
            - XiToeplitzEntry (rows 0) (cols 1) *
              XiToeplitzEntry (rows 1) (cols 0))

/-- Bracket form of the `T01 = 0` edge case.

Since `T00` is nonnegative from contiguous `1 × 1` positivity, it is enough to
prove the remaining `2 × 2`-style bracket is nonnegative. -/
def XiMinorThreeBandedT01ZeroBracketFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 1 →
    rows 0 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 1) (cols 1) *
            XiToeplitzEntry (rows 2) (cols 2)
          - XiToeplitzEntry (rows 1) (cols 2) *
            XiToeplitzEntry (rows 2) (cols 1)

/-- Bracket form of the `T12 = 0` edge case. -/
def XiMinorThreeBandedT12ZeroBracketFromContig : Prop :=
  ∀ (rows cols : Fin 3 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    rows 1 < cols 2 →
    cols 2 ≤ rows 2 →
    XiContigToeplitzTotalPositive →
      0 ≤
        XiToeplitzEntry (rows 0) (cols 0) *
            XiToeplitzEntry (rows 1) (cols 1)
          - XiToeplitzEntry (rows 0) (cols 1) *
            XiToeplitzEntry (rows 1) (cols 0)

/-- The full-support `2 × 2` theorem target proves the `T01 = 0` bracket
target.  If the lower-right `2 × 2` block is not fully supported, its first row
or upper-right entry vanishes and the bracket reduces to an already nonnegative
product. -/
theorem xiMinorThreeBandedT01ZeroBracket_of_twoFullSupport
    (hTwo : XiMinorTwoFullSupportFromContig) :
    XiMinorThreeBandedT01ZeroBracketFromContig := by
  intro rows cols hRows hCols hLeft h01zero hGap hRight hContig
  by_cases h11support : cols 1 ≤ rows 1
  · by_cases h12support : cols 2 ≤ rows 1
    · let rows2 : Fin 2 → ℕ := ![rows 1, rows 2]
      let cols2 : Fin 2 → ℕ := ![cols 1, cols 2]
      have hRows2 : StrictMono rows2 := by
        intro a b hab
        fin_cases a <;> fin_cases b
        · exact False.elim ((by decide : ¬ ((0 : Fin 2) < 0)) hab)
        · exact hRows (by decide : (1 : Fin 3) < 2)
        · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 0)) hab)
        · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 1)) hab)
      have hCols2 : StrictMono cols2 := by
        intro a b hab
        fin_cases a <;> fin_cases b
        · exact False.elim ((by decide : ¬ ((0 : Fin 2) < 0)) hab)
        · exact hCols (by decide : (1 : Fin 3) < 2)
        · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 0)) hab)
        · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 1)) hab)
      have hSupport2 : ∀ a b : Fin 2, cols2 b ≤ rows2 a := by
        intro a b
        fin_cases a <;> fin_cases b
        · exact h11support
        · exact h12support
        · exact le_trans h11support
            (le_of_lt (hRows (by decide : (1 : Fin 3) < 2)))
        · exact hRight
      have hdet := hTwo rows2 cols2 hRows2 hCols2 hSupport2 hContig
      rw [Matrix.det_fin_two] at hdet
      simpa [rows2, cols2, Matrix.of_apply] using hdet
    · have h12zero : XiToeplitzEntry (rows 1) (cols 2) = 0 := by
        unfold XiToeplitzEntry
        rw [if_neg (Nat.not_le_of_gt (Nat.lt_of_not_ge h12support))]
      have h11nonneg := xiToeplitzEntry_nonneg_of_contig hContig (rows 1) (cols 1)
      have h22nonneg := xiToeplitzEntry_nonneg_of_contig hContig (rows 2) (cols 2)
      rw [h12zero, zero_mul, sub_zero]
      exact mul_nonneg h11nonneg h22nonneg
  · have h11zero : XiToeplitzEntry (rows 1) (cols 1) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt (Nat.lt_of_not_ge h11support))]
    have hCols12 : cols 1 < cols 2 := hCols (by decide : (1 : Fin 3) < 2)
    have h12zero : XiToeplitzEntry (rows 1) (cols 2) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt (lt_trans (Nat.lt_of_not_ge h11support) hCols12))]
    rw [h11zero, h12zero, zero_mul, zero_mul, sub_self]

/-- The full-support `2 × 2` theorem target proves the `T12 = 0` bracket
target.  In this case the upper-left `2 × 2` block is fully supported by the
edge assumptions. -/
theorem xiMinorThreeBandedT12ZeroBracket_of_twoFullSupport
    (hTwo : XiMinorTwoFullSupportFromContig) :
    XiMinorThreeBandedT12ZeroBracketFromContig := by
  intro rows cols hRows hCols hLeft h01 hGap h12zero hRight hContig
  let rows2 : Fin 2 → ℕ := ![rows 0, rows 1]
  let cols2 : Fin 2 → ℕ := ![cols 0, cols 1]
  have hRows2 : StrictMono rows2 := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : Fin 2) < 0)) hab)
    · exact hRows (by decide : (0 : Fin 3) < 1)
    · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 1)) hab)
  have hCols2 : StrictMono cols2 := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : Fin 2) < 0)) hab)
    · exact hCols (by decide : (0 : Fin 3) < 1)
    · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : Fin 2) < 1)) hab)
  have hRows01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 3) < 1)
  have hSupport2 : ∀ a b : Fin 2, cols2 b ≤ rows2 a := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact hLeft
    · exact h01
    · exact le_trans hLeft (le_of_lt hRows01)
    · exact le_trans h01 (le_of_lt hRows01)
  have hdet := hTwo rows2 cols2 hRows2 hCols2 hSupport2 hContig
  rw [Matrix.det_fin_two] at hdet
  simpa [rows2, cols2, Matrix.of_apply] using hdet

/-- Pólya's positive kernel representation proves both bracket zero-edge
targets through the already-verified full-support `2 × 2` route. -/
theorem xiMinorThreeBandedT01ZeroBracket_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiMinorThreeBandedT01ZeroBracketFromContig :=
  xiMinorThreeBandedT01ZeroBracket_of_twoFullSupport
    (xiMinorTwoFullSupportFromContig_of_kernelRep hRep)

/-- Pólya's positive kernel representation proves the `T12 = 0` bracket target
through the already-verified full-support `2 × 2` route. -/
theorem xiMinorThreeBandedT12ZeroBracket_of_kernelRep
    (hRep : XiMomentKernelRep) :
    XiMinorThreeBandedT12ZeroBracketFromContig :=
  xiMinorThreeBandedT12ZeroBracket_of_twoFullSupport
    (xiMinorTwoFullSupportFromContig_of_kernelRep hRep)

/-- The `T01 = 0` bracket target implies the simplified `T01 = 0` target. -/
theorem xiMinorThreeBandedT01ZeroSimplified_of_bracket
    (hBracket : XiMinorThreeBandedT01ZeroBracketFromContig) :
    XiMinorThreeBandedT01ZeroSimplifiedFromContig := by
  intro rows cols hRows hCols hLeft h01zero hGap hRight hContig
  have h00 := xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hB := hBracket rows cols hRows hCols hLeft h01zero hGap hRight hContig
  exact mul_nonneg h00 hB

/-- The `T12 = 0` bracket target implies the simplified `T12 = 0` target. -/
theorem xiMinorThreeBandedT12ZeroSimplified_of_bracket
    (hBracket : XiMinorThreeBandedT12ZeroBracketFromContig) :
    XiMinorThreeBandedT12ZeroSimplifiedFromContig := by
  intro rows cols hRows hCols hLeft h01 hGap h12zero hRight hContig
  have h22 := xiToeplitzEntry_nonneg_of_contig hContig (rows 2) (cols 2)
  have hB := hBracket rows cols hRows hCols hLeft h01 hGap h12zero hRight hContig
  exact mul_nonneg h22 hB

/-- The simplified `T01 = 0` target implies the full `T01 = 0` edge target. -/
theorem xiMinorThreeBandedT01ZeroInequality_of_simplified
    (hSimp : XiMinorThreeBandedT01ZeroSimplifiedFromContig) :
    XiMinorThreeBandedT01ZeroInequalityFromContig := by
  intro rows cols hRows hCols hLeft h01zero hGap hRight hContig
  have h01 : XiToeplitzEntry (rows 0) (cols 1) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt h01zero)]
  have h := hSimp rows cols hRows hCols hLeft h01zero hGap hRight hContig
  rw [h01, zero_mul, sub_zero]
  exact h

/-- The simplified `T12 = 0` target implies the full `T12 = 0` edge target. -/
theorem xiMinorThreeBandedT12ZeroInequality_of_simplified
    (hSimp : XiMinorThreeBandedT12ZeroSimplifiedFromContig) :
    XiMinorThreeBandedT12ZeroInequalityFromContig := by
  intro rows cols hRows hCols hLeft h01 hGap h12zero hRight hContig
  have h12 : XiToeplitzEntry (rows 1) (cols 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt h12zero)]
  have h := hSimp rows cols hRows hCols hLeft h01 hGap h12zero hRight hContig
  rw [h12, zero_mul, sub_zero, zero_mul, sub_zero]
  ring_nf at h ⊢
  exact h

/-- Middle-supported moment control plus the two concrete edge cases supplies
the full expanded banded determinant target. -/
theorem xiMinorThreeBandedExpandedInequality_of_middleMoment_and_zeroEdges
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig)
    (hT01 : XiMinorThreeBandedT01ZeroInequalityFromContig)
    (hT12 : XiMinorThreeBandedT12ZeroInequalityFromContig) :
    XiMinorThreeBandedExpandedInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  by_cases h01 : cols 1 ≤ rows 0
  · by_cases h12 : cols 2 ≤ rows 1
    · exact xiMinorThreeBandedExpandedInequality_of_middleMoment
        hMoment rows cols hRows hCols hLeft h01 hGap h12 hRight hContig
    · have h12zero : rows 1 < cols 2 := Nat.lt_of_not_ge h12
      exact hT12 rows cols hRows hCols hLeft h01 hGap h12zero hRight hContig
  · have h01zero : rows 0 < cols 1 := Nat.lt_of_not_ge h01
    exact hT01 rows cols hRows hCols hLeft h01zero hGap hRight hContig

/-- Placeholder route target: the middle-supported moment inequality plus the
remaining edge-supported band cases should imply the full expanded banded
inequality. -/
def XiMinorThreeBandedEdgeCaseCertificates : Prop :=
  XiMinorThreeBandedMiddleMomentInequalityFromContig →
    XiMinorThreeBandedExpandedInequalityFromContig

/-- Middle-supported moment control plus the remaining band edge cases supplies
the expanded sparse determinant target. -/
theorem xiMinorThreeBandedExpandedInequality_of_middleMoment_and_edgeCases
    (hEdge : XiMinorThreeBandedEdgeCaseCertificates)
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig) :
    XiMinorThreeBandedExpandedInequalityFromContig :=
  hEdge hMoment

/-- The concrete `T01 = 0` and `T12 = 0` edge cases supply the previous
edge-case bridge. -/
theorem xiMinorThreeBandedEdgeCaseCertificates_of_zeroEdges
    (hT01 : XiMinorThreeBandedT01ZeroInequalityFromContig)
    (hT12 : XiMinorThreeBandedT12ZeroInequalityFromContig) :
    XiMinorThreeBandedEdgeCaseCertificates := by
  intro hMoment
  exact xiMinorThreeBandedExpandedInequality_of_middleMoment_and_zeroEdges
    hMoment hT01 hT12

/-- The expanded sparse determinant inequality implies the determinant-form
banded `3 × 3` target. -/
theorem xiMinorThreeBandedDetInequality_of_expanded
    (hExp : XiMinorThreeBandedExpandedInequalityFromContig) :
    XiMinorThreeBandedDetInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  have h02 : XiToeplitzEntry (rows 0) (cols 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hGap)]
  have h := hExp rows cols hRows hCols hLeft hGap hRight hContig
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [h02]
  ring_nf at h ⊢
  exact h

/-- The banded determinant inequality supplies local certificates for every
banded mixed-support `3 × 3` arbitrary minor. -/
def xiMinorThreeBandedDetCertificate
    (hDet : XiMinorThreeBandedDetInequalityFromContig)
    (rows cols : Fin 3 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hLeft : cols 0 ≤ rows 0)
    (hGap : rows 0 < cols 2)
    (hRight : cols 2 ≤ rows 2) :
    XiMinorContigCertificate 3 rows cols hRows hCols where
  certificate := cols 0 ≤ rows 0 ∧ rows 0 < cols 2 ∧ cols 2 ≤ rows 2
  proof := ⟨hLeft, hGap, hRight⟩
  nonneg := by
    intro hBand hContig
    exact hDet rows cols hRows hCols hBand.1 hBand.2.1 hBand.2.2 hContig

/-- The determinant inequality target implies the banded mixed-support
certificate target. -/
theorem xiMinorThreeBandedMixedSupportCertificates_of_detInequality
    (hDet : XiMinorThreeBandedDetInequalityFromContig) :
    XiMinorThreeBandedMixedSupportCertificates := by
  intro rows cols hRows hCols hLeft hGap hRight
  exact ⟨xiMinorThreeBandedDetCertificate
    hDet rows cols hRows hCols hLeft hGap hRight⟩

/-- The banded mixed-support certificate target is equivalent to the current
mixed-support frontier for monotone `3 × 3` patterns. -/
theorem xiMinorThreeMixedSupportCertificates_of_banded
    (hBand : XiMinorThreeBandedMixedSupportCertificates) :
    XiMinorThreeMixedSupportCertificates := by
  intro rows cols hRows hCols hNoZeroRow hNoZeroCol hNotFull
  have hCols01 : cols 0 < cols 1 := hCols (by decide : (0 : Fin 3) < 1)
  have hCols12 : cols 1 < cols 2 := hCols (by decide : (1 : Fin 3) < 2)
  have hRows01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 3) < 1)
  have hRows12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 3) < 2)
  have hLeft : cols 0 ≤ rows 0 := by
    by_contra h
    have hlt : rows 0 < cols 0 := Nat.lt_of_not_ge h
    apply hNoZeroRow
    refine ⟨0, ?_⟩
    intro b
    fin_cases b
    · exact hlt
    · exact lt_trans hlt hCols01
    · exact lt_trans hlt (lt_trans hCols01 hCols12)
  have hRight : cols 2 ≤ rows 2 := by
    by_contra h
    have hlt : rows 2 < cols 2 := Nat.lt_of_not_ge h
    apply hNoZeroCol
    refine ⟨2, ?_⟩
    intro a
    fin_cases a
    · exact lt_trans (lt_trans hRows01 hRows12) hlt
    · exact lt_trans hRows12 hlt
    · exact hlt
  have hGap : rows 0 < cols 2 := by
    by_contra h
    have h02 : cols 2 ≤ rows 0 := Nat.le_of_not_gt h
    apply hNotFull
    intro a b
    fin_cases a <;> fin_cases b
    · exact le_trans (le_of_lt (lt_trans hCols01 hCols12)) h02
    · exact le_trans (le_of_lt hCols12) h02
    · exact h02
    · exact le_trans (le_trans (le_of_lt (lt_trans hCols01 hCols12)) h02) (le_of_lt hRows01)
    · exact le_trans (le_trans (le_of_lt hCols12) h02) (le_of_lt hRows01)
    · exact le_trans h02 (le_of_lt hRows01)
    · exact le_trans (le_trans (le_of_lt (lt_trans hCols01 hCols12)) h02)
        (le_of_lt (lt_trans hRows01 hRows12))
    · exact le_trans (le_trans (le_of_lt hCols12) h02)
        (le_of_lt (lt_trans hRows01 hRows12))
    · exact le_trans h02 (le_of_lt (lt_trans hRows01 hRows12))
  exact hBand rows cols hRows hCols hLeft hGap hRight

/-- Full-support plus mixed-support certificates close the full `3 × 3`
certificate frontier.  Zero-row and zero-column cases are already handled by
arbitrary-size certificates. -/
theorem xiMinorThreeContigCertificates_of_full_and_mixed
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMixed : XiMinorThreeMixedSupportCertificates) :
    XiMinorThreeContigCertificates := by
  intro rows cols hRows hCols
  by_cases hZeroRow : ∃ a : Fin 3, ∀ b : Fin 3, rows a < cols b
  · exact exists_xiZeroRowMinorCertificate 3 rows cols hRows hCols hZeroRow
  by_cases hZeroCol : ∃ b : Fin 3, ∀ a : Fin 3, rows a < cols b
  · exact exists_xiZeroColumnMinorCertificate 3 rows cols hRows hCols hZeroCol
  by_cases hSupport : ∀ a b : Fin 3, cols b ≤ rows a
  · exact exists_xiMinorThreeFullSupportCertificate hFull rows cols hRows hCols hSupport
  · exact hMixed rows cols hRows hCols hZeroRow hZeroCol hSupport

/-- Any supplied `3 x 3` contiguous-certificate family closes the order-three
initial-column lift by specializing the columns to `0, 1, 2`. -/
theorem xiInitialColumnMinorThreeFromContig_of_threeCertificates
    (hThree : XiMinorThreeContigCertificates) :
    XiInitialColumnMinorThreeFromContig := by
  intro rows hRows hContig
  let cols : Fin 3 → ℕ := fun j => j.val
  have hCols : StrictMono cols := strictMono_fin_val 3
  rcases hThree rows cols hRows hCols with ⟨certificate⟩
  simpa [cols] using certificate.nonneg certificate.proof hContig

/-- Full-support and banded determinant positivity supply the order-three
initial-column lift through the existing three-minor certificate decomposition. -/
theorem xiInitialColumnMinorThreeFromContig_of_full_and_bandedDet
    (hFull : XiMinorThreeFullSupportFromContig)
    (hBanded : XiMinorThreeBandedDetInequalityFromContig) :
    XiInitialColumnMinorThreeFromContig :=
  xiInitialColumnMinorThreeFromContig_of_threeCertificates
    (xiMinorThreeContigCertificates_of_full_and_mixed hFull
      (xiMinorThreeMixedSupportCertificates_of_banded
        (xiMinorThreeBandedMixedSupportCertificates_of_detInequality hBanded)))

/-- Orders zero through three reduce the whole initial-column lift to the
remaining `k >= 4` arbitrary-row condition. -/
theorem xiContigToInitialColumnMinorBridge_of_two_three_and_geFour
    (hTwo : XiInitialColumnMinorTwoFromContig)
    (hThree : XiInitialColumnMinorThreeFromContig)
    (hGeFour : XiInitialColumnMinorGeFourFromContig) :
    XiContigToInitialColumnMinorBridge := by
  intro hContig k rows hRows
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk1 : k = 1
  · subst k
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply, Fin.val_zero]
    exact xiToeplitzEntry_nonneg_of_contig hContig (rows 0) 0
  by_cases hk2 : k = 2
  · subst k
    exact hTwo rows hRows hContig
  by_cases hk3 : k = 3
  · subst k
    exact hThree rows hRows hContig
  have hk4 : 4 ≤ k := by omega
  exact hGeFour k hk4 rows hRows hContig

/-- With the Pólya kernel representation, the full initial-column bridge has
only order `k >= 4` left once its order-three input is supplied. -/
theorem xiContigToInitialColumnMinorBridge_of_kernelRep_three_and_geFour
    (hRep : XiMomentKernelRep)
    (hThree : XiInitialColumnMinorThreeFromContig)
    (hGeFour : XiInitialColumnMinorGeFourFromContig) :
    XiContigToInitialColumnMinorBridge :=
  xiContigToInitialColumnMinorBridge_of_two_three_and_geFour
    (xiInitialColumnMinorTwoFromContig_of_kernelRep hRep) hThree hGeFour

/-- The tail frontier after the first unsolved `3 × 3` rung. -/
def XiAllMinorGeFourContigCertificates : Prop :=
  ∀ (k : ℕ), 4 ≤ k →
    ∀ (rows cols : Fin k → ℕ)
      (hRows : StrictMono rows) (hCols : StrictMono cols),
        Nonempty (XiMinorContigCertificate k rows cols hRows hCols)

/-- The first remaining tail rung after the `3 × 3` moment payload. -/
def XiMinorFourContigCertificates : Prop :=
  ∀ (rows cols : Fin 4 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      Nonempty (XiMinorContigCertificate 4 rows cols hRows hCols)

/-- Full-support `4 × 4` certificate target. -/
def XiMinorFourFullSupportFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    (∀ a b : Fin 4, cols b ≤ rows a) →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- Moment-index form of the full-support `4 × 4` target. -/
def XiMinorFourFullSupportMomentFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    (∀ a b : Fin 4, cols b ≤ rows a) →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiMomentCoeff (rows a - cols b))).det

/-- Unified low-rank moment payload through the first full-support `4 × 4`
rung. -/
def XiLowRankMomentPayloadFromContig : Prop :=
  XiMinorThreeMomentPayloadFromContig ∧
    XiMinorFourFullSupportMomentFromContig

/-- The unified low-rank moment payload supplies the `3 × 3` moment payload. -/
theorem xiMinorThreeMomentPayload_of_lowRankMomentPayload
    (hPayload : XiLowRankMomentPayloadFromContig) :
    XiMinorThreeMomentPayloadFromContig :=
  hPayload.1

/-- The unified low-rank moment payload supplies the full-support `4 × 4`
moment target. -/
theorem xiMinorFourFullSupportMoment_of_lowRankMomentPayload
    (hPayload : XiLowRankMomentPayloadFromContig) :
    XiMinorFourFullSupportMomentFromContig :=
  hPayload.2

/-- The moment-index full-support `4 × 4` target implies the Toeplitz-entry
full-support `4 × 4` target. -/
theorem xiMinorFourFullSupportFromContig_of_moment
    (hMoment : XiMinorFourFullSupportMomentFromContig) :
    XiMinorFourFullSupportFromContig := by
  intro rows cols hRows hCols hSupport hContig
  have h := hMoment rows cols hRows hCols hSupport hContig
  have hMat :
      Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b)) =
        Matrix.of (fun a b => XiMomentCoeff (rows a - cols b)) := by
    ext a b
    exact xiToeplitzEntry_sub (rows a) (cols b) (hSupport a b)
  rw [hMat]
  exact h

/-- A full-support `4 × 4` theorem target supplies local certificates for every
full-support `4 × 4` arbitrary minor. -/
def xiMinorFourFullSupportCertificate
    (hFull : XiMinorFourFullSupportFromContig)
    (rows cols : Fin 4 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin 4, cols b ≤ rows a) :
    XiMinorContigCertificate 4 rows cols hRows hCols where
  certificate := ∀ a b : Fin 4, cols b ≤ rows a
  proof := hSupport
  nonneg := by
    intro hSupp hContig
    exact hFull rows cols hRows hCols hSupp hContig

/-- The full-support `4 × 4` target gives certificates for every full-support
`4 × 4` pattern. -/
theorem exists_xiMinorFourFullSupportCertificate
    (hFull : XiMinorFourFullSupportFromContig)
    (rows cols : Fin 4 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hSupport : ∀ a b : Fin 4, cols b ≤ rows a) :
    Nonempty (XiMinorContigCertificate 4 rows cols hRows hCols) :=
  ⟨xiMinorFourFullSupportCertificate hFull rows cols hRows hCols hSupport⟩

/-- Mixed-support `4 × 4` certificate target after removing zero-row,
zero-column, and full-support cases. -/
def XiMinorFourMixedSupportCertificates : Prop :=
  ∀ (rows cols : Fin 4 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      (¬ ∃ a : Fin 4, ∀ b : Fin 4, rows a < cols b) →
      (¬ ∃ b : Fin 4, ∀ a : Fin 4, rows a < cols b) →
      (¬ ∀ a b : Fin 4, cols b ≤ rows a) →
        Nonempty (XiMinorContigCertificate 4 rows cols hRows hCols)

/-- Banded mixed-support `4 × 4` frontier.

For strictly monotone `4 × 4` row/column patterns, the broad mixed-support case
with no zero row and no zero column lies inside this support envelope:

* lower-left edge supported: `cols 0 ≤ rows 0`;
* upper-right corner missing: `rows 0 < cols 3`;
* lower-right edge supported: `cols 3 ≤ rows 3`.
-/
def XiMinorFourBandedMixedSupportCertificates : Prop :=
  ∀ (rows cols : Fin 4 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols),
      cols 0 ≤ rows 0 →
      rows 0 < cols 3 →
      cols 3 ≤ rows 3 →
        Nonempty (XiMinorContigCertificate 4 rows cols hRows hCols)

/-- Determinant inequality form of the banded mixed-support `4 × 4` frontier.

This exposes the exact finite determinant nonnegativity statement left after
the zero-row, zero-column, full-support, and monotone band reductions. -/
def XiMinorFourBandedDetInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      0 ≤ (Matrix.of (fun a b => XiToeplitzEntry (rows a) (cols b))).det

/-- Upper-right-zero determinant form of the banded mixed-support `4 × 4`
frontier.

The band condition forces the `(0, 3)` entry to vanish.  This condition records
that structural zero directly in the determinant matrix, preparing the next
step where the determinant is expanded into `3 × 3` cofactors. -/
def XiMinorFourBandedUpperRightZeroDetInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))).det

/-- Row-zero cofactor form of the banded mixed-support `4 × 4` frontier.

After inserting the forced upper-right zero, the next finite target is the
Laplacian expansion along row `0`: three potentially surviving row-zero entries
times their `3 × 3` cofactors, plus the formally present zero term. -/
def XiMinorFourBandedRowZeroCofactorInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      0 ≤
        ∑ j : Fin 4,
          (-1 : ℝ) ^ (j : ℕ) * A 0 j *
            (A.submatrix Fin.succ j.succAbove).det

/-- Three-surviving-cofactor form of the banded mixed-support `4 × 4`
frontier.

The `(0, 3)` row-zero cofactor term vanishes after inserting the structural
upper-right zero.  This target names the remaining three signed `3 × 3`
cofactors explicitly. -/
def XiMinorFourBandedThreeCofactorInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      0 ≤
        A 0 0 * (A.submatrix Fin.succ (0 : Fin 4).succAbove).det
          - A 0 1 * (A.submatrix Fin.succ (1 : Fin 4).succAbove).det
          + A 0 2 * (A.submatrix Fin.succ (2 : Fin 4).succAbove).det

/-- The named `3 × 3` cofactor matrix obtained from the structured banded
`4 × 4` matrix by deleting row `0` and column `j`.

The upper-right structural zero is retained in the ambient matrix before the
submatrix is taken. -/
def XiMinorFourBandedCofactorMatrix
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  A.submatrix Fin.succ j.succAbove

/-- Row selector for any `3 × 3` cofactor of the structured banded `4 × 4`
matrix: delete row `0`, so the remaining rows are `1, 2, 3`. -/
def XiMinorFourBandedCofactorRows (rows : Fin 4 → ℕ) : Fin 3 → ℕ :=
  fun a => rows (Fin.succ a)

/-- Column selector for the `j`th `3 × 3` cofactor of the structured banded
`4 × 4` matrix: delete column `j`. -/
def XiMinorFourBandedCofactorCols (cols : Fin 4 → ℕ) (j : Fin 4) : Fin 3 → ℕ :=
  fun b => cols (j.succAbove b)

/-- Strictly increasing `4`-row selectors remain strictly increasing after
deleting the first row for a `3 × 3` cofactor. -/
theorem xiMinorFourBandedCofactorRows_strictMono
    {rows : Fin 4 → ℕ} (hRows : StrictMono rows) :
    StrictMono (XiMinorFourBandedCofactorRows rows) := by
  intro a b hab
  exact hRows (by
    rw [Fin.lt_def, Fin.val_succ, Fin.val_succ]
    exact Nat.succ_lt_succ hab)

/-- Strictly increasing `4`-column selectors remain strictly increasing after
deleting one column for a `3 × 3` cofactor. -/
theorem xiMinorFourBandedCofactorCols_strictMono
    {cols : Fin 4 → ℕ} (hCols : StrictMono cols) (j : Fin 4) :
    StrictMono (XiMinorFourBandedCofactorCols cols j) := by
  intro a b hab
  exact hCols (Fin.strictMono_succAbove j hab)

/-- Full-support predicate for a named `3 × 3` cofactor matrix. -/
def XiMinorFourBandedCofactorFullSupport
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Prop :=
  ∀ a b : Fin 3,
    XiMinorFourBandedCofactorCols cols j b ≤
      XiMinorFourBandedCofactorRows rows a

/-- Banded mixed-support predicate for a named `3 × 3` cofactor matrix. -/
def XiMinorFourBandedCofactorBandedSupport
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Prop :=
  XiMinorFourBandedCofactorCols cols j 0 ≤
      XiMinorFourBandedCofactorRows rows 0 ∧
    XiMinorFourBandedCofactorRows rows 0 <
      XiMinorFourBandedCofactorCols cols j 2 ∧
    XiMinorFourBandedCofactorCols cols j 2 ≤
      XiMinorFourBandedCofactorRows rows 2

/-- Zero-row support predicate for a named `3 × 3` cofactor matrix. -/
def XiMinorFourBandedCofactorZeroRowSupport
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Prop :=
  ∃ a : Fin 3, ∀ b : Fin 3,
    XiMinorFourBandedCofactorRows rows a <
      XiMinorFourBandedCofactorCols cols j b

/-- Zero-column support predicate for a named `3 × 3` cofactor matrix. -/
def XiMinorFourBandedCofactorZeroColumnSupport
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Prop :=
  ∃ b : Fin 3, ∀ a : Fin 3,
    XiMinorFourBandedCofactorRows rows a <
      XiMinorFourBandedCofactorCols cols j b

/-- Support-class predicate for a named `3 × 3` cofactor matrix. -/
def XiMinorFourBandedCofactorSupportClass
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Prop :=
  XiMinorFourBandedCofactorZeroRowSupport rows cols j ∨
    XiMinorFourBandedCofactorZeroColumnSupport rows cols j ∨
      XiMinorFourBandedCofactorFullSupport rows cols j ∨
        XiMinorFourBandedCofactorBandedSupport rows cols j

/-- The named cofactor matrix is exactly the Toeplitz-entry matrix selected by
the cofactor row and column maps. -/
theorem xiMinorFourBandedCofactorMatrix_eq_toeplitz
    (rows cols : Fin 4 → ℕ) (j : Fin 4) :
    XiMinorFourBandedCofactorMatrix rows cols j =
      Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols j b)) := by
  ext a b
  simp [XiMinorFourBandedCofactorMatrix,
    XiMinorFourBandedCofactorRows, XiMinorFourBandedCofactorCols]

/-- A nonnegative `4 x 4` determinant gives left cofactor dominance when the
two rightmost top-row entries vanish. -/
theorem matrix_det_eq_cofactorLeftDifference_of_topRightTwoZero
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h02 : A 0 2 = 0) (h03 : A 0 3 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ (0 : Fin 4).succAbove).det -
      A 0 1 * (A.submatrix Fin.succ (1 : Fin 4).succAbove).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp [h02, h03]
  ring

/-- A nonnegative `4 x 4` determinant gives left cofactor dominance when the
two rightmost top-row entries vanish. -/
theorem matrix_cofactorLeftDominance_of_det_nonneg_and_topRightTwoZero
    (A : Matrix (Fin 4) (Fin 4) ℝ)
    (h02 : A 0 2 = 0) (h03 : A 0 3 = 0)
    (hDet : 0 ≤ A.det) :
    A 0 1 * (A.submatrix Fin.succ (1 : Fin 4).succAbove).det ≤
      A 0 0 * (A.submatrix Fin.succ (0 : Fin 4).succAbove).det := by
  rw [matrix_det_eq_cofactorLeftDifference_of_topRightTwoZero A h02 h03] at hDet
  linarith

set_option linter.style.longLine false in
/-- The gap-one consecutive `4 x 4` selector is an exact solved seed of the
active cofactor-ratio branch: its determinant is the contiguous minor at
offset one. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_contiguousSeed
    (hContig : XiContigToeplitzTotalPositive) :
    let rows : Fin 4 → ℕ := fun i => 1 + i.val
    let cols : Fin 4 → ℕ := fun j => j.val
    let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
      Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols j b))
    XiMomentCoeff (rows 0 - cols 1) * (C 1).det ≤
      XiMomentCoeff (rows 0 - cols 0) * (C 0).det := by
  dsimp only
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun i j => XiToeplitzEntry (1 + i.val) j.val)
  have h02 : A 0 2 = 0 := by
    simp [A, XiToeplitzEntry]
  have h03 : A 0 3 = 0 := by
    simp [A, XiToeplitzEntry]
  have hDet : 0 ≤ A.det := by
    simpa [A, XiToeplitzContigMinor] using hContig 4 1
  have hLeft :=
    matrix_cofactorLeftDominance_of_det_nonneg_and_topRightTwoZero A h02 h03 hDet
  simpa [A, XiMinorFourBandedCofactorRows,
    XiMinorFourBandedCofactorCols, XiToeplitzEntry] using hLeft

set_option linter.style.longLine false in
/-- The unshifted gap-one consecutive seed has an explicit one-term
subtraction-free certificate: its cofactor-ratio difference is exactly
`XiToeplitzContigMinor 4 1`. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificate_contiguousSeed :
    let rows : Fin 4 → ℕ := fun i => 1 + i.val
    let cols : Fin 4 → ℕ := fun j => j.val
    let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
      Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols j b))
    XiContigMinorPositivePolynomial
      (XiMomentCoeff (rows 0 - cols 0) * (C 0).det -
        XiMomentCoeff (rows 0 - cols 1) * (C 1).det) := by
  dsimp only
  refine ⟨1, fun _ => 1, fun _ => [(4, 1)], ?_⟩
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_one, one_mul,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun i j => XiToeplitzEntry (1 + i.val) j.val)
  have h02 : A 0 2 = 0 := by
    simp [A, XiToeplitzEntry]
  have h03 : A 0 3 = 0 := by
    simp [A, XiToeplitzEntry]
  have hEq :=
    matrix_det_eq_cofactorLeftDifference_of_topRightTwoZero A h02 h03
  simpa [A, XiToeplitzContigMinor,
    XiMinorFourBandedCofactorRows, XiMinorFourBandedCofactorCols,
    XiToeplitzEntry] using hEq.symm

set_option linter.style.longLine false in
/-- Every common translation of the gap-one consecutive seed has the same
one-term `XiToeplitzContigMinor 4 1` certificate. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificate_contiguousShiftedSeed
    (q : ℕ) :
    let rows : Fin 4 → ℕ := fun i => q + 1 + i.val
    let cols : Fin 4 → ℕ := fun j => q + j.val
    let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
      Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols j b))
    XiContigMinorPositivePolynomial
      (XiMomentCoeff (rows 0 - cols 0) * (C 0).det -
        XiMomentCoeff (rows 0 - cols 1) * (C 1).det) := by
  dsimp only
  simpa [XiMinorFourBandedCofactorRows, XiMinorFourBandedCofactorCols,
    Nat.add_assoc, xiToeplitzEntry_add_left] using
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificate_contiguousSeed

set_option linter.style.longLine false in
/-- Common translations of the gap-one consecutive seed remain solved by the
same contiguous minor, by Toeplitz shift invariance. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_contiguousShiftedSeed
    (q : ℕ) (hContig : XiContigToeplitzTotalPositive) :
    let rows : Fin 4 → ℕ := fun i => q + 1 + i.val
    let cols : Fin 4 → ℕ := fun j => q + j.val
    let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
      Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols j b))
    XiMomentCoeff (rows 0 - cols 1) * (C 1).det ≤
      XiMomentCoeff (rows 0 - cols 0) * (C 0).det := by
  dsimp only
  simpa [XiMinorFourBandedCofactorRows, XiMinorFourBandedCofactorCols,
    Nat.add_assoc, xiToeplitzEntry_add_left] using
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_contiguousSeed
      hContig

/-- Named-cofactor-matrix form of the banded mixed-support `4 × 4` frontier.

This is the same three-cofactor inequality, but each deleted-column `3 × 3`
cofactor is exposed as `XiMinorFourBandedCofactorMatrix rows cols j`. -/
def XiMinorFourBandedNamedCofactorInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      0 ≤
        A 0 0 * (XiMinorFourBandedCofactorMatrix rows cols 0).det
          - A 0 1 * (XiMinorFourBandedCofactorMatrix rows cols 1).det
          + A 0 2 * (XiMinorFourBandedCofactorMatrix rows cols 2).det

/-- Row/column-selector form of the named cofactor frontier.

This rewrites each cofactor as the `3 × 3` Toeplitz-entry matrix selected by
`XiMinorFourBandedCofactorRows` and `XiMinorFourBandedCofactorCols`, exposing
the exact row/column data needed by the existing `3 × 3` support machinery. -/
def XiMinorFourBandedCofactorRowColInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Support-class split form of the cofactor row/column frontier.

This keeps the same row/column-selector inequality but additionally records
that each surviving `3 × 3` cofactor belongs to a named support class:
zero-row, zero-column, full-support, or banded mixed-support. -/
def XiMinorFourBandedCofactorSupportSplitInequalityFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportClass rows cols 0 →
    XiMinorFourBandedCofactorSupportClass rows cols 1 →
    XiMinorFourBandedCofactorSupportClass rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- The four support kinds used to split a named `3 × 3` cofactor. -/
inductive XiMinorFourBandedCofactorSupportKind where
  | zeroRow
  | zeroColumn
  | full
  | banded
deriving DecidableEq

/-- A support kind holds for a selected cofactor when the matching support
predicate holds. -/
def XiMinorFourBandedCofactorSupportKindHolds
    (kind : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ) (j : Fin 4) : Prop :=
  match kind with
  | .zeroRow => XiMinorFourBandedCofactorZeroRowSupport rows cols j
  | .zeroColumn => XiMinorFourBandedCofactorZeroColumnSupport rows cols j
  | .full => XiMinorFourBandedCofactorFullSupport rows cols j
  | .banded => XiMinorFourBandedCofactorBandedSupport rows cols j

/-- A support kind has a potentially nonzero determinant precisely when it is
not one of the two structural-zero kinds. -/
def XiMinorFourBandedCofactorSupportKindActive
    (kind : XiMinorFourBandedCofactorSupportKind) : Prop :=
  kind = .full ∨ kind = .banded

/-- The full-support kind is active. -/
theorem xiMinorFourBandedCofactorSupportKindActive_full :
    XiMinorFourBandedCofactorSupportKindActive .full :=
  Or.inl rfl

/-- The banded-support kind is active. -/
theorem xiMinorFourBandedCofactorSupportKindActive_banded :
    XiMinorFourBandedCofactorSupportKindActive .banded :=
  Or.inr rfl

/-- Every support-kind proof supplies the corresponding support-class proof. -/
theorem xiMinorFourBandedCofactorSupportClass_of_kind
    {kind : XiMinorFourBandedCofactorSupportKind}
    {rows cols : Fin 4 → ℕ} {j : Fin 4}
    (hKind : XiMinorFourBandedCofactorSupportKindHolds kind rows cols j) :
    XiMinorFourBandedCofactorSupportClass rows cols j := by
  cases kind
  · exact Or.inl hKind
  · exact Or.inr (Or.inl hKind)
  · exact Or.inr (Or.inr (Or.inl hKind))
  · exact Or.inr (Or.inr (Or.inr hKind))

/-- A zero-row support cofactor has determinant zero. -/
theorem xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
    {rows cols : Fin 4 → ℕ} {j : Fin 4}
    (hZeroRow : XiMinorFourBandedCofactorZeroRowSupport rows cols j) :
    (Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))).det = 0 := by
  rcases hZeroRow with ⟨a0, ha0⟩
  apply Matrix.det_eq_zero_of_row_eq_zero a0
  intro b
  change
    XiToeplitzEntry
      (XiMinorFourBandedCofactorRows rows a0)
      (XiMinorFourBandedCofactorCols cols j b) = 0
  unfold XiToeplitzEntry
  rw [if_neg (Nat.not_le_of_gt (ha0 b))]

/-- A zero-column support cofactor has determinant zero. -/
theorem xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
    {rows cols : Fin 4 → ℕ} {j : Fin 4}
    (hZeroColumn : XiMinorFourBandedCofactorZeroColumnSupport rows cols j) :
    (Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))).det = 0 := by
  rcases hZeroColumn with ⟨b0, hb0⟩
  apply Matrix.det_eq_zero_of_column_eq_zero b0
  intro a
  change
    XiToeplitzEntry
      (XiMinorFourBandedCofactorRows rows a)
      (XiMinorFourBandedCofactorCols cols j b0) = 0
  unfold XiToeplitzEntry
  rw [if_neg (Nat.not_le_of_gt (hb0 a))]

/-- If a support kind is inactive, then the corresponding cofactor determinant
vanishes.  Inactive kinds are exactly the zero-row and zero-column classes. -/
theorem xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind
    {kind : XiMinorFourBandedCofactorSupportKind}
    {rows cols : Fin 4 → ℕ} {j : Fin 4}
    (hKind : XiMinorFourBandedCofactorSupportKindHolds kind rows cols j)
    (hInactive : ¬ XiMinorFourBandedCofactorSupportKindActive kind) :
    (Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))).det = 0 := by
  cases kind
  · exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport hKind
  · exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport hKind
  · exact False.elim (hInactive (by
      simp [XiMinorFourBandedCofactorSupportKindActive]))
  · exact False.elim (hInactive (by
      simp [XiMinorFourBandedCofactorSupportKindActive]))

/-- Support-kind case-table form of the cofactor support-split frontier.

This is the finite `4^3` support-kind table for the three surviving cofactors.
It is the right target for case-local arguments: zero-row and zero-column cases
should collapse determinants to zero, full-support cases should use ordinary
contiguous-kernel positivity, and banded cases carry the genuinely new sparse
`3 × 3` inequality. -/
def XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Reduced case-table form after the all-structural-zero rows have been
discharged.

Only triples with at least one active (`full` or `banded`) cofactor remain.
The complementary all-zero-kind triples are automatic because each cofactor
determinant is zero. -/
def XiMinorFourBandedCofactorNonzeroCaseTableInequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    (XiMinorFourBandedCofactorSupportKindActive kind0 ∨
      XiMinorFourBandedCofactorSupportKindActive kind1 ∨
        XiMinorFourBandedCofactorSupportKindActive kind2) →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Exactly one of the three surviving cofactors is active. -/
def XiMinorFourBandedCofactorExactlyOneActive
    (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind) : Prop :=
  (XiMinorFourBandedCofactorSupportKindActive kind0 ∧
      ¬ XiMinorFourBandedCofactorSupportKindActive kind1 ∧
      ¬ XiMinorFourBandedCofactorSupportKindActive kind2) ∨
    (¬ XiMinorFourBandedCofactorSupportKindActive kind0 ∧
      XiMinorFourBandedCofactorSupportKindActive kind1 ∧
      ¬ XiMinorFourBandedCofactorSupportKindActive kind2) ∨
      (¬ XiMinorFourBandedCofactorSupportKindActive kind0 ∧
        ¬ XiMinorFourBandedCofactorSupportKindActive kind1 ∧
        XiMinorFourBandedCofactorSupportKindActive kind2)

/-- At least two of the three surviving cofactors are active. -/
def XiMinorFourBandedCofactorAtLeastTwoActive
    (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind) : Prop :=
  (XiMinorFourBandedCofactorSupportKindActive kind0 ∧
      XiMinorFourBandedCofactorSupportKindActive kind1) ∨
    (XiMinorFourBandedCofactorSupportKindActive kind0 ∧
      XiMinorFourBandedCofactorSupportKindActive kind2) ∨
      (XiMinorFourBandedCofactorSupportKindActive kind1 ∧
        XiMinorFourBandedCofactorSupportKindActive kind2)

/-- One-survivor case-table target for the cofactor frontier.

This isolates rows where the signed three-cofactor expression has only one
potentially nonzero determinant after structural-zero cofactors are removed. -/
def XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorExactlyOneActive kind0 kind1 kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- One-survivor target where the only active cofactor is `j = 0`. -/
def XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- One-survivor target where the only active cofactor is `j = 1`.

This is the signed-negative survivor and should be isolated from the two
positive side survivors. -/
def XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    XiMinorFourBandedCofactorSupportKindActive kind1 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Determinant-sign target for the signed-negative `j = 1` one-survivor case.

Once the side cofactors are inactive, the cofactor expansion reduces to
`- A01 * det(C1)`.  Since `A01` is nonnegative under contiguous positivity, the
signed-negative survivor is discharged by showing the surviving middle cofactor
determinant is nonpositive. -/
def XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    XiMinorFourBandedCofactorSupportKindActive kind1 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 1 b))).det ≤ 0

/-- Full-support middle-cofactor determinant-sign target for the
signed-negative `j = 1` one-survivor case. -/
def XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig : Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 1 b))).det ≤ 0

/-- Moment-index form of the full-support middle-cofactor determinant-sign
target for the signed-negative `j = 1` one-survivor case. -/
def XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiMomentCoeff
          (XiMinorFourBandedCofactorRows rows a -
            XiMinorFourBandedCofactorCols cols 1 b))).det ≤ 0

/-- Moment-index zero-determinant form of the full-support middle-cofactor
obstruction for the signed-negative `j = 1` one-survivor case.

This is the compatible edge of the sign conflict: ordinary full-support PF
would push the determinant nonnegative, while the signed middle survivor needs
it nonpositive.  Equality is the clean meeting point. -/
def XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiMomentCoeff
          (XiMinorFourBandedCofactorRows rows a -
            XiMinorFourBandedCofactorCols cols 1 b))).det = 0

/-- Structural impossibility of the full-support middle cofactor in the signed
`j = 1` one-survivor case.

The inactive `j = 2` side cofactor cannot coexist with full support of the
middle `j = 1` cofactor and the global lower-right support. -/
def XiJ1FullSupportImpossibleFromSupport : Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    False

/-- Banded middle-cofactor determinant-sign target for the signed-negative
`j = 1` one-survivor case. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig : Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 1 b))).det ≤ 0

/-- Expanded sparse determinant form of the banded middle-cofactor
determinant-sign target for the signed-negative `j = 1` one-survivor case. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 0) (c 0) *
          (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1))
        - XiToeplitzEntry (r 0) (c 1) *
          (XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))
        ≤ 0

/-- Product-dominance form of the expanded banded middle-cofactor obstruction.

This names the remaining algebra in the sparse `j = 1` middle cofactor: the
`T00`-weighted adjacent `2 × 2` minor must be dominated by the `T01`-weighted
skew `2 × 2` minor. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 0) (c 0) *
          (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1))
        ≤ XiToeplitzEntry (r 0) (c 1) *
          (XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Bracket-sign form of the banded middle product-dominance obstruction.

This splits the product comparison into two signed `2 × 2` bracket claims.  The
Toeplitz prefactors are nonnegative from contiguous `1 × 1` positivity, so a
nonpositive left bracket and a nonnegative right bracket imply product
dominance. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Left bracket nonpositivity target inside the banded middle `j = 1`
cofactor obstruction. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedLeftBracketNonposFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0

/-- Right bracket nonnegativity target inside the banded middle `j = 1`
cofactor obstruction. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedRightBracketNonnegFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0)

/-- Split left/right bracket-sign target for the banded middle `j = 1`
cofactor obstruction. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig :
    Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ1BandedLeftBracketNonposFromContig ∧
    XiMinorFourBandedCofactorOneSurvivorJ1BandedRightBracketNonnegFromContig

/-- Top-supported branch of the split bracket target.

This is the branch where the far-right selected cofactor column is still
supported in the first bracket row, so all entries in the two bracket
determinants are supported and can later be rewritten into moment gaps. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorCols cols 1 2 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Moment-gap form of the top-supported banded middle bracket target. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorCols cols 1 2 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiMomentCoeff (r 1 - c 1) * XiMomentCoeff (r 2 - c 2)
        - XiMomentCoeff (r 1 - c 2) * XiMomentCoeff (r 2 - c 1) ≤ 0) ∧
      (0 ≤ XiMomentCoeff (r 1 - c 0) * XiMomentCoeff (r 2 - c 2)
        - XiMomentCoeff (r 1 - c 2) * XiMomentCoeff (r 2 - c 0))

/-- Structural impossibility of the top-supported branch.

The inactive `j = 2` side cofactor cannot coexist with the banded middle
cofactor and support of the far-right middle cofactor column in the first
bracket row. -/
def XiJ1TopSupportedImpossibleFromSupport : Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorCols cols 1 2 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    False

/-- Top-unsupported branch of the split bracket target.

This is the complementary branch where the far-right selected cofactor column
lies above the first bracket row, so the entries involving that row and column
are forced zero. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- The remaining hard subcase of the top-unsupported branch: the far-right
cofactor column is above the first bracket row, but the middle cofactor column
is still supported there. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Short alias for the remaining top-unsupported, middle-supported branch. -/
def XiJ1TopUnsupportedMiddleSupportedBracketsFromContig : Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig

/-- Moment-product form of the top-unsupported, middle-supported branch.

In this branch the far-right top entry is structurally zero, so the left
bracket has no cancellation term.  This exposes the hard product-sign
obstruction directly in signed-moment coordinates. -/
def XiJ1TopUnsupportedMiddleSupportedMomentProductFromContig :
    Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiMomentCoeff (r 1 - c 1) * XiMomentCoeff (r 2 - c 2) ≤ 0 ∧
      0 ≤ XiMomentCoeff (r 1 - c 0) * XiMomentCoeff (r 2 - c 2)

/-- Structural impossibility of the top-unsupported, middle-supported branch.

The inactive side cofactor at `j = 2`, together with the banded `j = 1`
support pattern, cannot coexist with `c₁ ≤ r₁ < c₂` in the middle cofactor.
This removes the suspicious product-sign obstruction from the main route. -/
def XiJ1TopUnsupportedMiddleSupportedImpossibleFromSupport : Prop :=
  ∀ (kind0 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    False

/-- Top-support split of the banded bracket target. -/
def XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportSplitBracketsFromContig :
    Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig ∧
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig

/-- Full and banded middle-cofactor sign targets together imply the signed
middle nonpositive determinant target. -/
def XiMinorFourBandedCofactorOneSurvivorJ1SupportNonposDetFromContig :
    Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig ∧
    XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig

/-- One-survivor target where the only active cofactor is `j = 2`. -/
def XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
    XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Positive-side one-survivor target: the `j = 0` and `j = 2` one-survivor
rows, both of which enter the cofactor expansion with positive sign. -/
def XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig : Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig ∧
    XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig

/-- Positive `j = 0` one-survivor target when the active cofactor is
full-support. -/
def XiMinorFourBandedCofactorOneSurvivorJ0FullInequalityFromContig : Prop :=
  ∀ (kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Positive `j = 0` one-survivor target when the active cofactor is
banded-support. -/
def XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig : Prop :=
  ∀ (kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Positive `j = 2` one-survivor target when the active cofactor is
full-support. -/
def XiMinorFourBandedCofactorOneSurvivorJ2FullInequalityFromContig : Prop :=
  ∀ (kind0 kind1 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Positive `j = 2` one-survivor target when the active cofactor is
banded-support. -/
def XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig : Prop :=
  ∀ (kind0 kind1 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
    ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Positive-side banded one-survivor target: the two side cofactors `j = 0`
and `j = 2` when the active surviving cofactor has banded support. -/
def XiMinorFourBandedCofactorPositiveBandedOneSurvivorInequalityFromContig :
    Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig ∧
    XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig

/-- Positive-side full-support one-survivor target: the two side cofactors
`j = 0` and `j = 2` when the active surviving cofactor has full support. -/
def XiMinorFourBandedCofactorPositiveFullOneSurvivorInequalityFromContig :
    Prop :=
  XiMinorFourBandedCofactorOneSurvivorJ0FullInequalityFromContig ∧
    XiMinorFourBandedCofactorOneSurvivorJ2FullInequalityFromContig

/-- Determinant-level positive full-support one-survivor target.

This removes the signed `4 × 4` cofactor expansion from the positive full-side
survivor problem.  It asks only for nonnegativity of the surviving full-support
side cofactor determinant in the `j = 0` and `j = 2` cases; inactive neighboring
cofactors are handled by zero-row/zero-column support. -/
def XiMinorFourBandedCofactorPositiveFullDetFromContig : Prop :=
  (∀ (kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
      (rows cols : Fin 4 → ℕ),
      StrictMono rows → StrictMono cols →
      cols 0 ≤ rows 0 →
      rows 0 < cols 3 →
      cols 3 ≤ rows 3 →
      XiMinorFourBandedCofactorFullSupport rows cols 0 →
      XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
      XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
      ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
      ¬ XiMinorFourBandedCofactorSupportKindActive kind2 →
      XiContigToeplitzTotalPositive →
        0 ≤ (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 0 b))).det) ∧
    (∀ (kind0 kind1 : XiMinorFourBandedCofactorSupportKind)
      (rows cols : Fin 4 → ℕ),
      StrictMono rows → StrictMono cols →
      cols 0 ≤ rows 0 →
      rows 0 < cols 3 →
      cols 3 ≤ rows 3 →
      XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
      XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
      XiMinorFourBandedCofactorFullSupport rows cols 2 →
      ¬ XiMinorFourBandedCofactorSupportKindActive kind0 →
      ¬ XiMinorFourBandedCofactorSupportKindActive kind1 →
      XiContigToeplitzTotalPositive →
        0 ≤ (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 2 b))).det)

/-- The ordinary full-support `3 × 3` target proves determinant-level
positive full-support side-survivor control for the `4 × 4` cofactor frontier.

This is the important reduction: once the neighboring cofactors are inactive,
the positive full side survivor only needs the determinant of its own
full-support `3 × 3` cofactor to be nonnegative. -/
theorem xiMinorFourBandedCofactorPositiveFullDet_of_threeFull
    (hThreeFull : XiMinorThreeFullSupportFromContig) :
    XiMinorFourBandedCofactorPositiveFullDetFromContig := by
  constructor
  · intro kind1 kind2 rows cols hRows hCols _hLeft _hGap _hRight
      hFull _hK1 _hK2 _h1 _h2 hContig
    exact hThreeFull
      (XiMinorFourBandedCofactorRows rows)
      (XiMinorFourBandedCofactorCols cols 0)
      (xiMinorFourBandedCofactorRows_strictMono hRows)
      (xiMinorFourBandedCofactorCols_strictMono hCols 0)
      hFull
      hContig
  · intro kind0 kind1 rows cols hRows hCols _hLeft _hGap _hRight
      _hK0 _hK1 hFull _h0 _h1 hContig
    exact hThreeFull
      (XiMinorFourBandedCofactorRows rows)
      (XiMinorFourBandedCofactorCols cols 2)
      (xiMinorFourBandedCofactorRows_strictMono hRows)
      (xiMinorFourBandedCofactorCols_strictMono hCols 2)
      hFull
      hContig

/-- The ordinary banded `3 × 3` determinant target proves the positive-side
banded one-survivor cofactor target for the `4 × 4` frontier. -/
theorem xiMinorFourBandedCofactorPositiveBandedOneSurvivor_of_threeBandedDet
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig) :
    XiMinorFourBandedCofactorPositiveBandedOneSurvivorInequalityFromContig := by
  constructor
  · intro kind1 kind2 rows cols hRows hCols _hLeft _hGap _hRight
      hBanded hK1 hK2 h1 h2 hContig
    have hdet0 := hThreeBanded
      (XiMinorFourBandedCofactorRows rows)
      (XiMinorFourBandedCofactorCols cols 0)
      (xiMinorFourBandedCofactorRows_strictMono hRows)
      (xiMinorFourBandedCofactorCols_strictMono hCols 0)
      hBanded.1
      hBanded.2.1
      hBanded.2.2
      hContig
    have hdet1 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 1 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK1 h1
    have hdet2 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 2 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK2 h2
    have hcoeff :
        0 ≤
          (Matrix.of (fun a b =>
            if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)))
            0 0 := by
      simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
    simpa [hdet1, hdet2] using mul_nonneg hcoeff hdet0
  · intro kind0 kind1 rows cols hRows hCols _hLeft _hGap _hRight
      hK0 hK1 hBanded h0 h1 hContig
    have hdet2 := hThreeBanded
      (XiMinorFourBandedCofactorRows rows)
      (XiMinorFourBandedCofactorCols cols 2)
      (xiMinorFourBandedCofactorRows_strictMono hRows)
      (xiMinorFourBandedCofactorCols_strictMono hCols 2)
      hBanded.1
      hBanded.2.1
      hBanded.2.2
      hContig
    have hdet0 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 0 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK0 h0
    have hdet1 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 1 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK1 h1
    have hcoeff :
        0 ≤
          (Matrix.of (fun a b =>
            if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)))
            0 2 := by
      simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
    simpa [hdet0, hdet1] using mul_nonneg hcoeff hdet2

/-- A nonpositive determinant for the signed middle survivor implies the
signed-negative `j = 1` one-survivor target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1_of_nonposDet
    (hNonpos : XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h0 h1 h2 hContig
  have hdet0 :
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 0 b))).det = 0 :=
    xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK0 h0
  have hdet2 :
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 2 b))).det = 0 :=
    xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK2 h2
  have hdet1 := hNonpos kind0 kind1 kind2 rows cols hRows hCols hLeft hGap
    hRight hK0 hK1 hK2 h0 h1 h2 hContig
  have hcoeff :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)))
          0 1 := by
    simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 1)
  have hmiddle :
      0 ≤ -(
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)))
          0 1 *
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 1 b))).det) := by
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hcoeff hdet1)
  simpa [hdet0, hdet2] using hmiddle

/-- Splitting the active middle cofactor into full-support and banded-support
cases proves the signed-middle nonpositive determinant target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1NonposDet_of_supportSplit
    (hSplit :
      XiMinorFourBandedCofactorOneSurvivorJ1SupportNonposDetFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h0 h1 h2 hContig
  cases kind1
  · have hNot :
        ¬ XiMinorFourBandedCofactorSupportKindActive .zeroRow := by
      simp [XiMinorFourBandedCofactorSupportKindActive]
    exact False.elim (hNot h1)
  · have hNot :
        ¬ XiMinorFourBandedCofactorSupportKindActive .zeroColumn := by
      simp [XiMinorFourBandedCofactorSupportKindActive]
    exact False.elim (hNot h1)
  · exact hSplit.1 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h0 h2 hContig
  · exact hSplit.2 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h0 h2 hContig

/-- The moment-index full-support middle determinant-sign target implies the
Toeplitz-entry full-support middle determinant-sign target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1FullNonposDet_of_moment
    (hMoment :
      XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1FullNonposDetFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hFull hK2 h0 h2 hContig
  have h := hMoment kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hFull hK2 h0 h2 hContig
  rw [Matrix.det_fin_three]
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply] at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 0)
        (hFull 0 0),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 1)
        (hFull 0 1),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 2)
        (hFull 0 2),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
        (hFull 1 0),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        (hFull 1 1),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2)
        (hFull 1 2),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 0)
        (hFull 2 0),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 1)
        (hFull 2 1),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        (hFull 2 2)]
  exact h

/-- The full-support middle cofactor is structurally impossible in the
signed-negative one-survivor row.  The inactive `j = 2` side cofactor
contradicts the full support of the `j = 1` cofactor or the global lower-right
support. -/
theorem xiJ1FullSupportImpossible_of_support :
    XiJ1FullSupportImpossibleFromSupport := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hFull hK2 h0 h2
  have hFull00 : cols 0 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull 0 0
  have hFull01 : cols 2 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull 0 1
  have hFull02 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull 0 2
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  cases kind2 with
  | zeroRow =>
      rcases hK2 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 2 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
  | zeroColumn =>
      rcases hK2 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      exact False.elim (h2 xiMinorFourBandedCofactorSupportKindActive_full)
  | banded =>
      exact False.elim (h2 xiMinorFourBandedCofactorSupportKindActive_banded)

/-- An impossible full-support middle cofactor proves the moment zero target
vacuously. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_impossible
    (hImpossible : XiJ1FullSupportImpossibleFromSupport) :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hFull hK2 h0 h2 hContig
  exact False.elim (hImpossible kind0 kind2 rows cols hRows hCols hLeft
    hGap hRight hK0 hFull hK2 h0 h2)

/-- The full-support middle cofactor zero target is discharged by support
bookkeeping alone. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_support :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig :=
  xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_impossible
    xiJ1FullSupportImpossible_of_support

/-- A zero determinant proves the moment-index nonpositive determinant target
for the full-support signed middle cofactor. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDet_of_zero
    (hZero :
      XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hFull hK2 h0 h2 hContig
  rw [hZero kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hFull hK2 h0 h2 hContig]

/-- The moment-gap top-supported bracket target rewrites to the Toeplitz-entry
top-supported bracket target. -/
theorem
    xiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBrackets_of_moment
    (hMoment :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hTop hContig
  have h := hMoment kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hTop hContig
  have hCofRows := xiMinorFourBandedCofactorRows_strictMono hRows
  have hCofCols := xiMinorFourBandedCofactorCols_strictMono hCols 1
  have h20 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 1 := by
    exact le_trans hBanded.1 (le_of_lt (hCofRows (by decide)))
  have h21 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1 := by
    exact le_trans (le_of_lt (hCofCols (by decide))) hTop
  have h22 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 1 :=
    hTop
  have h30 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h20 (le_of_lt (hCofRows (by decide)))
  have h31 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h21 (le_of_lt (hCofRows (by decide)))
  have h32 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    hBanded.2.2
  dsimp only at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h21,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h32,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h22,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h31,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h20,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h30]
  exact h

/-- The top-supported branch is structurally impossible.  The inactive `j = 2`
side cofactor contradicts the banded `j = 1` lower-left support, the
top-supported far-right column, and the global lower-right support. -/
theorem xiJ1TopSupportedImpossible_of_support :
    XiJ1TopSupportedImpossibleFromSupport := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hTop
  have hB0 : cols 0 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded.1
  have hTop' : cols 3 ≤ rows 2 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hTop
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind2 with
  | zeroRow =>
      rcases hK2 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 2 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
  | zeroColumn =>
      rcases hK2 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 2 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 1
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      exact False.elim (h2 xiMinorFourBandedCofactorSupportKindActive_full)
  | banded =>
      exact False.elim (h2 xiMinorFourBandedCofactorSupportKindActive_banded)

/-- An impossible top-supported branch proves its bracket target vacuously. -/
theorem xiJ1TopSupportedSplitBrackets_of_impossible
    (hImpossible : XiJ1TopSupportedImpossibleFromSupport) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hTop hContig
  exact False.elim (hImpossible kind0 kind2 rows cols hRows hCols hLeft
    hGap hRight hK0 hBanded hK2 h0 h2 hTop)

/-- The top-supported branch is discharged by support bookkeeping alone. -/
theorem xiJ1TopSupportedSplitBrackets_of_support :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig :=
  xiJ1TopSupportedSplitBrackets_of_impossible
    xiJ1TopSupportedImpossible_of_support

/-- The moment-product obstruction proves the top-unsupported,
middle-supported bracket target after rewriting all supported Toeplitz entries
to signed moments and the far-right top entry to zero. -/
theorem
    xiJ1TopUnsupportedMiddleSupportedBrackets_of_momentProduct
    (hMoment :
      XiJ1TopUnsupportedMiddleSupportedMomentProductFromContig) :
    XiJ1TopUnsupportedMiddleSupportedBracketsFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hUnsupported hMiddle hContig
  have h := hMoment kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hUnsupported hMiddle hContig
  have hCofRows := xiMinorFourBandedCofactorRows_strictMono hRows
  have hCofCols := xiMinorFourBandedCofactorCols_strictMono hCols 1
  have h20 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 1 := by
    exact le_trans hBanded.1 (le_of_lt (hCofRows (by decide)))
  have h21 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1 :=
    hMiddle
  have h12zero :
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hUnsupported)]
  have h30 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h20 (le_of_lt (hCofRows (by decide)))
  have h31 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h21 (le_of_lt (hCofRows (by decide)))
  have h32 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    hBanded.2.2
  dsimp only at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h21,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h32,
      h12zero,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h31,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h20,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h30]
  constructor
  · simpa using h.1
  · simpa using h.2

/-- The top-unsupported, middle-supported branch is structurally impossible.

Only the inactive `j = 2` side cofactor is needed: if it has a zero row, that
row is forced above `cols 0`, contradicting the banded lower-left support of
the middle cofactor; if it has a zero column, the column is forced below a
supported row or the global lower-right support. -/
theorem xiJ1TopUnsupportedMiddleSupportedImpossible_of_support :
    XiJ1TopUnsupportedMiddleSupportedImpossibleFromSupport := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hUnsupported hMiddle
  have hB0 : cols 0 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded.1
  have hMid : cols 2 ≤ rows 2 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hMiddle
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  cases kind2 with
  | zeroRow =>
      rcases hK2 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 2 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
  | zeroColumn =>
      rcases hK2 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 2 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 1
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      exact False.elim (h2 xiMinorFourBandedCofactorSupportKindActive_full)
  | banded =>
      exact False.elim (h2 xiMinorFourBandedCofactorSupportKindActive_banded)

/-- An impossible branch proves the top-unsupported, middle-supported bracket
target vacuously. -/
theorem
    xiJ1TopUnsupportedMiddleSupportedBrackets_of_impossible
    (hImpossible :
      XiJ1TopUnsupportedMiddleSupportedImpossibleFromSupport) :
    XiJ1TopUnsupportedMiddleSupportedBracketsFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hUnsupported hMiddle hContig
  exact False.elim (hImpossible kind0 kind2 rows cols hRows hCols hLeft
    hGap hRight hK0 hBanded hK2 h0 h2 hUnsupported hMiddle)

/-- The top-unsupported, middle-supported branch is discharged by support
bookkeeping alone. -/
theorem xiJ1TopUnsupportedMiddleSupportedBrackets_of_support :
    XiJ1TopUnsupportedMiddleSupportedBracketsFromContig :=
  xiJ1TopUnsupportedMiddleSupportedBrackets_of_impossible
    xiJ1TopUnsupportedMiddleSupportedImpossible_of_support

/-- The top-unsupported branch reduces to the middle-supported subcase; when
the middle column is also unsupported in the first bracket row, the needed
bracket signs follow from forced zeros and entry nonnegativity. -/
theorem
    xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_middleSupported
    (hMiddle :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hUnsupported hContig
  by_cases hMid :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1
  · exact hMiddle kind0 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hBanded hK2 h0 h2 hUnsupported hMid hContig
  · have hMidUnsupported :
        XiMinorFourBandedCofactorRows rows 1 <
          XiMinorFourBandedCofactorCols cols 1 1 :=
      Nat.lt_of_not_ge hMid
    have h11 :
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 1)
          (XiMinorFourBandedCofactorCols cols 1 1) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt hMidUnsupported)]
    have h12 :
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 1)
          (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt hUnsupported)]
    have h10nonneg :
        0 ≤ XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 1)
          (XiMinorFourBandedCofactorCols cols 1 0) :=
      xiToeplitzEntry_nonneg_of_contig hContig
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
    have h22nonneg :
        0 ≤ XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 2)
          (XiMinorFourBandedCofactorCols cols 1 2) :=
      xiToeplitzEntry_nonneg_of_contig hContig
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
    dsimp only
    rw [h11, h12]
    constructor
    · norm_num
    · simpa using mul_nonneg h10nonneg h22nonneg

/-- The full top-unsupported branch follows from support bookkeeping alone:
the middle-supported subcase is impossible, and the middle-unsupported subcase
is forced by zeros and entry nonnegativity. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_support :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig :=
  xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_middleSupported
    xiJ1TopUnsupportedMiddleSupportedBrackets_of_support

/-- Splitting on whether the top bracket row supports the far-right cofactor
column proves the split left/right bracket target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBrackets_of_topSupportSplit
    (hTopSplit :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportSplitBracketsFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig := by
  constructor
  · intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hBanded hK2 h0 h2 hContig
    by_cases hTop :
        XiMinorFourBandedCofactorCols cols 1 2 ≤
          XiMinorFourBandedCofactorRows rows 1
    · exact (hTopSplit.1 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hBanded hK2 h0 h2 hTop hContig).1
    · have hUnsupported :
          XiMinorFourBandedCofactorRows rows 1 <
            XiMinorFourBandedCofactorCols cols 1 2 :=
        Nat.lt_of_not_ge hTop
      exact (hTopSplit.2 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hBanded hK2 h0 h2 hUnsupported hContig).1
  · intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hBanded hK2 h0 h2 hContig
    by_cases hTop :
        XiMinorFourBandedCofactorCols cols 1 2 ≤
          XiMinorFourBandedCofactorRows rows 1
    · exact (hTopSplit.1 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hBanded hK2 h0 h2 hTop hContig).2
    · have hUnsupported :
          XiMinorFourBandedCofactorRows rows 1 <
            XiMinorFourBandedCofactorCols cols 1 2 :=
        Nat.lt_of_not_ge hTop
      exact (hTopSplit.2 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hBanded hK2 h0 h2 hUnsupported hContig).2

/-- Split left/right bracket targets imply the bundled bracket-sign target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSigns_of_split
    (hSplit :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBracketsFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  exact
    ⟨hSplit.1 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hBanded hK2 h0 h2 hContig,
      hSplit.2 kind0 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hBanded hK2 h0 h2 hContig⟩

/-- Bracket signs imply product dominance for the banded middle obstruction. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominance_of_bracketSigns
    (hSigns :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  have h := hSigns kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  have h00 :
      0 ≤ XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 0) :=
    xiToeplitzEntry_nonneg_of_contig hContig
      (XiMinorFourBandedCofactorRows rows 0)
      (XiMinorFourBandedCofactorCols cols 1 0)
  have h01 :
      0 ≤ XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 1) :=
    xiToeplitzEntry_nonneg_of_contig hContig
      (XiMinorFourBandedCofactorRows rows 0)
      (XiMinorFourBandedCofactorCols cols 1 1)
  have hLeftProd :
      XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 0)
          (XiMinorFourBandedCofactorCols cols 1 0) *
        (XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 1)
            (XiMinorFourBandedCofactorCols cols 1 1) *
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 2)
            (XiMinorFourBandedCofactorCols cols 1 2)
          - XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 1)
            (XiMinorFourBandedCofactorCols cols 1 2) *
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 2)
            (XiMinorFourBandedCofactorCols cols 1 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h00 h.1
  have hRightProd :
      0 ≤
        XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 0)
            (XiMinorFourBandedCofactorCols cols 1 1) *
          (XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 1)
              (XiMinorFourBandedCofactorCols cols 1 0) *
            XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 2)
              (XiMinorFourBandedCofactorCols cols 1 2)
            - XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 1)
              (XiMinorFourBandedCofactorCols cols 1 2) *
            XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 2)
              (XiMinorFourBandedCofactorCols cols 1 0)) :=
    mul_nonneg h01 h.2
  linarith

/-- Product dominance implies the expanded sparse determinant obstruction. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonpos_of_productDominance
    (hDom :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  have h := hDom kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  linarith

/-- The expanded sparse determinant target implies the determinant-form
banded middle-cofactor obstruction. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDet_of_expanded
    (hExp :
      XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig := by
  intro kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  have h02 :
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hBanded.2.1)]
  have h := hExp kind0 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hBanded hK2 h0 h2 hContig
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [h02]
  ring_nf at h ⊢
  exact h

/-- Multi-survivor case-table target for the cofactor frontier.

This is where the real cancellation problem remains, especially rows involving
the negative middle cofactor. -/
def XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorAtLeastTwoActive kind0 kind1 kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- The support-kind triples that survive the multi-survivor structural
bookkeeping probe.

The remaining active rows are the three all-active patterns plus the case where
the left side cofactor is certified by a structural zero row while the middle
and right cofactors are banded. -/
def XiMinorFourBandedCofactorReducedMultiKindTriple
    (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind) : Prop :=
  (kind0 = .full ∧ kind1 = .full ∧ kind2 = .full) ∨
    (kind0 = .banded ∧ kind1 = .banded ∧ kind2 = .banded) ∨
      (kind0 = .zeroRow ∧ kind1 = .banded ∧ kind2 = .banded)

/-- Support-bookkeeping target reducing the multi-survivor table to the three
realizable support-kind triples. -/
def XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport : Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorAtLeastTwoActive kind0 kind1 kind2 →
      XiMinorFourBandedCofactorReducedMultiKindTriple kind0 kind1 kind2

/-- Pair-`01` support-bookkeeping target for the multi-survivor reduction.

This isolates the case where the left and middle cofactors are active. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport :
    Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorSupportKindActive kind0 →
    XiMinorFourBandedCofactorSupportKindActive kind1 →
      XiMinorFourBandedCofactorReducedMultiKindTriple kind0 kind1 kind2

/-- Pair-`02` support-bookkeeping target for the multi-survivor reduction.

This isolates the case where the left and right cofactors are active. -/
def XiMinorFourBandedCofactorMultiSurvivorPair02KindReductionFromSupport :
    Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorSupportKindActive kind0 →
    XiMinorFourBandedCofactorSupportKindActive kind2 →
      XiMinorFourBandedCofactorReducedMultiKindTriple kind0 kind1 kind2

/-- Pair-`12` support-bookkeeping target for the multi-survivor reduction.

This isolates the case where the middle and right cofactors are active. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12KindReductionFromSupport :
    Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorSupportKindActive kind1 →
    XiMinorFourBandedCofactorSupportKindActive kind2 →
      XiMinorFourBandedCofactorReducedMultiKindTriple kind0 kind1 kind2

/-- Active-pair split of the multi-survivor support-kind reduction. -/
def XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport ∧
    XiMinorFourBandedCofactorMultiSurvivorPair02KindReductionFromSupport ∧
      XiMinorFourBandedCofactorMultiSurvivorPair12KindReductionFromSupport

/-- Pair-`12`, full/full active-kind support target.

If the middle and right cofactors are full-support, the left cofactor must also
be full-support for the reduced multi-survivor triple. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFullFromSupport :
    Prop :=
  ∀ (kind0 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
      kind0 = .full

/-- Pair-`12`, full/banded active-kind impossibility target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossibleFromSupport :
    Prop :=
  ∀ (kind0 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
      False

/-- Pair-`12`, banded/full active-kind impossibility target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossibleFromSupport :
    Prop :=
  ∀ (kind0 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
      False

/-- Pair-`12`, banded/banded active-kind support target.

If the middle and right cofactors are banded, the left cofactor must be either
banded or structurally zero-row for the reduced multi-survivor triple. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReducedFromSupport :
    Prop :=
  ∀ (kind0 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
      kind0 = .banded ∨ kind0 = .zeroRow

/-- Active-kind split for the pair-`12` support-bookkeeping target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFullFromSupport ∧
    XiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossibleFromSupport ∧
      XiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossibleFromSupport ∧
        XiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReducedFromSupport

/-- Pair-kind package with the `12` pair split into active-kind cases. -/
def XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport ∧
    XiMinorFourBandedCofactorMultiSurvivorPair02KindReductionFromSupport ∧
      XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport

/-- The pair-`12` full/full active-kind case follows from support bookkeeping.

Full support for the middle cofactor forces the far-right deleted-column
support low enough that the left cofactor cannot be zero-row, zero-column, or
banded. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFull_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFullFromSupport := by
  intro kind0 rows cols hRows hCols _hLeft _hGap _hRight hK0 hFull1 hFull2
  have hFull1_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull1 0 2
  have hFull2_c1 : cols 1 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull2 0 1
  have hFull1_c1 : cols 2 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull1 0 1
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind0 with
  | zeroRow =>
      rcases hK0 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
      · have hBad : rows 2 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
  | zeroColumn =>
      rcases hK0 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 2 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
  | full =>
      rfl
  | banded =>
      have hBad : rows 1 < cols 3 := by
        simpa [XiMinorFourBandedCofactorRows,
          XiMinorFourBandedCofactorCols] using hK0.2.1
      omega

/-- The pair-`12` full/banded active-kind case is structurally impossible. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossible_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossibleFromSupport := by
  intro kind0 rows cols hRows hCols _hLeft _hGap _hRight _hK0 hFull1 hBanded2
  have hFull1_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull1 0 2
  have hBanded2_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded2.2.1
  omega

/-- The pair-`12` banded/full active-kind case is structurally impossible. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossible_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossibleFromSupport := by
  intro kind0 rows cols hRows hCols _hLeft _hGap _hRight _hK0 hBanded1 hFull2
  have hBanded1_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded1.2.1
  have hFull2_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull2 0 2
  omega

/-- The pair-`12` banded/banded active-kind case follows from support
bookkeeping: the left cofactor can only be banded or zero-row. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReduced_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReducedFromSupport := by
  intro kind0 rows cols hRows hCols _hLeft _hGap _hRight hK0 hBanded1 hBanded2
  have hBanded1_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded1.2.1
  have hBanded2_right : cols 3 ≤ rows 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded2.2.2
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind0 with
  | zeroRow =>
      exact Or.inr rfl
  | zeroColumn =>
      rcases hK0 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 3 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
      · have hBad : rows 3 < cols 2 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      have hFull_c2 : cols 3 ≤ rows 1 := by
        simpa [XiMinorFourBandedCofactorRows,
          XiMinorFourBandedCofactorCols] using hK0 0 2
      omega
  | banded =>
      exact Or.inl rfl

/-- The pair-`12` active-kind split is fully discharged by support
bookkeeping. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair12KindCases_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport :=
  ⟨xiMinorFourBandedCofactorMultiSurvivorPair12FullFullLeftFull_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair12FullBandedImpossible_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair12BandedFullImpossible_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair12BandedBandedLeftReduced_of_support⟩

/-- Pair-kind package after pair-`12` has been discharged structurally. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport ∧
    XiMinorFourBandedCofactorMultiSurvivorPair02KindReductionFromSupport

/-- Pair-`01` and pair-`02` support reductions are enough, because pair-`12`
is structurally discharged. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReduction_of_pair01_pair02
    (hPairs :
      XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport := by
  rcases hPairs with ⟨h01, h02⟩
  exact ⟨h01, h02,
    xiMinorFourBandedCofactorMultiSurvivorPair12KindCases_of_support⟩

/-- Pair-`02`, full/full active-kind support target.

If the left and right cofactors are full-support, the middle cofactor must also
be full-support for the reduced multi-survivor triple. -/
def XiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFullFromSupport :
    Prop :=
  ∀ (kind1 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
      kind1 = .full

/-- Pair-`02`, full/banded active-kind impossibility target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossibleFromSupport :
    Prop :=
  ∀ (kind1 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
      False

/-- Pair-`02`, banded/full active-kind impossibility target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossibleFromSupport :
    Prop :=
  ∀ (kind1 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
      False

/-- Pair-`02`, banded/banded active-kind support target.

If the left and right cofactors are banded, the middle cofactor must also be
banded for the reduced multi-survivor triple. -/
def XiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBandedFromSupport :
    Prop :=
  ∀ (kind1 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
      kind1 = .banded

/-- Active-kind split for the pair-`02` support-bookkeeping target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair02KindCasesFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFullFromSupport ∧
    XiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossibleFromSupport ∧
      XiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossibleFromSupport ∧
        XiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBandedFromSupport

/-- The pair-`02` full/full active-kind case follows from support
bookkeeping. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFull_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFullFromSupport := by
  intro kind1 rows cols hRows hCols hLeft _hGap _hRight hFull0 hK1 hFull2
  have hFull0_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull0 0 2
  have hFull2_c0 : cols 0 ≤ rows 1 :=
    le_trans hLeft (le_of_lt (hRows (by decide)))
  have hFull2_c1 : cols 1 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull2 0 1
  have hFull0_c1 : cols 2 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull0 0 1
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols01 : cols 0 < cols 1 := hCols (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind1 with
  | zeroRow =>
      rcases hK1 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
      · have hBad : rows 2 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
  | zeroColumn =>
      rcases hK1 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 2 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
  | full =>
      rfl
  | banded =>
      have hBad : rows 1 < cols 3 := by
        simpa [XiMinorFourBandedCofactorRows,
          XiMinorFourBandedCofactorCols] using hK1.2.1
      omega

/-- The pair-`02` full/banded active-kind case is structurally impossible. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossible_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossibleFromSupport := by
  intro kind1 rows cols hRows hCols _hLeft _hGap _hRight hFull0 _hK1 hBanded2
  have hFull0_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull0 0 2
  have hBanded2_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded2.2.1
  omega

/-- The pair-`02` banded/full active-kind case is structurally impossible. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossible_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossibleFromSupport := by
  intro kind1 rows cols hRows hCols _hLeft _hGap _hRight hBanded0 _hK1 hFull2
  have hBanded0_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded0.2.1
  have hFull2_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull2 0 2
  omega

/-- The pair-`02` banded/banded active-kind case follows from support
bookkeeping. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBanded_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBandedFromSupport := by
  intro kind1 rows cols hRows hCols hLeft _hGap _hRight hBanded0 hK1 hBanded2
  have hBanded0_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded0.2.1
  have hBanded2_right : cols 3 ≤ rows 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded2.2.2
  have hRows01 : rows 0 < rows 1 := hRows (by decide)
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols01 : cols 0 < cols 1 := hCols (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind1 with
  | zeroRow =>
      rcases hK1 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 2 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
  | zeroColumn =>
      rcases hK1 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
      · have hBad : rows 3 < cols 2 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      have hFull_c2 : cols 3 ≤ rows 1 := by
        simpa [XiMinorFourBandedCofactorRows,
          XiMinorFourBandedCofactorCols] using hK1 0 2
      omega
  | banded =>
      rfl

/-- The pair-`02` active-kind split is fully discharged by support
bookkeeping. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair02KindCases_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair02KindCasesFromSupport :=
  ⟨xiMinorFourBandedCofactorMultiSurvivorPair02FullFullMiddleFull_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair02FullBandedImpossible_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair02BandedFullImpossible_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair02BandedBandedMiddleBanded_of_support⟩

/-- The active-kind split proves the pair-`02` support-kind reduction. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair02KindReduction_of_cases
    (hCases :
      XiMinorFourBandedCofactorMultiSurvivorPair02KindCasesFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorPair02KindReductionFromSupport := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h0 h2
  rcases hCases with ⟨hFF, hFB, hBF, hBB⟩
  rcases h0 with rfl | rfl
  · rcases h2 with rfl | rfl
    · left
      exact ⟨rfl,
        hFF kind1 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2,
        rfl⟩
    · exact False.elim
        (hFB kind1 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2)
  · rcases h2 with rfl | rfl
    · exact False.elim
        (hBF kind1 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2)
    · right
      left
      exact ⟨rfl,
        hBB kind1 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2,
        rfl⟩

/-- Pair-kind package after pair-`02` and pair-`12` have been discharged
structurally. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport

/-- Pair-`01` alone is enough, because pair-`02` and pair-`12` are
structurally discharged. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReduction_of_pair01
    (h01 :
      XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport :=
  ⟨h01,
    xiMinorFourBandedCofactorMultiSurvivorPair02KindReduction_of_cases
      xiMinorFourBandedCofactorMultiSurvivorPair02KindCases_of_support⟩

/-- Pair-`01`, full/full active-kind support target.

If the left and middle cofactors are full-support, the right cofactor must also
be full-support for the reduced multi-survivor triple. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFullFromSupport :
    Prop :=
  ∀ (kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
      kind2 = .full

/-- Pair-`01`, full/banded active-kind impossibility target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossibleFromSupport :
    Prop :=
  ∀ (kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
      False

/-- Pair-`01`, banded/full active-kind impossibility target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossibleFromSupport :
    Prop :=
  ∀ (kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
      False

/-- Pair-`01`, banded/banded active-kind support target.

If the left and middle cofactors are banded, the right cofactor must also be
banded for the reduced multi-survivor triple. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBandedFromSupport :
    Prop :=
  ∀ (kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
      kind2 = .banded

/-- Active-kind split for the pair-`01` support-bookkeeping target. -/
def XiMinorFourBandedCofactorMultiSurvivorPair01KindCasesFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFullFromSupport ∧
    XiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossibleFromSupport ∧
      XiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossibleFromSupport ∧
        XiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBandedFromSupport

/-- The pair-`01` full/full active-kind case follows from support
bookkeeping. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFull_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFullFromSupport := by
  intro kind2 rows cols hRows hCols hLeft _hGap _hRight hFull0 hFull1 hK2
  have hFull0_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull0 0 2
  have hFull2_c0 : cols 0 ≤ rows 1 :=
    le_trans hLeft (le_of_lt (hRows (by decide)))
  have hFull2_c1 : cols 1 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull0 0 0
  have hFull1_c1 : cols 2 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull1 0 1
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols01 : cols 0 < cols 1 := hCols (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind2 with
  | zeroRow =>
      rcases hK2 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
      · have hBad : rows 2 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 2
        omega
  | zeroColumn =>
      rcases hK2 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 1 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
  | full =>
      rfl
  | banded =>
      have hBad : rows 1 < cols 3 := by
        simpa [XiMinorFourBandedCofactorRows,
          XiMinorFourBandedCofactorCols] using hK2.2.1
      omega

/-- The pair-`01` full/banded active-kind case is structurally impossible. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossible_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossibleFromSupport := by
  intro kind2 rows cols hRows hCols _hLeft _hGap _hRight hFull0 hBanded1 _hK2
  have hFull0_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull0 0 2
  have hBanded1_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded1.2.1
  omega

/-- The pair-`01` banded/full active-kind case is structurally impossible. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossible_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossibleFromSupport := by
  intro kind2 rows cols hRows hCols _hLeft _hGap _hRight hBanded0 hFull1 _hK2
  have hBanded0_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded0.2.1
  have hFull1_c2 : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull1 0 2
  omega

/-- The pair-`01` banded/banded active-kind case follows from support
bookkeeping. -/
theorem
    xiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBanded_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBandedFromSupport := by
  intro kind2 rows cols hRows hCols hLeft _hGap _hRight hBanded0 hBanded1 hK2
  have hBanded0_gap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded0.2.1
  have hBanded0_right : cols 3 ≤ rows 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded0.2.2
  have hRows01 : rows 0 < rows 1 := hRows (by decide)
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hRows23 : rows 2 < rows 3 := hRows (by decide)
  have hCols01 : cols 0 < cols 1 := hCols (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  have hCols23 : cols 2 < cols 3 := hCols (by decide)
  cases kind2 with
  | zeroRow =>
      rcases hK2 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 2 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
  | zeroColumn =>
      rcases hK2 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
      · have hBad : rows 3 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      have hFull_c2 : cols 3 ≤ rows 1 := by
        simpa [XiMinorFourBandedCofactorRows,
          XiMinorFourBandedCofactorCols] using hK2 0 2
      omega
  | banded =>
      rfl

/-- The pair-`01` active-kind split is fully discharged by support
bookkeeping. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair01KindCases_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair01KindCasesFromSupport :=
  ⟨xiMinorFourBandedCofactorMultiSurvivorPair01FullFullRightFull_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair01FullBandedImpossible_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair01BandedFullImpossible_of_support,
    xiMinorFourBandedCofactorMultiSurvivorPair01BandedBandedRightBanded_of_support⟩

/-- The active-kind split proves the pair-`01` support-kind reduction. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair01KindReduction_of_cases
    (hCases :
      XiMinorFourBandedCofactorMultiSurvivorPair01KindCasesFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorPair01KindReductionFromSupport := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h0 h1
  rcases hCases with ⟨hFF, hFB, hBF, hBB⟩
  rcases h0 with rfl | rfl
  · rcases h1 with rfl | rfl
    · left
      exact ⟨rfl, rfl,
        hFF kind2 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2⟩
    · exact False.elim
        (hFB kind2 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2)
  · rcases h1 with rfl | rfl
    · exact False.elim
        (hBF kind2 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2)
    · right
      left
      exact ⟨rfl, rfl,
        hBB kind2 rows cols hRows hCols hLeft hGap hRight hK0 hK1 hK2⟩

/-- The full multi-survivor support-kind reduction follows from support
bookkeeping alone. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReduction_of_support :
    XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport :=
  xiMinorFourBandedCofactorMultiSurvivorPair01KindReduction_of_cases
    xiMinorFourBandedCofactorMultiSurvivorPair01KindCases_of_support

/-- The active-kind split proves the pair-`12` support-kind reduction. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPair12KindReduction_of_cases
    (hCases :
      XiMinorFourBandedCofactorMultiSurvivorPair12KindCasesFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorPair12KindReductionFromSupport := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h1 h2
  rcases hCases with ⟨hFF, hFB, hBF, hBB⟩
  rcases h1 with rfl | rfl
  · rcases h2 with rfl | rfl
    · left
      exact ⟨hFF kind0 rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2, rfl, rfl⟩
    · exact False.elim
        (hFB kind0 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2)
  · rcases h2 with rfl | rfl
    · exact False.elim
        (hBF kind0 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2)
    · rcases hBB kind0 rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2 with hKind0 | hKind0
      · right
        left
        exact ⟨hKind0, rfl, rfl⟩
      · right
        right
        exact ⟨hKind0, rfl, rfl⟩

/-- The `12` active-kind split package proves the active-pair package. -/
theorem xiMinorFourBandedCofactorMultiSurvivorPairKindReduction_of_pair12Cases
    (hCases :
      XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport := by
  rcases hCases with ⟨h01, h02, h12Cases⟩
  exact ⟨h01, h02,
    xiMinorFourBandedCofactorMultiSurvivorPair12KindReduction_of_cases
      h12Cases⟩

/-- The three active-pair reductions prove the original at-least-two-active
support-kind reduction. -/
theorem xiMinorFourBandedCofactorMultiSurvivorKindReduction_of_pair
    (hPair :
      XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport) :
    XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 hActive
  rcases hPair with ⟨h01, h02, h12⟩
  rcases hActive with h01Active | hRest
  · exact h01 kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h01Active.1 h01Active.2
  · rcases hRest with h02Active | h12Active
    · exact h02 kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2 h02Active.1 h02Active.2
    · exact h12 kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2 h12Active.1 h12Active.2

/-- Reduced multi-survivor case table after support-kind classification. -/
def XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig :
    Prop :=
  ∀ (kind0 kind1 kind2 : XiMinorFourBandedCofactorSupportKind)
    (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 →
    XiMinorFourBandedCofactorSupportKindHolds kind1 rows cols 1 →
    XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 →
    XiMinorFourBandedCofactorReducedMultiKindTriple kind0 kind1 kind2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Generic support-parametrized dominance form for a reduced
multi-survivor row.

The three remaining reduced-row frontiers have the same cofactor inequality
shape.  The support predicates decide which cofactors are full, banded, or
structurally zero-row. -/
def XiMinorFourBandedCofactorMultiSupportDominanceFromContig
    (S0 S1 S2 : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Fin 4 → Prop) : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    S0 rows cols 0 →
    S1 rows cols 1 →
    S2 rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- Bare middle-cofactor dominance inequality for the reduced four-banded
`4 × 4` row.

This is the algebraic core of the current frontier: the signed middle cofactor
is dominated by the two side cofactors. -/
def XiMinorFourBandedCofactorMiddleDominance
    (rows cols : Fin 4 → ℕ) : Prop :=
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- Side-positive plus middle-upper-bound form of the bare middle-cofactor
dominance inequality.

The side nonnegativity clauses expose the natural total-positivity estimates;
the middle-bound clause is the remaining cancellation estimate. -/
def XiMinorFourBandedCofactorMiddleDominanceSideBound
    (rows cols : Fin 4 → ℕ) : Prop :=
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  0 ≤ A 0 0 * (C 0).det ∧
    0 ≤ A 0 2 * (C 2).det ∧
      A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- Side-cofactor nonnegativity part of the middle-dominance side-bound
package. -/
def XiMinorFourBandedCofactorMiddleDominanceSideNonnegative
    (rows cols : Fin 4 → ℕ) : Prop :=
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  0 ≤ A 0 0 * (C 0).det ∧
    0 ≤ A 0 2 * (C 2).det

/-- Pure determinant part of side-cofactor nonnegativity.

The missing entry signs are already supplied by contiguous total positivity, so
this isolates the real side-cofactor determinant frontier. -/
def XiMinorFourBandedCofactorSideDetNonnegative
    (rows cols : Fin 4 → ℕ) : Prop :=
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  0 ≤ (C 0).det ∧
    0 ≤ (C 2).det

/-- Left side-cofactor determinant nonnegativity, i.e. the `C0` side term. -/
def XiMinorFourBandedCofactorSideDetLeftNonnegative
    (rows cols : Fin 4 → ℕ) : Prop :=
  let C : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols 0 b))
  0 ≤ C.det

/-- Right side-cofactor determinant nonnegativity, i.e. the `C2` side term. -/
def XiMinorFourBandedCofactorSideDetRightNonnegative
    (rows cols : Fin 4 → ℕ) : Prop :=
  let C : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols 2 b))
  0 ≤ C.det

/-- Middle-term upper-bound part of the middle-dominance side-bound package.
-/
def XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound
    (rows cols : Fin 4 → ℕ) : Prop :=
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- Middle cofactor determinant nonpositivity, i.e. the sign condition on the
`C1` term that enters the row-zero cofactor expansion with negative sign. -/
def XiMinorFourBandedCofactorMiddleDetNonpositive
    (rows cols : Fin 4 → ℕ) : Prop :=
  let C : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols 1 b))
  C.det ≤ 0

/-- The separated side and middle estimates prove the side-bound package. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSideBound_of_parts
    {rows cols : Fin 4 → ℕ}
    (hSide :
      XiMinorFourBandedCofactorMiddleDominanceSideNonnegative rows cols)
    (hMiddle :
      XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound rows cols) :
    XiMinorFourBandedCofactorMiddleDominanceSideBound rows cols := by
  rcases hSide with ⟨hLeft, hRight⟩
  exact ⟨hLeft, hRight, hMiddle⟩

/-- The side-bound form proves the bare middle-cofactor dominance inequality.
-/
theorem xiMinorFourBandedCofactorMiddleDominance_of_sideBound
    {rows cols : Fin 4 → ℕ}
    (hBound : XiMinorFourBandedCofactorMiddleDominanceSideBound rows cols) :
    XiMinorFourBandedCofactorMiddleDominance rows cols := by
  rcases hBound with ⟨_hLeft, _hRight, hMiddle⟩
  exact hMiddle

/-- Pure row-geometry dominance form for a reduced multi-survivor row.

This removes the support predicates from the remaining frontier.  If this
determinant dominance holds for every four-banded reduced row geometry, then
all support-parametrized dominance instances follow. -/
def XiMinorFourBandedCofactorMultiRowGeometryDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- Middle-cofactor dominance over every reduced four-banded row geometry. -/
def XiMinorFourBandedCofactorMiddleDominanceFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDominance rows cols

/-- Side-bound form of middle-cofactor dominance over every reduced
four-banded row geometry. -/
def XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDominanceSideBound rows cols

/-- Side-cofactor nonnegativity over every reduced four-banded row geometry. -/
def XiMinorFourBandedCofactorMiddleDominanceSideNonnegativeFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDominanceSideNonnegative rows cols

/-- Pure side-cofactor determinant nonnegativity over every reduced
four-banded row geometry. -/
def XiMinorFourBandedCofactorSideDetNonnegativeFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorSideDetNonnegative rows cols

/-- Left side-cofactor determinant nonnegativity over every reduced
four-banded row geometry. -/
def XiMinorFourBandedCofactorSideDetLeftNonnegativeFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorSideDetLeftNonnegative rows cols

/-- Right side-cofactor determinant nonnegativity over every reduced
four-banded row geometry. -/
def XiMinorFourBandedCofactorSideDetRightNonnegativeFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorSideDetRightNonnegative rows cols

/-- Middle-term upper bound over every reduced four-banded row geometry. -/
def XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound rows cols

set_option linter.style.longLine false in
/-- Cancellation-aware middle-cofactor target restricted to the genuinely
hard branch where the middle cofactor determinant is positive.

When the middle determinant is nonpositive, contiguous entry positivity and
the already-controlled side cofactor determinants prove the upper bound
automatically. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

set_option linter.style.longLine false in
/-- Division-free side-allocation form of positive-middle cancellation.

The positive weighted middle cofactor is split into nonnegative left and right
shares.  Each share must fit under the corresponding side cofactor term.  This
is suited to a path-family or flow construction and remains meaningful when a
side term or a condensation pivot vanishes. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        ∃ leftShare rightShare : ℝ,
          0 ≤ leftShare ∧
          0 ≤ rightShare ∧
          leftShare + rightShare = A 0 1 * (C 1).det ∧
          leftShare ≤ A 0 0 * (C 0).det ∧
          rightShare ≤ A 0 2 * (C 2).det

set_option linter.style.longLine false in
/-- Compound-minor geometric-mean domination for the positive-middle branch.

Writing the weighted cofactor terms as `M`, `L`, and `R`, this asks for
`M^2 ≤ L * R`.  Since `L` and `R` are already nonnegative, the elementary
geometric-mean bound gives `M ≤ L + R`.  This is a stronger candidate route to
the side-allocation frontier, suitable for a Cauchy-Binet or compound-minor
argument, and is not claimed to follow from contiguity here. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean
    (rows cols : Fin 4 → ℕ) : Prop :=
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  (A 0 1 * (C 1).det) ^ 2 ≤
    (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det)

set_option linter.style.longLine false in
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean
          rows cols

set_option linter.style.longLine false in
/-- In the top-right-unsupported branch, only the left side can absorb the
positive middle term, so this is the exact one-sided cancellation target. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedLeftDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    rows 0 < cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det

set_option linter.style.longLine false in
/-- The only active subcase of top-right-unsupported left dominance: the
middle top-row entry is supported while the right top-row entry is zero. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det

set_option linter.style.longLine false in
/-- Moment/cofactor cross-product form of the active left-dominance interval.

Both top-row factors are supported here, so they rewrite to explicit signed Xi
moment coefficients.  This is the natural compound-ratio condition for the
two adjacent cofactor minors without introducing division. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    XiContigToeplitzTotalPositive →
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        XiMomentCoeff (rows 0 - cols 1) * (C 1).det ≤
          XiMomentCoeff (rows 0 - cols 0) * (C 0).det

set_option linter.style.longLine false in
/-- A subtraction-free contiguous-minor certificate for the active left
cofactor-ratio difference.

This is a concrete Cauchy-Binet/planar-network-style sufficient condition:
the target difference is a natural-coefficient sum of products of contiguous
Toeplitz minors, hence is nonnegative whenever the contiguous ladder holds. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificateFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    XiContigToeplitzTotalPositive →
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        XiContigMinorPositivePolynomial
          (XiMomentCoeff (rows 0 - cols 0) * (C 0).det -
            XiMomentCoeff (rows 0 - cols 1) * (C 1).det)

set_option linter.style.longLine false in
/-- Normalized cofactor-ratio form of the active moment/cofactor inequality.

The left cofactor is required to be positive, then the comparison is expressed
as `det C1 / det C0 ≤ μ0 / μ1`.  Under the positive kernel representation,
cross multiplication recovers the division-free moment/cofactor target. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatioFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    cols 1 ≤ rows 0 →
    rows 0 < cols 2 →
    XiContigToeplitzTotalPositive →
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        0 < (C 0).det ∧
          (C 1).det / (C 0).det ≤
            XiMomentCoeff (rows 0 - cols 0) /
              XiMomentCoeff (rows 0 - cols 1)

set_option linter.style.longLine false in
/-- Geometric-mean domination restricted to the branch where the top-right
side term is supported and can contribute to cancellation. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportedGeometricMeanFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    cols 2 ≤ rows 0 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean rows cols

set_option linter.style.longLine false in
/-- Support-aware positive-middle cancellation payload: use left dominance
when the top-right entry vanishes and geometric-mean domination only where it
is supported. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplitFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedLeftDominanceFromContig ∧
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportedGeometricMeanFromContig

set_option linter.style.longLine false in
/-- Three-way support payload: the left dominance estimate is needed only
when `A01` is supported and `A02` is structurally zero. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplitFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominanceFromContig ∧
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportedGeometricMeanFromContig

set_option linter.style.longLine false in
/-- Moment/cofactor-ratio version of the three-way support payload. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig ∧
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportedGeometricMeanFromContig

set_option linter.style.longLine false in
/-- Subtraction-free contiguous-minor certificate version of the three-way
support payload. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificateFromContig ∧
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportedGeometricMeanFromContig

set_option linter.style.longLine false in
/-- Normalized moment/cofactor-ratio version of the three-way support payload.
-/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatioFromContig ∧
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportedGeometricMeanFromContig

set_option linter.style.longLine false in
/-- Factorized log-convexity route to geometric-mean domination.

The first factor is a three-term log-convexity inequality in the top row; the
second is the analogous inequality for the three maximal cofactor minors.
Their product is precisely the weighted geometric-mean condition.  This is a
stronger candidate route, not a claimed consequence of contiguity. -/
def XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetFactorizedLogConvexityFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 < (C 1).det →
        (A 0 1) ^ 2 ≤ A 0 0 * A 0 2 ∧
          ((C 1).det) ^ 2 ≤ (C 0).det * (C 2).det

/-- Middle cofactor determinant nonpositivity over every reduced four-banded
row geometry. -/
def XiMinorFourBandedCofactorMiddleDetNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDetNonpositive rows cols

/-- Full-support case of middle cofactor determinant nonpositivity. -/
def XiMinorFourBandedCofactorMiddleFullDetNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDetNonpositive rows cols

/-- Full-support case of middle cofactor zero determinant.

Because full-support `3 × 3` positivity already gives the opposite inequality,
zero determinant is the compatible form of the full-support middle sign target.
-/
def XiMinorFourBandedCofactorMiddleFullDetZeroFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 1 b))).det = 0

/-- Moment-index form of the full-support middle cofactor zero determinant.

This isolates the remaining full-support obstruction in the native moment
coordinates; full support then rewrites it back to the Toeplitz-entry
determinant. -/
def XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      (Matrix.of (fun a b =>
        XiMomentCoeff
          (XiMinorFourBandedCofactorRows rows a -
            XiMinorFourBandedCofactorCols cols 1 b))).det = 0

/-- Banded-support case of middle cofactor determinant nonpositivity. -/
def XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
    XiMinorFourBandedCofactorMiddleDetNonpositive rows cols

/-- Expanded sparse determinant form of the banded-support middle cofactor
determinant-sign target. -/
def XiMinorFourBandedCofactorMiddleBandedExpandedNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 0) (c 0) *
          (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1))
        - XiToeplitzEntry (r 0) (c 1) *
          (XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))
        ≤ 0

/-- Product-dominance form of the expanded banded-support middle cofactor
obstruction. -/
def XiMinorFourBandedCofactorMiddleBandedProductDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 0) (c 0) *
          (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1))
        ≤ XiToeplitzEntry (r 0) (c 1) *
          (XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
            - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Bracket-sign form of the banded-support middle product-dominance
obstruction. -/
def XiMinorFourBandedCofactorMiddleBandedBracketSignsFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Left bracket nonpositivity target inside the banded-support middle
cofactor obstruction. -/
def XiMinorFourBandedCofactorMiddleBandedLeftBracketNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0

/-- Right bracket nonnegativity target inside the banded-support middle
cofactor obstruction. -/
def XiMinorFourBandedCofactorMiddleBandedRightBracketNonnegativeFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0)

/-- Split left/right bracket-sign target for the banded-support middle
cofactor obstruction. -/
def XiMinorFourBandedCofactorMiddleBandedSplitBracketsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleBandedLeftBracketNonpositiveFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedRightBracketNonnegativeFromContig

/-- Top-supported branch of the split bracket target for the banded-support
middle cofactor. -/
def XiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBracketsFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorCols cols 1 2 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Moment-gap form of the top-supported banded-support middle bracket target.
-/
def XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorCols cols 1 2 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiMomentCoeff (r 1 - c 1) * XiMomentCoeff (r 2 - c 2)
        - XiMomentCoeff (r 1 - c 2) * XiMomentCoeff (r 2 - c 1) ≤ 0) ∧
      (0 ≤ XiMomentCoeff (r 1 - c 0) * XiMomentCoeff (r 2 - c 2)
        - XiMomentCoeff (r 1 - c 2) * XiMomentCoeff (r 2 - c 0))

/-- Top-unsupported branch of the split bracket target for the banded-support
middle cofactor. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBracketsFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Middle-supported subcase of the top-unsupported banded-support middle
branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBracketsFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      (XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0) ∧
      (0 ≤ XiToeplitzEntry (r 1) (c 0) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 0))

/-- Moment-product form of the top-unsupported, middle-supported branch.

The far-right top entry is structurally zero, so each bracket reduces to a
single product in moment coordinates. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProductFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiMomentCoeff (r 1 - c 1) * XiMomentCoeff (r 2 - c 2) ≤ 0 ∧
      0 ≤ XiMomentCoeff (r 1 - c 0) * XiMomentCoeff (r 2 - c 2)

set_option linter.style.longLine false in
/-- Left product-sign target inside the top-unsupported, middle-supported
moment-product branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiMomentCoeff (r 1 - c 1) * XiMomentCoeff (r 2 - c 2) ≤ 0

set_option linter.style.longLine false in
/-- Right product-sign target inside the top-unsupported, middle-supported
moment-product branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegativeFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      0 ≤ XiMomentCoeff (r 1 - c 0) * XiMomentCoeff (r 2 - c 2)

set_option linter.style.longLine false in
/-- Split product-sign target for the top-unsupported, middle-supported
moment-product branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProductsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductNonpositiveFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegativeFromContig

/-- Left-only product-sign package after the right product is discharged by
moment nonnegativity from contiguous `1 x 1` positivity. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductNonpositiveFromContig

set_option linter.style.longLine false in
/-- Moment-vanishing target that implies the remaining left product sign in
the top-unsupported, middle-supported branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiMomentCoeff (r 1 - c 1) = 0 ∨ XiMomentCoeff (r 2 - c 2) = 0

set_option linter.style.longLine false in
/-- Structural-impossibility target for the top-unsupported, middle-supported
branch of the middle cofactor.

This is sharper than moment vanishing: if the support inequalities cannot
coexist, the remaining left-moment-zero target follows by contradiction. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    False

set_option linter.style.longLine false in
/-- Gap-collapse target for the top-unsupported, middle-supported branch.

The local support inequalities alone do not force contradiction.  This names
the actual geometric payload needed from the surrounding support-class context:
the far-right cofactor column must collapse back below the middle cofactor row,
contradicting the top-unsupported hypothesis. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapseFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 1

set_option linter.style.longLine false in
/-- Original-index form of the contextual gap-collapse target.

For the `j = 1` middle cofactor, the cofactor inequality
`c 2 ≤ r 1` is exactly the original-index inequality `cols 3 ≤ rows 2`.
This is the clean geometric payload to seek from the surrounding reduced-row
context. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      cols 3 ≤ rows 2

set_option linter.style.longLine false in
/-- Inactive side-support context for the top-unsupported, middle-supported
branch.

This restores the support witnesses used by the earlier one-survivor
impossibility proof: the side cofactors at `j = 0` and `j = 2` are classified
by inactive support kinds, while the middle `j = 1` cofactor is in the banded
top-unsupported/middle-supported branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      ∃ kind0 kind2 : XiMinorFourBandedCofactorSupportKind,
        XiMinorFourBandedCofactorSupportKindHolds kind0 rows cols 0 ∧
          XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 ∧
            ¬ XiMinorFourBandedCofactorSupportKindActive kind0 ∧
              ¬ XiMinorFourBandedCofactorSupportKindActive kind2

set_option linter.style.longLine false in
/-- Right-side inactive support context for the top-unsupported,
middle-supported branch.

The support contradiction in this branch only needs the `j = 2` side cofactor:
it must be a zero-row or zero-column support kind, not an active full or
banded kind. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      ∃ kind2 : XiMinorFourBandedCofactorSupportKind,
        XiMinorFourBandedCofactorSupportKindHolds kind2 rows cols 2 ∧
          ¬ XiMinorFourBandedCofactorSupportKindActive kind2

set_option linter.style.longLine false in
/-- Right-side active-exclusion context for the top-unsupported,
middle-supported branch.

The proved `j = 2` support classification leaves four cases. This target asks
only for the two active cases, full and banded support, to be excluded in the
remaining branch; the zero-row and zero-column alternatives are then enough for
the existing support contradiction. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      ¬ XiMinorFourBandedCofactorFullSupport rows cols 2 ∧
        ¬ XiMinorFourBandedCofactorBandedSupport rows cols 2

set_option linter.style.longLine false in
/-- Right-side banded-exclusion context for the top-unsupported,
middle-supported branch.

The right-side full-support case is already impossible from the middle banded
support inequality, so this leaves only the right-side banded support case as
the active case still to exclude. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      ¬ XiMinorFourBandedCofactorBandedSupport rows cols 2

set_option linter.style.longLine false in
/-- Branch-impossibility context for the top-unsupported,
middle-supported branch.

The right `j = 2` banded predicate is forced by the same arithmetic inequalities
as the middle banded support predicate.  Therefore the next honest way to close
the current frontier is to prove that the whole top-unsupported,
middle-supported branch is empty. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      False

set_option linter.style.longLine false in
/-- Middle-column contradiction context for the top-unsupported branch.

This is a sharper way to close the current branch: show that the middle column
is also unsupported, contradicting the middle-supported hypothesis of the
remaining branch. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupportedFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
      XiMinorFourBandedCofactorRows rows 1 <
        XiMinorFourBandedCofactorCols cols 1 1

set_option linter.style.longLine false in
/-- No-straddle context for the top-unsupported branch.

This isolates the exact arithmetic gap between top-column unsupportedness and
middle-column unsupportedness: forbid `rows 1` from lying in the interval
between the middle and top deleted-column indices. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddleFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
      ¬ XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1

set_option linter.style.longLine false in
/-- Straddle-impossibility context for the top-unsupported branch.

This is the counterfactual form of the no-straddle target: assume the remaining
row lies in the middle/top-column interval and derive a contradiction. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
      False

set_option linter.style.longLine false in
/-- Straddle left-product target for the top-unsupported branch.

Inside the straddle interval, both left-product moment factors are strictly
positive under the kernel representation.  Therefore a nonpositive left product
is enough to contradict the straddle branch once the theorem package supplies
kernel moment positivity. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiMomentCoeff (r 1 - c 1) * XiMomentCoeff (r 2 - c 2) ≤ 0

set_option linter.style.longLine false in
/-- Straddle left-bracket target for the top-unsupported branch.

This keeps the obstruction in native Toeplitz `2 x 2` bracket form.  In the
top-unsupported branch the upper-right bracket entry is zero, so this bracket
reduces to the straddle left-product target. -/
def XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracketNonpositiveFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorRows rows 1 <
      XiMinorFourBandedCofactorCols cols 1 2 →
    XiMinorFourBandedCofactorCols cols 1 1 ≤
      XiMinorFourBandedCofactorRows rows 1 →
    XiContigToeplitzTotalPositive →
      let r := XiMinorFourBandedCofactorRows rows
      let c := XiMinorFourBandedCofactorCols cols 1
      XiToeplitzEntry (r 1) (c 1) * XiToeplitzEntry (r 2) (c 2)
        - XiToeplitzEntry (r 1) (c 2) * XiToeplitzEntry (r 2) (c 1) ≤ 0

/-- Top-support split of the banded-support middle bracket target. -/
def XiMinorFourBandedCofactorMiddleBandedTopSupportSplitBracketsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBracketsFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBracketsFromContig

/-- Support-split form of middle cofactor determinant nonpositivity.

The zero-row and zero-column support classes are discharged by structural
zero determinant lemmas, leaving only the active full-support and banded-support
cases. -/
def XiMinorFourBandedCofactorMiddleDetSupportSplitNonpositiveFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullDetNonpositiveFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig

/-- Support-split form with the full-support branch sharpened to determinant
zero. -/
def XiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositiveFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullDetZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the banded-support branch as determinant nonpositivity. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositiveFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the banded-support branch in expanded sparse determinant coordinates. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpandedFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedExpandedNonpositiveFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the banded-support branch as product dominance. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProductFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedProductDominanceFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the banded-support branch as bracket signs. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSignsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedBracketSignsFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the banded-support branch split into left/right brackets. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBracketsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedSplitBracketsFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the banded-support branch split by top support. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBracketsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportSplitBracketsFromContig

/-- Support-split form with the full-support branch in moment coordinates and
the top-supported banded branch also in moment coordinates. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMomentFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBracketsFromContig

/-- Support-split form with the top-unsupported banded branch reduced to the
middle-supported subcase. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBracketsFromContig

set_option linter.style.longLine false in
/-- Support-split form with the top-unsupported, middle-supported branch in
moment-product coordinates. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProductFromContig

set_option linter.style.longLine false in
/-- Support-split form with the top-unsupported, middle-supported branch split
into left/right product-sign targets. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProductsFromContig

set_option linter.style.longLine false in
/-- Support-split form after the right product has been discharged by moment
nonnegativity from contiguous `1 x 1` positivity. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductFromContig

set_option linter.style.longLine false in
/-- Support-split form where the remaining left product is reduced to a
moment-vanishing target. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to structural
impossibility. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to the contextual
gap-collapse inequality. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapseFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to the
original-index gap-collapse inequality `cols 3 ≤ rows 2`. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to inactive
side-support witnesses. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to a right-side
inactive support witness. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to excluding the
two active `j = 2` support cases. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining branch is reduced to excluding the
right-side banded support case. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining top-unsupported,
middle-supported branch is required to be empty. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining top-unsupported branch is closed by
forcing the middle column to be unsupported too. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupportedFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining top-unsupported branch is closed by
ruling out the middle/top-column straddle interval. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddleFromContext

set_option linter.style.longLine false in
/-- Support-split form where the remaining top-unsupported branch is closed by
contradicting the middle/top-column straddle interval. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext

set_option linter.style.longLine false in
/-- Support-split form where the straddle branch is reduced to a nonpositive
left moment-product estimate. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig

set_option linter.style.longLine false in
/-- Support-split form where the straddle branch is reduced to a native
Toeplitz left-bracket nonpositivity estimate. -/
def XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig ∧
    XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig ∧
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracketNonpositiveFromContig

/-- Separated side and middle estimates over the reduced row geometry. -/
def XiMinorFourBandedCofactorMiddleDominanceSeparatedBoundsFromContig :
    Prop :=
  XiMinorFourBandedCofactorMiddleDominanceSideNonnegativeFromContig ∧
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig

/-- Determinant-side plus middle-upper-bound form of the separated estimates.
-/
def XiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddleFromContig :
    Prop :=
  XiMinorFourBandedCofactorSideDetNonnegativeFromContig ∧
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig

/-- Left/right side determinant split over the reduced row geometry. -/
def XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig :
    Prop :=
  XiMinorFourBandedCofactorSideDetLeftNonnegativeFromContig ∧
    XiMinorFourBandedCofactorSideDetRightNonnegativeFromContig

/-- Support classification for the two side cofactors.

This asks only that the left (`j = 0`) and right (`j = 2`) side cofactors are
in one of the two already-controlled `3 × 3` regimes: full support or banded
support. -/
def XiMinorFourBandedCofactorSideDetLeftRightSupportFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      (XiMinorFourBandedCofactorFullSupport rows cols 0 ∨
        XiMinorFourBandedCofactorBandedSupport rows cols 0) ∧
        (XiMinorFourBandedCofactorFullSupport rows cols 2 ∨
          XiMinorFourBandedCofactorBandedSupport rows cols 2)

/-- Support-class classification for the two side cofactors.

Unlike the full-or-banded side-support condition, this also admits zero-row and
zero-column cofactors. Those cases still have nonnegative determinant because
the determinant is structurally zero. -/
def XiMinorFourBandedCofactorSideDetLeftRightSupportClassFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiContigToeplitzTotalPositive →
      XiMinorFourBandedCofactorSupportClass rows cols 0 ∧
        XiMinorFourBandedCofactorSupportClass rows cols 2

/-- Left/right side determinants plus the middle upper-bound estimate. -/
def XiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddleFromContig :
    Prop :=
  XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig ∧
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig

/-- Side support classification plus the middle upper-bound estimate. -/
def XiMinorFourBandedCofactorMiddleDominanceSupportSideAndMiddleFromContig :
    Prop :=
  XiMinorFourBandedCofactorSideDetLeftRightSupportFromContig ∧
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig

/-- Side support-class classification plus the middle upper-bound estimate. -/
def XiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddleFromContig :
    Prop :=
  XiMinorFourBandedCofactorSideDetLeftRightSupportClassFromContig ∧
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig

/-- Existing full-support and banded `3 × 3` targets turn side-support
classification into side determinant nonnegativity. -/
theorem xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_support
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hSupport :
      XiMinorFourBandedCofactorSideDetLeftRightSupportFromContig) :
    XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig := by
  constructor
  · intro rows cols hRows hCols hLeft hGap hRight hContig
    rcases hSupport rows cols hRows hCols hLeft hGap hRight hContig with
      ⟨hLeftSupport, _hRightSupport⟩
    cases hLeftSupport with
    | inl hFull =>
        simpa [XiMinorFourBandedCofactorSideDetLeftNonnegative] using
          hThreeFull
            (XiMinorFourBandedCofactorRows rows)
            (XiMinorFourBandedCofactorCols cols 0)
            (xiMinorFourBandedCofactorRows_strictMono hRows)
            (xiMinorFourBandedCofactorCols_strictMono hCols 0)
            hFull
            hContig
    | inr hBanded =>
        simpa [XiMinorFourBandedCofactorSideDetLeftNonnegative] using
          hThreeBanded
            (XiMinorFourBandedCofactorRows rows)
            (XiMinorFourBandedCofactorCols cols 0)
            (xiMinorFourBandedCofactorRows_strictMono hRows)
            (xiMinorFourBandedCofactorCols_strictMono hCols 0)
            hBanded.1
            hBanded.2.1
            hBanded.2.2
            hContig
  · intro rows cols hRows hCols hLeft hGap hRight hContig
    rcases hSupport rows cols hRows hCols hLeft hGap hRight hContig with
      ⟨_hLeftSupport, hRightSupport⟩
    cases hRightSupport with
    | inl hFull =>
        simpa [XiMinorFourBandedCofactorSideDetRightNonnegative] using
          hThreeFull
            (XiMinorFourBandedCofactorRows rows)
            (XiMinorFourBandedCofactorCols cols 2)
            (xiMinorFourBandedCofactorRows_strictMono hRows)
            (xiMinorFourBandedCofactorCols_strictMono hCols 2)
            hFull
            hContig
    | inr hBanded =>
        simpa [XiMinorFourBandedCofactorSideDetRightNonnegative] using
          hThreeBanded
            (XiMinorFourBandedCofactorRows rows)
            (XiMinorFourBandedCofactorCols cols 2)
            (xiMinorFourBandedCofactorRows_strictMono hRows)
            (xiMinorFourBandedCofactorCols_strictMono hCols 2)
            hBanded.1
            hBanded.2.1
            hBanded.2.2
            hContig

/-- The support-side and middle estimate package proves the split-side
determinant package using the existing `3 × 3` inputs. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddle_of_support
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hBounds :
      XiMinorFourBandedCofactorMiddleDominanceSupportSideAndMiddleFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddleFromContig := by
  rcases hBounds with ⟨hSupport, hMiddle⟩
  exact
    ⟨xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_support
      hThreeFull hThreeBanded hSupport,
      hMiddle⟩

/-- Existing zero-support, full-support, and banded `3 × 3` targets turn
side-support classification into side determinant nonnegativity. -/
theorem xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hSupport :
      XiMinorFourBandedCofactorSideDetLeftRightSupportClassFromContig) :
    XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig := by
  constructor
  · intro rows cols hRows hCols hLeft hGap hRight hContig
    rcases hSupport rows cols hRows hCols hLeft hGap hRight hContig with
      ⟨hLeftSupport, _hRightSupport⟩
    rcases hLeftSupport with hZeroRow | hRest
    · rw [XiMinorFourBandedCofactorSideDetLeftNonnegative]
      simpa using
        (le_of_eq
          (xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
            hZeroRow).symm)
    · rcases hRest with hZeroCol | hRest
      · rw [XiMinorFourBandedCofactorSideDetLeftNonnegative]
        simpa using
          (le_of_eq
            (xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
              hZeroCol).symm)
      · rcases hRest with hFull | hBanded
        · simpa [XiMinorFourBandedCofactorSideDetLeftNonnegative] using
            hThreeFull
              (XiMinorFourBandedCofactorRows rows)
              (XiMinorFourBandedCofactorCols cols 0)
              (xiMinorFourBandedCofactorRows_strictMono hRows)
              (xiMinorFourBandedCofactorCols_strictMono hCols 0)
              hFull
              hContig
        · simpa [XiMinorFourBandedCofactorSideDetLeftNonnegative] using
            hThreeBanded
              (XiMinorFourBandedCofactorRows rows)
              (XiMinorFourBandedCofactorCols cols 0)
              (xiMinorFourBandedCofactorRows_strictMono hRows)
              (xiMinorFourBandedCofactorCols_strictMono hCols 0)
              hBanded.1
              hBanded.2.1
              hBanded.2.2
              hContig
  · intro rows cols hRows hCols hLeft hGap hRight hContig
    rcases hSupport rows cols hRows hCols hLeft hGap hRight hContig with
      ⟨_hLeftSupport, hRightSupport⟩
    rcases hRightSupport with hZeroRow | hRest
    · rw [XiMinorFourBandedCofactorSideDetRightNonnegative]
      simpa using
        (le_of_eq
          (xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
            hZeroRow).symm)
    · rcases hRest with hZeroCol | hRest
      · rw [XiMinorFourBandedCofactorSideDetRightNonnegative]
        simpa using
          (le_of_eq
            (xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
              hZeroCol).symm)
      · rcases hRest with hFull | hBanded
        · simpa [XiMinorFourBandedCofactorSideDetRightNonnegative] using
            hThreeFull
              (XiMinorFourBandedCofactorRows rows)
              (XiMinorFourBandedCofactorCols cols 2)
              (xiMinorFourBandedCofactorRows_strictMono hRows)
              (xiMinorFourBandedCofactorCols_strictMono hCols 2)
              hFull
              hContig
        · simpa [XiMinorFourBandedCofactorSideDetRightNonnegative] using
            hThreeBanded
              (XiMinorFourBandedCofactorRows rows)
              (XiMinorFourBandedCofactorCols cols 2)
              (xiMinorFourBandedCofactorRows_strictMono hRows)
              (xiMinorFourBandedCofactorCols_strictMono hCols 2)
              hBanded.1
              hBanded.2.1
              hBanded.2.2
              hContig

/-- The support-class side and middle estimate package proves the split-side
determinant package using the existing `3 × 3` inputs. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddle_of_supportClass
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hBounds :
      XiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddleFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddleFromContig := by
  rcases hBounds with ⟨hSupport, hMiddle⟩
  exact
    ⟨xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
      hThreeFull hThreeBanded hSupport,
      hMiddle⟩

/-- The left/right determinant split proves the combined side-determinant
package. -/
theorem xiMinorFourBandedCofactorSideDetNonnegative_of_leftRight
    (hSide :
      XiMinorFourBandedCofactorSideDetLeftRightNonnegativeFromContig) :
    XiMinorFourBandedCofactorSideDetNonnegativeFromContig := by
  rcases hSide with ⟨hLeftDet, hRightDet⟩
  intro rows cols hRows hCols hLeft hGap hRight hContig
  exact
    ⟨hLeftDet rows cols hRows hCols hLeft hGap hRight hContig,
      hRightDet rows cols hRows hCols hLeft hGap hRight hContig⟩

/-- The left/right side determinant split and middle estimate prove the
determinant-side-plus-middle package. -/
theorem xiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddle_of_splitSideDet
    (hBounds :
      XiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddleFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddleFromContig := by
  rcases hBounds with ⟨hSide, hMiddle⟩
  exact
    ⟨xiMinorFourBandedCofactorSideDetNonnegative_of_leftRight hSide,
      hMiddle⟩

/-- Side determinant nonnegativity plus entry nonnegativity from contiguous
total positivity proves the side-nonnegative estimate. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSideNonnegative_of_sideDet
    (hSideDet : XiMinorFourBandedCofactorSideDetNonnegativeFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceSideNonnegativeFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  rcases hSideDet rows cols hRows hCols hLeft hGap hRight hContig with
    ⟨hdet0, hdet2⟩
  have hA00 :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 0 := by
    simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hA02 :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 2 := by
    simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
  exact ⟨mul_nonneg hA00 hdet0, mul_nonneg hA02 hdet2⟩

/-- The determinant-side and middle-upper-bound estimates prove the previous
separated-bounds package. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSeparatedBounds_of_sideDet
    (hBounds :
      XiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddleFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceSeparatedBoundsFromContig := by
  rcases hBounds with ⟨hSideDet, hMiddle⟩
  exact
    ⟨xiMinorFourBandedCofactorMiddleDominanceSideNonnegative_of_sideDet
      hSideDet,
      hMiddle⟩

/-- The separated bounds prove the side-bound middle-dominance target. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSideBound_of_separatedBounds
    (hBounds :
      XiMinorFourBandedCofactorMiddleDominanceSeparatedBoundsFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig := by
  rcases hBounds with ⟨hSide, hMiddle⟩
  intro rows cols hRows hCols hLeft hGap hRight hContig
  exact xiMinorFourBandedCofactorMiddleDominanceSideBound_of_parts
    (hSide rows cols hRows hCols hLeft hGap hRight hContig)
    (hMiddle rows cols hRows hCols hLeft hGap hRight hContig)

/-- The side-bound middle-dominance target proves bare middle-dominance. -/
theorem xiMinorFourBandedCofactorMiddleDominance_of_sideBoundFromContig
    (hBound : XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  exact xiMinorFourBandedCofactorMiddleDominance_of_sideBound
    (hBound rows cols hRows hCols hLeft hGap hRight hContig)

/-- The bare middle-dominance target proves row-geometry dominance. -/
theorem xiMinorFourBandedCofactorMultiRowGeometryDominance_of_middleDominance
    (hDom : XiMinorFourBandedCofactorMiddleDominanceFromContig) :
    XiMinorFourBandedCofactorMultiRowGeometryDominanceFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  exact hDom rows cols hRows hCols hLeft hGap hRight hContig

/-- Pure row-geometry dominance proves every support-parametrized dominance
instance. -/
theorem xiMinorFourBandedCofactorMultiSupportDominance_of_rowGeometryDominance
    (hDom :
      XiMinorFourBandedCofactorMultiRowGeometryDominanceFromContig)
    (S0 S1 S2 : (Fin 4 → ℕ) → (Fin 4 → ℕ) → Fin 4 → Prop) :
    XiMinorFourBandedCofactorMultiSupportDominanceFromContig S0 S1 S2 := by
  intro rows cols hRows hCols hLeft hGap hRight _hS0 _hS1 _hS2 hContig
  exact hDom rows cols hRows hCols hLeft hGap hRight hContig

/-- Reduced multi-survivor row where all three cofactors are full-support. -/
def XiMinorFourBandedCofactorMultiFullFullFullFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Dominance form of the all-full reduced multi-survivor row.

The all-full row is not just three nonnegative `3 × 3` determinants: the
signed middle cofactor must be dominated by the two positive side cofactors. -/
def XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorFullSupport rows cols 0 →
    XiMinorFourBandedCofactorFullSupport rows cols 1 →
    XiMinorFourBandedCofactorFullSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- The generic support-dominance predicate proves the all-full dominance
row. -/
theorem xiMinorFourBandedCofactorMultiFullFullFullDominance_of_supportDominance
    (hDom :
      XiMinorFourBandedCofactorMultiSupportDominanceFromContig
        XiMinorFourBandedCofactorFullSupport
        XiMinorFourBandedCofactorFullSupport
        XiMinorFourBandedCofactorFullSupport) :
    XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig := by
  exact hDom

/-- The dominance form proves the all-full reduced multi-survivor row. -/
theorem xiMinorFourBandedCofactorMultiFullFullFull_of_dominance
    (hDom :
      XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig) :
    XiMinorFourBandedCofactorMultiFullFullFullFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hFull0 hFull1 hFull2 hContig
  have h := hDom rows cols hRows hCols hLeft hGap hRight
    hFull0 hFull1 hFull2 hContig
  linarith

/-- Reduced multi-survivor row where all three cofactors are banded. -/
def XiMinorFourBandedCofactorMultiBandedBandedBandedFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Dominance form of the all-banded reduced multi-survivor row.

This is the sparse analogue of the all-full dominance target: the signed middle
cofactor is dominated by the two side cofactors. -/
def XiMinorFourBandedCofactorMultiBandedBandedBandedDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorBandedSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det

/-- The generic support-dominance predicate proves the all-banded dominance
row. -/
theorem xiMinorFourBandedCofactorMultiBandedBandedBandedDominance_of_supportDominance
    (hDom :
      XiMinorFourBandedCofactorMultiSupportDominanceFromContig
        XiMinorFourBandedCofactorBandedSupport
        XiMinorFourBandedCofactorBandedSupport
        XiMinorFourBandedCofactorBandedSupport) :
    XiMinorFourBandedCofactorMultiBandedBandedBandedDominanceFromContig := by
  exact hDom

/-- The dominance form proves the all-banded reduced multi-survivor row. -/
theorem xiMinorFourBandedCofactorMultiBandedBandedBanded_of_dominance
    (hDom :
      XiMinorFourBandedCofactorMultiBandedBandedBandedDominanceFromContig) :
    XiMinorFourBandedCofactorMultiBandedBandedBandedFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBand0 hBand1 hBand2 hContig
  have h := hDom rows cols hRows hCols hLeft hGap hRight
    hBand0 hBand1 hBand2 hContig
  linarith

/-- Reduced multi-survivor row where the left cofactor is structurally
zero-row and the middle/right cofactors are banded. -/
def XiMinorFourBandedCofactorMultiZeroRowBandedBandedFromContig : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorZeroRowSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ A 0 0 * (C 0).det - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Two-term form of the `zeroRow, banded, banded` reduced multi-survivor row.

The left cofactor determinant is structurally zero, so only the signed middle
and right cofactor terms remain. -/
def XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorZeroRowSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      0 ≤ - A 0 1 * (C 1).det + A 0 2 * (C 2).det

/-- Dominance form of the `zeroRow, banded, banded` reduced
multi-survivor row.

Once the left cofactor determinant is structurally zero, the whole row reduces
to domination of the signed middle cofactor by the right cofactor. -/
def XiMinorFourBandedCofactorMultiZeroRowBandedBandedDominanceFromContig :
    Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
    XiMinorFourBandedCofactorZeroRowSupport rows cols 0 →
    XiMinorFourBandedCofactorBandedSupport rows cols 1 →
    XiMinorFourBandedCofactorBandedSupport rows cols 2 →
    XiContigToeplitzTotalPositive →
      let A : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
      let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
        Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols j b))
      A 0 1 * (C 1).det ≤ A 0 2 * (C 2).det

/-- The generic support-dominance predicate proves the zero-row dominance row
after deleting the structurally zero left cofactor determinant. -/
theorem xiMinorFourBandedCofactorMultiZeroRowBandedBandedDominance_of_supportDominance
    (hDom :
      XiMinorFourBandedCofactorMultiSupportDominanceFromContig
        XiMinorFourBandedCofactorZeroRowSupport
        XiMinorFourBandedCofactorBandedSupport
        XiMinorFourBandedCofactorBandedSupport) :
    XiMinorFourBandedCofactorMultiZeroRowBandedBandedDominanceFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hZero hBand1 hBand2 hContig
  have hdet0 :
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 0 b))).det = 0 :=
    xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport hZero
  have h := hDom rows cols hRows hCols hLeft hGap hRight
    hZero hBand1 hBand2 hContig
  simpa [hdet0] using h

/-- The zero-row dominance form proves the zero-row two-term row. -/
theorem xiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTerm_of_dominance
    (hDom :
      XiMinorFourBandedCofactorMultiZeroRowBandedBandedDominanceFromContig) :
    XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hZero hBand1 hBand2 hContig
  have h := hDom rows cols hRows hCols hLeft hGap hRight
    hZero hBand1 hBand2 hContig
  linarith

/-- The two-term row proves the full `zeroRow, banded, banded` row by deleting
the structurally zero left cofactor determinant. -/
theorem xiMinorFourBandedCofactorMultiZeroRowBandedBanded_of_twoTerm
    (hTwo :
      XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig) :
    XiMinorFourBandedCofactorMultiZeroRowBandedBandedFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hZero hBand1 hBand2 hContig
  have hdet0 :
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 0 b))).det = 0 :=
    xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport hZero
  have h := hTwo rows cols hRows hCols hLeft hGap hRight
    hZero hBand1 hBand2 hContig
  simpa [hdet0] using h

/-- Row-level package for the reduced multi-survivor table. -/
def XiMinorFourBandedCofactorReducedMultiRowsFromContig : Prop :=
  XiMinorFourBandedCofactorMultiFullFullFullFromContig ∧
    XiMinorFourBandedCofactorMultiBandedBandedBandedFromContig ∧
      XiMinorFourBandedCofactorMultiZeroRowBandedBandedFromContig

/-- Sharper row-level package using the two-term form of the
`zeroRow, banded, banded` row. -/
def XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig : Prop :=
  XiMinorFourBandedCofactorMultiFullFullFullFromContig ∧
    XiMinorFourBandedCofactorMultiBandedBandedBandedFromContig ∧
      XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig

/-- Sparse part of the reduced multi-survivor row package.

The all-full row is separated out because it is the next natural target for
ordinary full-support total positivity, while these two rows retain the sparse
banded cancellation geometry. -/
def XiMinorFourBandedCofactorReducedMultiSparseRowsTwoTermFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiBandedBandedBandedFromContig ∧
    XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig

/-- Sparse row package with the all-banded row replaced by its dominance
form. -/
def XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiBandedBandedBandedDominanceFromContig ∧
    XiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTermFromContig

/-- Sparse row package with both sparse rows in dominance form. -/
def XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsDominanceFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiBandedBandedBandedDominanceFromContig ∧
    XiMinorFourBandedCofactorMultiZeroRowBandedBandedDominanceFromContig

/-- The sparse-dominance package proves the sparse two-term row package. -/
theorem xiMinorFourBandedCofactorReducedMultiSparseRowsTwoTerm_of_dominance
    (hRows :
      XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig) :
    XiMinorFourBandedCofactorReducedMultiSparseRowsTwoTermFromContig := by
  rcases hRows with ⟨hDom, hZBBTwo⟩
  exact ⟨xiMinorFourBandedCofactorMultiBandedBandedBanded_of_dominance hDom,
    hZBBTwo⟩

/-- The all-sparse-dominance package proves the sparse-dominance/two-term
package. -/
theorem xiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTerm_of_zeroDominance
    (hRows :
      XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsDominanceFromContig) :
    XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig := by
  rcases hRows with ⟨hBandDom, hZeroDom⟩
  exact ⟨hBandDom,
    xiMinorFourBandedCofactorMultiZeroRowBandedBandedTwoTerm_of_dominance
      hZeroDom⟩

/-- Split row-level package: the all-full row plus the sparse two-term package.
-/
def XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiFullFullFullFromContig ∧
    XiMinorFourBandedCofactorReducedMultiSparseRowsTwoTermFromContig

/-- Full-row dominance plus the sparse two-term row package. -/
def XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig ∧
    XiMinorFourBandedCofactorReducedMultiSparseRowsTwoTermFromContig

/-- Full-row dominance plus sparse-row dominance and the zero-row two-term
target. -/
def XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig ∧
    XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTermFromContig

/-- Full-row dominance plus both sparse rows in dominance form. -/
def XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiFullFullFullDominanceFromContig ∧
    XiMinorFourBandedCofactorReducedMultiSparseDominanceRowsDominanceFromContig

/-- Unified support-parametrized form of the all-dominance reduced-row
frontier. -/
def XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiSupportDominanceFromContig
    XiMinorFourBandedCofactorFullSupport
    XiMinorFourBandedCofactorFullSupport
    XiMinorFourBandedCofactorFullSupport ∧
  XiMinorFourBandedCofactorMultiSupportDominanceFromContig
    XiMinorFourBandedCofactorBandedSupport
    XiMinorFourBandedCofactorBandedSupport
    XiMinorFourBandedCofactorBandedSupport ∧
  XiMinorFourBandedCofactorMultiSupportDominanceFromContig
    XiMinorFourBandedCofactorZeroRowSupport
    XiMinorFourBandedCofactorBandedSupport
    XiMinorFourBandedCofactorBandedSupport

/-- Pure row-geometry version of the uniform dominance frontier. -/
def XiMinorFourBandedCofactorReducedMultiRowsRowGeometryDominanceFromContig :
    Prop :=
  XiMinorFourBandedCofactorMultiRowGeometryDominanceFromContig

/-- The full-dominance/sparse package proves the full/sparse row package. -/
theorem xiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTerm_of_dominance
    (hRows :
      XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig := by
  rcases hRows with ⟨hDom, hSparse⟩
  exact ⟨xiMinorFourBandedCofactorMultiFullFullFull_of_dominance hDom,
    hSparse⟩

/-- The full-dominance/sparse-dominance package proves the
full-dominance/sparse package. -/
theorem xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTerm_of_sparseDominance
    (hRows :
      XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig := by
  rcases hRows with ⟨hFullDom, hSparseDom⟩
  exact ⟨hFullDom,
    xiMinorFourBandedCofactorReducedMultiSparseRowsTwoTerm_of_dominance
      hSparseDom⟩

/-- The all-dominance row package proves the
full-dominance/sparse-dominance/two-term package. -/
theorem xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
    (hRows : XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig := by
  rcases hRows with ⟨hFullDom, hSparseDom⟩
  exact ⟨hFullDom,
    xiMinorFourBandedCofactorReducedMultiSparseDominanceRowsTwoTerm_of_zeroDominance
      hSparseDom⟩

/-- The uniform support-dominance package proves the all-dominance row package.
-/
theorem xiMinorFourBandedCofactorReducedMultiRowsAllDominance_of_uniformDominance
    (hRows :
      XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig := by
  rcases hRows with ⟨hFull, hBand, hZero⟩
  exact
    ⟨xiMinorFourBandedCofactorMultiFullFullFullDominance_of_supportDominance
        hFull,
      ⟨xiMinorFourBandedCofactorMultiBandedBandedBandedDominance_of_supportDominance
          hBand,
        xiMinorFourBandedCofactorMultiZeroRowBandedBandedDominance_of_supportDominance
          hZero⟩⟩

/-- Pure row-geometry dominance proves the uniform support-dominance package.
-/
theorem xiMinorFourBandedCofactorReducedMultiRowsUniformDominance_of_rowGeometryDominance
    (hRows :
      XiMinorFourBandedCofactorReducedMultiRowsRowGeometryDominanceFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig := by
  exact
    ⟨xiMinorFourBandedCofactorMultiSupportDominance_of_rowGeometryDominance
        hRows
        XiMinorFourBandedCofactorFullSupport
        XiMinorFourBandedCofactorFullSupport
        XiMinorFourBandedCofactorFullSupport,
      ⟨xiMinorFourBandedCofactorMultiSupportDominance_of_rowGeometryDominance
          hRows
          XiMinorFourBandedCofactorBandedSupport
          XiMinorFourBandedCofactorBandedSupport
          XiMinorFourBandedCofactorBandedSupport,
        xiMinorFourBandedCofactorMultiSupportDominance_of_rowGeometryDominance
          hRows
          XiMinorFourBandedCofactorZeroRowSupport
          XiMinorFourBandedCofactorBandedSupport
          XiMinorFourBandedCofactorBandedSupport⟩⟩

/-- The full/sparse split row package proves the sharper two-term row package.
-/
theorem xiMinorFourBandedCofactorReducedMultiRowsTwoTerm_of_fullSparse
    (hRows :
      XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig := by
  rcases hRows with ⟨hFFF, hSparse⟩
  rcases hSparse with ⟨hBBB, hZBBTwo⟩
  exact ⟨hFFF, hBBB, hZBBTwo⟩

/-- The sharper two-term row package proves the row-level reduced
multi-survivor package. -/
theorem xiMinorFourBandedCofactorReducedMultiRows_of_twoTerm
    (hRows :
      XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig) :
    XiMinorFourBandedCofactorReducedMultiRowsFromContig := by
  rcases hRows with ⟨hFFF, hBBB, hZBBTwo⟩
  exact ⟨hFFF, hBBB,
    xiMinorFourBandedCofactorMultiZeroRowBandedBanded_of_twoTerm hZBBTwo⟩

/-- The three row-level reduced multi-survivor targets prove the reduced
multi-survivor case table. -/
theorem xiMinorFourBandedCofactorReducedMultiSurvivor_of_rows
    (hRowsTarget : XiMinorFourBandedCofactorReducedMultiRowsFromContig) :
    XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 hReduced hContig
  rcases hRowsTarget with ⟨hFFF, hBBB, hZBB⟩
  rcases hReduced with hFFFcase | hRest
  · rcases hFFFcase with ⟨rfl, rfl, rfl⟩
    exact hFFF rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 hContig
  · rcases hRest with hBBBcase | hZBBcase
    · rcases hBBBcase with ⟨rfl, rfl, rfl⟩
      exact hBBB rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2 hContig
    · rcases hZBBcase with ⟨rfl, rfl, rfl⟩
      exact hZBB rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2 hContig

/-- A support-kind reduction plus the reduced case table proves the full
multi-survivor case table. -/
theorem xiMinorFourBandedCofactorMultiSurvivorCaseTable_of_reduced
    (hReduce :
      XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport)
    (hReduced :
      XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig) :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 hActive hContig
  exact hReduced kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2
    (hReduce kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 hActive)
    hContig

/-- Finite cofactor support-classification payload for the banded `4 × 4`
frontier.

This is the exact combinatorial claim that the three surviving row-zero
cofactors land in one of the named support classes. -/
def XiMinorFourBandedCofactorSupportClassesFromBand : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
      XiMinorFourBandedCofactorSupportClass rows cols 0 ∧
        XiMinorFourBandedCofactorSupportClass rows cols 1 ∧
          XiMinorFourBandedCofactorSupportClass rows cols 2

/-- Support-classification payload for the first surviving cofactor
`j = 0`. -/
def XiMinorFourBandedCofactorJ0SupportClassFromBand : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
      XiMinorFourBandedCofactorSupportClass rows cols 0

/-- Support-classification payload for the second surviving cofactor
`j = 1`. -/
def XiMinorFourBandedCofactorJ1SupportClassFromBand : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
      XiMinorFourBandedCofactorSupportClass rows cols 1

/-- Support-classification payload for the third surviving cofactor
`j = 2`. -/
def XiMinorFourBandedCofactorJ2SupportClassFromBand : Prop :=
  ∀ (rows cols : Fin 4 → ℕ),
    StrictMono rows → StrictMono cols →
    cols 0 ≤ rows 0 →
    rows 0 < cols 3 →
    cols 3 ≤ rows 3 →
      XiMinorFourBandedCofactorSupportClass rows cols 2

/-- The `j = 0` cofactor support classification follows directly from
strict monotonicity and the outer `4 × 4` band assumptions. -/
theorem xiMinorFourBandedCofactorJ0SupportClass_fromBand :
    XiMinorFourBandedCofactorJ0SupportClassFromBand := by
  intro rows cols hRows hCols hLeft hGap hRight
  have hCols12 : cols 1 < cols 2 := hCols (by decide : (1 : Fin 4) < 2)
  have hCols23 : cols 2 < cols 3 := hCols (by decide : (2 : Fin 4) < 3)
  have hRows12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 4) < 2)
  have hRows23 : rows 2 < rows 3 := hRows (by decide : (2 : Fin 4) < 3)
  by_cases h10 :
      XiMinorFourBandedCofactorCols cols 0 0 ≤
        XiMinorFourBandedCofactorRows rows 0
  · by_cases hGap0 :
        XiMinorFourBandedCofactorRows rows 0 <
          XiMinorFourBandedCofactorCols cols 0 2
    · right
      right
      right
      refine ⟨h10, hGap0, ?_⟩
      simpa [XiMinorFourBandedCofactorRows,
        XiMinorFourBandedCofactorCols] using hRight
    · right
      right
      left
      intro a b
      have hC :
          XiMinorFourBandedCofactorCols cols 0 b ≤
            XiMinorFourBandedCofactorCols cols 0 2 := by
        fin_cases b
        · change cols 1 ≤ cols 3
          exact le_of_lt (lt_trans hCols12 hCols23)
        · change cols 2 ≤ cols 3
          exact le_of_lt hCols23
        · change cols 3 ≤ cols 3
          exact le_rfl
      have hR :
          XiMinorFourBandedCofactorRows rows 0 ≤
            XiMinorFourBandedCofactorRows rows a := by
        fin_cases a
        · change rows 1 ≤ rows 1
          exact le_rfl
        · change rows 1 ≤ rows 2
          exact le_of_lt hRows12
        · change rows 1 ≤ rows 3
          exact le_of_lt (lt_trans hRows12 hRows23)
      exact le_trans (le_trans hC (Nat.le_of_not_gt hGap0)) hR
  · left
    refine ⟨0, ?_⟩
    intro b
    have hlt :
        XiMinorFourBandedCofactorRows rows 0 <
          XiMinorFourBandedCofactorCols cols 0 0 :=
      Nat.lt_of_not_ge h10
    have hlt' : rows 1 < cols 1 := by
      simpa [XiMinorFourBandedCofactorRows,
        XiMinorFourBandedCofactorCols] using hlt
    fin_cases b
    · simpa using hlt
    · change rows 1 < cols 2
      exact lt_trans hlt' hCols12
    · change rows 1 < cols 3
      exact lt_trans hlt' (lt_trans hCols12 hCols23)

/-- The `j = 1` cofactor support classification follows directly from
strict monotonicity and the outer `4 × 4` band assumptions. -/
theorem xiMinorFourBandedCofactorJ1SupportClass_fromBand :
    XiMinorFourBandedCofactorJ1SupportClassFromBand := by
  intro rows cols hRows hCols hLeft hGap hRight
  have hRows01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 4) < 1)
  have hRows12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 4) < 2)
  have hRows23 : rows 2 < rows 3 := hRows (by decide : (2 : Fin 4) < 3)
  have hCols02 : cols 0 < cols 2 :=
    lt_trans (hCols (by decide : (0 : Fin 4) < 1))
      (hCols (by decide : (1 : Fin 4) < 2))
  have hCols23 : cols 2 < cols 3 := hCols (by decide : (2 : Fin 4) < 3)
  have hLeft1 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 0 := by
    change cols 0 ≤ rows 1
    exact le_trans hLeft (le_of_lt hRows01)
  by_cases hGap1 :
      XiMinorFourBandedCofactorRows rows 0 <
        XiMinorFourBandedCofactorCols cols 1 2
  · right
    right
    right
    refine ⟨hLeft1, hGap1, ?_⟩
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hRight
  · right
    right
    left
    intro a b
    have hC :
        XiMinorFourBandedCofactorCols cols 1 b ≤
          XiMinorFourBandedCofactorCols cols 1 2 := by
      fin_cases b
      · change cols 0 ≤ cols 3
        exact le_of_lt (lt_trans hCols02 hCols23)
      · change cols 2 ≤ cols 3
        exact le_of_lt hCols23
      · change cols 3 ≤ cols 3
        exact le_rfl
    have hR :
        XiMinorFourBandedCofactorRows rows 0 ≤
          XiMinorFourBandedCofactorRows rows a := by
      fin_cases a
      · change rows 1 ≤ rows 1
        exact le_rfl
      · change rows 1 ≤ rows 2
        exact le_of_lt hRows12
      · change rows 1 ≤ rows 3
        exact le_of_lt (lt_trans hRows12 hRows23)
    exact le_trans (le_trans hC (Nat.le_of_not_gt hGap1)) hR

/-- The `j = 2` cofactor support classification follows directly from
strict monotonicity and the outer `4 × 4` band assumptions. -/
theorem xiMinorFourBandedCofactorJ2SupportClass_fromBand :
    XiMinorFourBandedCofactorJ2SupportClassFromBand := by
  intro rows cols hRows hCols hLeft hGap hRight
  have hRows01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 4) < 1)
  have hRows12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 4) < 2)
  have hRows23 : rows 2 < rows 3 := hRows (by decide : (2 : Fin 4) < 3)
  have hCols01 : cols 0 < cols 1 := hCols (by decide : (0 : Fin 4) < 1)
  have hCols13 : cols 1 < cols 3 :=
    lt_trans (hCols (by decide : (1 : Fin 4) < 2))
      (hCols (by decide : (2 : Fin 4) < 3))
  have hLeft2 :
      XiMinorFourBandedCofactorCols cols 2 0 ≤
        XiMinorFourBandedCofactorRows rows 0 := by
    change cols 0 ≤ rows 1
    exact le_trans hLeft (le_of_lt hRows01)
  by_cases hGap2 :
      XiMinorFourBandedCofactorRows rows 0 <
        XiMinorFourBandedCofactorCols cols 2 2
  · right
    right
    right
    refine ⟨hLeft2, hGap2, ?_⟩
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hRight
  · right
    right
    left
    intro a b
    have hC :
        XiMinorFourBandedCofactorCols cols 2 b ≤
          XiMinorFourBandedCofactorCols cols 2 2 := by
      fin_cases b
      · change cols 0 ≤ cols 3
        exact le_of_lt (lt_trans hCols01 hCols13)
      · change cols 1 ≤ cols 3
        exact le_of_lt hCols13
      · change cols 3 ≤ cols 3
        exact le_rfl
    have hR :
        XiMinorFourBandedCofactorRows rows 0 ≤
          XiMinorFourBandedCofactorRows rows a := by
      fin_cases a
      · change rows 1 ≤ rows 1
        exact le_rfl
      · change rows 1 ≤ rows 2
        exact le_of_lt hRows12
      · change rows 1 ≤ rows 3
        exact le_of_lt (lt_trans hRows12 hRows23)
    exact le_trans (le_trans hC (Nat.le_of_not_gt hGap2)) hR

/-- The three individual cofactor classifications supply the combined
classification payload. -/
theorem xiMinorFourBandedCofactorSupportClasses_of_j012
    (hJ0 : XiMinorFourBandedCofactorJ0SupportClassFromBand)
    (hJ1 : XiMinorFourBandedCofactorJ1SupportClassFromBand)
    (hJ2 : XiMinorFourBandedCofactorJ2SupportClassFromBand) :
    XiMinorFourBandedCofactorSupportClassesFromBand := by
  intro rows cols hRows hCols hLeft hGap hRight
  exact ⟨hJ0 rows cols hRows hCols hLeft hGap hRight,
    hJ1 rows cols hRows hCols hLeft hGap hRight,
    hJ2 rows cols hRows hCols hLeft hGap hRight⟩

/-- The side cofactor support-class condition is a direct consequence of the
existing `j = 0` and `j = 2` cofactor support-class lemmas. -/
theorem xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand :
    XiMinorFourBandedCofactorSideDetLeftRightSupportClassFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight _hContig
  exact
    ⟨xiMinorFourBandedCofactorJ0SupportClass_fromBand
      rows cols hRows hCols hLeft hGap hRight,
      xiMinorFourBandedCofactorJ2SupportClass_fromBand
      rows cols hRows hCols hLeft hGap hRight⟩

/-- The middle upper-bound estimate alone supplies the support-class side and
middle package, because side support-classification is already proved from the
outer four-banded geometry. -/
theorem xiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddle_of_middle
    (hMiddle :
      XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddleFromContig :=
  ⟨xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand, hMiddle⟩

/-- The moment-index full-support middle determinant-zero target implies the
Toeplitz-entry full-support middle determinant-zero target. -/
theorem xiMinorFourBandedCofactorMiddleFullDetZero_of_moment
    (hMoment :
      XiMinorFourBandedCofactorMiddleFullMomentZeroFromContig) :
    XiMinorFourBandedCofactorMiddleFullDetZeroFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hFull hContig
  have h := hMoment rows cols hRows hCols hLeft hGap hRight hFull hContig
  rw [Matrix.det_fin_three]
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply] at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 0)
        (hFull 0 0),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 1)
        (hFull 0 1),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 2)
        (hFull 0 2),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
        (hFull 1 0),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        (hFull 1 1),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2)
        (hFull 1 2),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 0)
        (hFull 2 0),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 1)
        (hFull 2 1),
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        (hFull 2 2)]
  exact h

/-- The moment-zero/banded-nonpositive package proves the full-zero/banded
package for middle determinant nonpositivity. -/
theorem xiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositive_of_moment
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositiveFromContig :=
  ⟨xiMinorFourBandedCofactorMiddleFullDetZero_of_moment hSplit.1, hSplit.2⟩

/-- Bracket signs imply product dominance for the banded middle obstruction. -/
theorem xiMinorFourBandedCofactorMiddleBandedProductDominance_of_bracketSigns
    (hSigns :
      XiMinorFourBandedCofactorMiddleBandedBracketSignsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedProductDominanceFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hContig
  have h := hSigns rows cols hRows hCols hLeft hGap hRight
    hBanded hContig
  have h00 :
      0 ≤ XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 0) :=
    xiToeplitzEntry_nonneg_of_contig hContig
      (XiMinorFourBandedCofactorRows rows 0)
      (XiMinorFourBandedCofactorCols cols 1 0)
  have h01 :
      0 ≤ XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 1) :=
    xiToeplitzEntry_nonneg_of_contig hContig
      (XiMinorFourBandedCofactorRows rows 0)
      (XiMinorFourBandedCofactorCols cols 1 1)
  have hLeftProd :
      XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 0)
          (XiMinorFourBandedCofactorCols cols 1 0) *
        (XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 1)
            (XiMinorFourBandedCofactorCols cols 1 1) *
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 2)
            (XiMinorFourBandedCofactorCols cols 1 2)
          - XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 1)
            (XiMinorFourBandedCofactorCols cols 1 2) *
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 2)
            (XiMinorFourBandedCofactorCols cols 1 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h00 h.1
  have hRightProd :
      0 ≤
        XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows 0)
            (XiMinorFourBandedCofactorCols cols 1 1) *
          (XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 1)
              (XiMinorFourBandedCofactorCols cols 1 0) *
            XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 2)
              (XiMinorFourBandedCofactorCols cols 1 2)
            - XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 1)
              (XiMinorFourBandedCofactorCols cols 1 2) *
            XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows 2)
              (XiMinorFourBandedCofactorCols cols 1 0)) :=
    mul_nonneg h01 h.2
  linarith

/-- Product dominance implies the expanded sparse middle-cofactor obstruction.
-/
theorem xiMinorFourBandedCofactorMiddleBandedExpandedNonpositive_of_productDominance
    (hDom :
      XiMinorFourBandedCofactorMiddleBandedProductDominanceFromContig) :
    XiMinorFourBandedCofactorMiddleBandedExpandedNonpositiveFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hContig
  have h := hDom rows cols hRows hCols hLeft hGap hRight hBanded hContig
  linarith

/-- The moment-zero/product-dominance package proves the
moment-zero/expanded-banded package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpanded_of_product
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProductFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpandedFromContig :=
  ⟨hSplit.1,
    xiMinorFourBandedCofactorMiddleBandedExpandedNonpositive_of_productDominance
      hSplit.2⟩

/-- The moment-zero/bracket-sign package proves the moment-zero/product package.
-/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProduct_of_bracketSigns
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSignsFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProductFromContig :=
  ⟨hSplit.1,
    xiMinorFourBandedCofactorMiddleBandedProductDominance_of_bracketSigns
      hSplit.2⟩

/-- Split left/right bracket targets imply the bundled bracket-sign target. -/
theorem xiMinorFourBandedCofactorMiddleBandedBracketSigns_of_split
    (hSplit :
      XiMinorFourBandedCofactorMiddleBandedSplitBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedBracketSignsFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hContig
  exact
    ⟨hSplit.1 rows cols hRows hCols hLeft hGap hRight hBanded hContig,
      hSplit.2 rows cols hRows hCols hLeft hGap hRight hBanded hContig⟩

/-- The moment-zero/split-bracket package proves the
moment-zero/bracket-sign package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSigns_of_split
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSignsFromContig :=
  ⟨hSplit.1,
    xiMinorFourBandedCofactorMiddleBandedBracketSigns_of_split hSplit.2⟩

/-- Splitting on whether the top bracket row supports the far-right cofactor
column proves the split left/right bracket target. -/
theorem xiMinorFourBandedCofactorMiddleBandedSplitBrackets_of_topSupportSplit
    (hTopSplit :
      XiMinorFourBandedCofactorMiddleBandedTopSupportSplitBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedSplitBracketsFromContig := by
  constructor
  · intro rows cols hRows hCols hLeft hGap hRight hBanded hContig
    by_cases hTop :
        XiMinorFourBandedCofactorCols cols 1 2 ≤
          XiMinorFourBandedCofactorRows rows 1
    · exact (hTopSplit.1 rows cols hRows hCols hLeft hGap hRight
        hBanded hTop hContig).1
    · have hUnsupported :
          XiMinorFourBandedCofactorRows rows 1 <
            XiMinorFourBandedCofactorCols cols 1 2 :=
        Nat.lt_of_not_ge hTop
      exact (hTopSplit.2 rows cols hRows hCols hLeft hGap hRight
        hBanded hUnsupported hContig).1
  · intro rows cols hRows hCols hLeft hGap hRight hBanded hContig
    by_cases hTop :
        XiMinorFourBandedCofactorCols cols 1 2 ≤
          XiMinorFourBandedCofactorRows rows 1
    · exact (hTopSplit.1 rows cols hRows hCols hLeft hGap hRight
        hBanded hTop hContig).2
    · have hUnsupported :
          XiMinorFourBandedCofactorRows rows 1 <
            XiMinorFourBandedCofactorCols cols 1 2 :=
        Nat.lt_of_not_ge hTop
      exact (hTopSplit.2 rows cols hRows hCols hLeft hGap hRight
        hBanded hUnsupported hContig).2

/-- The moment-zero/top-support-split package proves the
moment-zero/split-bracket package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBrackets_of_topSupportSplit
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBracketsFromContig :=
  ⟨hSplit.1,
    xiMinorFourBandedCofactorMiddleBandedSplitBrackets_of_topSupportSplit
      hSplit.2⟩

/-- The moment-gap top-supported bracket target rewrites to the Toeplitz-entry
top-supported bracket target. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBrackets_of_moment
    (hMoment :
      XiMinorFourBandedCofactorMiddleBandedTopSupportedMomentBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBracketsFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hTop hContig
  have h := hMoment rows cols hRows hCols hLeft hGap hRight
    hBanded hTop hContig
  have hCofRows := xiMinorFourBandedCofactorRows_strictMono hRows
  have hCofCols := xiMinorFourBandedCofactorCols_strictMono hCols 1
  have h20 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 1 := by
    exact le_trans hBanded.1 (le_of_lt (hCofRows (by decide)))
  have h21 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1 := by
    exact le_trans (le_of_lt (hCofCols (by decide))) hTop
  have h22 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 1 :=
    hTop
  have h30 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h20 (le_of_lt (hCofRows (by decide)))
  have h31 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h21 (le_of_lt (hCofRows (by decide)))
  have h32 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    hBanded.2.2
  dsimp only at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h21,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h32,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h22,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h31,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h20,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h30]
  exact h

set_option linter.style.longLine false in
/-- The moment top-supported package proves the previous top-support split
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBrackets_of_topSupportedMoment
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMomentFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBracketsFromContig :=
  ⟨hSplit.1,
    ⟨xiMinorFourBandedCofactorMiddleBandedTopSupportedSplitBrackets_of_moment
        hSplit.2.1,
      hSplit.2.2⟩⟩

/-- The top-unsupported branch reduces to the middle-supported subcase; when
the middle column is also unsupported in the first bracket row, the needed
bracket signs follow from forced zeros and entry nonnegativity. -/
theorem
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBrackets_of_middleSupported
    (hMiddle :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBracketsFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported hContig
  by_cases hMid :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1
  · exact hMiddle rows cols hRows hCols hLeft hGap hRight
      hBanded hUnsupported hMid hContig
  · have hMidUnsupported :
        XiMinorFourBandedCofactorRows rows 1 <
          XiMinorFourBandedCofactorCols cols 1 1 :=
      Nat.lt_of_not_ge hMid
    have h11 :
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 1)
          (XiMinorFourBandedCofactorCols cols 1 1) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt hMidUnsupported)]
    have h12 :
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 1)
          (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
      unfold XiToeplitzEntry
      rw [if_neg (Nat.not_le_of_gt hUnsupported)]
    have h10nonneg :
        0 ≤ XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 1)
          (XiMinorFourBandedCofactorCols cols 1 0) :=
      xiToeplitzEntry_nonneg_of_contig hContig
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
    have h22nonneg :
        0 ≤ XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows 2)
          (XiMinorFourBandedCofactorCols cols 1 2) :=
      xiToeplitzEntry_nonneg_of_contig hContig
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
    dsimp only
    rw [h11, h12]
    constructor
    · norm_num
    · simpa using mul_nonneg h10nonneg h22nonneg

set_option linter.style.longLine false in
/-- The middle-supported top-unsupported package proves the previous
top-supported-moment package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMoment_of_middleSupported
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMomentFromContig :=
  ⟨hSplit.1,
    hSplit.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedSplitBrackets_of_middleSupported
      hSplit.2.2⟩

/-- The moment-product obstruction proves the top-unsupported,
middle-supported bracket target after rewriting all supported Toeplitz entries
to signed moments and the far-right top entry to zero. -/
theorem
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBrackets_of_momentProduct
    (hMoment :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProductFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBracketsFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight
    hBanded hUnsupported hMiddle hContig
  have h := hMoment rows cols hRows hCols hLeft hGap hRight
    hBanded hUnsupported hMiddle hContig
  have hCofRows := xiMinorFourBandedCofactorRows_strictMono hRows
  have h20 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 1 := by
    exact le_trans hBanded.1 (le_of_lt (hCofRows (by decide)))
  have h21 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1 :=
    hMiddle
  have h12zero :
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hUnsupported)]
  have h30 :
      XiMinorFourBandedCofactorCols cols 1 0 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h20 (le_of_lt (hCofRows (by decide)))
  have h31 :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    le_trans h21 (le_of_lt (hCofRows (by decide)))
  have h32 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    hBanded.2.2
  dsimp only at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h21,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h32,
      h12zero,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 1)
        h31,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h20,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 0)
        h30]
  constructor
  · simpa using h.1
  · simpa using h.2

set_option linter.style.longLine false in
/-- The top-unsupported middle-supported moment-product package proves the
previous middle-supported package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported_of_momentProduct
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedFromContig :=
  ⟨hSplit.1,
    hSplit.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBrackets_of_momentProduct
      hSplit.2.2⟩

set_option linter.style.longLine false in
/-- Split product signs imply the bundled moment-product target. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
    (hSplit :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProductsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProductFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle hContig
  exact
    ⟨hSplit.1 rows cols hRows hCols hLeft hGap hRight hBanded
        hUnsupported hMiddle hContig,
      hSplit.2 rows cols hRows hCols hLeft hGap hRight hBanded
        hUnsupported hMiddle hContig⟩

set_option linter.style.longLine false in
/-- The split product package proves the bundled moment-product package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductFromContig :=
  ⟨hSplit.1,
    hSplit.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
      hSplit.2.2⟩

set_option linter.style.longLine false in
/-- The right product sign follows from moment nonnegativity supplied by
contiguous `1 x 1` positivity. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegative_of_momentNonnegative :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegativeFromContig := by
  intro rows cols _hRows _hCols _hLeft _hGap _hRight _hBanded
    _hUnsupported _hMiddle hContig
  exact
    mul_nonneg
      (xiMomentCoeffNonnegative_of_contig
        (XiMinorFourBandedCofactorRows rows 1 -
          XiMinorFourBandedCofactorCols cols 1 0)
        hContig)
      (xiMomentCoeffNonnegative_of_contig
        (XiMinorFourBandedCofactorRows rows 2 -
          XiMinorFourBandedCofactorCols cols 1 2)
        hContig)

set_option linter.style.longLine false in
/-- The left product package plus automatic right product nonnegativity proves
the split-products package. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
    (hLeft :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProductsFromContig :=
  ⟨hLeft,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightProductNonnegative_of_momentNonnegative⟩

set_option linter.style.longLine false in
/-- The left product package proves the split-products theorem package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsFromContig :=
  ⟨hSplit.1,
    hSplit.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
      hSplit.2.2⟩

set_option linter.style.longLine false in
/-- A zero factor proves the remaining left product sign. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
    (hZero :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProductFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle hContig
  rcases hZero rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported hMiddle hContig with hZeroLeft | hZeroRight
  · simp [hZeroLeft]
  · simp [hZeroRight]

set_option linter.style.longLine false in
/-- The left-moment-zero package proves the left-product theorem package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
    (hZero :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductFromContig :=
  ⟨hZero.1,
    hZero.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
      hZero.2.2⟩

set_option linter.style.longLine false in
/-- Structural impossibility proves the left-moment-zero target by
contradiction. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
    (hImpossible :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle _hContig
  exact False.elim
    (hImpossible rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported hMiddle)

set_option linter.style.longLine false in
/-- The structural-impossibility package proves the left-moment-zero theorem
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
    (hImpossible :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig :=
  ⟨hImpossible.1,
    hImpossible.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
      hImpossible.2.2⟩

set_option linter.style.longLine false in
/-- Contextual gap collapse contradicts the top-unsupported inequality. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
    (hGapCollapse :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapseFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle
  have hCollapse :=
    hGapCollapse rows cols hRows hCols hLeft hGap hRight hBanded hMiddle
  exact (not_lt_of_ge hCollapse) hUnsupported

set_option linter.style.longLine false in
/-- The contextual gap-collapse package proves the impossible-branch package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
    (hGapCollapse :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport :=
  ⟨hGapCollapse.1,
    hGapCollapse.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
      hGapCollapse.2.2⟩

set_option linter.style.longLine false in
/-- Original-index gap collapse is the same as cofactor gap collapse for the
`j = 1` middle cofactor. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
    (hOriginal :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapseFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hMiddle
  have h := hOriginal rows cols hRows hCols hLeft hGap hRight hBanded hMiddle
  simpa [XiMinorFourBandedCofactorRows, XiMinorFourBandedCofactorCols] using h

set_option linter.style.longLine false in
/-- The original-index gap-collapse package proves the cofactor gap-collapse
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
    (hOriginal :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseFromContext :=
  ⟨hOriginal.1,
    hOriginal.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
      hOriginal.2.2⟩

set_option linter.style.longLine false in
/-- Inactive side-support witnesses make the top-unsupported,
middle-supported branch impossible by the existing one-survivor support
argument. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
    (hSide :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle
  rcases hSide rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported hMiddle with
    ⟨kind0, kind2, hK0, hK2, hInactive0, hInactive2⟩
  exact
    xiJ1TopUnsupportedMiddleSupportedImpossible_of_support
      kind0 kind2 rows cols hRows hCols hLeft hGap hRight hK0 hBanded
      hK2 hInactive0 hInactive2 hUnsupported hMiddle

set_option linter.style.longLine false in
/-- The inactive-side-support package proves the impossible-branch package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
    (hSide :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport :=
  ⟨hSide.1,
    hSide.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
      hSide.2.2⟩

set_option linter.style.longLine false in
/-- A right-side inactive support witness is enough to make the
top-unsupported, middle-supported branch impossible. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
    (hSide :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossibleFromSupport := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle
  rcases hSide rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported hMiddle with ⟨kind2, hK2, hInactive2⟩
  have hB0 : cols 0 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded.1
  have hMid : cols 2 ≤ rows 2 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hMiddle
  have hRows12 : rows 1 < rows 2 := hRows (by decide)
  have hCols12 : cols 1 < cols 2 := hCols (by decide)
  cases kind2 with
  | zeroRow =>
      rcases hK2 with ⟨a, ha⟩
      fin_cases a
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 2 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
      · have hBad : rows 3 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using ha 0
        omega
  | zeroColumn =>
      rcases hK2 with ⟨b, hb⟩
      fin_cases b
      · have hBad : rows 1 < cols 0 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 0
        omega
      · have hBad : rows 2 < cols 1 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 1
        omega
      · have hBad : rows 3 < cols 3 := by
          simpa [XiMinorFourBandedCofactorRows,
            XiMinorFourBandedCofactorCols] using hb 2
        omega
  | full =>
      exact False.elim (hInactive2 xiMinorFourBandedCofactorSupportKindActive_full)
  | banded =>
      exact False.elim (hInactive2 xiMinorFourBandedCofactorSupportKindActive_banded)

set_option linter.style.longLine false in
/-- The right-side inactive support package proves the impossible-branch
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
    (hSide :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport :=
  ⟨hSide.1,
    hSide.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
      hSide.2.2⟩

set_option linter.style.longLine false in
/-- Excluding the two active `j = 2` support cases supplies the right-side
inactive support witness. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
    (hExcluded :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle
  have hClass :=
    xiMinorFourBandedCofactorJ2SupportClass_fromBand rows cols hRows hCols
      hLeft hGap hRight
  have hNoActive :=
    hExcluded rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
      hMiddle
  rcases hClass with hZeroRow | hZeroColumn | hFull | hBanded2
  · refine ⟨.zeroRow, hZeroRow, ?_⟩
    intro hActive
    rcases hActive with h | h <;> cases h
  · refine ⟨.zeroColumn, hZeroColumn, ?_⟩
    intro hActive
    rcases hActive with h | h <;> cases h
  · exact False.elim (hNoActive.1 hFull)
  · exact False.elim (hNoActive.2 hBanded2)

set_option linter.style.longLine false in
/-- The active-exclusion package produces the right-inactive-side-support
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
    (hExcluded :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext :=
  ⟨hExcluded.1,
    hExcluded.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
      hExcluded.2.2⟩

set_option linter.style.longLine false in
/-- In the top-unsupported, middle-supported branch, the right `j = 2`
cofactor cannot be full-supported: full support would force `cols 3 ≤ rows 1`,
while the middle banded support hypothesis gives `rows 1 < cols 3`. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightFullExcluded
    {rows cols : Fin 4 → ℕ}
    (_hRows : StrictMono rows) (_hCols : StrictMono cols)
    (_hLeft : cols 0 ≤ rows 0) (_hGap : rows 0 < cols 3)
    (_hRight : cols 3 ≤ rows 3)
    (hBanded : XiMinorFourBandedCofactorBandedSupport rows cols 1)
    (_hUnsupported :
      XiMinorFourBandedCofactorRows rows 1 <
        XiMinorFourBandedCofactorCols cols 1 2)
    (_hMiddle :
      XiMinorFourBandedCofactorCols cols 1 1 ≤
        XiMinorFourBandedCofactorRows rows 1) :
    ¬ XiMinorFourBandedCofactorFullSupport rows cols 2 := by
  intro hFull
  have hFullTopRight : cols 3 ≤ rows 1 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hFull 0 2
  have hMiddleGap : rows 1 < cols 3 := by
    simpa [XiMinorFourBandedCofactorRows,
      XiMinorFourBandedCofactorCols] using hBanded.2.1
  omega

set_option linter.style.longLine false in
/-- Once right-side full support is ruled out automatically, excluding only
right-side banded support supplies the active-exclusion condition. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
    (hExcluded :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle
  exact
    ⟨xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightFullExcluded
        hRows hCols hLeft hGap hRight hBanded hUnsupported hMiddle,
      hExcluded rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
        hMiddle⟩

set_option linter.style.longLine false in
/-- The right-banded-exclusion package produces the active-exclusion package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
    (hExcluded :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext :=
  ⟨hExcluded.1,
    hExcluded.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
      hExcluded.2.2⟩

set_option linter.style.longLine false in
/-- In the current reduced geometry, middle banded support also forces the
right `j = 2` cofactor to be banded-supported. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBanded_of_middleBanded
    {rows cols : Fin 4 → ℕ}
    (hBanded : XiMinorFourBandedCofactorBandedSupport rows cols 1) :
    XiMinorFourBandedCofactorBandedSupport rows cols 2 := by
  rcases hBanded with ⟨hLeft, hGap, hRight⟩
  exact ⟨hLeft, hGap, hRight⟩

set_option linter.style.longLine false in
/-- If the whole top-unsupported, middle-supported branch is impossible, then
right-side banded support is excluded there. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
    (hImpossible :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle hRightBanded
  exact False.elim
    (hImpossible rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported hMiddle)

set_option linter.style.longLine false in
/-- The branch-impossibility package produces the right-banded-exclusion
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
    (hImpossible :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext :=
  ⟨hImpossible.1,
    hImpossible.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
      hImpossible.2.2⟩

set_option linter.style.longLine false in
/-- Forcing the middle column to be unsupported closes the
top-unsupported/middle-supported branch. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
    (hMiddleUnsupported :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupportedFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hMiddle
  have hBad :=
    hMiddleUnsupported rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported
  exact (not_lt_of_ge hMiddle) hBad

set_option linter.style.longLine false in
/-- The middle-column-unsupported package produces the branch-impossibility
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
    (hMiddleUnsupported :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext :=
  ⟨hMiddleUnsupported.1,
    hMiddleUnsupported.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
      hMiddleUnsupported.2.2⟩

set_option linter.style.longLine false in
/-- Ruling out the middle/top-column straddle interval forces the middle column
to be unsupported. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
    (hNoStraddle :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddleFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupportedFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
  exact Nat.lt_of_not_ge
    (hNoStraddle rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported)

set_option linter.style.longLine false in
/-- The no-straddle package produces the middle-column-unsupported package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
    (hNoStraddle :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedFromContext :=
  ⟨hNoStraddle.1,
    hNoStraddle.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
      hNoStraddle.2.2⟩

set_option linter.style.longLine false in
/-- Contradicting the middle/top-column straddle interval supplies the
no-straddle condition. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
    (hImpossible :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddleFromContext := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hStraddle
  exact
    hImpossible rows cols hRows hCols hLeft hGap hRight hBanded
      hUnsupported hStraddle

set_option linter.style.longLine false in
/-- The straddle-impossibility package produces the no-straddle package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
    (hImpossible :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleFromContext :=
  ⟨hImpossible.1,
    hImpossible.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
      hImpossible.2.2⟩

set_option linter.style.longLine false in
/-- A nonpositive left product contradicts the straddle branch once the kernel
representation supplies strict positivity of every moment coefficient. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
    (hPos : XiMomentCoeffPositive)
    (hContig : XiContigToeplitzTotalPositive)
    (hLeft :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext := by
  intro rows cols hRows hCols hLeft0 hGap hRight hBanded hUnsupported
    hStraddle
  have hProduct :=
    hLeft rows cols hRows hCols hLeft0 hGap hRight hBanded hUnsupported
      hStraddle hContig
  dsimp only at hProduct
  have hPositive :
      0 <
        XiMomentCoeff
          (XiMinorFourBandedCofactorRows rows 1 -
            XiMinorFourBandedCofactorCols cols 1 1) *
          XiMomentCoeff
            (XiMinorFourBandedCofactorRows rows 2 -
              XiMinorFourBandedCofactorCols cols 1 2) :=
    mul_pos
      (hPos
        (XiMinorFourBandedCofactorRows rows 1 -
          XiMinorFourBandedCofactorCols cols 1 1))
      (hPos
        (XiMinorFourBandedCofactorRows rows 2 -
          XiMinorFourBandedCofactorCols cols 1 2))
  exact (not_lt_of_ge hProduct) hPositive

set_option linter.style.longLine false in
/-- No-go theorem for the straddle left-product target.

The concrete selectors `rows = (0, 2, 4, 6)` and `cols = (0, 1, 2, 5)`
satisfy the top-unsupported straddle support context.  Hence strict positivity
of the moment coefficients and contiguous positivity are incompatible with a
uniform nonpositive left-product estimate on this branch. -/
theorem not_xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_positive_and_contig
    (hPos : XiMomentCoeffPositive)
    (hContig : XiContigToeplitzTotalPositive) :
    ¬ XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig := by
  intro hProduct
  have hImpossible :=
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
      hPos hContig hProduct
  exact hImpossible
    (![0, 2, 4, 6] : Fin 4 → ℕ)
    (![0, 1, 2, 5] : Fin 4 → ℕ)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by
      change (0 : ℕ) ≤ 2 ∧ 2 < 5 ∧ 5 ≤ 6
      omega)
    (by decide)
    (by decide)

set_option linter.style.longLine false in
/-- The top-unsupported, middle-supported bracket package contains the
straddle left-bracket estimate as a subcase. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported
    (hMiddle :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleSupportedBracketsFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracketNonpositiveFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hStraddle hContig
  exact (hMiddle rows cols hRows hCols hLeft hGap hRight hBanded
    hUnsupported hStraddle hContig).1

set_option linter.style.longLine false in
/-- The top-unsupported, middle-supported package produces the straddle
left-bracket package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported
    (hMiddle :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketFromContig :=
  ⟨hMiddle.1,
    hMiddle.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported
      hMiddle.2.2⟩

set_option linter.style.longLine false in
/-- The native Toeplitz left bracket reduces to the straddle left moment
product because the top-right bracket entry is structurally zero. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
    (hBracket :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracketNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hStraddle hContig
  have h := hBracket rows cols hRows hCols hLeft hGap hRight hBanded
    hUnsupported hStraddle hContig
  have h12zero :
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hUnsupported)]
  have h32 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    hBanded.2.2
  dsimp only at h
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        hStraddle,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h32,
      h12zero] at h
  simpa using h

set_option linter.style.longLine false in
/-- The straddle left-bracket package produces the straddle left-product
package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
    (hBracket :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductFromContig :=
  ⟨hBracket.1,
    hBracket.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
      hBracket.2.2⟩

set_option linter.style.longLine false in
/-- In the top-unsupported straddle branch, the left moment product also
recovers the native Toeplitz left bracket because the top-right entry is zero. -/
theorem xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct
    (hProduct :
      XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProductNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracketNonpositiveFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hUnsupported
    hStraddle hContig
  have h := hProduct rows cols hRows hCols hLeft hGap hRight hBanded
    hUnsupported hStraddle hContig
  have h12zero :
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hUnsupported)]
  have h32 :
      XiMinorFourBandedCofactorCols cols 1 2 ≤
        XiMinorFourBandedCofactorRows rows 2 :=
    hBanded.2.2
  dsimp only at h ⊢
  rw [xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 1)
        (XiMinorFourBandedCofactorCols cols 1 1)
        hStraddle,
      xiToeplitzEntry_sub
        (XiMinorFourBandedCofactorRows rows 2)
        (XiMinorFourBandedCofactorCols cols 1 2)
        h32,
      h12zero]
  simpa using h

set_option linter.style.longLine false in
/-- The straddle left-product package produces the equivalent straddle
left-bracket package in the top-unsupported branch. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct
    (hProduct :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketFromContig :=
  ⟨hProduct.1,
    hProduct.2.1,
    xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct
      hProduct.2.2⟩

/-- The expanded sparse determinant target implies the determinant-form
banded middle-cofactor obstruction. -/
theorem xiMinorFourBandedCofactorMiddleBandedDetNonpositive_of_expanded
    (hExp :
      XiMinorFourBandedCofactorMiddleBandedExpandedNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleBandedDetNonpositiveFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hBanded hContig
  have h02 :
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows 0)
        (XiMinorFourBandedCofactorCols cols 1 2) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hBanded.2.1)]
  have h := hExp rows cols hRows hCols hLeft hGap hRight
    hBanded hContig
  rw [XiMinorFourBandedCofactorMiddleDetNonpositive]
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [h02]
  ring_nf at h ⊢
  exact h

/-- The moment-zero/expanded-banded package proves the
moment-zero/banded-determinant package. -/
theorem xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositive_of_expanded
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpandedFromContig) :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositiveFromContig :=
  ⟨hSplit.1,
    xiMinorFourBandedCofactorMiddleBandedDetNonpositive_of_expanded hSplit.2⟩

/-- The full-zero plus banded-nonpositive package proves the previous
full/banded support split for middle determinant nonpositivity. -/
theorem xiMinorFourBandedCofactorMiddleDetSupportSplit_of_fullZero
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleDetSupportSplitNonpositiveFromContig := by
  rcases hSplit with ⟨hFullZero, hBanded⟩
  exact
    ⟨by
      intro rows cols hRows hCols hLeft hGap hRight hFull hContig
      rw [XiMinorFourBandedCofactorMiddleDetNonpositive]
      exact le_of_eq
        (hFullZero rows cols hRows hCols hLeft hGap hRight hFull hContig),
      hBanded⟩

/-- The full/banded support split proves universal middle cofactor determinant
nonpositivity. -/
theorem xiMinorFourBandedCofactorMiddleDetNonpositive_of_supportSplit
    (hSplit :
      XiMinorFourBandedCofactorMiddleDetSupportSplitNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleDetNonpositiveFromContig := by
  rcases hSplit with ⟨hFull, hBanded⟩
  intro rows cols hRows hCols hLeft hGap hRight hContig
  have hClass :=
    xiMinorFourBandedCofactorJ1SupportClass_fromBand
      rows cols hRows hCols hLeft hGap hRight
  rcases hClass with hZeroRow | hRest
  · rw [XiMinorFourBandedCofactorMiddleDetNonpositive]
    simpa using
      (le_of_eq
        (xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
          hZeroRow))
  · rcases hRest with hZeroCol | hRest
    · rw [XiMinorFourBandedCofactorMiddleDetNonpositive]
      simpa using
        (le_of_eq
          (xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
            hZeroCol))
    · rcases hRest with hFullSupport | hBandedSupport
      · exact hFull rows cols hRows hCols hLeft hGap hRight
          hFullSupport hContig
      · exact hBanded rows cols hRows hCols hLeft hGap hRight
          hBandedSupport hContig

/-- Middle cofactor determinant nonpositivity proves the middle upper-bound
estimate once the side determinant signs are supplied by the existing `3 × 3`
targets and support-classification. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_middleUpperBound
    (hUpper :
      XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  dsimp only
  intro _hPositive
  exact hUpper rows cols hRows hCols hLeft hGap hRight hContig

set_option linter.style.longLine false in
/-- A side-allocation witness immediately proves positive-middle cancellation
by adding its two one-sided bounds. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_sideAllocation
    (hAllocation :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  dsimp only
  intro hdet1
  rcases hAllocation rows cols hRows hCols hLeft hGap hRight hContig hdet1 with
    ⟨leftShare, rightShare, _hLeftNonneg, _hRightNonneg, hSum,
      hLeftBound, hRightBound⟩
  calc
    _ = leftShare + rightShare := hSum.symm
    _ ≤ _ := add_le_add hLeftBound hRightBound

set_option linter.style.longLine false in
/-- Existing side determinant positivity constructs a side allocation from
every positive-middle cancellation estimate.  The construction assigns the
whole middle term to the left when it fits; otherwise it fills the left side
and sends the exact remainder to the right. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_cancellation
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hCancellation :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  dsimp only
  intro hdet1
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change
    ∃ leftShare rightShare : ℝ,
      0 ≤ leftShare ∧
      0 ≤ rightShare ∧
      leftShare + rightShare = A 0 1 * (C 1).det ∧
      leftShare ≤ A 0 0 * (C 0).det ∧
      rightShare ≤ A 0 2 * (C 2).det
  have hBound :
      A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det :=
    hCancellation rows cols hRows hCols hLeft hGap hRight hContig hdet1
  have hSide :=
    xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
      hThreeFull
      hThreeBanded
      xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
  rcases hSide with ⟨hSideLeft, hSideRight⟩
  have hdet0 : 0 ≤ (C 0).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetLeftNonnegative] using
      hSideLeft rows cols hRows hCols hLeft hGap hRight hContig
  have hdet2 : 0 ≤ (C 2).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetRightNonnegative] using
      hSideRight rows cols hRows hCols hLeft hGap hRight hContig
  have hA00 : 0 ≤ A 0 0 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hA01 : 0 ≤ A 0 1 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 1)
  have hA02 : 0 ≤ A 0 2 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
  have hMiddleNonneg : 0 ≤ A 0 1 * (C 1).det :=
    mul_nonneg hA01 (le_of_lt hdet1)
  have hLeftNonneg : 0 ≤ A 0 0 * (C 0).det :=
    mul_nonneg hA00 hdet0
  have hRightNonneg : 0 ≤ A 0 2 * (C 2).det :=
    mul_nonneg hA02 hdet2
  by_cases hFitsLeft : A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det
  · refine ⟨A 0 1 * (C 1).det, 0, hMiddleNonneg, le_rfl, ?_,
      hFitsLeft, hRightNonneg⟩
    ring
  · refine ⟨A 0 0 * (C 0).det,
      A 0 1 * (C 1).det - A 0 0 * (C 0).det,
      hLeftNonneg, ?_, ?_, le_rfl, ?_⟩
    · exact sub_nonneg.mpr (le_of_not_ge hFitsLeft)
    · ring
    · linarith

set_option linter.style.longLine false in
/-- Factorized row/cofactor log-convexity multiplies into the weighted
geometric-mean domination condition. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean_of_factorizedLogConvexity
    (hFactorized :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetFactorizedLogConvexityFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  dsimp only
  intro hdet1
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change
    (A 0 1 * (C 1).det) ^ 2 ≤
      (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det)
  rcases hFactorized rows cols hRows hCols hLeft hGap hRight hContig hdet1 with
    ⟨hTop, hCofactor⟩
  have hTopProductNonneg : 0 ≤ A 0 0 * A 0 2 :=
    le_trans (sq_nonneg (A 0 1)) hTop
  have hProduct :=
    mul_le_mul hTop hCofactor (sq_nonneg ((C 1).det)) hTopProductNonneg
  calc
    (A 0 1 * (C 1).det) ^ 2 =
        (A 0 1) ^ 2 * ((C 1).det) ^ 2 := by ring
    _ ≤ (A 0 0 * A 0 2) * ((C 0).det * (C 2).det) := hProduct
    _ = (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det) := by ring

set_option linter.style.longLine false in
/-- Pointwise arithmetic-geometric mean bridge from a weighted geometric-mean
bound to the middle upper bound. -/
theorem xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_geometricMeanAt
    {rows cols : Fin 4 → ℕ}
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hLeft : cols 0 ≤ rows 0) (hGap : rows 0 < cols 3)
    (hRight : cols 3 ≤ rows 3)
    (hContig : XiContigToeplitzTotalPositive)
    (hGeom :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean
        rows cols) :
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound rows cols := by
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det
  change
    (A 0 1 * (C 1).det) ^ 2 ≤
      (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det) at hGeom
  have hSide :=
    xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
      hThreeFull
      hThreeBanded
      xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
  rcases hSide with ⟨hSideLeft, hSideRight⟩
  have hdet0 : 0 ≤ (C 0).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetLeftNonnegative] using
      hSideLeft rows cols hRows hCols hLeft hGap hRight hContig
  have hdet2 : 0 ≤ (C 2).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetRightNonnegative] using
      hSideRight rows cols hRows hCols hLeft hGap hRight hContig
  have hA00 : 0 ≤ A 0 0 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hA02 : 0 ≤ A 0 2 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
  have hLeftNonneg : 0 ≤ A 0 0 * (C 0).det :=
    mul_nonneg hA00 hdet0
  have hRightNonneg : 0 ≤ A 0 2 * (C 2).det :=
    mul_nonneg hA02 hdet2
  have hSideProduct :
      (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det) ≤
        (A 0 0 * (C 0).det + A 0 2 * (C 2).det) ^ 2 := by
    nlinarith [sq_nonneg (A 0 0 * (C 0).det),
      sq_nonneg (A 0 2 * (C 2).det),
      mul_nonneg hLeftNonneg hRightNonneg]
  exact le_of_sq_le_sq (hGeom.trans hSideProduct)
    (add_nonneg hLeftNonneg hRightNonneg)

set_option linter.style.longLine false in
/-- The compound-minor geometric-mean condition proves positive-middle
cancellation by the arithmetic-geometric mean inequality for the two
nonnegative side terms. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_geometricMean
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hGeometricMean :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  dsimp only
  intro hdet1
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det
  have hGeom :
      (A 0 1 * (C 1).det) ^ 2 ≤
        (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det) :=
    hGeometricMean rows cols hRows hCols hLeft hGap hRight hContig hdet1
  have hSide :=
    xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
      hThreeFull
      hThreeBanded
      xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
  rcases hSide with ⟨hSideLeft, hSideRight⟩
  have hdet0 : 0 ≤ (C 0).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetLeftNonnegative] using
      hSideLeft rows cols hRows hCols hLeft hGap hRight hContig
  have hdet2 : 0 ≤ (C 2).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetRightNonnegative] using
      hSideRight rows cols hRows hCols hLeft hGap hRight hContig
  have hA00 : 0 ≤ A 0 0 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hA02 : 0 ≤ A 0 2 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
  have hLeftNonneg : 0 ≤ A 0 0 * (C 0).det :=
    mul_nonneg hA00 hdet0
  have hRightNonneg : 0 ≤ A 0 2 * (C 2).det :=
    mul_nonneg hA02 hdet2
  have hSideProduct :
      (A 0 0 * (C 0).det) * (A 0 2 * (C 2).det) ≤
        (A 0 0 * (C 0).det + A 0 2 * (C 2).det) ^ 2 := by
    nlinarith [sq_nonneg (A 0 0 * (C 0).det),
      sq_nonneg (A 0 2 * (C 2).det),
      mul_nonneg hLeftNonneg hRightNonneg]
  exact le_of_sq_le_sq (hGeom.trans hSideProduct)
    (add_nonneg hLeftNonneg hRightNonneg)

set_option linter.style.longLine false in
/-- The geometric-mean compound-minor condition produces the side-allocation
frontier through the verified cancellation bridge. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_geometricMean
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hGeometricMean :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig :=
  xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_cancellation
    hThreeFull
    hThreeBanded
    (xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_geometricMean
      hThreeFull hThreeBanded hGeometricMean)

set_option linter.style.longLine false in
/-- The moment/cofactor cross-product condition is exactly the left-dominance
condition on the active support interval. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominance_of_momentCofactorRatio
    (hRatio :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominanceFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hMiddleSupported
    hTopUnsupported hContig
  dsimp only
  intro hdet1
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det
  have hMoment :=
    hRatio rows cols hRows hCols hLeft hGap hRight hMiddleSupported
      hTopUnsupported hContig hdet1
  have hA00 : A 0 0 = XiMomentCoeff (rows 0 - cols 0) := by
    simpa [A] using xiToeplitzEntry_sub (rows 0) (cols 0) hLeft
  have hA01 : A 0 1 = XiMomentCoeff (rows 0 - cols 1) := by
    simpa [A] using xiToeplitzEntry_sub (rows 0) (cols 1) hMiddleSupported
  rw [hA00, hA01]
  exact hMoment

set_option linter.style.longLine false in
/-- A subtraction-free contiguous-minor certificate proves the active
moment/cofactor ratio inequality. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_of_positivePolynomialCertificate
    (hCertificate :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedPositivePolynomialCertificateFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hMiddleSupported
    hTopUnsupported hContig
  dsimp only
  intro hdet1
  apply sub_nonneg.mp
  exact xiContigMinorPositivePolynomial_nonneg hContig
    (hCertificate rows cols hRows hCols hLeft hGap hRight hMiddleSupported
      hTopUnsupported hContig hdet1)

set_option linter.style.longLine false in
/-- Positive normalization of the adjacent cofactor ratio implies the
division-free moment/cofactor comparison. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_of_normalized
    (hPos : XiMomentCoeffPositive)
    (hNormalized :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatioFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hMiddleSupported
    hTopUnsupported hContig
  dsimp only
  intro hdet1
  rcases hNormalized rows cols hRows hCols hLeft hGap hRight hMiddleSupported
    hTopUnsupported hContig hdet1 with ⟨hdet0, hRatio⟩
  have hMoment1 : 0 < XiMomentCoeff (rows 0 - cols 1) :=
    hPos (rows 0 - cols 1)
  have hCross := (div_le_div_iff₀ hdet0 hMoment1).mp hRatio
  simpa [mul_comm] using hCross

set_option linter.style.longLine false in
/-- With positive Xi moments, the division-free adjacent cofactor comparison
already forces positivity of the left cofactor and therefore admits quotient
normalization. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatio_of_momentCofactorRatio
    (hPos : XiMomentCoeffPositive)
    (hRatio :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatioFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatioFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hMiddleSupported
    hTopUnsupported hContig
  dsimp only
  intro hdet1
  have hCross :=
    hRatio rows cols hRows hCols hLeft hGap hRight hMiddleSupported
      hTopUnsupported hContig hdet1
  have hMoment0 : 0 < XiMomentCoeff (rows 0 - cols 0) :=
    hPos (rows 0 - cols 0)
  have hMoment1 : 0 < XiMomentCoeff (rows 0 - cols 1) :=
    hPos (rows 0 - cols 1)
  have hRightPos : 0 < XiMomentCoeff (rows 0 - cols 0) *
      (Matrix.of (fun a b =>
        XiToeplitzEntry
          (XiMinorFourBandedCofactorRows rows a)
          (XiMinorFourBandedCofactorCols cols 0 b))).det :=
    lt_of_lt_of_le (mul_pos hMoment1 hdet1) hCross
  have hdet0 : 0 < (Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols 0 b))).det := by
    rcases (mul_pos_iff.mp hRightPos) with hPositive | hNegative
    · exact hPositive.2
    · exact (not_lt_of_ge hMoment0.le hNegative.1).elim
  refine ⟨hdet0, ?_⟩
  apply (div_le_div_iff₀ hdet0 hMoment1).mpr
  simpa [mul_comm] using hCross

set_option linter.style.longLine false in
/-- The moment/cofactor-ratio three-way payload produces the prior three-way
support payload by rewriting the two supported top-row entries. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplit_of_momentCofactorRatio
    (hRatio :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplitFromContig :=
  ⟨xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominance_of_momentCofactorRatio
      hRatio.1,
    hRatio.2⟩

set_option linter.style.longLine false in
/-- The subtraction-free certificate payload produces the division-free
moment/cofactor payload. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_positivePolynomialCertificate
    (hCertificate :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig :=
  ⟨xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_of_positivePolynomialCertificate
      hCertificate.1,
    hCertificate.2⟩

set_option linter.style.longLine false in
/-- The normalized three-way payload implies the division-free three-way
payload once positive moment denominators are supplied. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_normalized
    (hPos : XiMomentCoeffPositive)
    (hNormalized :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig :=
  ⟨xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedMomentCofactorRatio_of_normalized
      hPos hNormalized.1,
    hNormalized.2⟩

set_option linter.style.longLine false in
/-- Under positive Xi moments, the division-free three-way payload also gives
the normalized three-way payload. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit_of_momentCofactorRatio
    (hPos : XiMomentCoeffPositive)
    (hRatio :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitFromContig :=
  ⟨xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedNormalizedMomentCofactorRatio_of_momentCofactorRatio
      hPos hRatio.1,
    hRatio.2⟩

set_option linter.style.longLine false in
/-- Middle-supported left dominance supplies the whole top-right-unsupported
left-dominance target.  If the middle top-row entry is unsupported as well,
that entry vanishes and the left side is nonnegative automatically. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedLeftDominance_of_middleSupported
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hMiddle :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedMiddleSupportedLeftDominanceFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedLeftDominanceFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hTopUnsupported hContig
  dsimp only
  intro hdet1
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det
  by_cases hMiddleSupported : cols 1 ≤ rows 0
  · exact hMiddle rows cols hRows hCols hLeft hGap hRight hMiddleSupported
      hTopUnsupported hContig hdet1
  · have hSide :=
      xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
        hThreeFull
        hThreeBanded
        xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
    rcases hSide with ⟨hSideLeft, _hSideRight⟩
    have hdet0 : 0 ≤ (C 0).det := by
      simpa [C, XiMinorFourBandedCofactorSideDetLeftNonnegative] using
        hSideLeft rows cols hRows hCols hLeft hGap hRight hContig
    have hA00 : 0 ≤ A 0 0 := by
      simpa [A] using
        xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
    have hA01zero : A 0 1 = 0 := by
      simp [A, XiToeplitzEntry, hMiddleSupported]
    rw [hA01zero]
    simpa using mul_nonneg hA00 hdet0

set_option linter.style.longLine false in
/-- The three-way support payload produces the previous top-right support
split after the `A01 = 0` subcase is discharged automatically. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplit_of_threeWay
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hThreeWay :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplitFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplitFromContig :=
  ⟨xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightUnsupportedLeftDominance_of_middleSupported
      hThreeFull hThreeBanded hThreeWay.1,
    hThreeWay.2⟩

set_option linter.style.longLine false in
/-- The top-right support split proves positive-middle cancellation without
requiring geometric-mean domination in the structurally zero right branch. -/
theorem xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_topRightSupportSplit
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hSplit :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplitFromContig) :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig := by
  rcases hSplit with ⟨hUnsupported, hSupported⟩
  intro rows cols hRows hCols hLeft hGap hRight hContig
  dsimp only
  intro hdet1
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det
  by_cases hTopSupported : cols 2 ≤ rows 0
  · exact
      xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_geometricMeanAt
        hThreeFull hThreeBanded hRows hCols hLeft hGap hRight hContig
        (hSupported rows cols hRows hCols hLeft hGap hRight hTopSupported hContig)
  · have hLeftDom :=
      hUnsupported rows cols hRows hCols hLeft hGap hRight
        (Nat.lt_of_not_ge hTopSupported) hContig hdet1
    have hSide :=
      xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
        hThreeFull
        hThreeBanded
        xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
    rcases hSide with ⟨_hSideLeft, hSideRight⟩
    have hdet2 : 0 ≤ (C 2).det := by
      simpa [C, XiMinorFourBandedCofactorSideDetRightNonnegative] using
        hSideRight rows cols hRows hCols hLeft hGap hRight hContig
    have hA02 : 0 ≤ A 0 2 := by
      simpa [A] using
        xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
    exact le_trans hLeftDom (le_add_of_nonneg_right (mul_nonneg hA02 hdet2))

set_option linter.style.longLine false in
/-- The positive-middle-determinant cancellation estimate recovers the full
middle upper bound.  The complementary nonpositive branch is automatic from
the existing side support-class determinant signs and entry nonnegativity. -/
theorem xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_positiveMiddleDetCancellation
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hCancellation :
      XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  let C : Fin 4 → Matrix (Fin 3) (Fin 3) ℝ := fun j =>
    Matrix.of (fun a b =>
      XiToeplitzEntry
        (XiMinorFourBandedCofactorRows rows a)
        (XiMinorFourBandedCofactorCols cols j b))
  change A 0 1 * (C 1).det ≤ A 0 0 * (C 0).det + A 0 2 * (C 2).det
  by_cases hdet1 : 0 < (C 1).det
  · exact hCancellation rows cols hRows hCols hLeft hGap hRight hContig hdet1
  have hSide :=
    xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
      hThreeFull
      hThreeBanded
      xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
  rcases hSide with ⟨hSideLeft, hSideRight⟩
  have hdet0 : 0 ≤ (C 0).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetLeftNonnegative] using
      hSideLeft rows cols hRows hCols hLeft hGap hRight hContig
  have hdet2 : 0 ≤ (C 2).det := by
    simpa [C, XiMinorFourBandedCofactorSideDetRightNonnegative] using
      hSideRight rows cols hRows hCols hLeft hGap hRight hContig
  have hA00 : 0 ≤ A 0 0 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hA01 : 0 ≤ A 0 1 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 1)
  have hA02 : 0 ≤ A 0 2 := by
    simpa [A] using
      xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
  exact le_trans
    (mul_nonpos_of_nonneg_of_nonpos hA01 (le_of_not_gt hdet1))
    (add_nonneg (mul_nonneg hA00 hdet0) (mul_nonneg hA02 hdet2))

/-- Middle cofactor determinant nonpositivity proves the middle upper-bound
estimate once the side determinant signs are supplied by the existing `3 × 3`
targets and support-classification. -/
theorem xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_middleDetNonpositive
    (hThreeFull : XiMinorThreeFullSupportFromContig)
    (hThreeBanded : XiMinorThreeBandedDetInequalityFromContig)
    (hMiddleDet : XiMinorFourBandedCofactorMiddleDetNonpositiveFromContig) :
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  have hSide :=
    xiMinorFourBandedCofactorSideDetLeftRightNonnegative_of_supportClass
      hThreeFull
      hThreeBanded
      xiMinorFourBandedCofactorSideDetLeftRightSupportClass_fromBand
  rcases hSide with ⟨hSideLeft, hSideRight⟩
  have hdet0 := hSideLeft rows cols hRows hCols hLeft hGap hRight hContig
  have hdet2 := hSideRight rows cols hRows hCols hLeft hGap hRight hContig
  have hdet1 :=
    hMiddleDet rows cols hRows hCols hLeft hGap hRight hContig
  have hA00 :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 0 := by
    simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
  have hA01 :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 1 := by
    simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 1)
  have hA02 :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 2 := by
    simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
  have hLeftProd :
      (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 1 *
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 1 b))).det ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hA01 hdet1
  have hRightSum :
      0 ≤
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 0 *
          (Matrix.of (fun a b =>
            XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows a)
              (XiMinorFourBandedCofactorCols cols 0 b))).det +
        (Matrix.of (fun a b =>
          if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)) :
            Matrix (Fin 4) (Fin 4) ℝ) 0 2 *
          (Matrix.of (fun a b =>
            XiToeplitzEntry
              (XiMinorFourBandedCofactorRows rows a)
              (XiMinorFourBandedCofactorCols cols 2 b))).det :=
    add_nonneg (mul_nonneg hA00 hdet0) (mul_nonneg hA02 hdet2)
  exact le_trans hLeftProd hRightSum

/-- The three position-specific one-survivor targets imply the combined
one-survivor case table. -/
theorem xiMinorFourBandedCofactorOneSurvivorCaseTable_of_j012
    (hJ0 : XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig)
    (hJ1 : XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig)
    (hJ2 : XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig) :
    XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 hExactlyOne hContig
  rcases hExactlyOne with h0 | h1 | h2
  · exact hJ0 kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h0.1 h0.2.1 h0.2.2 hContig
  · exact hJ1 kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h1.1 h1.2.1 h1.2.2 hContig
  · exact hJ2 kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h2.1 h2.2.1 h2.2.2 hContig

/-- The positive-side one-survivor payload plus the signed-negative `j = 1`
target imply the combined one-survivor case table. -/
theorem xiMinorFourBandedCofactorOneSurvivorCaseTable_of_positive_and_j1
    (hPositive :
      XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig)
    (hJ1 : XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig) :
    XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig :=
  xiMinorFourBandedCofactorOneSurvivorCaseTable_of_j012
    hPositive.1 hJ1 hPositive.2

/-- The full/banded `j = 0` one-survivor subcases imply the combined positive
`j = 0` one-survivor target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ0_of_full_banded
    (hFull : XiMinorFourBandedCofactorOneSurvivorJ0FullInequalityFromContig)
    (hBanded : XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h0 h1 h2 hContig
  cases kind0
  · have hNot :
        ¬ XiMinorFourBandedCofactorSupportKindActive .zeroRow := by
      simp [XiMinorFourBandedCofactorSupportKindActive]
    exact False.elim (hNot h0)
  · have hNot :
        ¬ XiMinorFourBandedCofactorSupportKindActive .zeroColumn := by
      simp [XiMinorFourBandedCofactorSupportKindActive]
    exact False.elim (hNot h0)
  · exact hFull kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h1 h2 hContig
  · exact hBanded kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h1 h2 hContig

/-- The full/banded `j = 2` one-survivor subcases imply the combined positive
`j = 2` one-survivor target. -/
theorem xiMinorFourBandedCofactorOneSurvivorJ2_of_full_banded
    (hFull : XiMinorFourBandedCofactorOneSurvivorJ2FullInequalityFromContig)
    (hBanded : XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig) :
    XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 h0 h1 h2 hContig
  cases kind2
  · have hNot :
        ¬ XiMinorFourBandedCofactorSupportKindActive .zeroRow := by
      simp [XiMinorFourBandedCofactorSupportKindActive]
    exact False.elim (hNot h2)
  · have hNot :
        ¬ XiMinorFourBandedCofactorSupportKindActive .zeroColumn := by
      simp [XiMinorFourBandedCofactorSupportKindActive]
    exact False.elim (hNot h2)
  · exact hFull kind0 kind1 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h0 h1 hContig
  · exact hBanded kind0 kind1 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 h0 h1 hContig

/-- The four full/banded positive one-survivor subcases imply the positive-side
one-survivor payload. -/
theorem xiMinorFourBandedCofactorPositiveOneSurvivor_of_full_banded
    (hJ0Full : XiMinorFourBandedCofactorOneSurvivorJ0FullInequalityFromContig)
    (hJ0Banded : XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig)
    (hJ2Full : XiMinorFourBandedCofactorOneSurvivorJ2FullInequalityFromContig)
    (hJ2Banded : XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig) :
    XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig :=
  ⟨xiMinorFourBandedCofactorOneSurvivorJ0_of_full_banded hJ0Full hJ0Banded,
    xiMinorFourBandedCofactorOneSurvivorJ2_of_full_banded hJ2Full hJ2Banded⟩

/-- The positive full-support bundle plus the two banded side cases imply the
positive-side one-survivor payload. -/
theorem xiMinorFourBandedCofactorPositiveOneSurvivor_of_fullBundle_banded
    (hFull :
      XiMinorFourBandedCofactorPositiveFullOneSurvivorInequalityFromContig)
    (hJ0Banded : XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig)
    (hJ2Banded : XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig) :
    XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig :=
  xiMinorFourBandedCofactorPositiveOneSurvivor_of_full_banded
    hFull.1 hJ0Banded hFull.2 hJ2Banded

/-- The determinant-level positive full-support target implies the
cofactor-expansion positive full-support one-survivor target. -/
theorem xiMinorFourBandedCofactorPositiveFullOneSurvivor_of_det
    (hDet : XiMinorFourBandedCofactorPositiveFullDetFromContig) :
    XiMinorFourBandedCofactorPositiveFullOneSurvivorInequalityFromContig := by
  constructor
  · intro kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hFull hK1 hK2 h1 h2 hContig
    have hdet0 := hDet.1 kind1 kind2 rows cols hRows hCols hLeft hGap
      hRight hFull hK1 hK2 h1 h2 hContig
    have hdet1 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 1 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK1 h1
    have hdet2 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 2 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK2 h2
    have hcoeff :
        0 ≤
          (Matrix.of (fun a b =>
            if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)))
            0 0 := by
      simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 0)
    simpa [hdet1, hdet2] using mul_nonneg hcoeff hdet0
  · intro kind0 kind1 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hFull h0 h1 hContig
    have hdet2 := hDet.2 kind0 kind1 rows cols hRows hCols hLeft hGap
      hRight hK0 hK1 hFull h0 h1 hContig
    have hdet0 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 0 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK0 h0
    have hdet1 :
        (Matrix.of (fun a b =>
          XiToeplitzEntry
            (XiMinorFourBandedCofactorRows rows a)
            (XiMinorFourBandedCofactorCols cols 1 b))).det = 0 :=
      xiMinorFourBandedCofactorDet_eq_zero_of_inactiveKind hK1 h1
    have hcoeff :
        0 ≤
          (Matrix.of (fun a b =>
            if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b)))
            0 2 := by
      simpa using xiToeplitzEntry_nonneg_of_contig hContig (rows 0) (cols 2)
    simpa [hdet0, hdet1] using mul_nonneg hcoeff hdet2

/-- The one-survivor and multi-survivor tables together imply the reduced
nonzero-survivor case table. -/
theorem xiMinorFourBandedCofactorNonzeroCaseTable_of_survivorSplit
    (hOne : XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig)
    (hMulti : XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig) :
    XiMinorFourBandedCofactorNonzeroCaseTableInequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 hActive hContig
  by_cases h0 : XiMinorFourBandedCofactorSupportKindActive kind0
  · by_cases h1 : XiMinorFourBandedCofactorSupportKindActive kind1
    · exact hMulti kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
        hK0 hK1 hK2 (Or.inl ⟨h0, h1⟩) hContig
    · by_cases h2 : XiMinorFourBandedCofactorSupportKindActive kind2
      · exact hMulti kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2 (Or.inr (Or.inl ⟨h0, h2⟩)) hContig
      · exact hOne kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2 (Or.inl ⟨h0, h1, h2⟩) hContig
  · by_cases h1 : XiMinorFourBandedCofactorSupportKindActive kind1
    · by_cases h2 : XiMinorFourBandedCofactorSupportKindActive kind2
      · exact hMulti kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2 (Or.inr (Or.inr ⟨h1, h2⟩)) hContig
      · exact hOne kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2 (Or.inr (Or.inl ⟨h0, h1, h2⟩)) hContig
    · by_cases h2 : XiMinorFourBandedCofactorSupportKindActive kind2
      · exact hOne kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
          hK0 hK1 hK2 (Or.inr (Or.inr ⟨h0, h1, h2⟩)) hContig
      · exact False.elim (hActive.elim h0 (fun h12 => h12.elim h1 h2))

/-- The reduced nonzero-survivor case table implies the full case table because
the complementary rows have only zero-row/zero-column cofactors, hence all
three cofactor determinants vanish. -/
theorem xiMinorFourBandedCofactorCaseTable_of_nonzeroCaseTable
    (hNonzero :
      XiMinorFourBandedCofactorNonzeroCaseTableInequalityFromContig) :
    XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig := by
  intro kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
    hK0 hK1 hK2 hContig
  by_cases hActive :
      XiMinorFourBandedCofactorSupportKindActive kind0 ∨
        XiMinorFourBandedCofactorSupportKindActive kind1 ∨
          XiMinorFourBandedCofactorSupportKindActive kind2
  · exact hNonzero kind0 kind1 kind2 rows cols hRows hCols hLeft hGap hRight
      hK0 hK1 hK2 hActive hContig
  · cases kind0 <;> cases kind1 <;> cases kind2
    all_goals
      first
      | simp only [XiMinorFourBandedCofactorSupportKindHolds, Fin.isValue]
          at hK0 hK1 hK2
        have hdet0 :
            (Matrix.of (fun a b =>
              XiToeplitzEntry
                (XiMinorFourBandedCofactorRows rows a)
                (XiMinorFourBandedCofactorCols cols 0 b))).det = 0 := by
          first
          | exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
              (rows := rows) (cols := cols) (j := 0) hK0
          | exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
              (rows := rows) (cols := cols) (j := 0) hK0
        have hdet1 :
            (Matrix.of (fun a b =>
              XiToeplitzEntry
                (XiMinorFourBandedCofactorRows rows a)
                (XiMinorFourBandedCofactorCols cols 1 b))).det = 0 := by
          first
          | exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
              (rows := rows) (cols := cols) (j := 1) hK1
          | exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
              (rows := rows) (cols := cols) (j := 1) hK1
        have hdet2 :
            (Matrix.of (fun a b =>
              XiToeplitzEntry
                (XiMinorFourBandedCofactorRows rows a)
                (XiMinorFourBandedCofactorCols cols 2 b))).det = 0 := by
          first
          | exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroRowSupport
              (rows := rows) (cols := cols) (j := 2) hK2
          | exact xiMinorFourBandedCofactorDet_eq_zero_of_zeroColumnSupport
              (rows := rows) (cols := cols) (j := 2) hK2
        simp [hdet0, hdet1, hdet2]
      | exact False.elim (hActive (by
          simp [XiMinorFourBandedCofactorSupportKindActive]))

/-- The support-kind case table implies the support-class split target by
exhausting the four possible support classes for each surviving cofactor. -/
theorem xiMinorFourBandedCofactorSupportSplit_of_caseTable
    (hCase : XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig) :
    XiMinorFourBandedCofactorSupportSplitInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hC0 hC1 hC2 hContig
  rcases hC0 with h0 | h0 | h0 | h0
  · rcases hC1 with h1 | h1 | h1 | h1
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroRow .zeroRow .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .zeroRow .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .zeroRow .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .zeroRow .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroRow .zeroColumn .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .zeroColumn .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .zeroColumn .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .zeroColumn .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroRow .full .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .full .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .full .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .full .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroRow .banded .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .banded .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .banded .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroRow .banded .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
  · rcases hC1 with h1 | h1 | h1 | h1
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroColumn .zeroRow .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .zeroRow .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .zeroRow .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .zeroRow .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroColumn .zeroColumn .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .zeroColumn .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .zeroColumn .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .zeroColumn .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroColumn .full .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .full .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .full .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .full .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .zeroColumn .banded .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .banded .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .banded .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .zeroColumn .banded .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
  · rcases hC1 with h1 | h1 | h1 | h1
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .full .zeroRow .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .zeroRow .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .zeroRow .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .zeroRow .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .full .zeroColumn .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .zeroColumn .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .zeroColumn .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .zeroColumn .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .full .full .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .full .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .full .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .full .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .full .banded .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .banded .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .banded .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .full .banded .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
  · rcases hC1 with h1 | h1 | h1 | h1
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .banded .zeroRow .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .zeroRow .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .zeroRow .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .zeroRow .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .banded .zeroColumn .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .zeroColumn .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .zeroColumn .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .zeroColumn .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .banded .full .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .full .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .full .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .full .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
    · rcases hC2 with h2 | h2 | h2 | h2
      · exact hCase .banded .banded .zeroRow rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .banded .zeroColumn rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .banded .full rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig
      · exact hCase .banded .banded .banded rows cols hRows hCols
          hLeft hGap hRight h0 h1 h2 hContig

/-- The support-class split target implies the row/column-selector target once
the three surviving cofactors are classified. -/
theorem xiMinorFourBandedCofactorRowCol_of_supportSplit
    (hSplit : XiMinorFourBandedCofactorSupportSplitInequalityFromContig)
    (hClass : XiMinorFourBandedCofactorSupportClassesFromBand) :
    XiMinorFourBandedCofactorRowColInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  rcases hClass rows cols hRows hCols hLeft hGap hRight with
    ⟨hC0, hC1, hC2⟩
  exact hSplit rows cols hRows hCols hLeft hGap hRight hC0 hC1 hC2 hContig

/-- The row/column-selector cofactor target implies the named-cofactor target
by rewriting the named cofactors to their selected Toeplitz-entry matrices. -/
theorem xiMinorFourBandedNamedCofactor_of_rowCol
    (hRowCol : XiMinorFourBandedCofactorRowColInequalityFromContig) :
    XiMinorFourBandedNamedCofactorInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  have h := hRowCol rows cols hRows hCols hLeft hGap hRight hContig
  rw [xiMinorFourBandedCofactorMatrix_eq_toeplitz rows cols 0,
      xiMinorFourBandedCofactorMatrix_eq_toeplitz rows cols 1,
      xiMinorFourBandedCofactorMatrix_eq_toeplitz rows cols 2]
  simpa using h

/-- The named-cofactor target implies the explicit three-cofactor target by
unfolding the cofactor matrices. -/
theorem xiMinorFourBandedThreeCofactor_of_namedCofactor
    (hNamed : XiMinorFourBandedNamedCofactorInequalityFromContig) :
    XiMinorFourBandedThreeCofactorInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  have h := hNamed rows cols hRows hCols hLeft hGap hRight hContig
  simpa [XiMinorFourBandedCofactorMatrix] using h

/-- The three-cofactor target implies the row-zero cofactor target by expanding
the `Fin 4` sum and dropping the formally zero `j = 3` term. -/
theorem xiMinorFourBandedRowZeroCofactor_of_threeCofactor
    (hThree : XiMinorFourBandedThreeCofactorInequalityFromContig) :
    XiMinorFourBandedRowZeroCofactorInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  have h :=
    hThree rows cols hRows hCols hLeft hGap hRight hContig
  change 0 ≤
    ∑ j : Fin 4,
      (-1 : ℝ) ^ (j : ℕ) * A 0 j *
        (A.submatrix Fin.succ j.succAbove).det
  rw [Fin.sum_univ_four]
  simpa [A, add_assoc, sub_eq_add_neg] using h

/-- The row-zero cofactor target implies the upper-right-zero determinant
target by the `4 × 4` Laplacian row expansion. -/
theorem xiMinorFourBandedUpperRightZero_of_rowZeroCofactor
    (hCofactor : XiMinorFourBandedRowZeroCofactorInequalityFromContig) :
    XiMinorFourBandedUpperRightZeroDetInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    Matrix.of (fun a b =>
      if a = 0 ∧ b = 3 then 0 else XiToeplitzEntry (rows a) (cols b))
  have h :=
    hCofactor rows cols hRows hCols hLeft hGap hRight hContig
  change 0 ≤ A.det
  rw [Matrix.det_succ_row_zero]
  simpa [A] using h

/-- The upper-right-zero determinant target implies the determinant-form
banded `4 × 4` target. -/
theorem xiMinorFourBandedDetInequality_of_upperRightZero
    (hZero : XiMinorFourBandedUpperRightZeroDetInequalityFromContig) :
    XiMinorFourBandedDetInequalityFromContig := by
  intro rows cols hRows hCols hLeft hGap hRight hContig
  have h03 : XiToeplitzEntry (rows 0) (cols 3) = 0 := by
    unfold XiToeplitzEntry
    rw [if_neg (Nat.not_le_of_gt hGap)]
  have h := hZero rows cols hRows hCols hLeft hGap hRight hContig
  convert h using 2
  ext a b
  by_cases hab : a = 0 ∧ b = 3
  · rcases hab with ⟨rfl, rfl⟩
    simp [h03]
  · simp [hab]

/-- The banded determinant inequality supplies local certificates for every
banded mixed-support `4 × 4` arbitrary minor. -/
def xiMinorFourBandedDetCertificate
    (hDet : XiMinorFourBandedDetInequalityFromContig)
    (rows cols : Fin 4 → ℕ)
    (hRows : StrictMono rows) (hCols : StrictMono cols)
    (hLeft : cols 0 ≤ rows 0)
    (hGap : rows 0 < cols 3)
    (hRight : cols 3 ≤ rows 3) :
    XiMinorContigCertificate 4 rows cols hRows hCols where
  certificate := cols 0 ≤ rows 0 ∧ rows 0 < cols 3 ∧ cols 3 ≤ rows 3
  proof := ⟨hLeft, hGap, hRight⟩
  nonneg := by
    intro hBand hContig
    exact hDet rows cols hRows hCols hBand.1 hBand.2.1 hBand.2.2 hContig

/-- The determinant inequality target implies the banded mixed-support
certificate target. -/
theorem xiMinorFourBandedMixedSupportCertificates_of_detInequality
    (hDet : XiMinorFourBandedDetInequalityFromContig) :
    XiMinorFourBandedMixedSupportCertificates := by
  intro rows cols hRows hCols hLeft hGap hRight
  exact ⟨xiMinorFourBandedDetCertificate
    hDet rows cols hRows hCols hLeft hGap hRight⟩

/-- The banded `4 × 4` mixed-support target implies the broader mixed-support
target for monotone `4 × 4` patterns. -/
theorem xiMinorFourMixedSupportCertificates_of_banded
    (hBand : XiMinorFourBandedMixedSupportCertificates) :
    XiMinorFourMixedSupportCertificates := by
  intro rows cols hRows hCols hNoZeroRow hNoZeroCol hNotFull
  have hCols01 : cols 0 < cols 1 := hCols (by decide : (0 : Fin 4) < 1)
  have hCols12 : cols 1 < cols 2 := hCols (by decide : (1 : Fin 4) < 2)
  have hCols23 : cols 2 < cols 3 := hCols (by decide : (2 : Fin 4) < 3)
  have hRows01 : rows 0 < rows 1 := hRows (by decide : (0 : Fin 4) < 1)
  have hRows12 : rows 1 < rows 2 := hRows (by decide : (1 : Fin 4) < 2)
  have hRows23 : rows 2 < rows 3 := hRows (by decide : (2 : Fin 4) < 3)
  have hCols03 : cols 0 < cols 3 := lt_trans hCols01 (lt_trans hCols12 hCols23)
  have hRows03 : rows 0 < rows 3 := lt_trans hRows01 (lt_trans hRows12 hRows23)
  have hLeft : cols 0 ≤ rows 0 := by
    by_contra h
    have hlt : rows 0 < cols 0 := Nat.lt_of_not_ge h
    apply hNoZeroRow
    refine ⟨0, ?_⟩
    intro b
    fin_cases b
    · exact hlt
    · exact lt_trans hlt hCols01
    · exact lt_trans hlt (lt_trans hCols01 hCols12)
    · exact lt_trans hlt hCols03
  have hRight : cols 3 ≤ rows 3 := by
    by_contra h
    have hlt : rows 3 < cols 3 := Nat.lt_of_not_ge h
    apply hNoZeroCol
    refine ⟨3, ?_⟩
    intro a
    fin_cases a
    · exact lt_trans hRows03 hlt
    · exact lt_trans (lt_trans hRows12 hRows23) hlt
    · exact lt_trans hRows23 hlt
    · exact hlt
  have hGap : rows 0 < cols 3 := by
    by_contra h
    have h03 : cols 3 ≤ rows 0 := Nat.le_of_not_gt h
    apply hNotFull
    intro a b
    have hcb : cols b ≤ cols 3 := by
      fin_cases b
      · exact le_of_lt hCols03
      · exact le_of_lt (lt_trans hCols12 hCols23)
      · exact le_of_lt hCols23
      · exact le_rfl
    have hra : rows 0 ≤ rows a := by
      fin_cases a
      · exact le_rfl
      · exact le_of_lt hRows01
      · exact le_of_lt (lt_trans hRows01 hRows12)
      · exact le_of_lt hRows03
    exact le_trans (le_trans hcb h03) hra
  exact hBand rows cols hRows hCols hLeft hGap hRight

/-- Full-support plus mixed-support certificates close the `4 × 4`
certificate rung. -/
theorem xiMinorFourContigCertificates_of_full_and_mixed
    (hFull : XiMinorFourFullSupportFromContig)
    (hMixed : XiMinorFourMixedSupportCertificates) :
    XiMinorFourContigCertificates := by
  intro rows cols hRows hCols
  by_cases hZeroRow : ∃ a : Fin 4, ∀ b : Fin 4, rows a < cols b
  · exact exists_xiZeroRowMinorCertificate 4 rows cols hRows hCols hZeroRow
  by_cases hZeroCol : ∃ b : Fin 4, ∀ a : Fin 4, rows a < cols b
  · exact exists_xiZeroColumnMinorCertificate 4 rows cols hRows hCols hZeroCol
  by_cases hSupport : ∀ a b : Fin 4, cols b ≤ rows a
  · exact exists_xiMinorFourFullSupportCertificate hFull rows cols hRows hCols hSupport
  · exact hMixed rows cols hRows hCols hZeroRow hZeroCol hSupport

/-- Tail frontier after the first `4 × 4` tail rung. -/
def XiAllMinorGeFiveContigCertificates : Prop :=
  ∀ (k : ℕ), 5 ≤ k →
    ∀ (rows cols : Fin k → ℕ)
      (hRows : StrictMono rows) (hCols : StrictMono cols),
        Nonempty (XiMinorContigCertificate k rows cols hRows hCols)

/-- A solved `4 × 4` certificate theory plus the `k ≥ 5` tail recovers the
previous `k ≥ 4` tail. -/
theorem xiAllMinorGeFour_of_four_and_geFive
    (hFour : XiMinorFourContigCertificates)
    (hGeFive : XiAllMinorGeFiveContigCertificates) :
    XiAllMinorGeFourContigCertificates := by
  intro k hk rows cols hRows hCols
  by_cases hk4 : k = 4
  · subst k
    exact hFour rows cols hRows hCols
  have hk5 : 5 ≤ k := by omega
  exact hGeFive k hk5 rows cols hRows hCols

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

/-- Kernel representation plus the split full/mixed `3 × 3` frontier and the
`k ≥ 4` tail is enough to produce the full contiguous-to-arbitrary PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullMixed_and_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMixed : XiMinorThreeMixedSupportCertificates)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_three_and_geFour hRep
    (xiMinorThreeContigCertificates_of_full_and_mixed hFull hMixed)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, banded mixed-support
`3 × 3`, and the `k ≥ 4` tail is enough to produce the full PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullBandedMixed_and_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hBanded : XiMinorThreeBandedMixedSupportCertificates)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullMixed_and_geFour
    hRep hFull
    (xiMinorThreeMixedSupportCertificates_of_banded hBanded)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, banded determinant
nonnegativity, and the `k ≥ 4` tail is enough to produce the full PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullBandedDet_and_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hDet : XiMinorThreeBandedDetInequalityFromContig)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullBandedMixed_and_geFour
    hRep hFull
    (xiMinorThreeBandedMixedSupportCertificates_of_detInequality hDet)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, expanded banded
determinant nonnegativity, and the `k ≥ 4` tail is enough to produce the full
PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullBandedExpanded_and_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hExp : XiMinorThreeBandedExpandedInequalityFromContig)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullBandedDet_and_geFour
    hRep hFull
    (xiMinorThreeBandedDetInequality_of_expanded hExp)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, middle-supported moment
control, the remaining band edge cases, and the `k ≥ 4` tail is enough to
produce the full PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_and_edgeCases_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig)
    (hEdge : XiMinorThreeBandedEdgeCaseCertificates)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullBandedExpanded_and_geFour
    hRep hFull
    (xiMinorThreeBandedExpandedInequality_of_middleMoment_and_edgeCases
      hEdge hMoment)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, middle-supported moment
control, the two concrete zero-edge cases, and the `k ≥ 4` tail is enough to
produce the full PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_zeroEdges_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig)
    (hT01 : XiMinorThreeBandedT01ZeroInequalityFromContig)
    (hT12 : XiMinorThreeBandedT12ZeroInequalityFromContig)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_and_edgeCases_geFour
    hRep hFull hMoment
    (xiMinorThreeBandedEdgeCaseCertificates_of_zeroEdges hT01 hT12)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, middle-supported moment
control, simplified zero-edge cases, and the `k ≥ 4` tail is enough to produce
the full PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_simplifiedZeroEdges_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig)
    (hT01 : XiMinorThreeBandedT01ZeroSimplifiedFromContig)
    (hT12 : XiMinorThreeBandedT12ZeroSimplifiedFromContig)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_zeroEdges_geFour
    hRep hFull hMoment
    (xiMinorThreeBandedT01ZeroInequality_of_simplified hT01)
    (xiMinorThreeBandedT12ZeroInequality_of_simplified hT12)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, middle-supported moment
control, bracket zero-edge cases, and the `k ≥ 4` tail is enough to produce the
full PF bridge. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_bracketZeroEdges_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig)
    (hT01 : XiMinorThreeBandedT01ZeroBracketFromContig)
    (hT12 : XiMinorThreeBandedT12ZeroBracketFromContig)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_simplifiedZeroEdges_geFour
    hRep hFull hMoment
    (xiMinorThreeBandedT01ZeroSimplified_of_bracket hT01)
    (xiMinorThreeBandedT12ZeroSimplified_of_bracket hT12)
    hGeFour

/-- Kernel representation plus full-support `3 × 3`, middle-supported moment
control, and the `k ≥ 4` tail is enough to produce the full PF bridge: the
remaining bracket zero-edge cases are already consequences of the kernel
representation through the proved `2 × 2` route. -/
theorem xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_geFour
    (hRep : XiMomentKernelRep)
    (hFull : XiMinorThreeFullSupportFromContig)
    (hMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig)
    (hGeFour : XiAllMinorGeFourContigCertificates) :
    XiContigToFullPFBridge :=
  xiContigToFullPFBridge_of_kernelRep_threeFullMiddleMoment_bracketZeroEdges_geFour
    hRep hFull hMoment
    (xiMinorThreeBandedT01ZeroBracket_of_kernelRep hRep)
    (xiMinorThreeBandedT12ZeroBracket_of_kernelRep hRep)
    hGeFour

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

/-- Two-stage lower-triangular route: first lift contiguous minors to arbitrary
rows with initial consecutive columns, then apply the initial-column criterion
for full PF positivity. -/
structure KernelContigToPFInitialColumnTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  contigToInitialColumns : XiContigToInitialColumnMinorBridge
  initialColumnsToPF : XiInitialColumnMinorToFullPFBridge

/-- Reduced initial-column theorem target: Pólya's kernel already closes
orders at most two, so only arbitrary-row initial-column minors of order at
least three remain. -/
structure KernelContigToPFInitialColumnGeThreeTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  initialColumnsGeThree : XiInitialColumnMinorGeThreeFromContig
  initialColumnsToPF : XiInitialColumnMinorToFullPFBridge

/-- Further reduced initial-column target: order three is supplied separately,
leaving only arbitrary-row initial-column minors of order at least four. -/
structure KernelContigToPFInitialColumnGeFourTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  initialColumnsThree : XiInitialColumnMinorThreeFromContig
  initialColumnsGeFour : XiInitialColumnMinorGeFourFromContig
  initialColumnsToPF : XiInitialColumnMinorToFullPFBridge

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

/-- Split `3 × 3` theorem target: prove full-support and mixed-support `3 × 3`
certificates separately, plus the `k ≥ 4` tail. -/
structure KernelContigToPFThreeSupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMixed : XiMinorThreeMixedSupportCertificates
  geFour : XiAllMinorGeFourContigCertificates

/-- Sharper sparse-support theorem target: replace the broad mixed-support
`3 × 3` condition by the banded mixed-support condition forced by monotone
support. -/
structure KernelContigToPFThreeBandedSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeBanded : XiMinorThreeBandedMixedSupportCertificates
  geFour : XiAllMinorGeFourContigCertificates

/-- Determinant-form sparse-support theorem target: replace the banded
certificate condition by the raw banded `3 × 3` determinant inequality. -/
structure KernelContigToPFThreeBandedDetTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Expanded determinant-form sparse-support theorem target. -/
structure KernelContigToPFThreeBandedExpandedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedExpanded : XiMinorThreeBandedExpandedInequalityFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Middle-supported moment theorem target plus the remaining band edge cases.
-/
structure KernelContigToPFThreeMiddleMomentTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMiddleMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig
  threeBandEdgeCases : XiMinorThreeBandedEdgeCaseCertificates
  geFour : XiAllMinorGeFourContigCertificates

/-- Concrete zero-edge theorem target: split the remaining band edge cases into
`T01 = 0` and `T12 = 0`. -/
structure KernelContigToPFThreeZeroEdgesTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMiddleMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig
  threeT01Zero : XiMinorThreeBandedT01ZeroInequalityFromContig
  threeT12Zero : XiMinorThreeBandedT12ZeroInequalityFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Simplified zero-edge theorem target. -/
structure KernelContigToPFThreeSimplifiedZeroEdgesTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMiddleMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig
  threeT01ZeroSimplified : XiMinorThreeBandedT01ZeroSimplifiedFromContig
  threeT12ZeroSimplified : XiMinorThreeBandedT12ZeroSimplifiedFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Bracket zero-edge theorem target. -/
structure KernelContigToPFThreeBracketZeroEdgesTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMiddleMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig
  threeT01ZeroBracket : XiMinorThreeBandedT01ZeroBracketFromContig
  threeT12ZeroBracket : XiMinorThreeBandedT12ZeroBracketFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Kernel-zero-edge theorem target: after the `2 × 2` route, the concrete
zero-edge bracket cases no longer need to be assumed separately. -/
structure KernelContigToPFThreeKernelZeroEdgesTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMiddleMoment : XiMinorThreeBandedMiddleMomentInequalityFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Compound-ratio theorem target: replace the raw middle-supported `3 × 3`
moment inequality by the ratio-monotonicity condition for adjacent `2 × 2`
compound minors. -/
structure KernelContigToPFThreeCompoundRatioTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFull : XiMinorThreeFullSupportFromContig
  threeMiddleCompoundRatio : XiMinorThreeBandedMiddleCompoundRatioFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Moment-form compound-ratio theorem target: both remaining `3 × 3` payloads
are stated directly in moment-index language. -/
structure KernelContigToPFThreeMomentCompoundRatioTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeFullMoment : XiMinorThreeFullSupportMomentFromContig
  threeMiddleCompoundRatio : XiMinorThreeBandedMiddleCompoundRatioFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Unified moment-payload theorem target: the two explicit `3 × 3`
moment-index conditions are supplied as a single named payload. -/
structure KernelContigToPFThreeMomentPayloadTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeMomentPayload : XiMinorThreeMomentPayloadFromContig
  geFour : XiAllMinorGeFourContigCertificates

/-- Moment-payload plus explicit `4 × 4` rung target: split the remaining tail
into the first concrete `4 × 4` certificate frontier and the `k ≥ 5` tail. -/
structure KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeMomentPayload : XiMinorThreeMomentPayloadFromContig
  four : XiMinorFourContigCertificates
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-split `4 × 4` theorem target after the unified `3 × 3` moment
payload. -/
structure KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeMomentPayload : XiMinorThreeMomentPayloadFromContig
  fourFull : XiMinorFourFullSupportFromContig
  fourMixed : XiMinorFourMixedSupportCertificates
  geFive : XiAllMinorGeFiveContigCertificates

/-- Moment-form support-split `4 × 4` theorem target. -/
structure KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  threeMomentPayload : XiMinorThreeMomentPayloadFromContig
  fourFullMoment : XiMinorFourFullSupportMomentFromContig
  fourMixed : XiMinorFourMixedSupportCertificates
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment-payload theorem target: package the `3 × 3` moment payload
and the full-support `4 × 4` moment target into one condition. -/
structure KernelContigToPFLowRankMomentFourMixedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourMixed : XiMinorFourMixedSupportCertificates
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus banded `4 × 4` mixed-support theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedMixedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedMixed : XiMinorFourBandedMixedSupportCertificates
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus determinant-form banded `4 × 4` mixed-support
theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedDetTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedDet : XiMinorFourBandedDetInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus upper-right-zero determinant-form banded
`4 × 4` mixed-support theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedUpperRightZero :
    XiMinorFourBandedUpperRightZeroDetInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus row-zero cofactor-form banded `4 × 4`
mixed-support theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedRowZeroCofactor :
    XiMinorFourBandedRowZeroCofactorInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus three-cofactor-form banded `4 × 4`
mixed-support theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedThreeCofactor :
    XiMinorFourBandedThreeCofactorInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus named-cofactor-matrix banded `4 × 4`
mixed-support theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedNamedCofactor :
    XiMinorFourBandedNamedCofactorInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus row/column-selector cofactor theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  fourBandedCofactorRowCol :
    XiMinorFourBandedCofactorRowColInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus support-class split cofactor theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorSupportSplit :
    XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  cofactorSupportClasses : XiMinorFourBandedCofactorSupportClassesFromBand
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus individual `j = 0, 1, 2` cofactor
support-class theorem target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorSupportSplit :
    XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  cofactorJ0 : XiMinorFourBandedCofactorJ0SupportClassFromBand
  cofactorJ1 : XiMinorFourBandedCofactorJ1SupportClassFromBand
  cofactorJ2 : XiMinorFourBandedCofactorJ2SupportClassFromBand
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the remaining `j = 1, 2` cofactor
support-class theorem target; the `j = 0` classification is already proved. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorSupportSplit :
    XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  cofactorJ1 : XiMinorFourBandedCofactorJ1SupportClassFromBand
  cofactorJ2 : XiMinorFourBandedCofactorJ2SupportClassFromBand
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the remaining `j = 2` cofactor support-class
theorem target; the `j = 0` and `j = 1` classifications are already proved. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ2Theorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorSupportSplit :
    XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  cofactorJ2 : XiMinorFourBandedCofactorJ2SupportClassFromBand
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the cofactor support-split theorem target;
all three individual cofactor support classifications are now proved. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorSupportSplit :
    XiMinorFourBandedCofactorSupportSplitInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the finite cofactor support-kind case table;
the case table implies the cofactor support-split target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorCaseTable :
    XiMinorFourBandedCofactorSupportCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the reduced nonzero-survivor cofactor
case-table target; all-structural-zero rows are already proved. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorNonzeroCaseTable :
    XiMinorFourBandedCofactorNonzeroCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the one-survivor/multi-survivor split cofactor
case-table targets. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorOneSurvivor :
    XiMinorFourBandedCofactorOneSurvivorCaseTableInequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the position-specific one-survivor targets and
the multi-survivor cofactor case-table target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorOneSurvivorJ0 :
    XiMinorFourBandedCofactorOneSurvivorJ0InequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorOneSurvivorJ2 :
    XiMinorFourBandedCofactorOneSurvivorJ2InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the positive-side one-survivor target, the
signed-negative `j = 1` one-survivor target, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorPositiveOneSurvivor :
    XiMinorFourBandedCofactorPositiveOneSurvivorInequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the full/banded positive one-survivor
subcases, the signed-negative `j = 1` one-survivor target, and the
multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorJ0Full :
    XiMinorFourBandedCofactorOneSurvivorJ0FullInequalityFromContig
  cofactorJ0Banded :
    XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig
  cofactorJ2Full :
    XiMinorFourBandedCofactorOneSurvivorJ2FullInequalityFromContig
  cofactorJ2Banded :
    XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus a bundled full-support positive one-survivor
target, the two banded positive side targets, the signed-negative `j = 1`
one-survivor target, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorPositiveFull :
    XiMinorFourBandedCofactorPositiveFullOneSurvivorInequalityFromContig
  cofactorJ0Banded :
    XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig
  cofactorJ2Banded :
    XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus determinant-level positive full-support side
cofactor control, the two banded positive side targets, the signed-negative
`j = 1` one-survivor target, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  cofactorPositiveFullDet :
    XiMinorFourBandedCofactorPositiveFullDetFromContig
  cofactorJ0Banded :
    XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig
  cofactorJ2Banded :
    XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the already named full-support `3 × 3`
frontier, the two banded positive side targets, the signed-negative `j = 1`
one-survivor target, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  cofactorJ0Banded :
    XiMinorFourBandedCofactorOneSurvivorJ0BandedInequalityFromContig
  cofactorJ2Banded :
    XiMinorFourBandedCofactorOneSurvivorJ2BandedInequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus the full-support `3 × 3` frontier, the
banded `3 × 3` determinant frontier for the positive side cofactors, the
signed-negative `j = 1` one-survivor target, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorOneSurvivorJ1 :
    XiMinorFourBandedCofactorOneSurvivorJ1InequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the explicit nonpositive middle-determinant target for the signed-negative
`j = 1` one-survivor case, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1Nonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1NonposDetFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the full/banded support split for the signed-negative middle determinant, and
the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1SupportNonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1SupportNonposDetFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the moment-index full-support middle determinant obstruction, the banded middle
determinant obstruction, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentNonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDetFromContig
  cofactorJ1BandedNonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
banded middle determinant obstruction, and the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedNonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDetFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
expanded banded middle determinant obstruction, and the multi-survivor target.
-/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedExpandedNonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonposFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
product-dominance form of the expanded banded middle obstruction, and the
multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedProductDominance :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominanceFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
bracket-sign form of the banded middle obstruction, and the multi-survivor
target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedBracketSigns :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSignsFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
separate left/right bracket-sign targets for the banded middle obstruction, and
the multi-survivor target. -/
structure KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedLeftBracketNonpos :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedLeftBracketNonposFromContig
  cofactorJ1BandedRightBracketNonneg :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedRightBracketNonnegFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
top-supported/top-unsupported split for the banded middle brackets, and the
multi-survivor target. -/
structure
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedTopSupported :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBracketsFromContig
  cofactorJ1BandedTopUnsupported :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
moment-gap top-supported branch for the banded middle brackets, the
top-unsupported branch, and the multi-survivor target. -/
structure
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedTopSupportedMoment :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig
  cofactorJ1BandedTopUnsupported :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBracketsFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
moment-gap top-supported branch, the middle-supported part of the
top-unsupported branch, and the multi-survivor target. -/
structure
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem
    where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedTopSupportedMoment :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig
  cofactorJ1BandedTopUnsupportedMiddleSupported :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedMiddleSupportedBracketsFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
moment-gap top-supported branch, the moment-product form of the
top-unsupported middle-supported branch, and the multi-survivor target. -/
structure
    KernelContigToPFJ1TopMomentMiddleProductTheorem
    where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedTopSupportedMoment :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig
  cofactorJ1BandedTopUnsupportedMiddleSupportedMomentProduct :
    XiJ1TopUnsupportedMiddleSupportedMomentProductFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, the
moment-gap top-supported branch, and the multi-survivor target.

The top-unsupported banded middle branch is now discharged by support
bookkeeping alone. -/
structure KernelContigToPFJ1TopMomentSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorJ1BandedTopSupportedMoment :
    XiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedMomentBracketsFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the zero-determinant moment condition for the full-support middle cofactor, and
the multi-survivor target.

Both top branches of the banded middle cofactor are now discharged by support
bookkeeping alone. -/
structure KernelContigToPFJ1SupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorJ1FullMomentZero :
    XiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDetFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers
and the multi-survivor target.

All signed-negative `j = 1` one-survivor middle-cofactor support cases are now
discharged by support bookkeeping alone. -/
structure KernelContigToPFJ1StructuralSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiSurvivor :
    XiMinorFourBandedCofactorMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the reduced multi-survivor support-kind classification and reduced case table.

This is the current sharp cofactor frontier: one-survivor `j = 1` rows are
structural, and multi-survivor rows are reduced to three support-kind triples. -/
structure KernelContigToPFJ1StructuralReducedMultiTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiKindReduction :
    XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport
  cofactorReducedMultiSurvivor :
    XiMinorFourBandedCofactorReducedMultiSurvivorCaseTableInequalityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the reduced multi-survivor support-kind classification, and the three explicit
reduced multi-survivor rows. -/
structure KernelContigToPFJ1StructuralReducedRowsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiKindReduction :
    XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport
  cofactorReducedMultiRows :
    XiMinorFourBandedCofactorReducedMultiRowsFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the reduced multi-survivor support-kind classification, and the sharper
two-term form of the `zeroRow, banded, banded` row. -/
structure KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiKindReduction :
    XiMinorFourBandedCofactorMultiSurvivorKindReductionFromSupport
  cofactorReducedMultiRowsTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the active-pair split of the multi-survivor support-kind classification, and
the sharper two-term form of the `zeroRow, banded, banded` row. -/
structure KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiPairKindReduction :
    XiMinorFourBandedCofactorMultiSurvivorPairKindReductionFromSupport
  cofactorReducedMultiRowsTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
the active-pair split with pair-`12` reduced to active-kind cases, and the
sharper two-term form of the `zeroRow, banded, banded` row. -/
structure KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiPair12CasesKindReduction :
    XiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReductionFromSupport
  cofactorReducedMultiRowsTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
with pair-`12` discharged structurally, leaving only pair-`01` and pair-`02`
support-kind reductions for the multi-survivor support classification. -/
structure KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiPair01Pair02KindReduction :
    XiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReductionFromSupport
  cofactorReducedMultiRowsTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
with pair-`02` and pair-`12` discharged structurally, leaving only pair-`01`
support-kind reduction for the multi-survivor support classification. -/
structure KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorMultiPair01KindReduction :
    XiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReductionFromSupport
  cofactorReducedMultiRowsTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Low-rank moment payload plus full-support and banded `3 × 3` frontiers,
with multi-survivor support-kind classification fully discharged, leaving only
the reduced multi-survivor row inequalities. -/
structure KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target with the reduced rows split into the all-full
row and the sparse two-term row package. -/
structure KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsFullSparseTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target with the all-full row replaced by its
dominance form and the sparse two-term row package left explicit. -/
structure KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsFullDominanceSparseTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target with both all-full and all-banded sparse rows
replaced by their dominance forms, leaving the zero-row two-term target
explicit. -/
structure KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm :
    XiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTermFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target with all three reduced multi-survivor rows
replaced by exact cofactor dominance inequalities. -/
structure KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsAllDominance :
    XiMinorFourBandedCofactorReducedMultiRowsAllDominanceFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the three reduced multi-survivor rows
are instances of one support-parametrized dominance predicate. -/
structure KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsUniformDominance :
    XiMinorFourBandedCofactorReducedMultiRowsUniformDominanceFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the reduced multi-survivor rows follow
from one pure row-geometry dominance condition. -/
structure KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsRowGeometryDominance :
    XiMinorFourBandedCofactorReducedMultiRowsRowGeometryDominanceFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the reduced multi-survivor rows follow
from the bare middle-cofactor dominance inequality. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominance :
    XiMinorFourBandedCofactorMiddleDominanceFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the bare middle-cofactor dominance
inequality is supplied in side-positive plus middle-upper-bound form. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceSideBound :
    XiMinorFourBandedCofactorMiddleDominanceSideBoundFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the side nonnegativity and middle
upper-bound estimates are supplied as separate conditions. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceSeparatedBounds :
    XiMinorFourBandedCofactorMiddleDominanceSeparatedBoundsFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the side determinant estimates and
middle upper-bound estimate are supplied separately. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceDetSideAndMiddle :
    XiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddleFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the left and right side determinant
estimates are supplied separately from the middle upper-bound estimate. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceSplitSideDetAndMiddle :
    XiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddleFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-free theorem target where the side determinant signs are reduced
to side-support classification plus the middle upper-bound estimate. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceSupportSideAndMiddle :
    XiMinorFourBandedCofactorMiddleDominanceSupportSideAndMiddleFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Support-free theorem target where side determinants are controlled by the
proved support-class classification, leaving the middle upper-bound estimate as
the only new cofactor-dominance input. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceSupportClassSideAndMiddle :
    XiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddleFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Middle-only theorem target for the reduced multi-row cofactor frontier.

At this point the side cofactor support classes are proved from geometry and
their determinant signs follow from the existing `3 × 3` fields, so the only
remaining cofactor-dominance input is the middle upper-bound estimate. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominanceMiddleUpperBound :
    XiMinorFourBandedCofactorMiddleDominanceMiddleUpperBoundFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Cancellation-aware theorem target where only the positive-middle-
determinant branch remains as a new cofactor input. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetCancellation :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellationFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Combinatorial side-allocation theorem target for the positive-middle-
determinant cancellation branch. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetSideAllocation :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocationFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Compound-minor theorem target where geometric-mean domination closes the
positive-middle cofactor branch. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMeanTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetGeometricMean :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMeanFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Factorized log-convexity theorem target for the positive-middle cofactor
branch. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexityTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexity :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetFactorizedLogConvexityFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Support-aware theorem target: left dominance handles the top-right-zero
branch, while geometric-mean domination handles the top-right-supported branch. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplitFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Three-way support theorem target: only the interval with supported `A01`
and zero `A02` retains a one-sided left-dominance input. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplitFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Moment/cofactor-ratio theorem target for the three-way top-row support
decomposition. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Subtraction-free contiguous-minor certificate theorem target for the
three-way top-row support decomposition. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Normalized moment/cofactor-ratio theorem target for the three-way top-row
support decomposition.  This stronger frontier target adds positivity of the
left cofactor so that the active comparison is a genuine quotient inequality. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit :
    XiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Middle-determinant-sign theorem target for the reduced multi-row cofactor
frontier.  The middle upper-bound estimate follows if the middle `C1`
cofactor determinant is always nonpositive. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDetNonpositive :
    XiMinorFourBandedCofactorMiddleDetNonpositiveFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Support-split middle determinant-sign theorem target. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleDetSupportSplit :
    XiMinorFourBandedCofactorMiddleDetSupportSplitNonpositiveFromContig
  geFive : XiAllMinorGeFiveContigCertificates

/-- Middle determinant-sign theorem target with the full-support branch
sharpened to determinant zero. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullZeroBandedNonpositive :
    XiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositiveFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates and the banded branch kept as determinant nonpositivity. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedNonpositive :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositiveFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates and the banded branch expanded into sparse determinant
coordinates. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedExpanded :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpandedFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates and the banded branch as product dominance. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedProduct :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProductFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates and the banded branch as bracket signs. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedBracketSigns :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSignsFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates and the banded branch split into left/right brackets. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedSplitBrackets :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBracketsFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates and the banded branch split by top support. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopSupportSplitBrackets :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBracketsFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target with the full-support branch in
moment coordinates, the top-supported banded branch in moment coordinates, and
the top-unsupported branch in Toeplitz coordinates. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopSupportedMoment :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMomentFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the top-unsupported banded
branch is reduced to its middle-supported subcase. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupported :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the remaining top-unsupported,
middle-supported branch is in moment-product coordinates. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the remaining top-unsupported,
middle-supported branch is split into left/right moment products. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where only the left product remains,
because the right product follows from contiguous `1 x 1` moment
nonnegativity. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final product sign is
reduced to vanishing of one left-product moment factor. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to structural impossibility from support inequalities. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleFromSupport
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to a contextual gap-collapse inequality. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to original-index gap collapse, `cols 3 ≤ rows 2`. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to inactive side-support witnesses. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to a right-side inactive support witness. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to excluding the two active right-side support cases. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final branch is reduced
to excluding the right-side banded support case. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final
top-unsupported/middle-supported branch is required to be empty. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final top-unsupported
branch is closed by forcing the middle column to be unsupported. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final top-unsupported
branch is closed by ruling out the middle/top-column straddle interval. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final top-unsupported
branch is closed by contradicting the middle/top-column straddle interval. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleFromContext
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final straddle branch is
reduced to a nonpositive left moment-product estimate. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductFromContig
  geFive : XiAllMinorGeFiveContigCertificates

set_option linter.style.longLine false in
/-- Middle determinant-sign theorem target where the final straddle branch is
reduced to a native Toeplitz left-bracket nonpositivity estimate. -/
structure KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem where
  M : ℕ → ℝ
  positive : ∀ n, 0 < M n
  kernelRep : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ))
  contig : KernelContigTotalPositive M
  lowRankMomentPayload : XiLowRankMomentPayloadFromContig
  threeFull : XiMinorThreeFullSupportFromContig
  threeBandedDet : XiMinorThreeBandedDetInequalityFromContig
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket :
    XiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketFromContig
  geFive : XiAllMinorGeFiveContigCertificates

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

/-- The full/mixed `3 × 3` split target produces the previous `3 × 3` target. -/
def kernelContigToPFThreeAndGeFour_of_threeSupportSplit
    (T : KernelContigToPFThreeSupportSplitTheorem) :
    KernelContigToPFThreeAndGeFourTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  three :=
    xiMinorThreeContigCertificates_of_full_and_mixed
      T.threeFull T.threeMixed
  geFour := T.geFour

/-- The banded-support `3 × 3` target produces the broader support-split
target. -/
def kernelContigToPFThreeSupportSplit_of_bandedSupport
    (T : KernelContigToPFThreeBandedSupportTheorem) :
    KernelContigToPFThreeSupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeMixed := xiMinorThreeMixedSupportCertificates_of_banded T.threeBanded
  geFour := T.geFour

/-- The banded determinant target produces the banded-support target. -/
def kernelContigToPFThreeBandedSupport_of_bandedDet
    (T : KernelContigToPFThreeBandedDetTheorem) :
    KernelContigToPFThreeBandedSupportTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeBanded :=
    xiMinorThreeBandedMixedSupportCertificates_of_detInequality
      T.threeBandedDet
  geFour := T.geFour

/-- The expanded determinant target produces the determinant target. -/
def kernelContigToPFThreeBandedDet_of_expanded
    (T : KernelContigToPFThreeBandedExpandedTheorem) :
    KernelContigToPFThreeBandedDetTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeBandedDet :=
    xiMinorThreeBandedDetInequality_of_expanded
      T.threeBandedExpanded
  geFour := T.geFour

/-- The middle-supported moment target plus edge cases produces the expanded
determinant target. -/
def kernelContigToPFThreeBandedExpanded_of_middleMoment
    (T : KernelContigToPFThreeMiddleMomentTheorem) :
    KernelContigToPFThreeBandedExpandedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeBandedExpanded :=
    xiMinorThreeBandedExpandedInequality_of_middleMoment_and_edgeCases
      T.threeBandEdgeCases T.threeMiddleMoment
  geFour := T.geFour

/-- The concrete zero-edge target produces the middle-moment target with an
edge-case bridge. -/
def kernelContigToPFThreeMiddleMoment_of_zeroEdges
    (T : KernelContigToPFThreeZeroEdgesTheorem) :
    KernelContigToPFThreeMiddleMomentTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeMiddleMoment := T.threeMiddleMoment
  threeBandEdgeCases :=
    xiMinorThreeBandedEdgeCaseCertificates_of_zeroEdges
      T.threeT01Zero T.threeT12Zero
  geFour := T.geFour

/-- The simplified zero-edge target produces the concrete zero-edge target. -/
def kernelContigToPFThreeZeroEdges_of_simplified
    (T : KernelContigToPFThreeSimplifiedZeroEdgesTheorem) :
    KernelContigToPFThreeZeroEdgesTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeMiddleMoment := T.threeMiddleMoment
  threeT01Zero :=
    xiMinorThreeBandedT01ZeroInequality_of_simplified
      T.threeT01ZeroSimplified
  threeT12Zero :=
    xiMinorThreeBandedT12ZeroInequality_of_simplified
      T.threeT12ZeroSimplified
  geFour := T.geFour

/-- The bracket zero-edge target produces the simplified zero-edge target. -/
def kernelContigToPFThreeSimplifiedZeroEdges_of_bracketZeroEdges
    (T : KernelContigToPFThreeBracketZeroEdgesTheorem) :
    KernelContigToPFThreeSimplifiedZeroEdgesTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeMiddleMoment := T.threeMiddleMoment
  threeT01ZeroSimplified :=
    xiMinorThreeBandedT01ZeroSimplified_of_bracket
      T.threeT01ZeroBracket
  threeT12ZeroSimplified :=
    xiMinorThreeBandedT12ZeroSimplified_of_bracket
      T.threeT12ZeroBracket
  geFour := T.geFour

/-- The kernel-zero-edge target produces the bracket zero-edge target by using
the kernel representation to discharge both bracket cases. -/
def kernelContigToPFThreeBracketZeroEdges_of_kernelZeroEdges
    (T : KernelContigToPFThreeKernelZeroEdgesTheorem) :
    KernelContigToPFThreeBracketZeroEdgesTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeMiddleMoment := T.threeMiddleMoment
  threeT01ZeroBracket :=
    xiMinorThreeBandedT01ZeroBracket_of_kernelRep
      ⟨T.M, T.positive, T.kernelRep⟩
  threeT12ZeroBracket :=
    xiMinorThreeBandedT12ZeroBracket_of_kernelRep
      ⟨T.M, T.positive, T.kernelRep⟩
  geFour := T.geFour

/-- The compound-ratio target produces the kernel-zero-edge target by turning
compound-ratio monotonicity into the middle-supported moment inequality. -/
def kernelContigToPFThreeKernelZeroEdges_of_compoundRatio
    (T : KernelContigToPFThreeCompoundRatioTheorem) :
    KernelContigToPFThreeKernelZeroEdgesTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull := T.threeFull
  threeMiddleMoment :=
    xiMinorThreeBandedMiddleMoment_of_compoundRatio
      T.threeMiddleCompoundRatio
  geFour := T.geFour

/-- The moment-form compound-ratio target produces the compound-ratio target by
rewriting full-support Toeplitz entries to moment coefficients. -/
def kernelContigToPFThreeCompoundRatio_of_momentCompoundRatio
    (T : KernelContigToPFThreeMomentCompoundRatioTheorem) :
    KernelContigToPFThreeCompoundRatioTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFull :=
    xiMinorThreeFullSupportFromContig_of_moment
      T.threeFullMoment
  threeMiddleCompoundRatio := T.threeMiddleCompoundRatio
  geFour := T.geFour

/-- The unified moment-payload target produces the moment-form compound-ratio
target by unpacking the two `3 × 3` moment conditions. -/
def kernelContigToPFThreeMomentCompoundRatio_of_momentPayload
    (T : KernelContigToPFThreeMomentPayloadTheorem) :
    KernelContigToPFThreeMomentCompoundRatioTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeFullMoment :=
    xiMinorThreeFullSupportMoment_of_momentPayload
      T.threeMomentPayload
  threeMiddleCompoundRatio :=
    xiMinorThreeBandedMiddleCompoundRatio_of_momentPayload
      T.threeMomentPayload
  geFour := T.geFour

/-- The explicit `4 × 4` plus `k ≥ 5` target produces the previous
moment-payload target by rebuilding the `k ≥ 4` tail. -/
def kernelContigToPFThreeMomentPayload_of_four_and_geFive
    (T : KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem) :
    KernelContigToPFThreeMomentPayloadTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeMomentPayload := T.threeMomentPayload
  geFour := xiAllMinorGeFour_of_four_and_geFive T.four T.geFive

/-- The support-split `4 × 4` target produces the explicit `4 × 4` rung
target. -/
def kernelContigToPFThreeMomentPayloadFourAndGeFive_of_fourSupportSplit
    (T : KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem) :
    KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeMomentPayload := T.threeMomentPayload
  four :=
    xiMinorFourContigCertificates_of_full_and_mixed
      T.fourFull T.fourMixed
  geFive := T.geFive

/-- The moment-form `4 × 4` support-split target produces the Toeplitz-entry
support-split target by rewriting full-support entries to moment coefficients.
-/
def kernelContigToPFThreeMomentPayloadFourSupportSplit_of_fourMomentSupportSplit
    (T : KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem) :
    KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeMomentPayload := T.threeMomentPayload
  fourFull :=
    xiMinorFourFullSupportFromContig_of_moment
      T.fourFullMoment
  fourMixed := T.fourMixed
  geFive := T.geFive

/-- The low-rank moment payload target produces the previous moment-form
`4 × 4` support split target by unpacking the low-rank moment condition. -/
def kernelContigToPFThreeMomentPayloadFourMomentSupportSplit_of_lowRankMoment
    (T : KernelContigToPFLowRankMomentFourMixedTheorem) :
    KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  threeMomentPayload :=
    xiMinorThreeMomentPayload_of_lowRankMomentPayload
      T.lowRankMomentPayload
  fourFullMoment :=
    xiMinorFourFullSupportMoment_of_lowRankMomentPayload
      T.lowRankMomentPayload
  fourMixed := T.fourMixed
  geFive := T.geFive

/-- The banded `4 × 4` mixed-support target produces the broader mixed-support
target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourMixed_of_bandedMixed
    (T : KernelContigToPFLowRankMomentFourBandedMixedTheorem) :
    KernelContigToPFLowRankMomentFourMixedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourMixed :=
    xiMinorFourMixedSupportCertificates_of_banded
      T.fourBandedMixed
  geFive := T.geFive

/-- The determinant-form banded `4 × 4` target produces the banded
mixed-support target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedMixed_of_bandedDet
    (T : KernelContigToPFLowRankMomentFourBandedDetTheorem) :
    KernelContigToPFLowRankMomentFourBandedMixedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedMixed :=
    xiMinorFourBandedMixedSupportCertificates_of_detInequality
      T.fourBandedDet
  geFive := T.geFive

/-- The upper-right-zero determinant-form banded `4 × 4` target produces the
determinant-form banded target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedDet_of_upperRightZero
    (T : KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem) :
    KernelContigToPFLowRankMomentFourBandedDetTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedDet :=
    xiMinorFourBandedDetInequality_of_upperRightZero
      T.fourBandedUpperRightZero
  geFive := T.geFive

/-- The row-zero cofactor-form banded `4 × 4` target produces the
upper-right-zero determinant-form banded target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedUpperRightZero_of_rowZeroCofactor
    (T : KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem) :
    KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedUpperRightZero :=
    xiMinorFourBandedUpperRightZero_of_rowZeroCofactor
      T.fourBandedRowZeroCofactor
  geFive := T.geFive

/-- The three-cofactor-form banded `4 × 4` target produces the row-zero
cofactor-form banded target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedRowZeroCofactor_of_threeCofactor
    (T : KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem) :
    KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedRowZeroCofactor :=
    xiMinorFourBandedRowZeroCofactor_of_threeCofactor
      T.fourBandedThreeCofactor
  geFive := T.geFive

/-- The named-cofactor-matrix banded `4 × 4` target produces the
three-cofactor-form banded target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedThreeCofactor_of_namedCofactor
    (T : KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem) :
    KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedThreeCofactor :=
    xiMinorFourBandedThreeCofactor_of_namedCofactor
      T.fourBandedNamedCofactor
  geFive := T.geFive

/-- The row/column-selector cofactor target produces the named-cofactor target
in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedNamedCofactor_of_rowCol
    (T : KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem) :
    KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedNamedCofactor :=
    xiMinorFourBandedNamedCofactor_of_rowCol
      T.fourBandedCofactorRowCol
  geFive := T.geFive

/-- The support-class split cofactor target produces the row/column-selector
cofactor target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedCofactorRowCol_of_supportSplit
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  fourBandedCofactorRowCol :=
    xiMinorFourBandedCofactorRowCol_of_supportSplit
      T.cofactorSupportSplit T.cofactorSupportClasses
  geFive := T.geFive

/-- The individual `j = 0, 1, 2` cofactor classifications produce the combined
support-class split target in the low-rank moment route. -/
def kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit_of_j012
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorSupportSplit := T.cofactorSupportSplit
  cofactorSupportClasses :=
    xiMinorFourBandedCofactorSupportClasses_of_j012
      T.cofactorJ0 T.cofactorJ1 T.cofactorJ2
  geFive := T.geFive

/-- The remaining `j = 1, 2` cofactor classifications produce the individual
`j = 0, 1, 2` target, since `j = 0` is already classified. -/
def kernelContigToPFLowRankMomentFourBandedCofactorJ012_of_j12
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorSupportSplit := T.cofactorSupportSplit
  cofactorJ0 := xiMinorFourBandedCofactorJ0SupportClass_fromBand
  cofactorJ1 := T.cofactorJ1
  cofactorJ2 := T.cofactorJ2
  geFive := T.geFive

/-- The remaining `j = 2` cofactor classification produces the `j = 1, 2`
target, since `j = 1` is already classified. -/
def kernelContigToPFLowRankMomentFourBandedCofactorJ12_of_j2
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ2Theorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorSupportSplit := T.cofactorSupportSplit
  cofactorJ1 := xiMinorFourBandedCofactorJ1SupportClass_fromBand
  cofactorJ2 := T.cofactorJ2
  geFive := T.geFive

/-- The cofactor support-split-only target produces the previous `j = 2`
target, since `j = 2` is now classified. -/
def kernelContigToPFLowRankMomentFourBandedCofactorJ2_of_supportSplitOnly
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ2Theorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorSupportSplit := T.cofactorSupportSplit
  cofactorJ2 := xiMinorFourBandedCofactorJ2SupportClass_fromBand
  geFive := T.geFive

/-- The cofactor support-kind case-table target produces the support-split-only
target. -/
def kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly_of_caseTable
    (T : KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorSupportSplit :=
    xiMinorFourBandedCofactorSupportSplit_of_caseTable T.cofactorCaseTable
  geFive := T.geFive

/-- The reduced nonzero-survivor case-table target produces the full case-table
target because all-zero-kind rows have already been discharged. -/
def kernelContigToPFLowRankMomentFourBandedCofactorCaseTable_of_nonzeroCaseTable
    (T : KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorCaseTable :=
    xiMinorFourBandedCofactorCaseTable_of_nonzeroCaseTable
      T.cofactorNonzeroCaseTable
  geFive := T.geFive

/-- The survivor-split case-table target produces the reduced nonzero-survivor
case-table target. -/
def kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable_of_survivorSplit
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorNonzeroCaseTable :=
    xiMinorFourBandedCofactorNonzeroCaseTable_of_survivorSplit
      T.cofactorOneSurvivor T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The position-specific one-survivor targets produce the survivor-split
case-table target. -/
def kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit_of_oneSurvivorPosition
    (T : KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorOneSurvivor :=
    xiMinorFourBandedCofactorOneSurvivorCaseTable_of_j012
      T.cofactorOneSurvivorJ0 T.cofactorOneSurvivorJ1 T.cofactorOneSurvivorJ2
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The positive-side one-survivor theorem produces the position-specific
one-survivor theorem. -/
def kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition_of_positiveOneSurvivor
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorOneSurvivorJ0 := T.cofactorPositiveOneSurvivor.1
  cofactorOneSurvivorJ1 := T.cofactorOneSurvivorJ1
  cofactorOneSurvivorJ2 := T.cofactorPositiveOneSurvivor.2
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The full/banded positive one-survivor support theorem produces the
positive-side one-survivor theorem. -/
def kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor_of_support
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorPositiveOneSurvivor :=
    xiMinorFourBandedCofactorPositiveOneSurvivor_of_full_banded
      T.cofactorJ0Full T.cofactorJ0Banded T.cofactorJ2Full T.cofactorJ2Banded
  cofactorOneSurvivorJ1 := T.cofactorOneSurvivorJ1
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The positive full-support bundle theorem produces the full/banded positive
support theorem. -/
def kernelContigToPFCofactorPositiveSupport_of_positiveFull
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorJ0Full := T.cofactorPositiveFull.1
  cofactorJ0Banded := T.cofactorJ0Banded
  cofactorJ2Full := T.cofactorPositiveFull.2
  cofactorJ2Banded := T.cofactorJ2Banded
  cofactorOneSurvivorJ1 := T.cofactorOneSurvivorJ1
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The determinant-level positive full-support theorem produces the bundled
positive full-support theorem. -/
def kernelContigToPFCofactorPositiveFull_of_det
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorPositiveFull :=
    xiMinorFourBandedCofactorPositiveFullOneSurvivor_of_det
      T.cofactorPositiveFullDet
  cofactorJ0Banded := T.cofactorJ0Banded
  cofactorJ2Banded := T.cofactorJ2Banded
  cofactorOneSurvivorJ1 := T.cofactorOneSurvivorJ1
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The full-support `3 × 3` cofactor theorem produces the determinant-level
positive full-support theorem. -/
def kernelContigToPFCofactorPositiveFullDet_of_threeFull
    (T : KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  cofactorPositiveFullDet :=
    xiMinorFourBandedCofactorPositiveFullDet_of_threeFull T.threeFull
  cofactorJ0Banded := T.cofactorJ0Banded
  cofactorJ2Banded := T.cofactorJ2Banded
  cofactorOneSurvivorJ1 := T.cofactorOneSurvivorJ1
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The full-support and banded `3 × 3` theorem produces the previous
positive-side cofactor theorem. -/
def kernelContigToPFCofactorThreeFull_of_threeFullBanded
    (T : KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  cofactorJ0Banded :=
    (xiMinorFourBandedCofactorPositiveBandedOneSurvivor_of_threeBandedDet
      T.threeBandedDet).1
  cofactorJ2Banded :=
    (xiMinorFourBandedCofactorPositiveBandedOneSurvivor_of_threeBandedDet
      T.threeBandedDet).2
  cofactorOneSurvivorJ1 := T.cofactorOneSurvivorJ1
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The explicit nonpositive middle-determinant theorem produces the previous
full-support and banded `3 × 3` cofactor theorem. -/
def kernelContigToPFCofactorThreeFullBanded_of_j1Nonpos
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorOneSurvivorJ1 :=
    xiMinorFourBandedCofactorOneSurvivorJ1_of_nonposDet
      T.cofactorJ1Nonpos
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The support-split middle determinant theorem produces the previous
nonpositive middle determinant theorem. -/
def kernelContigToPFCofactorJ1Nonpos_of_supportSplit
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1Nonpos :=
    xiMinorFourBandedCofactorOneSurvivorJ1NonposDet_of_supportSplit
      T.cofactorJ1SupportNonpos
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The moment-index full-support middle determinant theorem produces the
support-split middle determinant theorem. -/
def kernelContigToPFCofactorJ1SupportSplit_of_fullMoment
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1SupportNonpos :=
    ⟨xiMinorFourBandedCofactorOneSurvivorJ1FullNonposDet_of_moment
        T.cofactorJ1FullMomentNonpos,
      T.cofactorJ1BandedNonpos⟩
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The zero-determinant full-support middle moment theorem produces the
nonpositive moment theorem. -/
def kernelContigToPFCofactorJ1FullMoment_of_zero
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentNonpos :=
    xiMinorFourBandedCofactorOneSurvivorJ1FullMomentNonposDet_of_zero
      T.cofactorJ1FullMomentZero
  cofactorJ1BandedNonpos := T.cofactorJ1BandedNonpos
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The expanded banded middle determinant theorem produces the previous
zero/full-moment theorem. -/
def kernelContigToPFCofactorJ1FullMomentZero_of_bandedExpanded
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedNonpos :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedNonposDet_of_expanded
      T.cofactorJ1BandedExpandedNonpos
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The product-dominance banded middle theorem produces the expanded-banded
middle theorem. -/
def kernelContigToPFCofactorJ1BandedExpanded_of_productDominance
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedExpandedNonpos :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedExpandedNonpos_of_productDominance
      T.cofactorJ1BandedProductDominance
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The bracket-sign banded middle theorem produces the product-dominance
middle theorem. -/
def kernelContigToPFCofactorJ1BandedProduct_of_bracketSigns
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedProductDominance :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedProductDominance_of_bracketSigns
      T.cofactorJ1BandedBracketSigns
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The split left/right bracket theorem produces the bracket-sign theorem. -/
def kernelContigToPFCofactorJ1BandedSigns_of_split
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedBracketSigns :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedBracketSigns_of_split
      ⟨T.cofactorJ1BandedLeftBracketNonpos,
        T.cofactorJ1BandedRightBracketNonneg⟩
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The top-support split theorem produces the split left/right bracket
theorem. -/
def kernelContigToPFCofactorJ1BandedSplit_of_topSupport
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedLeftBracketNonpos :=
    (xiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBrackets_of_topSupportSplit
      ⟨T.cofactorJ1BandedTopSupported,
        T.cofactorJ1BandedTopUnsupported⟩).1
  cofactorJ1BandedRightBracketNonneg :=
    (xiMinorFourBandedCofactorOneSurvivorJ1BandedSplitBrackets_of_topSupportSplit
      ⟨T.cofactorJ1BandedTopSupported,
        T.cofactorJ1BandedTopUnsupported⟩).2
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The moment-gap top-supported branch theorem produces the top-support split
theorem. -/
def kernelContigToPFCofactorJ1BandedTopSupport_of_topMoment
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedTopSupported :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedTopSupportedSplitBrackets_of_moment
      T.cofactorJ1BandedTopSupportedMoment
  cofactorJ1BandedTopUnsupported := T.cofactorJ1BandedTopUnsupported
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The top-unsupported middle-supported theorem produces the top-moment
theorem, because the middle-unsupported subcase is automatic. -/
def kernelContigToPFCofactorJ1BandedTopMoment_of_middleSupported
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedTopSupportedMoment := T.cofactorJ1BandedTopSupportedMoment
  cofactorJ1BandedTopUnsupported :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_middleSupported
      T.cofactorJ1BandedTopUnsupportedMiddleSupported
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The moment-product theorem produces the middle-supported theorem by
rewriting the top-unsupported branch into moment coordinates. -/
def kernelContigToPFJ1TopMomentMiddle_of_momentProduct
    (T :
      KernelContigToPFJ1TopMomentMiddleProductTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem
    where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedTopSupportedMoment := T.cofactorJ1BandedTopSupportedMoment
  cofactorJ1BandedTopUnsupportedMiddleSupported :=
    xiJ1TopUnsupportedMiddleSupportedBrackets_of_momentProduct
      T.cofactorJ1BandedTopUnsupportedMiddleSupportedMomentProduct
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The top-supported moment theorem produces the top-moment theorem because
the full top-unsupported branch is now support-bookkeeping. -/
def kernelContigToPFCofactorJ1BandedTopMoment_of_support
    (T : KernelContigToPFJ1TopMomentSupportTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem
    where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedTopSupportedMoment := T.cofactorJ1BandedTopSupportedMoment
  cofactorJ1BandedTopUnsupported :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_support
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The support-only theorem produces the top-support theorem because both
top-supported and top-unsupported branches are impossible/support-automatic. -/
def kernelContigToPFCofactorJ1BandedTopSupport_of_support
    (T : KernelContigToPFJ1SupportTheorem) :
    KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem
    where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero := T.cofactorJ1FullMomentZero
  cofactorJ1BandedTopSupported := xiJ1TopSupportedSplitBrackets_of_support
  cofactorJ1BandedTopUnsupported :=
    xiMinorFourBandedCofactorOneSurvivorJ1BandedTopUnsupportedSplitBrackets_of_support
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The structural-support theorem produces the support theorem because the
full-support middle cofactor is also impossible. -/
def kernelContigToPFJ1Support_of_structuralSupport
    (T : KernelContigToPFJ1StructuralSupportTheorem) :
    KernelContigToPFJ1SupportTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorJ1FullMomentZero :=
    xiMinorFourBandedCofactorOneSurvivorJ1FullMomentZeroDet_of_support
  cofactorMultiSurvivor := T.cofactorMultiSurvivor
  geFive := T.geFive

/-- The reduced multi-survivor theorem produces the structural-support theorem
by reconstructing the full multi-survivor table from the reduced one. -/
def kernelContigToPFJ1StructuralSupport_of_reducedMulti
    (T : KernelContigToPFJ1StructuralReducedMultiTheorem) :
    KernelContigToPFJ1StructuralSupportTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiSurvivor :=
    xiMinorFourBandedCofactorMultiSurvivorCaseTable_of_reduced
      T.cofactorMultiKindReduction
      T.cofactorReducedMultiSurvivor
  geFive := T.geFive

/-- The three-row reduced theorem produces the reduced multi-survivor theorem.
-/
def kernelContigToPFJ1StructuralReducedMulti_of_rows
    (T : KernelContigToPFJ1StructuralReducedRowsTheorem) :
    KernelContigToPFJ1StructuralReducedMultiTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiKindReduction := T.cofactorMultiKindReduction
  cofactorReducedMultiSurvivor :=
    xiMinorFourBandedCofactorReducedMultiSurvivor_of_rows
      T.cofactorReducedMultiRows
  geFive := T.geFive

/-- The two-term row theorem produces the row-level reduced theorem. -/
def kernelContigToPFJ1StructuralReducedRows_of_twoTerm
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem) :
    KernelContigToPFJ1StructuralReducedRowsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiKindReduction := T.cofactorMultiKindReduction
  cofactorReducedMultiRows :=
    xiMinorFourBandedCofactorReducedMultiRows_of_twoTerm
      T.cofactorReducedMultiRowsTwoTerm
  geFive := T.geFive

/-- The active-pair support-kind theorem produces the previous two-term
row-level theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsTwoTerm_of_pair
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem) :
    KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiKindReduction :=
    xiMinorFourBandedCofactorMultiSurvivorKindReduction_of_pair
      T.cofactorMultiPairKindReduction
  cofactorReducedMultiRowsTwoTerm := T.cofactorReducedMultiRowsTwoTerm
  geFive := T.geFive

/-- The pair-`12` active-kind case theorem produces the previous active-pair
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsTwoTermPair_of_pair12Cases
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem) :
    KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiPairKindReduction :=
    xiMinorFourBandedCofactorMultiSurvivorPairKindReduction_of_pair12Cases
      T.cofactorMultiPair12CasesKindReduction
  cofactorReducedMultiRowsTwoTerm := T.cofactorReducedMultiRowsTwoTerm
  geFive := T.geFive

/-- The pair-`01`/pair-`02` theorem target produces the pair-`12` cases
theorem target, because pair-`12` is structurally discharged. -/
def kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases_of_pair01_pair02
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem) :
    KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiPair12CasesKindReduction :=
    xiMinorFourBandedCofactorMultiSurvivorPair12CasesKindReduction_of_pair01_pair02
      T.cofactorMultiPair01Pair02KindReduction
  cofactorReducedMultiRowsTwoTerm := T.cofactorReducedMultiRowsTwoTerm
  geFive := T.geFive

/-- The pair-`01` theorem target produces the pair-`01`/pair-`02` theorem
target, because pair-`02` is structurally discharged. -/
def kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02_of_pair01
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem) :
    KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiPair01Pair02KindReduction :=
    xiMinorFourBandedCofactorMultiSurvivorPair01Pair02KindReduction_of_pair01
      T.cofactorMultiPair01KindReduction
  cofactorReducedMultiRowsTwoTerm := T.cofactorReducedMultiRowsTwoTerm
  geFive := T.geFive

/-- The support-free theorem target produces the pair-`01` theorem target,
because pair-`01` is structurally discharged. -/
def kernelContigToPFJ1StructuralReducedRowsTwoTermPair01_of_supportFree
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem) :
    KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorMultiPair01KindReduction :=
    xiMinorFourBandedCofactorMultiSurvivorPair01KindOnlyReduction_of_support
  cofactorReducedMultiRowsTwoTerm := T.cofactorReducedMultiRowsTwoTerm
  geFive := T.geFive

/-- The full/sparse split row theorem target produces the support-free
two-term row theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree_of_fullSparse
    (T : KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem) :
    KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsTwoTerm :=
    xiMinorFourBandedCofactorReducedMultiRowsTwoTerm_of_fullSparse
      T.cofactorReducedMultiRowsFullSparseTwoTerm
  geFive := T.geFive

/-- The full-dominance/sparse row theorem target produces the full/sparse row
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm_of_fullDominance
    (T : KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem) :
    KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsFullSparseTwoTerm :=
    xiMinorFourBandedCofactorReducedMultiRowsFullSparseTwoTerm_of_dominance
      T.cofactorReducedMultiRowsFullDominanceSparseTwoTerm
  geFive := T.geFive

/-- The full-dominance/sparse-dominance row theorem target produces the
full-dominance/sparse theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm_of_sparseDominance
    (T : KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem) :
    KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsFullDominanceSparseTwoTerm :=
    xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseTwoTerm_of_sparseDominance
      T.cofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm
  geFive := T.geFive

/-- The all-dominance theorem target produces the previous
full-dominance/sparse-dominance/two-term target. -/
def kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
    (T : KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem) :
    KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm :=
    xiMinorFourBandedCofactorReducedMultiRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
      T.cofactorReducedMultiRowsAllDominance
  geFive := T.geFive

/-- The uniform-dominance theorem target produces the all-dominance theorem
target. -/
def kernelContigToPFJ1StructuralReducedRowsAllDominance_of_uniformDominance
    (T : KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem) :
    KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsAllDominance :=
    xiMinorFourBandedCofactorReducedMultiRowsAllDominance_of_uniformDominance
      T.cofactorReducedMultiRowsUniformDominance
  geFive := T.geFive

/-- The row-geometry theorem target produces the uniform-dominance theorem
target. -/
def kernelContigToPFJ1StructuralReducedRowsUniformDominance_of_rowGeometryDominance
    (T : KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem) :
    KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsUniformDominance :=
    xiMinorFourBandedCofactorReducedMultiRowsUniformDominance_of_rowGeometryDominance
      T.cofactorReducedMultiRowsRowGeometryDominance
  geFive := T.geFive

/-- The middle-dominance theorem target produces the row-geometry theorem
target. -/
def kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance_of_middleDominance
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem) :
    KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsRowGeometryDominance :=
    xiMinorFourBandedCofactorMultiRowGeometryDominance_of_middleDominance
      T.cofactorReducedMultiRowsMiddleDominance
  geFive := T.geFive

/-- The side-bound middle-dominance theorem target produces the bare
middle-dominance theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominance_of_sideBound
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominance :=
    xiMinorFourBandedCofactorMiddleDominance_of_sideBoundFromContig
      T.cofactorReducedMultiRowsMiddleDominanceSideBound
  geFive := T.geFive

/-- The separated-bounds theorem target produces the side-bound theorem target.
-/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound_of_separatedBounds
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceSideBound :=
    xiMinorFourBandedCofactorMiddleDominanceSideBound_of_separatedBounds
      T.cofactorReducedMultiRowsMiddleDominanceSeparatedBounds
  geFive := T.geFive

/-- The determinant-side theorem target produces the separated-bounds target.
-/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds_of_sideDet
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceSeparatedBounds :=
    xiMinorFourBandedCofactorMiddleDominanceSeparatedBounds_of_sideDet
      T.cofactorReducedMultiRowsMiddleDominanceDetSideAndMiddle
  geFive := T.geFive

/-- The split-side-determinant theorem target produces the determinant-side
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle_of_splitSideDet
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceDetSideAndMiddle :=
    xiMinorFourBandedCofactorMiddleDominanceDetSideAndMiddle_of_splitSideDet
      T.cofactorReducedMultiRowsMiddleDominanceSplitSideDetAndMiddle
  geFive := T.geFive

/-- The support-side theorem target produces the split-side-determinant theorem
target using the existing `3 × 3` theorem fields. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle_of_supportSide
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceSplitSideDetAndMiddle :=
    xiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddle_of_support
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominanceSupportSideAndMiddle
  geFive := T.geFive

/-- The support-class-side theorem target produces the split-side-determinant
theorem target using the existing `3 × 3` theorem fields. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle_of_supportClassSide
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceSplitSideDetAndMiddle :=
    xiMinorFourBandedCofactorMiddleDominanceSplitSideDetAndMiddle_of_supportClass
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominanceSupportClassSideAndMiddle
  geFive := T.geFive

/-- The middle-only theorem target produces the support-class-side theorem
target because side support classes are already proved from the outer band
geometry. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle_of_middleOnly
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceSupportClassSideAndMiddle :=
    xiMinorFourBandedCofactorMiddleDominanceSupportClassSideAndMiddle_of_middle
      T.cofactorReducedMultiRowsMiddleDominanceMiddleUpperBound
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The positive-middle-determinant cancellation theorem target produces the
middle-only target by discharging the nonpositive branch automatically. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly_of_positiveMiddleDetCancellation
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceMiddleUpperBound :=
    xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_positiveMiddleDetCancellation
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetCancellation
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The middle-only target restricts to the positive-middle-determinant
cancellation target, so the two formulations are equivalent under the shared
theorem fields. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation_of_middleOnly
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetCancellation :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_middleUpperBound
      T.cofactorReducedMultiRowsMiddleDominanceMiddleUpperBound
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The side-allocation theorem target produces the positive-middle-
determinant cancellation target by adding the two allocated bounds. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation_of_sideAllocation
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetCancellation :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_sideAllocation
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetSideAllocation
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The geometric-mean theorem target produces the side-allocation target via
the arithmetic-geometric mean bridge. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation_of_geometricMean
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMeanTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetSideAllocation :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_geometricMean
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetGeometricMean
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The factorized log-convexity theorem target produces geometric-mean
domination by multiplying its row and cofactor factors. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean_of_factorizedLogConvexity
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexityTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMeanTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetGeometricMean :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetGeometricMean_of_factorizedLogConvexity
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexity
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The support-aware top-right split theorem target produces positive-middle
cancellation without the global geometric-mean requirement. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation_of_topRightSupportSplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetCancellation :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetCancellation_of_topRightSupportSplit
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The three-way support theorem target produces the previous top-right
support-split target after discharging the automatic `A01 = 0` branch. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit_of_threeWay
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightSupportSplit_of_threeWay
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment/cofactor-ratio theorem target produces the prior three-way
support target by rewriting the supported top-row factors. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit_of_momentCofactorRatio
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightThreeWaySplit_of_momentCofactorRatio
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The subtraction-free certificate theorem target produces the division-free
moment/cofactor theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_positivePolynomialCertificate
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_positivePolynomialCertificate
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The normalized moment/cofactor-ratio target clears positive denominators
and produces the division-free moment/cofactor target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_normalizedMomentCofactorRatio
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_normalized
      (xiMomentCoeffPositive_of_kernelRep ⟨T.M, T.positive, T.kernelRep⟩)
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit
  geFive := T.geFive

set_option linter.style.longLine false in
/-- With the positive kernel representation, the division-free theorem target
also yields its quotient-normalized presentation. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit_of_momentCofactorRatio
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit_of_momentCofactorRatio
      (xiMomentCoeffPositive_of_kernelRep ⟨T.M, T.positive, T.kernelRep⟩)
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
  geFive := T.geFive

set_option linter.style.longLine false in
/-- Under the shared side-minor fields, the positive-middle cancellation target
also constructs the equivalent side-allocation target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation_of_cancellation
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetSideAllocation :=
    xiMinorFourBandedCofactorMiddleDominancePositiveMiddleDetSideAllocation_of_cancellation
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDominancePositiveMiddleDetCancellation
  geFive := T.geFive

/-- The middle determinant-sign theorem target produces the middle-only
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly_of_middleDetSign
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDominanceMiddleUpperBound :=
    xiMinorFourBandedCofactorMiddleDominanceMiddleUpperBound_of_middleDetNonpositive
      T.threeFull
      T.threeBandedDet
      T.cofactorReducedMultiRowsMiddleDetNonpositive
  geFive := T.geFive

/-- The support-split middle determinant-sign theorem target produces the
middle determinant-sign theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign_of_supportSplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDetNonpositive :=
    xiMinorFourBandedCofactorMiddleDetNonpositive_of_supportSplit
      T.cofactorReducedMultiRowsMiddleDetSupportSplit
  geFive := T.geFive

/-- The full-zero/banded-nonpositive theorem target produces the support-split
middle determinant-sign theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit_of_fullZero
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleDetSupportSplit :=
    xiMinorFourBandedCofactorMiddleDetSupportSplit_of_fullZero
      T.cofactorReducedMultiRowsMiddleFullZeroBandedNonpositive
  geFive := T.geFive

/-- The moment-zero/banded-nonpositive theorem target produces the
full-zero/banded-nonpositive theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded_of_moment
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullZeroBandedNonpositive :=
    xiMinorFourBandedCofactorMiddleDetFullZeroBandedNonpositive_of_moment
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedNonpositive
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment-zero/expanded-banded theorem target produces the
moment-zero/banded-determinant theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded_of_expanded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedNonpositive :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedNonpositive_of_expanded
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedExpanded
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment-zero/product theorem target produces the
moment-zero/expanded-banded theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded_of_product
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedExpanded :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedExpanded_of_product
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedProduct
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment-zero/bracket-sign theorem target produces the
moment-zero/product theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct_of_bracketSigns
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedProduct :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedProduct_of_bracketSigns
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedBracketSigns
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment-zero/split-bracket theorem target produces the
moment-zero/bracket-sign theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns_of_split
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedBracketSigns :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedBracketSigns_of_split
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedSplitBrackets
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment-zero/top-support-split theorem target produces the
moment-zero/split-bracket theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets_of_topSupportSplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedSplitBrackets :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedSplitBrackets_of_topSupportSplit
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopSupportSplitBrackets
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment top-supported theorem target produces the top-support split
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets_of_topSupportedMoment
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopSupportSplitBrackets :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportSplitBrackets_of_topSupportedMoment
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopSupportedMoment
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The top-unsupported middle-supported theorem target produces the
top-supported-moment theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment_of_middleSupported
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopSupportedMoment :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopSupportedMoment_of_middleSupported
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupported
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The moment-product theorem target produces the top-unsupported
middle-supported theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported_of_momentProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupported :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported_of_momentProduct
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The split-products theorem target produces the moment-product theorem
target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The left-product theorem target produces the split-products theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The left-moment-zero theorem target produces the left-product theorem
target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The structural-impossibility theorem target produces the left-moment-zero
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The contextual gap-collapse theorem target produces the impossible-branch
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The original-index gap-collapse theorem target produces the cofactor
gap-collapse theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The inactive-side-support theorem target produces the impossible-branch
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The right-side inactive support theorem target produces the
impossible-branch theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The right-active-exclusion theorem target produces the right-inactive
support theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The right-banded-exclusion theorem target produces the right-active-
exclusion theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The branch-impossibility theorem target produces the right-banded-
exclusion theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The middle-column-unsupported theorem target produces the branch-
impossibility theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The middle/top-column no-straddle theorem target produces the
middle-column-unsupported theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The middle/top-column straddle-impossibility theorem target produces the
no-straddle theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The straddle left-product theorem target produces the straddle-
impossibility theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible :=
    ⟨T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct.1,
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct.2.1,
      xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
        (xiMomentCoeffPositive_of_kernelRep
          ⟨T.M, T.positive, T.kernelRep⟩)
        ((xiContigToeplitzTotalPositive_iff_kernelContig T.kernelRep).mpr
          T.contig)
        T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct.2.2⟩
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The older middle-supported theorem target produces the straddle
left-bracket theorem target by restriction to the straddle subcase. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_middleSupported
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleSupported
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The straddle left-bracket theorem target produces the straddle left-product
theorem target. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The straddle left-product theorem target recovers the equivalent native
left-bracket theorem target in the top-unsupported branch. -/
def kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem) :
    KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  lowRankMomentPayload := T.lowRankMomentPayload
  threeFull := T.threeFull
  threeBandedDet := T.threeBandedDet
  cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket :=
    xiMinorFourBandedCofactorMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_of_leftProduct
      T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
  geFive := T.geFive

set_option linter.style.longLine false in
/-- The straddle left-product theorem target is uninhabited: its own positive
kernel and contiguous-positivity fields contradict its left-product field on a
concrete admissible support pattern. -/
theorem kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_false
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem) :
    False :=
  (not_xiMinorFourBandedCofactorMiddleBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_positive_and_contig
      (xiMomentCoeffPositive_of_kernelRep
        ⟨T.M, T.positive, T.kernelRep⟩)
      ((xiContigToeplitzTotalPositive_iff_kernelContig T.kernelRep).mpr
        T.contig))
    T.cofactorReducedMultiRowsMiddleFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct.2.2

set_option linter.style.longLine false in
/-- The equivalent native left-bracket theorem target is also uninhabited. -/
theorem kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket_false
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem) :
    False :=
  kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_false
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
      T)

/-- The level-2.5 theorem target produces the full PF condition. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPF
    (T : KernelContigToPFTheorem) : XiToeplitzTotalPositive :=
  T.upgrade ((xiContigToeplitzTotalPositive_iff_kernelContig T.kernelRep).mpr T.contig)

/-- The initial-column reduction target produces full PF positivity through the
lower-triangular initial-column criterion. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFInitialColumn
    (T : KernelContigToPFInitialColumnTheorem) : XiToeplitzTotalPositive :=
  T.initialColumnsToPF
    (xiMomentCoeffPositive_of_kernelRep ⟨T.M, T.positive, T.kernelRep⟩)
    (T.contigToInitialColumns
      ((xiContigToeplitzTotalPositive_iff_kernelContig T.kernelRep).mpr T.contig))

/-- The `k >= 3` initial-column target upgrades to the full initial-column
target using the kernel-backed order-two base. -/
def kernelContigToPFInitialColumn_of_geThree
    (T : KernelContigToPFInitialColumnGeThreeTheorem) :
    KernelContigToPFInitialColumnTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  contigToInitialColumns :=
    xiContigToInitialColumnMinorBridge_of_kernelRep_and_geThree
      ⟨T.M, T.positive, T.kernelRep⟩ T.initialColumnsGeThree
  initialColumnsToPF := T.initialColumnsToPF

/-- The reduced `k >= 3` initial-column target also produces full PF
positivity. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeThree
    (T : KernelContigToPFInitialColumnGeThreeTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFInitialColumn
    (kernelContigToPFInitialColumn_of_geThree T)

/-- The `k >= 4` initial-column target upgrades to the `k >= 3` target using
the kernel-backed order-two base and its supplied order-three input. -/
def kernelContigToPFInitialColumnGeThree_of_geFour
    (T : KernelContigToPFInitialColumnGeFourTheorem) :
    KernelContigToPFInitialColumnGeThreeTheorem where
  M := T.M
  positive := T.positive
  kernelRep := T.kernelRep
  contig := T.contig
  initialColumnsGeThree := by
    intro k hk rows hRows hContig
    by_cases hk3 : k = 3
    · subst k
      exact T.initialColumnsThree rows hRows hContig
    have hk4 : 4 ≤ k := by omega
    exact T.initialColumnsGeFour k hk4 rows hRows hContig
  initialColumnsToPF := T.initialColumnsToPF

/-- The reduced `k >= 4` initial-column target also produces full PF
positivity. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeFour
    (T : KernelContigToPFInitialColumnGeFourTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeThree
    (kernelContigToPFInitialColumnGeThree_of_geFour T)

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

/-- The full/mixed `3 × 3` split target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeSupportSplit
    (T : KernelContigToPFThreeSupportSplitTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeAndGeFour
    (kernelContigToPFThreeAndGeFour_of_threeSupportSplit T)

/-- The banded-support `3 × 3` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedSupport
    (T : KernelContigToPFThreeBandedSupportTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeSupportSplit
    (kernelContigToPFThreeSupportSplit_of_bandedSupport T)

/-- The banded determinant target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedDet
    (T : KernelContigToPFThreeBandedDetTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedSupport
    (kernelContigToPFThreeBandedSupport_of_bandedDet T)

/-- The expanded banded determinant target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedExpanded
    (T : KernelContigToPFThreeBandedExpandedTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedDet
    (kernelContigToPFThreeBandedDet_of_expanded T)

/-- The middle-supported moment target plus edge cases also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeMiddleMoment
    (T : KernelContigToPFThreeMiddleMomentTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedExpanded
    (kernelContigToPFThreeBandedExpanded_of_middleMoment T)

/-- The concrete zero-edge target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeZeroEdges
    (T : KernelContigToPFThreeZeroEdgesTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeMiddleMoment
    (kernelContigToPFThreeMiddleMoment_of_zeroEdges T)

/-- The simplified zero-edge target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeSimplifiedZeroEdges
    (T : KernelContigToPFThreeSimplifiedZeroEdgesTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeZeroEdges
    (kernelContigToPFThreeZeroEdges_of_simplified T)

/-- The bracket zero-edge target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeBracketZeroEdges
    (T : KernelContigToPFThreeBracketZeroEdgesTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeSimplifiedZeroEdges
    (kernelContigToPFThreeSimplifiedZeroEdges_of_bracketZeroEdges T)

/-- The kernel-zero-edge target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeKernelZeroEdges
    (T : KernelContigToPFThreeKernelZeroEdgesTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeBracketZeroEdges
    (kernelContigToPFThreeBracketZeroEdges_of_kernelZeroEdges T)

/-- The compound-ratio target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeCompoundRatio
    (T : KernelContigToPFThreeCompoundRatioTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeKernelZeroEdges
    (kernelContigToPFThreeKernelZeroEdges_of_compoundRatio T)

/-- The moment-form compound-ratio target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentCompoundRatio
    (T : KernelContigToPFThreeMomentCompoundRatioTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeCompoundRatio
    (kernelContigToPFThreeCompoundRatio_of_momentCompoundRatio T)

/-- The unified moment-payload target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayload
    (T : KernelContigToPFThreeMomentPayloadTheorem) : XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentCompoundRatio
    (kernelContigToPFThreeMomentCompoundRatio_of_momentPayload T)

/-- The explicit `4 × 4` plus `k ≥ 5` tail target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourAndGeFive
    (T : KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayload
    (kernelContigToPFThreeMomentPayload_of_four_and_geFive T)

/-- The support-split `4 × 4` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourSupportSplit
    (T : KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourAndGeFive
    (kernelContigToPFThreeMomentPayloadFourAndGeFive_of_fourSupportSplit T)

/-- The moment-form `4 × 4` support-split target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit
    (T : KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourSupportSplit
    (kernelContigToPFThreeMomentPayloadFourSupportSplit_of_fourMomentSupportSplit T)

/-- The low-rank moment payload target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourMixed
    (T : KernelContigToPFLowRankMomentFourMixedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit
    (kernelContigToPFThreeMomentPayloadFourMomentSupportSplit_of_lowRankMoment T)

/-- The banded `4 × 4` mixed-support target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedMixed
    (T : KernelContigToPFLowRankMomentFourBandedMixedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourMixed
    (kernelContigToPFLowRankMomentFourMixed_of_bandedMixed T)

/-- The determinant-form banded `4 × 4` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedDet
    (T : KernelContigToPFLowRankMomentFourBandedDetTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedMixed
    (kernelContigToPFLowRankMomentFourBandedMixed_of_bandedDet T)

/-- The upper-right-zero determinant-form banded `4 × 4` target also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero
    (T : KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedDet
    (kernelContigToPFLowRankMomentFourBandedDet_of_upperRightZero T)

/-- The row-zero cofactor-form banded `4 × 4` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor
    (T : KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero
    (kernelContigToPFLowRankMomentFourBandedUpperRightZero_of_rowZeroCofactor T)

/-- The three-cofactor-form banded `4 × 4` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor
    (T : KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor
    (kernelContigToPFLowRankMomentFourBandedRowZeroCofactor_of_threeCofactor T)

/-- The named-cofactor-matrix banded `4 × 4` target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor
    (T : KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor
    (kernelContigToPFLowRankMomentFourBandedThreeCofactor_of_namedCofactor T)

/-- The row/column-selector cofactor target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol
    (T : KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor
    (kernelContigToPFLowRankMomentFourBandedNamedCofactor_of_rowCol T)

/-- The support-class split cofactor target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol
    (kernelContigToPFLowRankMomentFourBandedCofactorRowCol_of_supportSplit T)

/-- The individual `j = 0, 1, 2` cofactor classification target also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit
    (kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit_of_j012 T)

/-- The remaining `j = 1, 2` cofactor classification target also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012
    (kernelContigToPFLowRankMomentFourBandedCofactorJ012_of_j12 T)

/-- The remaining `j = 2` cofactor classification target also produces full
PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ2
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ2Theorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12
    (kernelContigToPFLowRankMomentFourBandedCofactorJ12_of_j2 T)

/-- The cofactor support-split-only target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ2
    (kernelContigToPFLowRankMomentFourBandedCofactorJ2_of_supportSplitOnly T)

/-- The cofactor support-kind case-table target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable
    (T : KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly
    (kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly_of_caseTable T)

/-- The reduced nonzero-survivor case-table target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable
    (T : KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable
    (kernelContigToPFLowRankMomentFourBandedCofactorCaseTable_of_nonzeroCaseTable T)

/-- The survivor-split case-table target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable
    (kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable_of_survivorSplit T)

/-- The position-specific one-survivor target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition
    (T : KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit
    (kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit_of_oneSurvivorPosition T)

/-- The positive-side one-survivor target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition
    (kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition_of_positiveOneSurvivor
      T)

/-- The full/banded positive one-survivor support target also produces full
PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveSupport
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor
    (kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor_of_support T)

/-- The positive full-support bundle target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFull
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveSupport
    (kernelContigToPFCofactorPositiveSupport_of_positiveFull T)

/-- The determinant-level positive full-support target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFullDet
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFull
    (kernelContigToPFCofactorPositiveFull_of_det T)

/-- The full-support `3 × 3` cofactor target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFull
    (T : KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFullDet
    (kernelContigToPFCofactorPositiveFullDet_of_threeFull T)

/-- The full-support and banded `3 × 3` cofactor target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFullBanded
    (T : KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFull
    (kernelContigToPFCofactorThreeFull_of_threeFullBanded T)

/-- The explicit nonpositive middle-determinant target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1Nonpos
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFullBanded
    (kernelContigToPFCofactorThreeFullBanded_of_j1Nonpos T)

/-- The full/banded middle determinant support split also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1SupportSplit
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1Nonpos
    (kernelContigToPFCofactorJ1Nonpos_of_supportSplit T)

/-- The moment-index full-support middle determinant target also produces full
PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMoment
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1SupportSplit
    (kernelContigToPFCofactorJ1SupportSplit_of_fullMoment T)

/-- The zero-determinant full-support middle moment target also produces full
PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMomentZero
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMoment
    (kernelContigToPFCofactorJ1FullMoment_of_zero T)

/-- The expanded banded middle determinant target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedExpanded
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMomentZero
    (kernelContigToPFCofactorJ1FullMomentZero_of_bandedExpanded T)

/-- The product-dominance form of the banded middle determinant target also
produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedProduct
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedExpanded
    (kernelContigToPFCofactorJ1BandedExpanded_of_productDominance T)

/-- The bracket-sign form of the banded middle determinant target also
produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSigns
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedProduct
    (kernelContigToPFCofactorJ1BandedProduct_of_bracketSigns T)

/-- The split left/right bracket form of the banded middle determinant target
also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSplit
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSigns
    (kernelContigToPFCofactorJ1BandedSigns_of_split T)

/-- The top-support split form of the banded middle bracket target also
produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopSupport
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSplit
    (kernelContigToPFCofactorJ1BandedSplit_of_topSupport T)

/-- The moment-gap top-supported branch form of the banded middle bracket
target also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMoment
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopSupport
    (kernelContigToPFCofactorJ1BandedTopSupport_of_topMoment T)

/-- The top-unsupported middle-supported branch theorem also produces full PF.
-/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMoment
    (kernelContigToPFCofactorJ1BandedTopMoment_of_middleSupported T)

/-- The top-unsupported moment-product theorem also produces full PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFJ1TopMomentMiddleProduct
    (T :
      KernelContigToPFJ1TopMomentMiddleProductTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle
    (kernelContigToPFJ1TopMomentMiddle_of_momentProduct T)

/-- The support-only top-moment theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1TopMomentSupport
    (T : KernelContigToPFJ1TopMomentSupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMoment
    (kernelContigToPFCofactorJ1BandedTopMoment_of_support T)

/-- The support-only `j = 1` theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1Support
    (T : KernelContigToPFJ1SupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopSupport
    (kernelContigToPFCofactorJ1BandedTopSupport_of_support T)

/-- The structural-support `j = 1` theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralSupport
    (T : KernelContigToPFJ1StructuralSupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1Support
    (kernelContigToPFJ1Support_of_structuralSupport T)

/-- The reduced multi-survivor theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedMulti
    (T : KernelContigToPFJ1StructuralReducedMultiTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralSupport
    (kernelContigToPFJ1StructuralSupport_of_reducedMulti T)

/-- The three-row reduced theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRows
    (T : KernelContigToPFJ1StructuralReducedRowsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedMulti
    (kernelContigToPFJ1StructuralReducedMulti_of_rows T)

/-- The two-term row theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTerm
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRows
    (kernelContigToPFJ1StructuralReducedRows_of_twoTerm T)

/-- The active-pair split theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTerm
    (kernelContigToPFJ1StructuralReducedRowsTwoTerm_of_pair T)

/-- The pair-`12` active-kind case theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair
    (kernelContigToPFJ1StructuralReducedRowsTwoTermPair_of_pair12Cases T)

/-- The pair-`01`/pair-`02` theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases
    (kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases_of_pair01_pair02
      T)

/-- The pair-`01` theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02
    (kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02_of_pair01 T)

/-- The support-free reduced-row theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01
    (kernelContigToPFJ1StructuralReducedRowsTwoTermPair01_of_supportFree T)

/-- The full/sparse split reduced-row theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm
    (T : KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree
    (kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree_of_fullSparse T)

/-- The full-dominance/sparse reduced-row theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm
    (T : KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm
    (kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm_of_fullDominance
      T)

set_option linter.style.longLine false in
/-- The full-dominance/sparse-dominance reduced-row theorem also produces full
PF. -/
theorem
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm
    (T :
      KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm
    (kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm_of_sparseDominance
      T)

set_option linter.style.longLine false in
/-- The all-dominance reduced-row theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsAllDominance
    (T : KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem) :
    XiToeplitzTotalPositive :=
  have T' :
      KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem :=
    kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm_of_allDominance
      T
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm
    T'

/-- The uniform-dominance reduced-row theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsUniformDominance
    (T : KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsAllDominance
    (kernelContigToPFJ1StructuralReducedRowsAllDominance_of_uniformDominance
      T)

/-- The row-geometry dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance
    (T : KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsUniformDominance
    (kernelContigToPFJ1StructuralReducedRowsUniformDominance_of_rowGeometryDominance
      T)

/-- The middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominance
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance
    (kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance_of_middleDominance
      T)

/-- The side-bound middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominance
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominance_of_sideBound T)

set_option linter.style.longLine false in
/-- The separated-bounds middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound_of_separatedBounds
      T)

set_option linter.style.longLine false in
/-- The determinant-side middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds_of_sideDet
      T)

set_option linter.style.longLine false in
/-- The split-side-determinant middle-dominance theorem also produces full PF.
-/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle_of_splitSideDet
      T)

set_option linter.style.longLine false in
/-- The support-side middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddle
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle_of_supportSide
      T)

set_option linter.style.longLine false in
/-- The support-class-side middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle_of_supportClassSide
      T)

set_option linter.style.longLine false in
/-- The middle-only middle-dominance theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle_of_middleOnly
      T)

set_option linter.style.longLine false in
/-- The positive-middle-determinant cancellation theorem also produces full
PF through the middle-only target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly_of_positiveMiddleDetCancellation
      T)

set_option linter.style.longLine false in
/-- The positive-middle side-allocation theorem also produces full PF through
the cancellation target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation_of_sideAllocation
      T)

set_option linter.style.longLine false in
/-- The geometric-mean compound-minor theorem also produces full PF through
the side-allocation target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMeanTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation_of_geometricMean
      T)

set_option linter.style.longLine false in
/-- The factorized log-convexity theorem also produces full PF through the
geometric-mean compound-minor target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexity
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexityTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean_of_factorizedLogConvexity
      T)

set_option linter.style.longLine false in
/-- The support-aware top-right split theorem also produces full PF through
the positive-middle cancellation target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation_of_topRightSupportSplit
      T)

set_option linter.style.longLine false in
/-- The three-way top-right support theorem also produces full PF through the
top-right support split. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit_of_threeWay
      T)

set_option linter.style.longLine false in
/-- The moment/cofactor-ratio three-way theorem also produces full PF through
the support-split theorem target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit_of_momentCofactorRatio
      T)

set_option linter.style.longLine false in
/-- The subtraction-free contiguous-minor certificate three-way target also
produces full PF through the division-free cofactor-ratio target. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_positivePolynomialCertificate
      T)

set_option linter.style.longLine false in
/-- The normalized moment/cofactor-ratio three-way target also produces full
PF after clearing its positive denominators. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit_of_normalizedMomentCofactorRatio
      T)

set_option linter.style.longLine false in
/-- The middle determinant-sign theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly_of_middleDetSign
      T)

set_option linter.style.longLine false in
/-- The support-split middle determinant-sign theorem also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign_of_supportSplit
      T)

set_option linter.style.longLine false in
/-- The full-zero/banded-nonpositive middle determinant theorem also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit_of_fullZero
      T)

set_option linter.style.longLine false in
/-- The moment-zero/banded-nonpositive middle determinant theorem also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded_of_moment
      T)

set_option linter.style.longLine false in
/-- The moment-zero/expanded-banded middle determinant theorem also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded_of_expanded
      T)

set_option linter.style.longLine false in
/-- The moment-zero/product-dominance middle determinant theorem also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded_of_product
      T)

set_option linter.style.longLine false in
/-- The moment-zero/bracket-sign middle determinant theorem also produces full
PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct_of_bracketSigns
      T)

set_option linter.style.longLine false in
/-- The moment-zero/split-bracket middle determinant theorem also produces full
PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns_of_split
      T)

set_option linter.style.longLine false in
/-- The moment-zero/top-support-split middle determinant theorem also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets_of_topSupportSplit
      T)

set_option linter.style.longLine false in
/-- The moment-supported top-supported middle determinant theorem also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets_of_topSupportedMoment
      T)

set_option linter.style.longLine false in
/-- The top-unsupported middle-supported theorem target also produces full PF.
-/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment_of_middleSupported
      T)

set_option linter.style.longLine false in
/-- The top-unsupported middle-supported moment-product theorem target also
produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported_of_momentProduct
      T)

set_option linter.style.longLine false in
/-- The split-products theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct_of_splitProducts
      T)

set_option linter.style.longLine false in
/-- The left-product theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts_of_leftProduct
      T)

set_option linter.style.longLine false in
/-- The left-moment-zero theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct_of_leftMomentZero
      T)

set_option linter.style.longLine false in
/-- The structural-impossibility theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero_of_impossible
      T)

set_option linter.style.longLine false in
/-- The contextual gap-collapse theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_gapCollapse
      T)

set_option linter.style.longLine false in
/-- The original-index gap-collapse theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse_of_originalGapCollapse
      T)

set_option linter.style.longLine false in
/-- The inactive-side-support theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_inactiveSideSupport
      T)

set_option linter.style.longLine false in
/-- The right-side inactive support theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible_of_rightInactiveSideSupport
      T)

set_option linter.style.longLine false in
/-- The right-active-exclusion theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport_of_rightActiveExcluded
      T)

set_option linter.style.longLine false in
/-- The right-banded-exclusion theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded_of_rightBandedExcluded
      T)

set_option linter.style.longLine false in
/-- The branch-impossibility theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded_of_branchImpossible
      T)

set_option linter.style.longLine false in
/-- The middle-column-unsupported theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible_of_middleColumnUnsupported
      T)

set_option linter.style.longLine false in
/-- The middle/top-column no-straddle theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported_of_noStraddle
      T)

set_option linter.style.longLine false in
/-- The middle/top-column straddle-impossibility theorem target also produces
full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle_of_straddleImpossible
      T)

set_option linter.style.longLine false in
/-- The straddle left-product theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible_of_leftProduct
      T)

set_option linter.style.longLine false in
/-- The straddle left-bracket theorem target also produces full PF. -/
theorem xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem) :
    XiToeplitzTotalPositive :=
  xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
    (kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct_of_leftBracket
      T)

/-- Kernel-contiguous positivity plus the contiguous-to-full upgrade closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPF
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPF T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the initial-column lift and the
lower-triangular initial-column criterion closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFInitialColumn
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFInitialColumnTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFInitialColumn T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus arbitrary-row initial-column positivity
only in orders `k >= 3` closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFInitialColumnGeThree
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFInitialColumnGeThreeTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeThree T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the initial-column order-three input and
arbitrary-row initial-column positivity in orders `k >= 4` closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFInitialColumnGeFour
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFInitialColumnGeFourTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFInitialColumnGeFour T)
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

/-- Contiguous kernel positivity plus the full/mixed `3 × 3` split and
`k ≥ 4` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeSupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeSupportSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeSupportSplit T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, banded mixed-support
`3 × 3`, and the `k ≥ 4` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeBandedSupport
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeBandedSupportTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedSupport T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, banded determinant
nonnegativity, and the `k ≥ 4` tail closes RH under the classical scaffolding.
-/
theorem riemannHypothesis_of_kernelContigToPFThreeBandedDet
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeBandedDetTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedDet T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, expanded banded
determinant nonnegativity, and the `k ≥ 4` tail closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeBandedExpanded
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeBandedExpandedTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeBandedExpanded T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, middle-supported
moment inequality, remaining band edge cases, and the `k ≥ 4` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeMiddleMoment
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeMiddleMomentTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeMiddleMoment T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, middle-supported
moment inequality, concrete zero-edge cases, and the `k ≥ 4` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeZeroEdges
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeZeroEdgesTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeZeroEdges T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, middle-supported
moment inequality, simplified zero-edge cases, and the `k ≥ 4` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeSimplifiedZeroEdges
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeSimplifiedZeroEdgesTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeSimplifiedZeroEdges T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, middle-supported
moment inequality, bracket zero-edge cases, and the `k ≥ 4` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeBracketZeroEdges
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeBracketZeroEdgesTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeBracketZeroEdges T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, middle-supported
moment inequality, and the `k ≥ 4` tail closes RH under the classical
scaffolding; the zero-edge brackets are discharged by the kernel representation.
-/
theorem riemannHypothesis_of_kernelContigToPFThreeKernelZeroEdges
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeKernelZeroEdgesTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeKernelZeroEdges T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support `3 × 3`, compound-ratio
middle control, and the `k ≥ 4` tail closes RH under the classical scaffolding.
-/
theorem riemannHypothesis_of_kernelContigToPFThreeCompoundRatio
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeCompoundRatioTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeCompoundRatio T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus moment-form full-support `3 × 3`,
compound-ratio middle control, and the `k ≥ 4` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeMomentCompoundRatio
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeMomentCompoundRatioTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentCompoundRatio T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified `3 × 3` moment payload and
the `k ≥ 4` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeMomentPayload
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeMomentPayloadTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayload T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified `3 × 3` moment payload, the
`4 × 4` certificate frontier, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourAndGeFive
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeMomentPayloadFourAndGeFiveTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourAndGeFive T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified `3 × 3` moment payload,
support-split `4 × 4` certificates, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourSupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeMomentPayloadFourSupportSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourSupportSplit T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified `3 × 3` moment payload,
moment-form full-support `4 × 4`, mixed-support `4 × 4`, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFThreeMomentPayloadFourMomentSupportSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFThreeMomentPayloadFourMomentSupportSplit T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
mixed-support `4 × 4`, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourMixed
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourMixedTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourMixed T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
banded mixed-support `4 × 4`, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedMixed
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedMixedTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedMixed T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
determinant-form banded mixed-support `4 × 4`, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedDet
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedDetTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedDet T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
upper-right-zero determinant-form banded mixed-support `4 × 4`, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedUpperRightZeroTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedUpperRightZero T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
row-zero cofactor-form banded mixed-support `4 × 4`, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedRowZeroCofactorTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedRowZeroCofactor T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
three-cofactor-form banded mixed-support `4 × 4`, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedThreeCofactorTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedThreeCofactor T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
named-cofactor-matrix banded mixed-support `4 × 4`, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedNamedCofactorTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedNamedCofactor T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
row/column-selector cofactor `4 × 4` frontier, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorRowColTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorRowCol T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
support-class split cofactor `4 × 4` frontier, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplit T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload,
individual `j = 0, 1, 2` cofactor classification targets, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ012Theorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ012 T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
remaining `j = 1, 2` cofactor classification targets, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ12Theorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ12 T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
remaining `j = 2` cofactor classification target, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorJ2
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ2Theorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorJ2 T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
cofactor support-split target, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnlyTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSupportSplitOnly T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
cofactor support-kind case table, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorCaseTableTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorCaseTable T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
reduced nonzero-survivor cofactor case table, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTableTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorNonzeroCaseTable T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
one-survivor/multi-survivor cofactor case-table split, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorSurvivorSplit T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
position-specific one-survivor cofactor targets, the multi-survivor cofactor
target, and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPositionTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorOneSurvivorPosition
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
positive-side one-survivor cofactor target, the signed-negative one-survivor
target, the multi-survivor target, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivor
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the unified low-rank moment payload, the
full/banded positive one-survivor subcases, the signed-negative one-survivor
target, the multi-survivor target, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorPositiveSupport
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveOneSurvivorSupportTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveSupport
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the bundled full-support positive
one-survivor target, the two banded positive side targets, the signed-negative
one-survivor target, the multi-survivor target, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorPositiveFull
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFull
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus determinant-level positive full-support
side cofactor control, the two banded positive side targets, the
signed-negative one-survivor target, the multi-survivor target, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorPositiveFullDet
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorPositiveFullDetTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorPositiveFullDet
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the full-support `3 × 3` target, the two
banded positive side targets, the signed-negative one-survivor target, the
multi-survivor target, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorThreeFull
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorThreeFullTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFull
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus the full-support `3 × 3` target, the
banded `3 × 3` determinant target, the signed-negative one-survivor target, the
multi-survivor target, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorThreeFullBanded
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorThreeFullBandedTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorThreeFullBanded
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the explicit nonpositive middle-determinant target, the multi-survivor target,
and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1Nonpos
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1NonposTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1Nonpos
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full/banded middle determinant support split, the multi-survivor target,
and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1SupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1SupportSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1SupportSplit
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the moment-index full-support middle determinant obstruction, the banded middle
determinant obstruction, the multi-survivor target, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1FullMoment
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMoment
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the zero-determinant moment condition for the full-support middle cofactor, the
banded middle determinant obstruction, the multi-survivor target, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1FullMomentZero
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1FullMomentZero
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the expanded banded middle
determinant obstruction, the multi-survivor target, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedExpanded
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedExpandedTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedExpanded
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the product-dominance banded
middle obstruction, the multi-survivor target, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedProduct
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedProductTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedProduct
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the banded middle bracket-sign
obstruction, the multi-survivor target, and the `k ≥ 5` tail closes RH under
the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedSigns
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSignsTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSigns
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, separate left/right banded
middle bracket targets, the multi-survivor target, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedSplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedSplitTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedSplit
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the top-supported and
top-unsupported banded middle bracket targets, the multi-survivor target, and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedTopSupport
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopSupportTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopSupport
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the moment-gap top-supported
banded middle bracket target, the top-unsupported branch, the multi-survivor
target, and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedTopMoment
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMoment
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the moment-gap top-supported
banded middle bracket target, the middle-supported top-unsupported branch, the
multi-survivor target, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFLowRankMomentFourBandedCofactorJ1FullMomentZeroBandedTopMomentMiddleTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFCofactorJ1BandedTopMomentMiddle
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the moment-gap top-supported
banded middle bracket target, the moment-product top-unsupported
middle-supported branch, the multi-survivor target, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFJ1TopMomentMiddleProduct
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1TopMomentMiddleProductTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1TopMomentMiddleProduct
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the moment-gap top-supported
banded middle bracket target, the multi-survivor target, and the `k ≥ 5` tail
closes RH under the classical scaffolding.  The top-unsupported banded middle
branch is discharged by support bookkeeping alone. -/
theorem riemannHypothesis_of_kernelContigToPFJ1TopMomentSupport
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1TopMomentSupportTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1TopMomentSupport T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-support middle moment zero condition, the multi-survivor target, and
the `k ≥ 5` tail closes RH under the classical scaffolding.  Both banded middle
top branches are discharged by support bookkeeping alone. -/
theorem riemannHypothesis_of_kernelContigToPFJ1Support
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1SupportTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1Support T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the multi-survivor target, and the `k ≥ 5` tail closes RH under the classical
scaffolding.  All signed-negative `j = 1` one-survivor cases are discharged by
support bookkeeping alone. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralSupport
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralSupportTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralSupport T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the reduced multi-survivor support-kind table, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedMulti
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedMultiTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedMulti T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the multi-survivor support-kind reduction, the three reduced rows, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRows
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRows T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the multi-survivor support-kind reduction, the sharper two-term reduced row
package, and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTerm
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTerm
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the active-pair split of the multi-survivor support-kind reduction, the sharper
two-term reduced row package, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPairTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the active-pair split with pair-`12` reduced to active-kind cases, the sharper
two-term reduced row package, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair12CasesTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair12Cases
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
pair-`12` discharged structurally, pair-`01`/pair-`02` support reductions, the
sharper two-term reduced row package, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02Theorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01Pair02
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
pair-`02`/pair-`12` discharged structurally, pair-`01` support reduction, the
sharper two-term reduced row package, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermPair01Theorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermPair01
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the reduced two-term row package, and the `k ≥ 5` tail closes RH under the
classical scaffolding; all multi-survivor support-kind classification has been
discharged structurally. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsTwoTermSupportFreeTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsTwoTermSupportFree
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full/sparse split reduced-row package, and the `k ≥ 5` tail closes RH under
the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsFullSparseTwoTermTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullSparseTwoTerm
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-row dominance condition, the sparse two-term row package, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTermTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseTwoTerm
      T)
    S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the full-row dominance condition, the sparse-row dominance condition, the
zero-row two-term package, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem
    riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTermTheorem) :
    RiemannHypothesis :=
  have hPF :
      XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsFullDominanceSparseDominanceTwoTerm
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the all-dominance reduced-row package, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsAllDominance
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsAllDominanceTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsAllDominance
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the uniform support-dominance reduced-row package, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsUniformDominance
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsUniformDominanceTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsUniformDominance
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the row-geometry dominance condition, and the `k ≥ 5` tail closes RH under the
classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsRowGeometryDominanceTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsRowGeometryDominance
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the bare middle-cofactor dominance inequality, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominance
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominance
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the side-bound middle-cofactor dominance package, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBoundTheorem) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSideBound
      T)
    S.asw S.lp S.polyaJensen

/-- Contiguous kernel positivity plus full-support and banded `3 × 3` targets,
the separated side and middle estimates, and the `k ≥ 5` tail closes RH under
the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds
    (S : ClassicalToeplitzScaffolding)
    (T : KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBoundsTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSeparatedBounds
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus side determinant estimates, the middle
upper-bound estimate, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceDetSideAndMiddle
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus split side determinant estimates, the
middle upper-bound estimate, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSplitSideDetAndMiddle
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus side-support classification, the middle
upper-bound estimate, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddle
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportSideAndMiddle
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus side support-class classification, the
middle upper-bound estimate, and the `k ≥ 5` tail closes RH under the classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceSupportClassSideAndMiddle
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus the middle upper-bound estimate and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnlyTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleOnly
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus positive-middle-determinant cancellation
and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellationTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetCancellation
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus positive-middle side allocation and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocationTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetSideAllocation
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus positive-middle geometric-mean domination
and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMeanTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetGeometricMean
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus factorized positive-middle log-convexity
and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexity
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexityTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetFactorizedLogConvexity
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus the support-aware top-right split and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplitTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightSupportSplit
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus the three-way top-right support split and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplitTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightThreeWaySplit
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus the moment/cofactor-ratio three-way
support theorem and the `k ≥ 5` tail closes RH under classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplitTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightMomentCofactorRatioThreeWaySplit
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus a subtraction-free contiguous-minor
certificate for the three-way support theorem and the `k ≥ 5` tail closes RH
under classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplitTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightPositivePolynomialCertificateThreeWaySplit
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus the normalized moment/cofactor-ratio
three-way support theorem and the `k ≥ 5` tail closes RH under classical
scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplitTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominancePositiveMiddleDetTopRightNormalizedMomentCofactorRatioThreeWaySplit
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus middle cofactor determinant
nonpositivity and the `k ≥ 5` tail closes RH under the classical scaffolding.
-/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSignTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSign
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus the support-split middle determinant
sign target and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplitTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetSupportSplit
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus full-support middle determinant zero,
banded middle determinant nonpositivity, and the `k ≥ 5` tail closes RH under
the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBandedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullZeroBanded
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, banded middle determinant nonpositivity, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBanded
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, expanded sparse banded middle determinant nonpositivity, and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpandedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedExpanded
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, banded middle product dominance, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProductTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedProduct
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, banded middle bracket signs, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSignsTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedBracketSigns
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, split banded middle bracket signs, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBracketsTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedSplitBrackets
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, a top-support split of the banded middle bracket signs, and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBracketsTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportSplitBrackets
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, a top-unsupported
banded branch, and the `k ≥ 5` tail closes RH under the classical scaffolding.
-/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMomentTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopSupportedMoment
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets,
top-unsupported/middle-supported banded brackets, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupported
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets,
top-unsupported/middle-supported moment products, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProductTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedMomentProduct
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, split
top-unsupported/middle-supported moment products, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProductsTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedSplitProducts
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, left
top-unsupported/middle-supported moment product, and the `k ≥ 5` tail closes
RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProductTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftProduct
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, vanishing of one
left-product moment factor in the top-unsupported/middle-supported branch, and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZeroTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedLeftMomentZero
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, impossibility of
the top-unsupported/middle-supported branch, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossibleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedImpossible
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, contextual
gap-collapse for the top-unsupported/middle-supported branch, and the `k ≥ 5`
tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapseTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedGapCollapse
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, original-index
gap-collapse `cols 3 ≤ rows 2` for the top-unsupported/middle-supported
branch, and the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapseTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedOriginalGapCollapse
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, inactive
side-support witnesses for the top-unsupported/middle-supported branch, and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupportTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedInactiveSideSupport
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, a right-side
inactive support witness for the top-unsupported/middle-supported branch, and
the `k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupportTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightInactiveSideSupport
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, exclusion of the
two active `j = 2` right-side cases in the remaining branch, and the `k ≥ 5`
tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcludedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightActiveExcluded
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, exclusion of the
right-side banded case in the remaining branch, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcludedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedRightBandedExcluded
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, emptiness of the
top-unsupported/middle-supported branch, and the `k ≥ 5` tail closes RH under
the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossibleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleSupportedBranchImpossible
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, middle-column
unsupportedness in the top-unsupported branch, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupportedTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnUnsupported
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, exclusion of the
middle/top-column straddle interval in the top-unsupported branch, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnNoStraddle
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, contradiction of
the middle/top-column straddle interval in the top-unsupported branch, and the
`k ≥ 5` tail closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossibleTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleImpossible
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, a nonpositive
left moment product in the straddle branch, and the `k ≥ 5` tail closes RH
under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProductTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftProduct
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

set_option linter.style.longLine false in
/-- Contiguous kernel positivity plus moment-index full-support middle
determinant zero, moment-index top-supported banded brackets, a nonpositive
native Toeplitz left bracket in the straddle branch, and the `k ≥ 5` tail
closes RH under the classical scaffolding. -/
theorem riemannHypothesis_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket
    (S : ClassicalToeplitzScaffolding)
    (T :
      KernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracketTheorem) :
    RiemannHypothesis :=
  have hPF : XiToeplitzTotalPositive :=
    xiToeplitzTotalPositive_of_kernelContigToPFJ1StructuralReducedRowsMiddleDominanceMiddleDetFullMomentZeroBandedTopUnsupportedMiddleColumnStraddleLeftBracket
      T
  riemannHypothesis_of_pf_and_classical_inputs hPF S.asw S.lp S.polyaJensen

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

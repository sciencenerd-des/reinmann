/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.GrassmannSyzygy
import Reinmann.FeketeRowGap

/-!
# All-orders Fekete induction for initial-column minors

This module runs Fekete's gap-shrinking induction at **every** order, powered
by the generic Grassmann three-term identity of `Reinmann/GrassmannSyzygy.lean`.

## Headline

`xiInitialMinor_pos_of_strictLadder`: if every contiguous Toeplitz minor of the
signed xi moment sequence is **strictly** positive
(`XiContigToeplitzStrictPositive`), then every arbitrary-row initial-column
minor, of every order, is strictly positive.  In particular the named targets
`XiInitialColumnMinorTotalPositive`, `XiInitialColumnMinorThreeFromContig`,
`XiInitialColumnMinorGeFourFromContig`, and
`XiInitialColumnMinorGeFiveFromContig` all follow from this single strictness
hypothesis.

The induction is joint: an outer induction on the order `k` (each order divides
by a strict order-`(k-1)` arbitrary-row minor) and an inner induction on the
row dispersion (each three-term application shrinks the span by at least one,
landing on the contiguous ladder).

The strict ladder hypothesis subsumes the previous granular inputs: its
`k = 1` rung is strict coefficient positivity and its `k = 2` rung is the
classical strict Turán inequality (`xiMomentStrictTuran_of_strictLadder`).

## What remains open

RH is **not** proved.  After this module the open surface of the
initial-column route is exactly:

* `XiContigToeplitzStrictPositive` — the strict contiguous ladder.  This is
  RH-adjacent: no unconditional proof is known.  Interval scans support it.
* `XiInitialColumnMinorToFullPFBridge` — Cryer's lower-triangular
  initial-column criterion (classical, unformalized).
* `XiMomentKernelRep` — Pólya's kernel representation (classical,
  unformalized).
-/

noncomputable section

open Matrix

namespace Reinmann

/-! ## The strict contiguous ladder -/

/-- **The strict contiguous ladder**: every contiguous Toeplitz minor of the
signed xi moment sequence is strictly positive.  This is a strict refinement of
`XiContigToeplitzTotalPositive`; the `k = 1` rung is strict coefficient
positivity and the `k = 2` rung is the classical strict Turán inequality. -/
def XiContigToeplitzStrictPositive : Prop :=
  ∀ k : ℕ, XiContigMinorStrictPositiveAt k

theorem xiContigToeplitzTotalPositive_of_strictLadder
    (h : XiContigToeplitzStrictPositive) : XiContigToeplitzTotalPositive :=
  fun k m => le_of_lt (h k m)

/-- The `k = 1` rung of the strict ladder is strict positivity of every signed
moment coefficient. -/
theorem xiMomentCoeffPositive_of_strictLadder
    (h : XiContigToeplitzStrictPositive) : XiMomentCoeffPositive := by
  intro n
  have h1 := h 1 n
  unfold XiToeplitzContigMinor at h1
  rw [Matrix.det_fin_one] at h1
  simpa [XiToeplitzEntry] using h1

/-- The `k = 2` rung of the strict ladder is the classical strict Turán
inequality (Csordas–Norfolk–Varga). -/
theorem xiMomentStrictTuran_of_strictLadder
    (h : XiContigToeplitzStrictPositive) : XiMomentStrictTuran := by
  intro n
  have h2 := h 2 (n + 1)
  rw [← xiToeplitzMinor2_eq_contig n] at h2
  unfold XiToeplitzMinor2 at h2
  nlinarith

/-! ## Initial-column minors of every order -/

/-- The arbitrary-row initial-column minor of order `k`. -/
def XiInitialMinor (k : ℕ) (rows : Fin k → ℕ) : ℝ :=
  (Matrix.of (fun i j : Fin k => XiToeplitzEntry (rows i) j.val)).det

/-- `maxMinor` of the Toeplitz family is an initial-column minor. -/
theorem maxMinor_eq_xiInitialMinor {q : ℕ} (ρ : Fin (q + 3) → ℕ) (i : Fin (q + 3)) :
    maxMinor (fun i' (b : Fin (q + 2)) => XiToeplitzEntry (ρ i') (b : ℕ)) i =
      XiInitialMinor (q + 2) (fun a => ρ (i.succAbove a)) := rfl

/-- `subMinor` of the Toeplitz family is an initial-column minor. -/
theorem subMinor_eq_xiInitialMinor {q : ℕ} (ρ : Fin (q + 3) → ℕ)
    (e : Fin (q + 1) → Fin (q + 3)) :
    subMinor (fun i' (b : Fin (q + 2)) => XiToeplitzEntry (ρ i') (b : ℕ)) e =
      XiInitialMinor (q + 1) (fun a => ρ (e a)) := rfl

/-! ## Arithmetic helpers -/

/-- Strictly monotone `Fin`-indexed naturals grow at least linearly. -/
theorem strictMono_val_le {K : ℕ} {rows : Fin K → ℕ} (h : StrictMono rows) :
    ∀ n : ℕ, ∀ a b : Fin K, (b : ℕ) = (a : ℕ) + n → rows a + n ≤ rows b := by
  intro n
  induction n with
  | zero =>
      intro a b hb
      have hba : b = a := Fin.ext (by omega)
      subst hba
      simp
  | succ n ih =>
      intro a b hb
      obtain ⟨b', hb'⟩ : ∃ b' : Fin K, (b' : ℕ) = (a : ℕ) + n :=
        ⟨⟨(a : ℕ) + n, by have := b.isLt; omega⟩, rfl⟩
      have h1 := ih a b' hb'
      have h2 : rows b' < rows b := h (by rw [Fin.lt_def]; omega)
      omega

/-- A strictly monotone row selection with minimal span is contiguous. -/
theorem rows_eq_add_of_span {K : ℕ} (rows : Fin (K + 1) → ℕ) (hRows : StrictMono rows)
    (hspan : rows (Fin.last K) ≤ rows 0 + K) (i : Fin (K + 1)) :
    rows i = rows 0 + (i : ℕ) := by
  have hi := i.isLt
  have h0v : ((0 : Fin (K + 1)) : ℕ) = 0 := rfl
  have hlv : ((Fin.last K : Fin (K + 1)) : ℕ) = K := rfl
  have hlow : rows 0 + (i : ℕ) ≤ rows i :=
    strictMono_val_le hRows (i : ℕ) 0 i (by omega)
  have hup : rows i + (K - (i : ℕ)) ≤ rows (Fin.last K) :=
    strictMono_val_le hRows (K - (i : ℕ)) i (Fin.last K) (by omega)
  omega

/-- Contiguous specialization: a minimal-span minor is a ladder minor. -/
theorem xiInitialMinor_contig_of_span {K : ℕ} (rows : Fin (K + 1) → ℕ)
    (hRows : StrictMono rows) (hspan : rows (Fin.last K) ≤ rows 0 + K) :
    XiInitialMinor (K + 1) rows = XiToeplitzContigMinor (K + 1) (rows 0) := by
  unfold XiInitialMinor XiToeplitzContigMinor
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [rows_eq_add_of_span rows hRows hspan i]

/-- Inserting a value strictly between the surrounding rows preserves strict
monotonicity. -/
theorem strictMono_insertNth {K : ℕ} {rows : Fin (K + 1) → ℕ} (hRows : StrictMono rows)
    (t : Fin (K + 2)) (s : ℕ)
    (hlow : ∀ a : Fin (K + 1), (a : ℕ) < (t : ℕ) → rows a < s)
    (hhigh : ∀ a : Fin (K + 1), (t : ℕ) ≤ (a : ℕ) → s < rows a) :
    StrictMono (t.insertNth s rows) := by
  intro i j hij
  by_cases hi : i = t
  · by_cases hj : j = t
    · rw [hi, hj] at hij
      exact absurd hij (lt_irrefl t)
    · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hj
      rw [hi, ← hb, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      apply hhigh
      have hv : (t : ℕ) < ((t.succAbove b : Fin (K + 2)) : ℕ) := by
        rw [hi, ← hb] at hij
        exact hij
      rw [val_succAbove] at hv
      split_ifs at hv <;> omega
  · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hi
    by_cases hj : j = t
    · rw [hj, ← hb, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      apply hlow
      have hv : ((t.succAbove b : Fin (K + 2)) : ℕ) < (t : ℕ) := by
        rw [hj, ← hb] at hij
        exact hij
      rw [val_succAbove] at hv
      split_ifs at hv <;> omega
    · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hj
      rw [← hb, ← hc, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      apply hRows
      have hv : ((t.succAbove b : Fin (K + 2)) : ℕ) < ((t.succAbove c : Fin (K + 2)) : ℕ) := by
        rw [← hb, ← hc] at hij
        exact hij
      rw [Fin.lt_def]
      rw [val_succAbove, val_succAbove] at hv
      split_ifs at hv <;> omega

/-! ## The all-orders Fekete induction -/

/-- **All-orders Fekete theorem.**  Under the strict contiguous ladder, every
arbitrary-row initial-column Toeplitz minor of every order is strictly
positive.  Joint induction: outer on the order, inner on the row dispersion,
with the generic Grassmann three-term identity shrinking one gap per step. -/
theorem xiInitialMinor_pos_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) :
    ∀ (k : ℕ) (rows : Fin k → ℕ), StrictMono rows → 0 < XiInitialMinor k rows := by
  intro k
  induction k with
  | zero =>
      intro rows _
      unfold XiInitialMinor
      rw [Matrix.det_fin_zero]
      exact zero_lt_one
  | succ k ihk =>
      cases k with
      | zero =>
          intro rows _
          unfold XiInitialMinor
          rw [Matrix.det_fin_one]
          have h1 := hLadder 1 (rows 0)
          unfold XiToeplitzContigMinor at h1
          rw [Matrix.det_fin_one] at h1
          simpa using h1
      | succ q =>
          suffices hd : ∀ d : ℕ, ∀ rows : Fin (q + 2) → ℕ, StrictMono rows →
              rows (Fin.last (q + 1)) ≤ rows 0 + (q + 1) + d →
              0 < XiInitialMinor (q + 2) rows by
            intro rows hRows
            exact hd (rows (Fin.last (q + 1))) rows hRows (by omega)
          intro d
          induction d with
          | zero =>
              intro rows hRows hspan
              rw [xiInitialMinor_contig_of_span rows hRows (by omega)]
              exact hLadder (q + 2) (rows 0)
          | succ d ihd =>
              intro rows hRows hspan
              by_cases hin : rows (Fin.last (q + 1)) ≤ rows 0 + (q + 1) + d
              · exact ihd rows hRows hin
              -- there is an adjacent gap
              obtain ⟨g, hg⟩ : ∃ g : Fin (q + 1), rows g.castSucc + 1 < rows g.succ := by
                by_contra hng
                push Not at hng
                have hstep : ∀ j : Fin (q + 2), rows j ≤ rows 0 + (j : ℕ) := by
                  intro j
                  induction j using Fin.induction with
                  | zero => simp
                  | succ i ih =>
                      have h1 := hng i
                      have h2 : ((i.succ : Fin (q + 2)) : ℕ) = (i : ℕ) + 1 := rfl
                      have h3 : ((i.castSucc : Fin (q + 2)) : ℕ) = (i : ℕ) := rfl
                      omega
                have hlast := hstep (Fin.last (q + 1))
                have hlv : ((Fin.last (q + 1) : Fin (q + 2)) : ℕ) = q + 1 := rfl
                omega
              have hgv : ((g.castSucc : Fin (q + 2)) : ℕ) = (g : ℕ) := rfl
              have hgs : ((g.succ : Fin (q + 2)) : ℕ) = (g : ℕ) + 1 := rfl
              have hglt := g.isLt
              have h0v3 : ((0 : Fin (q + 3)) : ℕ) = 0 := rfl
              have hl3v : ((Fin.last (q + 2) : Fin (q + 3)) : ℕ) = q + 2 := rfl
              have hl2v : ((Fin.last (q + 1) : Fin (q + 2)) : ℕ) = q + 1 := rfl
              -- the insertion position and inserted value
              obtain ⟨t, htv⟩ : ∃ t : Fin (q + 3), (t : ℕ) = (g : ℕ) + 1 :=
                ⟨⟨(g : ℕ) + 1, by omega⟩, rfl⟩
              have ht0 : 0 < t := by
                rw [Fin.lt_def]
                omega
              have htl : t < Fin.last (q + 2) := by
                rw [Fin.lt_def]
                omega
              set s : ℕ := rows g.castSucc + 1 with hs
              set ρ : Fin (q + 3) → ℕ := t.insertNth s rows with hρ
              have hρmono : StrictMono ρ := by
                apply strictMono_insertNth hRows
                · intro a ha
                  have := strictMono_val_le hRows ((g : ℕ) - (a : ℕ)) a g.castSucc
                    (by omega)
                  omega
                · intro a ha
                  have := strictMono_val_le hRows ((a : ℕ) - ((g : ℕ) + 1)) g.succ a
                    (by omega)
                  omega
              have hρrows : ∀ a : Fin (q + 2), ρ (t.succAbove a) = rows a := by
                intro a
                rw [hρ]
                exact Fin.insertNth_apply_succAbove (α := fun _ => ℕ) t s rows a
              -- endpoints of the extended family
              have hρ0 : ρ 0 = rows 0 := by
                have h00 : t.succAbove 0 = 0 := by
                  apply Fin.ext
                  rw [val_succAbove]
                  have h4 : ((0 : Fin (q + 2)) : ℕ) = 0 := rfl
                  split_ifs <;> omega
                calc ρ 0 = ρ (t.succAbove 0) := by rw [h00]
                  _ = rows 0 := hρrows 0
              have hρlast : ρ (Fin.last (q + 2)) = rows (Fin.last (q + 1)) := by
                have hll : t.succAbove (Fin.last (q + 1)) = Fin.last (q + 2) := by
                  apply Fin.ext
                  rw [val_succAbove]
                  split_ifs <;> omega
                calc ρ (Fin.last (q + 2)) = ρ (t.succAbove (Fin.last (q + 1))) := by
                      rw [hll]
                  _ = rows (Fin.last (q + 1)) := hρrows _
              -- the three-term identity for the Toeplitz family
              have hkey := grassmann_three_term
                (fun i' (b : Fin (q + 2)) => XiToeplitzEntry (ρ i') (b : ℕ)) t ht0 htl
              simp only [maxMinor_eq_xiInitialMinor, subMinor_eq_xiInitialMinor] at hkey
              have htarget : (fun a => ρ (t.succAbove a)) = rows := funext hρrows
              rw [htarget] at hkey
              -- divisor and side sub-minors are strict by the order induction
              have hP : 0 < XiInitialMinor (q + 1) (fun a => ρ (dropEnds a)) :=
                ihk _ (fun _ _ hab => hρmono (strictMono_dropEnds hab))
              have hQ : 0 < XiInitialMinor (q + 1) (fun a => ρ (dropMidLast t a)) :=
                ihk _ (fun _ _ hab => hρmono (strictMono_dropMidLast t hab))
              have hR : 0 < XiInitialMinor (q + 1) (fun a => ρ (dropZeroMid t a)) :=
                ihk _ (fun _ _ hab => hρmono (strictMono_dropZeroMid t hab))
              -- the two flanking order-(q+2) minors have smaller dispersion
              have hA : 0 < XiInitialMinor (q + 2)
                  (fun a => ρ ((0 : Fin (q + 3)).succAbove a)) := by
                refine ihd _ (fun _ _ hab => hρmono (Fin.strictMono_succAbove 0 hab)) ?_
                have he1 : (0 : Fin (q + 3)).succAbove (Fin.last (q + 1)) =
                    Fin.last (q + 2) := by
                  apply Fin.ext
                  rw [val_succAbove]
                  split_ifs <;> omega
                have hgt : ρ 0 < ρ ((0 : Fin (q + 3)).succAbove 0) := by
                  apply hρmono
                  rw [Fin.lt_def, val_succAbove]
                  have h4 : ((0 : Fin (q + 2)) : ℕ) = 0 := rfl
                  split_ifs <;> omega
                rw [he1, hρlast]
                rw [hρ0] at hgt
                omega
              have hB : 0 < XiInitialMinor (q + 2)
                  (fun a => ρ ((Fin.last (q + 2)).succAbove a)) := by
                refine ihd _
                  (fun _ _ hab => hρmono (Fin.strictMono_succAbove (Fin.last (q + 2)) hab)) ?_
                have he0 : (Fin.last (q + 2)).succAbove 0 = 0 := by
                  apply Fin.ext
                  rw [val_succAbove]
                  have h4 : ((0 : Fin (q + 2)) : ℕ) = 0 := rfl
                  split_ifs <;> omega
                have helt : ρ ((Fin.last (q + 2)).succAbove (Fin.last (q + 1))) <
                    ρ (Fin.last (q + 2)) := by
                  apply hρmono
                  rw [Fin.lt_def, val_succAbove]
                  split_ifs <;> omega
                rw [he0, hρ0]
                rw [hρlast] at helt
                omega
              nlinarith [hkey, hP, mul_pos hA hQ, mul_pos hB hR]

/-! ## Named-target corollaries -/

/-- **The full initial-column total positivity condition holds under the strict
contiguous ladder.**  This discharges, in one theorem, the previously named
row-gap targets at every order. -/
theorem xiInitialColumnMinorTotalPositive_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) :
    XiInitialColumnMinorTotalPositive := by
  intro k rows hRows
  have h := xiInitialMinor_pos_of_strictLadder hLadder k rows hRows
  unfold XiInitialMinor at h
  exact le_of_lt h

/-- The contiguous-to-initial-column bridge holds under the strict ladder. -/
theorem xiContigToInitialColumnMinorBridge_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) :
    XiContigToInitialColumnMinorBridge :=
  fun _ => xiInitialColumnMinorTotalPositive_of_strictLadder hLadder

/-- Order-three target from the strict ladder alone. -/
theorem xiInitialColumnMinorThreeFromContig_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) :
    XiInitialColumnMinorThreeFromContig :=
  fun rows hRows _ =>
    xiInitialColumnMinorTotalPositive_of_strictLadder hLadder 3 rows hRows

/-- The whole `k ≥ 4` tail from the strict ladder alone. -/
theorem xiInitialColumnMinorGeFourFromContig_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) :
    XiInitialColumnMinorGeFourFromContig :=
  fun k _ rows hRows _ =>
    xiInitialColumnMinorTotalPositive_of_strictLadder hLadder k rows hRows

/-- The `k ≥ 5` tail from the strict ladder alone. -/
theorem xiInitialColumnMinorGeFiveFromContig_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) :
    XiInitialColumnMinorGeFiveFromContig :=
  fun k _ rows hRows _ =>
    xiInitialColumnMinorTotalPositive_of_strictLadder hLadder k rows hRows

/-! ## Capstone wiring -/

/-- **The sharpest capstone constructor so far.**  The open surface of
`KernelContigToPFInitialColumnGeFourTheorem` shrinks to: Pólya's kernel data,
the **strict contiguous ladder**, and Cryer's initial-column criterion.  Every
arbitrary-row condition — order three, order four, and the whole tail — is now
a theorem. -/
def kernelContigToPFInitialColumnGeFourTheorem_of_strictLadder
    (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (hLadder : XiContigToeplitzStrictPositive)
    (hCriterion : XiInitialColumnMinorToFullPFBridge) :
    KernelContigToPFInitialColumnGeFourTheorem where
  M := M
  positive := hMpos
  kernelRep := hM
  contig := (xiContigToeplitzTotalPositive_iff_kernelContig hM).mp
    (xiContigToeplitzTotalPositive_of_strictLadder hLadder)
  initialColumnsThree := xiInitialColumnMinorThreeFromContig_of_strictLadder hLadder
  initialColumnsGeFour := xiInitialColumnMinorGeFourFromContig_of_strictLadder hLadder
  initialColumnsToPF := hCriterion

/-- **The sharpest end-to-end conditional reduction so far.**  RH follows from:
the classical Toeplitz scaffolding, Pólya's kernel data, the **strict
contiguous ladder**, and Cryer's initial-column criterion.  All arbitrary-row
positivity conditions — formerly the named frontier — are supplied by the
all-orders Fekete theorem.  This is still conditional: none of the four inputs
is proved here, and the strict ladder is RH-adjacent. -/
theorem riemannHypothesis_of_strictLadder_and_criterion
    (S : ClassicalToeplitzScaffolding)
    (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n)
    (hM : ∀ n, XiCoeff n = (-1) ^ n * (2 * M n / ((2 * n).factorial : ℝ)))
    (hLadder : XiContigToeplitzStrictPositive)
    (hCriterion : XiInitialColumnMinorToFullPFBridge) :
    RiemannHypothesis :=
  riemannHypothesis_of_kernelContigToPFInitialColumnGeFour S
    (kernelContigToPFInitialColumnGeFourTheorem_of_strictLadder
      M hMpos hM hLadder hCriterion)

end Reinmann

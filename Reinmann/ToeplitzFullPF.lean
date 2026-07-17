/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FeketeAllOrders
import Reinmann.RHReductionCapstone

/-!
# Full Pólya-frequency positivity from the strict contiguous ladder

This module removes **Cryer's initial-column criterion** and **Pólya's kernel
representation** from the sharpest conditional reduction: the strict contiguous
ladder alone implies the full arbitrary-row/arbitrary-column Pólya-frequency
condition `XiToeplitzTotalPositive`.

## Mechanism

Every minor obeys a **dominance dichotomy**:

* if some `a` has `rows a < cols a`, the minor vanishes
  (`xiMinor_eq_zero_of_lt`, a permutation-pigeonhole argument on the zero
  pattern of the lower-triangular Toeplitz matrix);
* otherwise (`cols a ≤ rows a` for all `a`) the minor is **strictly** positive
  (`xiMinor_pos_of_dominant`).

The dominant case is another Fekete gap-shrinking induction (outer on the
order, inner on the row dispersion), now with the columns fixed but arbitrary.
Its base case — contiguous rows, arbitrary columns — reduces to the
initial-column theorem of `Reinmann/FeketeAllOrders.lean` by the Toeplitz
**reversal symmetry** (`xiMinor_contigRows`): reversing both row and column
orders and transposing turns a contiguous-row minor into an arbitrary-row
initial-column minor.  In the induction step the only possibly-degenerate term
is the drop-last-row flanking minor, and there the dichotomy supplies `≥ 0`.

## Headlines

* `xiToeplitzTotalPositive_of_strictLadder` — the strict ladder implies the
  full RH-equivalent PF condition.  **RH-strength warning**: with the classical
  scaffolding, `XiToeplitzTotalPositive` is equivalent to RH, so the strict
  ladder is at least RH-strength; it must never be assumed or axiomatized.
* `riemannHypothesis_of_strictLadder` — the sharpest end-to-end conditional
  reduction: RH follows from the classical scaffolding plus the strict ladder,
  with **no** initial-column criterion and **no** kernel representation.

RH remains unproved: `XiContigToeplitzStrictPositive` and the four classical
scaffolding bridges are the remaining named inputs.
-/

noncomputable section

open Matrix

namespace Reinmann

/-! ## Arbitrary minors and the dominance dichotomy -/

/-- The arbitrary Toeplitz minor with selected rows and columns. -/
def XiMinor (k : ℕ) (rows cols : Fin k → ℕ) : ℝ :=
  (Matrix.of (fun a b : Fin k => XiToeplitzEntry (rows a) (cols b))).det

theorem xiMinor_congr_rows {k : ℕ} (rows rows' cols : Fin k → ℕ)
    (h : ∀ i, rows i = rows' i) :
    XiMinor k rows cols = XiMinor k rows' cols := by
  unfold XiMinor
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [h i]

/-- **Zero half of the dichotomy.**  If some selected column index exceeds the
matching selected row index, the whole minor vanishes: every permutation term
contains an entry above the lower-triangular support, by pigeonhole. -/
theorem xiMinor_eq_zero_of_lt {k : ℕ} (rows cols : Fin k → ℕ)
    (hR : StrictMono rows) (hC : StrictMono cols)
    (a : Fin k) (ha : rows a < cols a) :
    XiMinor k rows cols = 0 := by
  classical
  unfold XiMinor
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hzero : ∃ i : Fin k, XiToeplitzEntry (rows (σ i)) (cols i) = 0 := by
    by_contra hno
    push Not at hno
    have hle : ∀ i : Fin k, cols i ≤ rows (σ i) := by
      intro i
      by_contra hlt
      push Not at hlt
      exact hno i (by unfold XiToeplitzEntry; rw [if_neg (by omega)])
    have hmaps : ∀ i : Fin k, a ≤ i → a < σ i := by
      intro i hi
      by_contra hle2
      push Not at hle2
      have h1 : cols a ≤ cols i := hC.monotone hi
      have h2 : rows (σ i) ≤ rows a := hR.monotone hle2
      have h3 := hle i
      omega
    have himg : (Finset.Ici a).image σ ⊆ Finset.Ioi a := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [Finset.mem_Ioi]
      exact hmaps i (Finset.mem_Ici.mp hi)
    have hcard := Finset.card_le_card himg
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Ici, Fin.card_Ioi] at hcard
    have hak := a.isLt
    omega
  obtain ⟨i, hi⟩ := hzero
  have hprod : (∏ x : Fin k,
      (Matrix.of (fun a b : Fin k => XiToeplitzEntry (rows a) (cols b))) (σ x) x) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  rw [hprod, smul_zero]

/-! ## The Toeplitz reversal symmetry -/

/-- **Reversal symmetry.**  A contiguous-row minor with arbitrary dominated
columns equals an arbitrary-row initial-column minor: reverse both index
orders and transpose.  This turns the base case of the arbitrary-column
induction into the already-proved initial-column theorem. -/
theorem xiMinor_contigRows {K : ℕ} (m : ℕ) (C : Fin (K + 1) → ℕ)
    (hdom : ∀ a, C a ≤ m + (a : ℕ)) :
    XiMinor (K + 1) (fun a => m + (a : ℕ)) C =
      XiInitialMinor (K + 1) (fun b => m + K - C b.rev) := by
  unfold XiMinor XiInitialMinor
  have hmat : (Matrix.of fun a b : Fin (K + 1) =>
      XiToeplitzEntry (m + (a : ℕ)) (C b)) =
      ((Matrix.of fun i j : Fin (K + 1) =>
        XiToeplitzEntry (m + K - C i.rev) (j : ℕ)).submatrix
          (Fin.revPerm : Equiv.Perm (Fin (K + 1))) Fin.revPerm)ᵀ := by
    ext a b
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Fin.revPerm_apply, Fin.rev_rev]
    have hCb : C b ≤ m + K := le_trans (hdom b) (by have := b.isLt; omega)
    have hra : ((a.rev : Fin (K + 1)) : ℕ) = K - (a : ℕ) := by
      rw [Fin.val_rev]
      omega
    rw [hra]
    unfold XiToeplitzEntry
    have hb := b.isLt
    have haa := a.isLt
    split_ifs <;> first
      | rfl
      | (congr 1; omega)
  rw [hmat, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]

/-! ## The dominant case: strict positivity -/

/-- `maxMinor` of the two-parameter Toeplitz family is an arbitrary minor. -/
theorem maxMinor_eq_xiMinor {q : ℕ} (ρ : Fin (q + 3) → ℕ) (cols : Fin (q + 2) → ℕ)
    (i : Fin (q + 3)) :
    maxMinor (fun i' (b : Fin (q + 2)) => XiToeplitzEntry (ρ i') (cols b)) i =
      XiMinor (q + 2) (fun a => ρ (i.succAbove a)) cols := rfl

/-- `subMinor` of the two-parameter Toeplitz family is an arbitrary minor with
the last column dropped. -/
theorem subMinor_eq_xiMinor {q : ℕ} (ρ : Fin (q + 3) → ℕ) (cols : Fin (q + 2) → ℕ)
    (e : Fin (q + 1) → Fin (q + 3)) :
    subMinor (fun i' (b : Fin (q + 2)) => XiToeplitzEntry (ρ i') (cols b)) e =
      XiMinor (q + 1) (fun a => ρ (e a)) (fun b => cols b.castSucc) := rfl

/-- **Positive half of the dichotomy.**  Under the strict contiguous ladder,
every dominated arbitrary minor is strictly positive.  Fekete induction with
fixed arbitrary columns; the base case is the reversal symmetry into the
initial-column theorem. -/
theorem xiMinor_pos_of_dominant
    (hLadder : XiContigToeplitzStrictPositive) :
    ∀ (k : ℕ) (cols rows : Fin k → ℕ), StrictMono cols → StrictMono rows →
      (∀ a, cols a ≤ rows a) → 0 < XiMinor k rows cols := by
  intro k
  induction k with
  | zero =>
      intro cols rows _ _ _
      unfold XiMinor
      rw [Matrix.det_fin_zero]
      exact zero_lt_one
  | succ k ihk =>
      cases k with
      | zero =>
          intro cols rows _ _ hdom
          unfold XiMinor
          rw [Matrix.det_fin_one]
          simp only [Matrix.of_apply]
          rw [xiToeplitzEntry_sub _ _ (hdom 0)]
          exact xiMomentCoeffPositive_of_strictLadder hLadder _
      | succ q =>
          suffices hd : ∀ d : ℕ, ∀ cols rows : Fin (q + 2) → ℕ,
              StrictMono cols → StrictMono rows →
              (∀ a, cols a ≤ rows a) →
              rows (Fin.last (q + 1)) ≤ rows 0 + (q + 1) + d →
              0 < XiMinor (q + 2) rows cols by
            intro cols rows hC hR hdom
            exact hd (rows (Fin.last (q + 1))) cols rows hC hR hdom (by omega)
          intro d
          induction d with
          | zero =>
              intro cols rows hC hR hdom hspan
              have hrw := rows_eq_add_of_span rows hR (by omega)
              rw [xiMinor_congr_rows rows (fun a => rows 0 + (a : ℕ)) cols hrw]
              have hdom' : ∀ a, cols a ≤ rows 0 + (a : ℕ) := by
                intro a
                have := hdom a
                rw [hrw a] at this
                exact this
              rw [xiMinor_contigRows (rows 0) cols hdom']
              apply xiInitialMinor_pos_of_strictLadder hLadder
              intro b b' hbb
              change rows 0 + (q + 1) - cols b.rev < rows 0 + (q + 1) - cols b'.rev
              have hbK := b.isLt
              have hbK' := b'.isLt
              have hrb : ((b.rev : Fin (q + 2)) : ℕ) = q + 1 - (b : ℕ) := by
                rw [Fin.val_rev]; omega
              have hrb' : ((b'.rev : Fin (q + 2)) : ℕ) = q + 1 - (b' : ℕ) := by
                rw [Fin.val_rev]; omega
              have hrevlt : b'.rev < b.rev := by
                rw [Fin.lt_def, hrb, hrb']
                have : (b : ℕ) < (b' : ℕ) := hbb
                omega
              have hClt : cols b'.rev < cols b.rev := hC hrevlt
              have hub : cols b.rev ≤ rows 0 + (q + 1) := by
                have := hdom' b.rev
                rw [hrb] at this
                omega
              omega
          | succ d ihd =>
              intro cols rows hC hR hdom hspan
              by_cases hin : rows (Fin.last (q + 1)) ≤ rows 0 + (q + 1) + d
              · exact ihd cols rows hC hR hdom hin
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
                apply strictMono_insertNth hR
                · intro a ha
                  have := strictMono_val_le hR ((g : ℕ) - (a : ℕ)) a g.castSucc
                    (by omega)
                  omega
                · intro a ha
                  have := strictMono_val_le hR ((a : ℕ) - ((g : ℕ) + 1)) g.succ a
                    (by omega)
                  omega
              have hρrows : ∀ a : Fin (q + 2), ρ (t.succAbove a) = rows a := by
                intro a
                rw [hρ]
                exact Fin.insertNth_apply_succAbove (α := fun _ => ℕ) t s rows a
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
              -- row values dominate through the insertion
              have hρge : ∀ a : Fin (q + 2), ∀ x : Fin (q + 3),
                  (a : ℕ) + 1 ≤ (x : ℕ) → rows a ≤ ρ x := by
                intro a x hx
                rw [← hρrows a]
                apply hρmono.monotone
                rw [Fin.le_def, val_succAbove]
                split_ifs <;> omega
              -- embedding identifications: the sub-minors drop rows cleanly
              have hdropML : ∀ a : Fin (q + 1), ρ (dropMidLast t a) = rows a.castSucc := by
                intro a
                have he : dropMidLast t a = t.succAbove a.castSucc := by
                  apply Fin.ext
                  rw [val_dropMidLast, val_succAbove]
                  have h4 : ((a.castSucc : Fin (q + 2)) : ℕ) = (a : ℕ) := rfl
                  split_ifs <;> omega
                rw [he, hρrows]
              have hdropZM : ∀ a : Fin (q + 1), ρ (dropZeroMid t a) = rows a.succ := by
                intro a
                have he : dropZeroMid t a = t.succAbove a.succ := by
                  apply Fin.ext
                  rw [val_dropZeroMid, val_succAbove]
                  have h4 : ((a.succ : Fin (q + 2)) : ℕ) = (a : ℕ) + 1 := rfl
                  split_ifs <;> omega
                rw [he, hρrows]
              -- restricted columns
              have hCcast : StrictMono (fun b : Fin (q + 1) => cols b.castSucc) := by
                intro x y hxy
                apply hC
                rw [Fin.lt_def]
                exact hxy
              -- the generic three-term identity
              have hkey := grassmann_three_term
                (fun i' (b : Fin (q + 2)) => XiToeplitzEntry (ρ i') (cols b)) t ht0 htl
              simp only [maxMinor_eq_xiMinor, subMinor_eq_xiMinor] at hkey
              have htarget : (fun a => ρ (t.succAbove a)) = rows := funext hρrows
              rw [htarget] at hkey
              -- the divisor: rows strictly inside, dominant
              have hP : 0 < XiMinor (q + 1) (fun a => ρ (dropEnds a))
                  (fun b => cols b.castSucc) := by
                apply ihk _ _ hCcast
                  (fun _ _ hab => hρmono (strictMono_dropEnds hab))
                intro a
                have h1 : cols a.castSucc ≤ rows a.castSucc := hdom a.castSucc
                have h2 : rows a.castSucc ≤ ρ (dropEnds a) := by
                  apply hρge
                  rw [val_dropEnds]
                  have h4 : ((a.castSucc : Fin (q + 2)) : ℕ) = (a : ℕ) := rfl
                  omega
                omega
              -- the two dropped-row side minors, dominant
              have hQ : 0 < XiMinor (q + 1) (fun a => ρ (dropMidLast t a))
                  (fun b => cols b.castSucc) := by
                apply ihk _ _ hCcast
                  (fun _ _ hab => hρmono (strictMono_dropMidLast t hab))
                intro a
                rw [hdropML a]
                exact hdom a.castSucc
              have hRpos : 0 < XiMinor (q + 1) (fun a => ρ (dropZeroMid t a))
                  (fun b => cols b.castSucc) := by
                apply ihk _ _ hCcast
                  (fun _ _ hab => hρmono (strictMono_dropZeroMid t hab))
                intro a
                rw [hdropZM a]
                have h1 : cols a.castSucc ≤ cols a.succ := by
                  apply hC.monotone
                  rw [Fin.le_def]
                  have h4 : ((a.castSucc : Fin (q + 2)) : ℕ) = (a : ℕ) := rfl
                  have h5 : ((a.succ : Fin (q + 2)) : ℕ) = (a : ℕ) + 1 := rfl
                  omega
                have h2 := hdom a.succ
                omega
              -- the drop-first flanking minor: dominant, smaller dispersion
              have hA : 0 < XiMinor (q + 2)
                  (fun a => ρ ((0 : Fin (q + 3)).succAbove a)) cols := by
                refine ihd cols _ hC
                  (fun _ _ hab => hρmono (Fin.strictMono_succAbove 0 hab)) ?_ ?_
                · intro a
                  have h2 : rows a ≤ ρ ((0 : Fin (q + 3)).succAbove a) := by
                    apply hρge
                    rw [val_succAbove]
                    split_ifs <;> omega
                  have h1 := hdom a
                  omega
                · have he1 : (0 : Fin (q + 3)).succAbove (Fin.last (q + 1)) =
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
              -- the drop-last flanking minor: either dominant or zero
              have hB : 0 ≤ XiMinor (q + 2)
                  (fun a => ρ ((Fin.last (q + 2)).succAbove a)) cols := by
                have hmono : StrictMono (fun a : Fin (q + 2) =>
                    ρ ((Fin.last (q + 2)).succAbove a)) :=
                  fun _ _ hab => hρmono (Fin.strictMono_succAbove (Fin.last (q + 2)) hab)
                by_cases hdomB : ∀ a : Fin (q + 2),
                    cols a ≤ ρ ((Fin.last (q + 2)).succAbove a)
                · apply le_of_lt
                  refine ihd cols _ hC hmono hdomB ?_
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
                · push Not at hdomB
                  obtain ⟨a, ha⟩ := hdomB
                  rw [xiMinor_eq_zero_of_lt _ cols hmono hC a ha]
              nlinarith [hkey, hP, mul_pos hA hQ, mul_nonneg hB (le_of_lt hRpos)]

/-! ## The dichotomy assembled: full PF positivity -/

/-- **Full Pólya-frequency positivity from the strict contiguous ladder.**
Every arbitrary Toeplitz minor is nonnegative: dominated minors are strictly
positive, the rest vanish.

**RH-strength warning**: with the classical scaffolding,
`XiToeplitzTotalPositive` is equivalent to RH
(`xiToeplitzTotalPositive_iff_riemannHypothesis`), so the hypothesis
`XiContigToeplitzStrictPositive` is at least RH-strength.  It is a named open
input, never to be assumed. -/
theorem xiToeplitzTotalPositive_of_strictLadder
    (hLadder : XiContigToeplitzStrictPositive) : XiToeplitzTotalPositive := by
  intro k rows cols hR hC
  by_cases hdom : ∀ a, cols a ≤ rows a
  · have h := xiMinor_pos_of_dominant hLadder k cols rows hC hR hdom
    unfold XiMinor at h
    exact le_of_lt h
  · push Not at hdom
    obtain ⟨a, ha⟩ := hdom
    have h := xiMinor_eq_zero_of_lt rows cols hR hC a ha
    unfold XiMinor at h
    rw [h]

/-! ## The sharpest end-to-end conditional reduction -/

/-- **RH from the classical scaffolding and the strict contiguous ladder.**
Neither Cryer's initial-column criterion nor Pólya's kernel representation is
needed any longer: the whole positivity side of the reduction is the single
strict-ladder input.  This is still a conditional reduction, not a proof of
RH: the scaffolding bridges are classical-but-unformalized, and the strict
ladder is an open, at-least-RH-strength condition. -/
theorem riemannHypothesis_of_strictLadder
    (S : ClassicalToeplitzScaffolding)
    (hLadder : XiContigToeplitzStrictPositive) :
    RiemannHypothesis :=
  riemannHypothesis_of_pf_and_classical_inputs
    (xiToeplitzTotalPositive_of_strictLadder hLadder)
    S.asw S.lp S.polyaJensen

/-- With the scaffolding, the strict ladder squeezes between RH and RH:
it implies the RH-equivalent PF condition, and RH implies its nonnegative
relaxation.  Packaged to keep the strength labeling machine-checked. -/
theorem riemannHypothesis_iff_pf_and_strictLadder_implies
    (S : ClassicalToeplitzScaffolding)
    (hLadder : XiContigToeplitzStrictPositive) :
    RiemannHypothesis ∧ XiToeplitzTotalPositive :=
  ⟨riemannHypothesis_of_strictLadder S hLadder,
    xiToeplitzTotalPositive_of_strictLadder hLadder⟩

end Reinmann

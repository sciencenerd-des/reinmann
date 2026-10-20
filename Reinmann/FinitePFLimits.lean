/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.FinitePFBaseline
import Mathlib.Topology.Instances.Matrix

/-! Coefficientwise closure of finite Pólya frequency.
This is the limit step of the polynomial-sector route. It supplies neither
Schoenberg's polynomial theorem nor a canonical product for folded Xi. -/
noncomputable section
namespace Reinmann
open Filter

/-- Any coefficientwise limit of eventually PF-r sequences is PF-r.
All arbitrary minors are covered, including rank zero; contiguity is not assumed. -/
theorem finitePF_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {a : ℕ → ℝ} {f : ι → ℕ → ℝ} {r : ℕ}
    (hlim : ∀ n, Tendsto (fun t => f t n) l (nhds (a n)))
    (hpf : ∀ᶠ t in l, FinitePF (f t) r) : FinitePF a r := by
  intro k hk rows cols hr hc
  have hentry (i j : Fin k) :
      Tendsto (fun t => sequenceToeplitz (f t) (rows i) (cols j)) l
        (nhds (sequenceToeplitz a (rows i) (cols j))) := by
    simp only [sequenceToeplitz]
    split_ifs
    · exact hlim _
    · exact tendsto_const_nhds
  have hmatrix := tendsto_pi_nhds.mpr (fun i =>
    tendsto_pi_nhds.mpr (fun j => hentry i j))
  have hdet := (continuous_id.matrix_det.tendsto
    (Matrix.of fun i j : Fin k => sequenceToeplitz a (rows i) (cols j))).comp hmatrix
  exact isClosed_Ici.mem_of_tendsto hdet
    (hpf.mono (fun t ht => ht k hk rows cols hr hc))

end Reinmann

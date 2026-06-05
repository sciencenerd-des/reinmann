/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HilbertPolyaExperiment
import Reinmann.HilbertPolyaConstruction
import Reinmann.RiemannSpine

/-!
# Experiment E4a: Faithful Hilbert–Pólya Converse (finite form)

`riemannHypothesis_of_symmetric_eigendata` (Experiment B) shows that a symmetric
operator with eigenvalue `μ(s) = -i(s-1/2)` per critical-strip zero implies RH.
This file proves the *converse mechanism*: under RH the spectral parameter is real
and equals the height, and the diagonal construction (`diagOp`) realizes the
spectral data of the **actual** zeta zeros.

* `spectralParam_eq_im_of_re_half`: on the critical line `μ(s) = (Im s : ℂ)`.
* `exists_finite_eigendata_of_rh`: under RH, for any finite family of critical-strip
  zeros, there is a genuine symmetric operator with eigenvalue `μ(s i)` at each.

So the Hilbert–Pólya framework is *faithful* in finite form: RH ⇒ the eigendata
exists (realized by a real diagonal operator). The remaining step to a full `iff`
is the infinite (ℓ²) operator over the countable zero set — flagged, not faked.
-/

noncomputable section

open Complex

namespace Reinmann

/-- On the critical line the spectral parameter `μ(s) = -i(s-1/2)` is the real
number `Im s`. -/
theorem spectralParam_eq_im_of_re_half {s : ℂ} (hs : s.re = 1 / 2) :
    spectralParam s = (s.im : ℂ) := by
  unfold spectralParam
  apply Complex.ext
  · simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, hs]
  · simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, hs]

/-- **Faithful Hilbert–Pólya converse (finite).** Under RH, any finite family of
critical-strip zeros is realized by a symmetric operator carrying eigenvalue
`μ(s i)` at the `i`-th basis vector. -/
theorem exists_finite_eigendata_of_rh (hrh : RiemannHypothesis) {n : ℕ}
    (s : Fin n → ℂ) (hz : ∀ i, riemannZeta (s i) = 0)
    (hpos : ∀ i, 0 < (s i).re) (hlt : ∀ i, (s i).re < 1) :
    ∃ T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n),
      T.IsSymmetric ∧
        ∀ i : Fin n,
          T (EuclideanSpace.single i 1) = spectralParam (s i) • EuclideanSpace.single i 1 := by
  have hhalf : ∀ i, (s i).re = 1 / 2 := fun i =>
    (criticalStripObligations_of_riemannHypothesis hrh).strip_zero_on_line
      (s i) (hpos i) (hlt i) (hz i)
  refine ⟨diagOp (fun i => (s i).im), diagOp_isSymmetric _, fun i => ?_⟩
  rw [diagOp_eigen, spectralParam_eq_im_of_re_half (hhalf i)]

end Reinmann

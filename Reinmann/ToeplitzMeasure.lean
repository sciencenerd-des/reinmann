/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.ToeplitzFullRank
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Finite unit-circle measures representing Toeplitz matrices

Shared measure-theoretic consequences of the finite atomic representation.
No arithmetic positivity or infinite moment sequence is supplied.
-/

noncomputable section

namespace Reinmann.ToeplitzMeasure

open Matrix Polynomial MeasureTheory Reinmann.ToeplitzKernel Reinmann.ToeplitzAtomic
  Reinmann.ToeplitzExtension Reinmann.ToeplitzUniqueness
open scoped ComplexOrder ENNReal

/-- A finite positive Borel measure, concentrated on the unit circle, reproduces the entries. -/
structure Represents {n : ℕ} (T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (μ : Measure ℂ) : Prop where
  finite : IsFiniteMeasure μ
  circle : ∀ᵐ z ∂μ, ‖z‖ = 1
  entries : ∀ i j : Fin (n + 1), T i j = ∫ z, star (z ^ (i : ℕ)) * z ^ (j : ℕ) ∂μ

/-- Positive real weights interpreted as nonnegative Dirac masses. -/
def atomicMeasure (s : Finset ℂ) (w : ℂ → ℝ) : Measure ℂ :=
  ∑ z ∈ s, ENNReal.ofReal (w z) • Measure.dirac z

instance atomicMeasure_finite (s : Finset ℂ) (w : ℂ → ℝ) :
    IsFiniteMeasure (atomicMeasure s w) := by
  change IsFiniteMeasure (∑ z ∈ s, Real.toNNReal (w z) • Measure.dirac z)
  infer_instance

lemma integral_atomicMeasure (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ s, 0 ≤ w z) (f : ℂ → ℂ) :
    ∫ z, f z ∂atomicMeasure s w = ∑ z ∈ s, (w z : ℂ) * f z := by
  unfold atomicMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw z hz)]
    rfl
  · intro z _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma atomicMeasure_represents {n : ℕ} (s : Finset ℂ) (w : ℂ → ℝ)
    (hw : ∀ z ∈ s, ‖z‖ = 1 ∧ 0 ≤ w z) :
    Represents (atomicMatrix n s w) (atomicMeasure s w) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro z hz
    apply Measure.ae_smul_measure
    · simpa using (hw z hz).1
  · intro i j
    rw [integral_atomicMeasure s w (fun z hz => (hw z hz).2)]
    apply Finset.sum_congr rfl
    intro z _
    ring

/-- Every PSD Toeplitz matrix has a finite positive unit-circle representing measure. -/
theorem exists_representing_measure {n : ℕ}
    {T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hpsd : T.PosSemidef) (htoe : IsToeplitz T) : ∃ μ : Measure ℂ, Represents T μ := by
  obtain ⟨s, w, _, hnodes, hentries⟩ :=
    ToeplitzRepresentation.exists_atomic_representation hpsd htoe
  refine ⟨atomicMeasure s w, ?_⟩
  have heq : T = atomicMatrix n s w := by ext i j; exact hentries i j
  rw [heq]
  exact atomicMeasure_represents s w (fun z hz => ⟨(hnodes z hz).1, (hnodes z hz).2.le⟩)

lemma integrable_of_continuous_circle {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1) {f : ℂ → ℂ} (hf : Continuous f) : Integrable f μ := by
  have hi := hf.continuousOn.integrableOn_compact (μ := μ) (isCompact_sphere (0 : ℂ) 1)
  have hm : ∀ᵐ z ∂μ, z ∈ Metric.sphere (0 : ℂ) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hμ
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hm] using hi

end Reinmann.ToeplitzMeasure

import Reinmann.WeilClusterActivation

/-!
# Scalar estimates for localized complementary resolvents

The second resolvent identity, Dirichlet semigroup domination, Fourier
localization, and inverse Jensen bound remain written analytic inputs.
These lemmas check the combination of their error terms. No operator
identity or actual eigenfunction bound is introduced as an axiom.
-/
noncomputable section
open Filter Topology
namespace Reinmann.WeilLocalizedResolvent

/-- Scalar terms furnished by the noncommutative SECOND resolvent identity.
The linear term may have either sign. -/
def SecondResolventTermsHypothesis
    (r first second linear remainder W gamma : ℝ) : Prop :=
  r = first - linear + remainder ∧
  |linear| ≤ W * second ∧ remainder ≤ (W ^ 2 / gamma) * second

theorem second_resolvent_upper {r first second linear remainder W gamma : ℝ}
    (h : SecondResolventTermsHypothesis r first second linear remainder W gamma) :
    r ≤ first + (W + W ^ 2 / gamma) * second := by
  have hl : -linear ≤ W * second := le_trans (neg_le_abs _) h.2.1
  rw [h.1]
  nlinarith [h.2.2]

/-- The first TWO inverse moments are separately dominated; squaring an
operator-order inequality would not establish this hypothesis. -/
def LocalizedInverseMomentsHypothesis (first second low denominator : ℝ) : Prop :=
  first ≤ low + 1 / denominator ∧ second ≤ low + 1 / denominator ^ 2

theorem localized_resolvent_upper {r first second low denominator C : ℝ}
    (hC : 0 ≤ C) (hr : r ≤ first + C * second)
    (hm : LocalizedInverseMomentsHypothesis first second low denominator) :
    r ≤ (1 + C) * low + 1 / denominator + C / denominator ^ 2 := by
  have hs := mul_le_mul_of_nonneg_left hm.2 hC
  calc
    r ≤ first + C * second := hr
    _ ≤ (low + 1 / denominator) + C * (low + 1 / denominator ^ 2) := by
      linarith [hm.1]
    _ = (1 + C) * low + 1 / denominator + C / denominator ^ 2 := by ring

theorem second_resolvent_coefficient_nonneg {W gamma : ℝ}
    (hW : 0 ≤ W) (hg : 0 < gamma) : 0 ≤ W + W ^ 2 / gamma := by
  positivity

/-- Remove the lifted ground-space inverse before using a localized trial.
The actual Jensen and ground-projection estimates are explicit inputs. -/
theorem localized_resolvent_lower {omega lifted projection energy cost gamma : ℝ}
    (hg : 0 < gamma) (htrial : lifted - projection / gamma ≤ omega)
    (hjensen : 1 / energy ≤ lifted) (hprojection : projection ≤ cost) :
    1 / energy - cost / gamma ≤ omega := by
  have hp := (div_le_div_iff_of_pos_right hg).mpr hprojection
  linarith

/-- Combine the enclosure with the localized Schur cost from the cluster law. -/
theorem localized_schur_rate {cost scale omega K bound : ℝ}
    (hs : 0 < scale) (hK : 0 ≤ K)
    (hc : Reinmann.WeilClusterActivation.LocalizedSchurCostHypothesis cost scale omega K)
    (hw : omega ≤ bound) : cost / scale ≤ K * bound := by
  exact le_trans (Reinmann.WeilClusterActivation.localized_cost_ratio hs hc).2
    (mul_le_mul_of_nonneg_left hw hK)

/-- Positivity converts a near-unit quadratic form and a near-contractive
norm bound into strong convergence on a fixed unit profile. The scalar
input `action_sq` is the squared action error, not an operator-norm error. -/
theorem fixed_profile_action_error {action_sq quadratic epsilon eta : ℝ}
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1) (heta : 0 ≤ eta)
    (hq : 1 - eta ≤ quadratic)
    (ha : action_sq ≤ (1 + epsilon) * quadratic - 2 * quadratic + 1) :
    action_sq ≤ epsilon + eta := by
  have hprod : 0 ≤ (1 - epsilon) * (quadratic - (1 - eta)) :=
    mul_nonneg (by linarith) (by linarith)
  have herr : 0 ≤ epsilon * eta := mul_nonneg he heta
  nlinarith

/-- Actual scalar Schur-coefficient limit for a chosen real minimizing
state. The operator/profile analysis furnishing it is not axiomatized. -/
def SchurCoefficientLimitHypothesis {ι : Type*} (l : Filter ι)
    (cost scale : ι → ℝ) (w left right : ℝ) : Prop :=
  Tendsto (fun x => cost x / scale x) l (𝓝 (w ^ 2 * (left ^ 2 + right ^ 2)))

/-- The exact scalar Feshbach root equation, before any head approximation. -/
def ExactScalarSchurHypothesis (actual head cost : ℝ) : Prop :=
  actual = head - cost

/-- The Schur coefficient is the negative leading error of the exact
one-state Rayleigh prediction. The real trace convention is explicit. -/
theorem exact_rayleigh_error_limit {ι : Type*} {l : Filter ι}
    {actual head cost scale : ι → ℝ} {w left right : ℝ}
    (hroot : ∀ᶠ x in l, ExactScalarSchurHypothesis (actual x) (head x) (cost x))
    (hc : SchurCoefficientLimitHypothesis l cost scale w left right) :
    Tendsto (fun x => (actual x - head x) / scale x) l
      (𝓝 (-(w ^ 2 * (left ^ 2 + right ^ 2)))) := by
  have heq : (fun x => -(cost x / scale x)) =ᶠ[l]
      (fun x => (actual x - head x) / scale x) := by
    filter_upwards [hroot] with x hx
    change actual x = head x - cost x at hx
    rw [hx]
    ring
  exact hc.neg.congr' heq

end Reinmann.WeilLocalizedResolvent

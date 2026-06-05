/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.VdpCertificates
import Mathlib.Data.Nat.Choose.Basic

/-!
# Experiment E3: The Certificate-Method Ceiling (Barrier)

The de la Vallée Poussin certificate family `2^{n-1}(1+cosθ)^n` (see
`VdpCertificates`) expands in the cosine basis with coefficients

  `c₀(n) = ½·C(2n,n)`,  `c₁(n) = C(2n,n-1)`

(verified directly for `n = 2,3,4`: `(3,4)`, `(10,15)`, `(35,56)`). The dVP
mechanism's strength is governed by the **gap ratio** `c₁/c₀`. Here we prove the
ceiling, unconditionally:

  `c₁(n)/c₀(n) = 2n/(n+1) < 2`  for all `n ≥ 1`.

The ratio increases toward `2` but never reaches it. Since pushing the zero-free
boundary to `Re = 1/2` would require the gap ratio to attain the threshold `2`,
**this family of certificates cannot, by itself, reach the critical line** — a
machine-checked statement of the classical limitation of the method.

The crux is the binomial identity `C(2n,n)·n = C(2n,n-1)·(n+1)`, from
`Nat.choose_succ_right_eq`.

## Honest scope

This is the *coefficient-level* barrier (the precise, provable form). The full
"reach" statement (relating gap ratio to the attained zero-free boundary)
additionally needs the dVP growth machinery not present in Mathlib; the barrier is
therefore formalized exactly where it is rigorous — on the certificate coefficients.
-/

noncomputable section

namespace Reinmann

/-- **Key binomial identity.** `C(2m,m)·m = C(2m,m-1)·(m+1)` for `m ≥ 1`. -/
theorem cert_binom_identity {m : ℕ} (hm : 1 ≤ m) :
    Nat.choose (2 * m) m * m = Nat.choose (2 * m) (m - 1) * (m + 1) := by
  have h := Nat.choose_succ_right_eq (2 * m) (m - 1)
  have e1 : m - 1 + 1 = m := by omega
  have e2 : 2 * m - (m - 1) = m + 1 := by omega
  rw [e1, e2] at h
  exact h

/-- The constant cosine coefficient of the order-`n` certificate. -/
def certC0 (n : ℕ) : ℝ := (1 / 2) * (Nat.choose (2 * n) n : ℝ)

/-- The first cosine coefficient of the order-`n` certificate. -/
def certC1 (n : ℕ) : ℝ := (Nat.choose (2 * n) (n - 1) : ℝ)

theorem certC0_two : certC0 2 = 3 := by
  unfold certC0; rw [show Nat.choose (2 * 2) 2 = 6 from by decide]; norm_num
theorem certC1_two : certC1 2 = 4 := by
  unfold certC1; rw [show Nat.choose (2 * 2) (2 - 1) = 4 from by decide]; norm_num
theorem certC0_three : certC0 3 = 10 := by
  unfold certC0; rw [show Nat.choose (2 * 3) 3 = 20 from by decide]; norm_num
theorem certC1_three : certC1 3 = 15 := by
  unfold certC1; rw [show Nat.choose (2 * 3) (3 - 1) = 15 from by decide]; norm_num
theorem certC0_four : certC0 4 = 35 := by
  unfold certC0; rw [show Nat.choose (2 * 4) 4 = 70 from by decide]; norm_num
theorem certC1_four : certC1 4 = 56 := by
  unfold certC1; rw [show Nat.choose (2 * 4) (4 - 1) = 56 from by decide]; norm_num

/-- **The gap ratio formula.** `c₁(n)/c₀(n) = 2n/(n+1)`. -/
theorem certGapRatio_eq {m : ℕ} (hm : 1 ≤ m) :
    certC1 m / certC0 m = 2 * (m : ℝ) / ((m : ℝ) + 1) := by
  have hcpos : 0 < (Nat.choose (2 * m) m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
  have hid : (Nat.choose (2 * m) m : ℝ) * (m : ℝ)
      = (Nat.choose (2 * m) (m - 1) : ℝ) * ((m : ℝ) + 1) := by
    exact_mod_cast cert_binom_identity hm
  unfold certC0 certC1
  rw [div_eq_div_iff (by positivity) (by positivity)]
  · linear_combination -hid

/-- **The barrier.** The certificate gap ratio is strictly below `2`, for every
order `n ≥ 1`. The family cannot reach the critical-line threshold. -/
theorem certGapRatio_lt_two {m : ℕ} (hm : 1 ≤ m) :
    certC1 m / certC0 m < 2 := by
  rw [certGapRatio_eq hm, div_lt_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The gap ratios are strictly increasing in the order (they climb toward `2`). -/
theorem certGapRatio_strictMono {m : ℕ} (hm : 1 ≤ m) :
    certC1 m / certC0 m < certC1 (m + 1) / certC0 (m + 1) := by
  rw [certGapRatio_eq hm, certGapRatio_eq (by omega : 1 ≤ m + 1)]
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

end Reinmann

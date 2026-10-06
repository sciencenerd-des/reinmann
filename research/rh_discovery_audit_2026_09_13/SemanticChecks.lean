import Reinmann.EffectiveAssembly

/- Read-only audit lemmas. This file is outside the active library.
   It does not prove any new analytic statement about Xi or RH. -/
namespace DiscoveryAudit
open Reinmann

/-- Regression: the repaired entire extension takes the correct values at 0,1. -/
theorem xiCompleted_zero_value : xiCompleted 0 = 1 / 2 := by
  simp [xiCompleted]

theorem xiCompleted_one_value : xiCompleted 1 = 1 / 2 := by
  simp [xiCompleted]

theorem jensen_input_is_output (d n : ℕ) :
    jensenCoeffPoly d n = JensenPoly d n := rfl

theorem hpss_payload_already_has_hyperbolicity
    (h : XiJensenCoeffHyperbolic) : AllJensenHyperbolic := by
  intro d n
  exact (h d n).2

theorem certificates_iff_ladder (M : ℕ → ℝ) :
    KernelEffectiveCertificates M ↔ KernelLadderStrict M := by
  constructor
  · exact kernelLadderStrict_of_certificates
  · intro h k
    refine ⟨0, ?_, ?_⟩
    · intro m hm
      omega
    · intro m _
      exact h k m

/-- Generic exact identity, independent of any assertion about Xi. -/
theorem order_three_deficit_identity (a b c d e : ℝ)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (c ^ 3 - 2 * b * c * d + b ^ 2 * e + a * d ^ 2 - a * c * e) / c ^ 3 =
      (1 - b * d / c ^ 2) ^ 2 -
        (b * d / c ^ 2) ^ 2 * (1 - a * c / b ^ 2) * (1 - c * e / d ^ 2) := by
  field_simp [hb, hc, hd]
  ring

#print axioms jensen_input_is_output
#print axioms xiCompleted_zero_value
#print axioms xiCompleted_one_value
#print axioms hpss_payload_already_has_hyperbolicity
#print axioms certificates_iff_ladder
#print axioms order_three_deficit_identity
end DiscoveryAudit

import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum

/-! A pointwise range certificate for 17 weighted theta integrands on one panel.
This is a panel benchmark, not a certified Xi jet or a complete hard tile. -/
open LeanCert.Core
namespace HardTilePanel
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def panel : IntervalRat := ⟨1,1025/1024,by norm_num⟩
def piBox : IntervalRat :=
  ⟨3.14159265358979323846,3.14159265358979323847,by norm_num⟩
def logBox := IntervalRat.logComputable panel 16
def weightBox := IntervalRat.expComputable
  (IntervalRat.mul logBox (IntervalRat.singleton (-3/4))) 16
def thetaBox := IntervalRat.expComputable
  (IntervalRat.neg (IntervalRat.mul piBox panel)) 16
def phaseBox := IntervalRat.mul logBox (IntervalRat.singleton 7)
def trigBox (imaginary : Bool) :=
  if imaginary then IntervalRat.sinComputable phaseBox 16 else IntervalRat.cosComputable phaseBox 16
def coefficientBox (k : ℕ) (imaginary : Bool) :=
  IntervalRat.mul
    (IntervalRat.mul
      (IntervalRat.mul (IntervalRat.singleton 2) thetaBox)
      (IntervalRat.mul weightBox (trigBox imaginary)))
    (IntervalRat.mul
      (IntervalRat.pow (IntervalRat.mul logBox (IntervalRat.singleton (1/2))) k)
      (IntervalRat.singleton (1/(k.factorial : ℚ))))
noncomputable def value (k : ℕ) (imaginary : Bool) (t : ℝ) : ℝ :=
  (2*Real.exp (-Real.pi*t)) *
    (Real.exp (Real.log t*(-3/4)) *
      (if imaginary then Real.sin (Real.log t*7) else Real.cos (Real.log t*7))) *
    ((Real.log t*(1/2))^k * (1/(k.factorial : ℝ)))

theorem pointwise_enclosure (k : ℕ) (imaginary : Bool) {t : ℝ} (ht : t ∈ panel) :
    value k imaginary t ∈ coefficientBox k imaginary := by
  have hp : Real.pi ∈ piBox := ⟨Real.pi_gt_d20.le,Real.pi_lt_d20.le⟩
  have hlog := IntervalRat.mem_logComputable ht (by norm_num [panel]) 16
  have hc (q : ℚ) : (q : ℝ) ∈ IntervalRat.singleton q := IntervalRat.mem_singleton q
  have hw := IntervalRat.mem_expComputable (IntervalRat.mem_mul hlog (hc (-3/4))) 16
  have he := IntervalRat.mem_expComputable (IntervalRat.mem_neg (IntervalRat.mem_mul hp ht)) 16
  have hphase := IntervalRat.mem_mul hlog (hc 7)
  have htrig : (if imaginary then Real.sin (Real.log t*7) else Real.cos (Real.log t*7)) ∈
      trigBox imaginary := by
    cases imaginary
    · exact IntervalRat.mem_cosComputable (by simpa using hphase) 16
    · exact IntervalRat.mem_sinComputable (by simpa using hphase) 16
  have h := IntervalRat.mem_mul
    (IntervalRat.mem_mul (IntervalRat.mem_mul (hc 2) he) (IntervalRat.mem_mul hw htrig))
    (IntervalRat.mem_mul (IntervalRat.mem_pow (IntervalRat.mem_mul hlog (hc (1/2))) k)
      (hc (1/(k.factorial : ℚ))))
  simpa only [coefficientBox,value,thetaBox,weightBox,logBox,trigBox,phaseBox,
    Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg,neg_mul] using h

theorem value_integrable (k : ℕ) (imaginary : Bool) :
    IntervalIntegrable (value k imaginary) MeasureTheory.volume 1 (1025/1024) := by
  have hl : ContinuousOn Real.log (Set.uIcc (1 : ℝ) (1025/1024)) := by
    apply Real.continuousOn_log.mono
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 1025/1024)] at ht
    exact ne_of_gt (by linarith [ht.1])
  have he : ContinuousOn (fun t : ℝ => Real.exp (-Real.pi*t))
      (Set.uIcc (1 : ℝ) (1025/1024)) := Real.continuous_exp.comp_continuousOn
    (continuousOn_const.mul continuousOn_id)
  have hw := Real.continuous_exp.comp_continuousOn (hl.mul_const (-3/4))
  have htrig : ContinuousOn (fun t => if imaginary then Real.sin (Real.log t*7)
      else Real.cos (Real.log t*7)) (Set.uIcc (1 : ℝ) (1025/1024)) := by
    cases imaginary
    · exact Real.continuous_cos.comp_continuousOn (hl.mul_const 7)
    · exact Real.continuous_sin.comp_continuousOn (hl.mul_const 7)
  apply ContinuousOn.intervalIntegrable
  exact ((continuousOn_const.mul he).mul (hw.mul htrig)).mul
    (((hl.mul_const (1/2)).pow k).mul continuousOn_const)

/-- A genuine integral panel enclosure, including every point between samples. -/
theorem integral_enclosure (k : ℕ) (imaginary : Bool) :
    ((coefficientBox k imaginary).lo : ℝ)/1024 ≤
      ∫ t in (1 : ℝ)..(1025/1024), value k imaginary t ∧
    (∫ t in (1 : ℝ)..(1025/1024), value k imaginary t) ≤
      ((coefficientBox k imaginary).hi : ℝ)/1024 := by
  have hb (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) (1025/1024)) : t ∈ panel := by
    simpa [panel,IntervalRat.mem_def] using ht
  constructor
  · have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 1025/1024)
      intervalIntegrable_const (value_integrable k imaginary)
      (fun t ht => (pointwise_enclosure k imaginary (hb t ht)).1)
    norm_num [intervalIntegral.integral_const,smul_eq_mul] at h ⊢
    nlinarith only [h]
  · have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 1025/1024)
      (value_integrable k imaginary) intervalIntegrable_const
      (fun t ht => (pointwise_enclosure k imaginary (hb t ht)).2)
    norm_num [intervalIntegral.integral_const,smul_eq_mul] at h ⊢
    nlinarith only [h]

-- All 17 complex-parameter coefficient weights, real and imaginary components.
theorem all_widths : ∀ k : Fin 17, ∀ imaginary : Bool,
    (coefficientBox k.val imaginary).width ≤ (1/1000 : ℚ) := by
  decide +kernel
#print axioms pointwise_enclosure
#print axioms all_widths
#print axioms integral_enclosure
end HardTilePanel

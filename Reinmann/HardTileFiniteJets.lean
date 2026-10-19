/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.StirlingAnalytic
import Reinmann.HardTileFiniteIdentities
import Reinmann.CertifiedTaylorInputs
import Reinmann.HardTileGammaLogJet
import Reinmann.HardTileLogInputs
import Mathlib.Tactic.IntervalCases

/-! Generated rational Taylor proposals with kernel-checked soundness proofs. -/
noncomputable section
namespace Reinmann.HardTileFiniteJets
open CertifiedTaylorModel CertifiedTaylorComposition CertifiedTaylorInputs
open scoped Topology
set_option maxRecDepth 20000

def c : ℂ := HardTileGammaLogJet.centre

def F_variable (s : ℂ) : ℂ := s

def J_variable : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_variable : AnalyticAt ℂ F_variable c := by
  exact analyticAt_id

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound ((1/2 : ℚ),14)
  convert h using 1
  · funext k
    fin_cases k <;> rfl
  · norm_num [c, HardTileGammaLogJet.centre, value]

def F_log2 (s : ℂ) : ℂ := (Real.log (2 : ℝ) : ℂ)

def J_log2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log2 : AnalyticAt ℂ F_log2 c := by
  exact analyticAt_const

theorem S_log2 : Sound J_log2 F_log2 c := by
  have hlog : Contains ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩ (Real.log (2 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_2 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_logpi (s : ℂ) : ℂ := (Real.log (Real.pi : ℝ) : ℂ)

def J_logpi : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_logpi : AnalyticAt ℂ F_logpi c := by
  exact analyticAt_const

theorem S_logpi : Sound J_logpi F_logpi c := by
  have hlog : Contains ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (Real.pi : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_pi using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift (s : ℂ) : ℂ := HardTileGammaLogJet.shifted s
def J_shift : Jet8 := HardTileGammaLogJet.affineJet
theorem A_shift : AnalyticAt ℂ F_shift c := HardTileGammaLogJet.shifted_analytic
theorem S_shift : Sound J_shift F_shift c := HardTileGammaLogJet.affine_sound

def F_shiftinv (s : ℂ) : ℂ := (HardTileGammaLogJet.shifted s)⁻¹
def J_shiftinv : Jet8 := HardTileGammaLogJet.inverseJet
theorem A_shiftinv : AnalyticAt ℂ F_shiftinv c := HardTileGammaLogJet.shifted_analytic.inv HardTileGammaLogJet.shifted_nonzero
theorem S_shiftinv : Sound J_shiftinv F_shiftinv c := HardTileGammaLogJet.inverse_sound

def F_shiftlog (s : ℂ) : ℂ := Complex.log (HardTileGammaLogJet.shifted s)
def J_shiftlog : Jet8 := HardTileGammaLogJet.logJet
theorem A_shiftlog : AnalyticAt ℂ F_shiftlog c := HardTileGammaLogJet.shifted_analytic.clog HardTileGammaLogJet.shifted_slit
theorem S_shiftlog : Sound J_shiftlog F_shiftlog c := HardTileGammaLogJet.log_sound

def F_q0 (s : ℂ) : ℂ := value ((-1/2), 0)

def J_q0 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q0 : AnalyticAt ℂ F_q0 c := by
  exact analyticAt_const

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (c := c) (contains_exact ((-1/2), 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_wmhalf (s : ℂ) : ℂ := F_shift s+F_q0 s

def J_wmhalf : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((47/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_wmhalf : AnalyticAt ℂ F_wmhalf c := by
  exact A_shift.add A_q0

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_wmhalf : Sound J_wmhalf F_wmhalf c := by
  apply sound_round (sound_add A_shift A_q0 S_shift S_q0)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_wmhalf, J_shift, J_q0, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_wlog (s : ℂ) : ℂ := F_wmhalf s*F_shiftlog s

def J_wlog : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((966373538734827/35184372088832), (866507796193079/35184372088832)), (5/8796093022208), by norm_num⟩
  | 1 => ⟨((1017824828860089/562949953421312), (9442228187281/35184372088832)), (9/281474976710656), by norm_num⟩
  | 2 => ⟨((35360952514365/4503599627370496), (-1313391269181/281474976710656)), (77/4503599627370496), by norm_num⟩
  | 3 => ⟨((-119869526459/2251799813685248), (439476442443/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 4 => ⟨((-159316627/2251799813685248), (-9127685719/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 5 => ⟨((26888311/1125899906842624), (168416909/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2164477/2251799813685248), (-2197991/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 7 => ⟨((126081/4503599627370496), (-1957/1125899906842624)), (77/4503599627370496), by norm_num⟩
  | 8 => ⟨((-355/562949953421312), (1925/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | _ => zero

theorem A_wlog : AnalyticAt ℂ F_wlog c := by
  exact A_wmhalf.mul A_shiftlog

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_wlog : Sound J_wlog F_wlog c := by
  apply sound_round (sound_mul A_wmhalf A_shiftlog S_wmhalf S_shiftlog)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_q0, J_wmhalf, J_wlog,
    J_wmhalf, J_shiftlog, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_negw (s : ℂ) : ℂ := value (-1, 0)*F_shift s

def J_negw : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-49/4), -7), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negw : AnalyticAt ℂ F_negw c := by
  exact analyticAt_const.mul A_shift

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negw : Sound J_negw F_negw c := by
  apply sound_round (sound_scale A_shift S_shift)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_wmhalf, J_wlog, J_negw,
    J_shift, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_mainbase (s : ℂ) : ℂ := F_wlog s+F_negw s

def J_mainbase : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((535364980646635/35184372088832), (620217191571255/35184372088832)), (5/8796093022208), by norm_num⟩
  | 1 => ⟨((736349852149433/562949953421312), (9442228187281/35184372088832)), (9/281474976710656), by norm_num⟩
  | 2 => ⟨((35360952514365/4503599627370496), (-1313391269181/281474976710656)), (77/4503599627370496), by norm_num⟩
  | 3 => ⟨((-119869526459/2251799813685248), (439476442443/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 4 => ⟨((-159316627/2251799813685248), (-9127685719/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 5 => ⟨((26888311/1125899906842624), (168416909/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2164477/2251799813685248), (-2197991/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 7 => ⟨((126081/4503599627370496), (-1957/1125899906842624)), (77/4503599627370496), by norm_num⟩
  | 8 => ⟨((-355/562949953421312), (1925/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | _ => zero

theorem A_mainbase : AnalyticAt ℂ F_mainbase c := by
  exact A_wlog.add A_negw

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_mainbase : Sound J_mainbase F_mainbase c := by
  apply sound_round (sound_add A_wlog A_negw S_wlog S_negw)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_mainbase, J_wlog, J_negw, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_log2pi (s : ℂ) : ℂ := F_log2 s+F_logpi s

def J_log2pi : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((2069265617858477/1125899906842624), 0), (9/1125899906842624), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log2pi : AnalyticAt ℂ F_log2pi c := by
  exact A_log2.add A_logpi

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_log2pi : Sound J_log2pi F_log2pi c := by
  apply sound_round (sound_add A_log2 A_logpi S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log2pi, J_log2, J_logpi, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_halfLog2pi (s : ℂ) : ℂ := value ((1/2), 0)*F_log2pi s

def J_halfLog2pi : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((2069265617858477/2251799813685248), 0), (9/2251799813685248), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_halfLog2pi : AnalyticAt ℂ F_halfLog2pi c := by
  exact analyticAt_const.mul A_log2pi

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_halfLog2pi : Sound J_halfLog2pi F_halfLog2pi c := by
  apply sound_round (sound_scale A_log2pi S_log2pi)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_mainbase, J_log2pi, J_halfLog2pi,
    J_log2pi, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_mainconstant (s : ℂ) : ℂ := F_mainbase s+F_halfLog2pi s

def J_mainconstant : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((283848627962837/17592186044416), (620217191571255/35184372088832)), (21/35184372088832), by norm_num⟩
  | 1 => ⟨((736349852149433/562949953421312), (9442228187281/35184372088832)), (9/281474976710656), by norm_num⟩
  | 2 => ⟨((35360952514365/4503599627370496), (-1313391269181/281474976710656)), (77/4503599627370496), by norm_num⟩
  | 3 => ⟨((-119869526459/2251799813685248), (439476442443/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 4 => ⟨((-159316627/2251799813685248), (-9127685719/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 5 => ⟨((26888311/1125899906842624), (168416909/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2164477/2251799813685248), (-2197991/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | 7 => ⟨((126081/4503599627370496), (-1957/1125899906842624)), (77/4503599627370496), by norm_num⟩
  | 8 => ⟨((-355/562949953421312), (1925/4503599627370496)), (77/4503599627370496), by norm_num⟩
  | _ => zero

theorem A_mainconstant : AnalyticAt ℂ F_mainconstant c := by
  exact A_mainbase.add A_halfLog2pi

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_mainconstant : Sound J_mainconstant F_mainconstant c := by
  apply sound_round (sound_add A_mainbase A_halfLog2pi S_mainbase S_halfLog2pi)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_mainconstant, J_mainbase, J_halfLog2pi, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_iw2 (s : ℂ) : ℂ := F_shiftinv s*F_shiftinv s

def J_iw2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((735107540674333/288230376151711744), (-623727610269131/144115188075855872)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((-10966639301517/2305843009213693952), (1641862569700827/4611686018427387904)), (793/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-338316518429783/36893488147419103232), (-1221707720688249/73786976294838206464)), (13127/73786976294838206464), by norm_num⟩
  | 3 => ⟨((451200569235851/590295810358705651712), (548142126643355/1180591620717411303424)), (52551/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-1496154106115077/37778931862957161709568), (-39980714873677/37778931862957161709568)), (6726791/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((448689311679679/302231454903657293676544), (-481455943446003/604462909807314587353088)), (107628801/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-357401570104427/9671406556917033397649408), (1142106655666025/19342813113834066795298816)), (3444121733/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((34972811215751/309485009821345068724781056), (-1744847305134649/618970019642690137449562112)), (110211895629/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((513199807189859/9903520314283042199192993792), (494074371332239/4951760157141521099596496896)), (1763390330163/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem A_iw2 : AnalyticAt ℂ F_iw2 c := by
  exact A_shiftinv.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw2 : Sound J_iw2 F_iw2 c := by
  apply sound_round (sound_mul A_shiftinv A_shiftinv S_shiftinv S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_halfLog2pi, J_mainconstant, J_iw2,
    J_shiftinv, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw3 (s : ℂ) : ℂ := F_iw2 s*F_shiftinv s

def J_iw3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((21933278602871/4611686018427387904), (-1641862569700595/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 1 => ⟨((676633036861405/36893488147419103232), (1221707720684089/36893488147419103232)), (105/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-1353601707712593/590295810358705651712), (-822213189959849/590295810358705651712)), (14301/590295810358705651712), by norm_num⟩
  | 3 => ⟨((1496154105649571/9444732965739290427392), (19990358910349/4722366482869645213696)), (14343/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-70107702900477/9444732965739290427392), (601819928871155/151115727451828646838272)), (459041/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((536101721193981/2417851639229258349412352), (-856579204546791/2417851639229258349412352)), (29378793/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-61214141976633/77371252455336267181195264), (1526709796367857/77371252455336267181195264)), (940121605/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-256731874086355/618970019642690137449562112), (-988503144427359/1237940039285380274899124224)), (30083891661/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((1326995349642127/39614081257132168796771975168), (427713487144321/19807040628566084398385987584)), (481342266751/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem A_iw3 : AnalyticAt ℂ F_iw3 c := by
  exact A_iw2.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw3 : Sound J_iw3 F_iw3 c := by
  apply sound_round (sound_mul A_iw2 A_shiftinv S_iw2 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_mainconstant, J_iw2, J_iw3,
    J_iw2, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw4 (s : ℂ) : ℂ := F_iw3 s*F_shiftinv s

def J_iw4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-56386086405119/4611686018427387904), (-50904488361827/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((451200569237389/147573952589676412928), (548142126637293/295147905179352825856)), (373/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-1496154105649721/4722366482869645213696), (-39980717815525/4722366482869645213696)), (13163/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((747815497904337/37778931862957161709568), (-100303321281125/9444732965739290427392)), (3311/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-446751426687377/604462909807314587353088), (89226999845575/75557863725914323419136)), (423945/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((7651755828787/2417851639229258349412352), (-1526709221230187/19342813113834066795298816)), (54265931/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((599033594956509/309485009821345068724781056), (1153247230004465/309485009821345068724781056)), (868255645/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-442386455071309/2475880078570760549798248448), (-570333685696931/4951760157141521099596496896)), (13892090851/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((1639004413564235/158456325028528675187087900672), (43833444597245/79228162514264337593543950336)), (444546908023/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem A_iw4 : AnalyticAt ℂ F_iw4 c := by
  exact A_iw3.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw4 : Sound J_iw4 F_iw4 c := by
  apply sound_round (sound_mul A_iw3 A_shiftinv S_iw3 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw2, J_iw3, J_iw4,
    J_iw3, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw5 (s : ℂ) : ℂ := F_iw4 s*F_shiftinv s

def J_iw5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-902401138474703/590295810358705651712), (-274071063318563/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 1 => ⟨((1496154105647933/4722366482869645213696), (1249397431659/147573952589676412928)), (1301/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-560861623427171/18889465931478580854784), (601819927689687/37778931862957161709568)), (11829/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((111687856763971/75557863725914323419136), (-713815998460475/302231454903657293676544)), (95549/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((-76517554125343/9671406556917033397649408), (1908386517199451/9671406556917033397649408)), (3059555/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-449275138499869/77371252455336267181195264), (-432467632317747/38685626227668133590597632)), (24477413/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((774173485402915/1237940039285380274899124224), (499041375791657/1237940039285380274899124224)), (391639447/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-819534467126201/19807040628566084398385987584), (-5478828827011/2475880078570760549798248448)), (6266231849/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((19490027371223/9903520314283042199192993792), (-156725911557869/158456325028528675187087900672)), (100259710155/316912650057057350374175801344), by norm_num⟩
  | _ => zero

theorem A_iw5 : AnalyticAt ℂ F_iw5 c := by
  exact A_iw4.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw5 : Sound J_iw5 F_iw5 c := by
  apply sound_round (sound_mul A_iw4 A_shiftinv S_iw4 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw3, J_iw4, J_iw5,
    J_iw4, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw6 (s : ℂ) : ℂ := F_iw5 s*F_shiftinv s

def J_iw6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-598461642259089/4722366482869645213696), (-7996143562587/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((448689298740939/18889465931478580854784), (-481455942152449/37778931862957161709568)), (273/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((-268050856232339/151115727451828646838272), (856579198153355/302231454903657293676544)), (5093/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((61214043832831/4835703278458516698824704), (-763354606833583/2417851639229258349412352)), (165315/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((56159392258361/4835703278458516698824704), (864935261803507/38685626227668133590597632)), (1323987/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-464504054323847/309485009821345068724781056), (-18714049631095/19342813113834066795298816)), (21185373/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((573673323772651/4951760157141521099596496896), (61363368530671/9903520314283042199192993792)), (338967557/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-3898061865491/618970019642690137449562112), (125383171687471/39614081257132168796771975168)), (2711741191/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((569047732210773/2535301200456458802993406410752), (-857404167064167/2535301200456458802993406410752)), (5423482461/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem A_iw6 : AnalyticAt ℂ F_iw6 c := by
  exact A_iw5.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw6 : Sound J_iw6 F_iw6 c := by
  apply sound_round (sound_mul A_iw5 A_shiftinv S_iw5 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw4, J_iw5, J_iw6,
    J_iw5, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw7 (s : ℂ) : ℂ := F_iw6 s*F_shiftinv s

def J_iw7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-598252398321135/75557863725914323419136), (160485314050823/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((357401141642121/302231454903657293676544), (-71381599846099/37778931862957161709568)), (1763/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-61214043829583/4835703278458516698824704), (1526709213666263/4835703278458516698824704)), (8479/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-599033517135015/38685626227668133590597632), (-576623507920831/19342813113834066795298816)), (138361/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((387086711403519/154742504910672534362390528), (249520661144709/154742504910672534362390528)), (554397/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-286836648169253/1237940039285380274899124224), (-61363358113271/4951760157141521099596496896)), (4435761/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((145527557456619/9903520314283042199192993792), (-585120766550633/79228162514264337593543950336)), (283891297/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((-758734528700839/1267650600228229401496703205376), (142901736154869/158456325028528675187087900672)), (4542263333/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((22716552756303/5070602400912917605986812821504), (-1358448993063715/20282409603651670423947251286016)), (36338107907/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

theorem A_iw7 : AnalyticAt ℂ F_iw7 c := by
  exact A_iw6.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw7 : Sound J_iw7 F_iw7 c := by
  apply sound_round (sound_mul A_iw6 A_shiftinv S_iw6 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw5, J_iw6, J_iw7,
    J_iw6, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw8 (s : ℂ) : ℂ := F_iw7 s*F_shiftinv s

def J_iw8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-408458447590873/1208925819614629174706176), (40789485626339/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((69958907231947/9671406556917033397649408), (-1744810529902929/9671406556917033397649408)), (2837/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((513457300402919/38685626227668133590597632), (494248721074169/19342813113834066795298816)), (877/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-884769625952937/309485009821345068724781056), (-570332939890627/309485009821345068724781056)), (57567/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((1639066559220401/4951760157141521099596496896), (87661939669937/4951760157141521099596496896)), (1846783/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((-997903220689253/39614081257132168796771975168), (125383018795825/9903520314283042199192993792)), (14777415/39614081257132168796771975168), by norm_num⟩
  | 6 => ⟨((379367188560151/316912650057057350374175801344), (-571606668900707/316912650057057350374175801344)), (59110603/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((-51923455818473/5070602400912917605986812821504), (1552518110193943/10141204801825835211973625643008)), (3783082753/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-361525245651931/81129638414606681695789005144064), (-1487867657219481/162259276829213363391578010288128)), (60529328331/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

theorem A_iw8 : AnalyticAt ℂ F_iw8 c := by
  exact A_iw7.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw8 : Sound J_iw8 F_iw8 c := by
  apply sound_round (sound_mul A_iw7 A_shiftinv S_iw7 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw6, J_iw7, J_iw8,
    J_iw7, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw9 (s : ℂ) : ℂ := F_iw8 s*F_shiftinv s

def J_iw9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-69958907231765/38685626227668133590597632), (54525329059459/1208925819614629174706176)), (25/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((-513457300403453/77371252455336267181195264), (-494248721073559/38685626227668133590597632)), (565/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((1327154438929887/618970019642690137449562112), (427749704916551/309485009821345068724781056)), (22923/618970019642690137449562112), by norm_num⟩
  | 3 => ⟨((-1639066559183467/4951760157141521099596496896), (-43830969930799/2475880078570760549798248448)), (189307/4951760157141521099596496896), by norm_num⟩
  | 4 => ⟨((311844756220279/9903520314283042199192993792), (-78364386709689/4951760157141521099596496896)), (759883/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((-569050770589137/316912650057057350374175801344), (857409989439525/316912650057057350374175801344)), (6081027/158456325028528675187087900672), by norm_num⟩
  | 6 => ⟨((45433063035007/2535301200456458802993406410752), (-1358453022005105/5070602400912917605986812821504)), (194598009/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((180762963246657/20282409603651670423947251286016), (185983739550555/10141204801825835211973625643008)), (1556787137/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((-48408054140963/40564819207303340847894502572032), (-264540702030895/324518553658426726783156020576256)), (24908597547/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

theorem A_iw9 : AnalyticAt ℂ F_iw9 c := by
  exact A_iw8.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw9 : Sound J_iw9 F_iw9 c := by
  apply sound_round (sound_mul A_iw8 A_shiftinv S_iw8 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw7, J_iw8, J_iw9,
    J_iw8, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw10 (s : ℂ) : ℂ := F_iw9 s*F_shiftinv s

def J_iw10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((28525405577971/19342813113834066795298816), (439332196509745/154742504910672534362390528)), (5/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((-589846417302087/618970019642690137449562112), (-380221959925061/618970019642690137449562112)), (3555/1237940039285380274899124224), by norm_num⟩
  | 2 => ⟨((1092711039454955/4951760157141521099596496896), (58441293239357/4951760157141521099596496896)), (18525/4951760157141521099596496896), by norm_num⟩
  | 3 => ⟨((-554390677742603/19807040628566084398385987584), (278628930471127/19807040628566084398385987584)), (154061/39614081257132168796771975168), by norm_num⟩
  | 4 => ⟨((79034829201685/39614081257132168796771975168), (-238169441399719/79228162514264337593543950336)), (1238257/316912650057057350374175801344), by norm_num⟩
  | 5 => ⟨((-60577415232705/2535301200456458802993406410752), (1811270675091937/5070602400912917605986812821504)), (19821469/5070602400912917605986812821504), by norm_num⟩
  | 6 => ⟨((-562373531694559/40564819207303340847894502572032), (-1157232013791221/40564819207303340847894502572032)), (79289183/20282409603651670423947251286016), by norm_num⟩
  | 7 => ⟨((344235351848303/162259276829213363391578010288128), (470294929190841/324518553658426726783156020576256)), (317157781/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((-1001389131139063/5192296858534827628530496329220096), (-160863090455219/10384593717069655257060992658440192)), (40596205865/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

theorem A_iw10 : AnalyticAt ℂ F_iw10 c := by
  exact A_iw9.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw10 : Sound J_iw10 F_iw10 c := by
  apply sound_round (sound_mul A_iw9 A_shiftinv S_iw9 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw8, J_iw9, J_iw10,
    J_iw9, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_iw11 (s : ℂ) : ℂ := F_iw10 s*F_shiftinv s

def J_iw11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((943754267683265/4951760157141521099596496896), (608355135879917/4951760157141521099596496896)), (63/4951760157141521099596496896), by norm_num⟩
  | 1 => ⟨((-874168831563441/9903520314283042199192993792), (-93506069181549/19807040628566084398385987584)), (2793/9903520314283042199192993792), by norm_num⟩
  | 2 => ⟨((665268813290189/39614081257132168796771975168), (-167177358283025/19807040628566084398385987584)), (29861/79228162514264337593543950336), by norm_num⟩
  | 3 => ⟨((-505822906937223/316912650057057350374175801344), (762142212437671/316912650057057350374175801344)), (125067/316912650057057350374175801344), by norm_num⟩
  | 4 => ⟨((121154830381635/5070602400912917605986812821504), (-452817668608933/1267650600228229401496703205376)), (1006607/2535301200456458802993406410752), by norm_num⟩
  | 5 => ⟨((674848234192317/40564819207303340847894502572032), (1388678404871449/40564819207303340847894502572032)), (16116371/40564819207303340847894502572032), by norm_num⟩
  | 6 => ⟨((-481929438693105/162259276829213363391578010288128), (-164603216247679/81129638414606681695789005144064)), (128939035/324518553658426726783156020576256), by norm_num⟩
  | 7 => ⟨((1602223333473319/5192296858534827628530496329220096), (64345244846329/2596148429267413814265248164610048)), (515758889/1298074214633706907132624082305024), by norm_num⟩
  | 8 => ⟨((-232028351079309/10384593717069655257060992658440192), (435802410388801/41538374868278621028243970633760768)), (8252145667/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

theorem A_iw11 : AnalyticAt ℂ F_iw11 c := by
  exact A_iw10.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_iw11 : Sound J_iw11 F_iw11 c := by
  apply sound_round (sound_mul A_iw10 A_shiftinv S_iw10 S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw9, J_iw10, J_iw11,
    J_iw10, J_shiftinv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_gcorr1 (s : ℂ) : ℂ := value ((1/12), 0)*F_shiftinv s

def J_gcorr1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((739052246542851/144115188075855872), (-211157784726529/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((-119646409615/1125899906842624), (831636813692245/4611686018427387904)), (171/2305843009213693952), by norm_num⟩
  | 2 => ⟨((29244371479211/295147905179352825856), (-2189150092940629/295147905179352825856)), (10923/147573952589676412928), by norm_num⟩
  | 3 => ⟨((601451588310357/4722366482869645213696), (1035654467/4503599627370496)), (174763/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-1203201522357589/151115727451828646838272), (-21781211/4503599627370496)), (11184811/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((1595897820129963/4835703278458516698824704), (42646161937749/4835703278458516698824704)), (178956971/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-797672779459243/77371252455336267181195264), (427961994619563/77371252455336267181195264)), (2863311531/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((544624759625045/2475880078570760549798248448), (-1583/4503599627370496)), (183251937963/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-46912496118443/79228162514264337593543950336), (33/2251799813685248)), (2932031007403/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem A_gcorr1 : AnalyticAt ℂ F_gcorr1 c := by
  exact analyticAt_const.mul A_shiftinv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gcorr1 : Sound J_gcorr1 F_gcorr1 c := by
  apply sound_round (sound_scale A_shiftinv S_shiftinv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_iw10, J_iw11, J_gcorr1,
    J_shiftinv, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_maincorr1 (s : ℂ) : ℂ := F_mainconstant s+F_gcorr1 s

def J_maincorr1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((567877688603053/35184372088832), (620114087184181/35184372088832)), (11/17592186044416), by norm_num⟩
  | 1 => ⟨((1472580057889251/1125899906842624), (75588584581115/281474976710656)), (37/1125899906842624), by norm_num⟩
  | 2 => ⟨((1131564759937941/144115188075855872), (-673525250764491/144115188075855872)), (619/36028797018963968), by norm_num⟩
  | 3 => ⟨((-489810870242645/9223372036854775808), (220256048455/2251799813685248)), (39595/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-46463903814997/590295810358705651712), (-4574733465/2251799813685248)), (10136235/590295810358705651712), by norm_num⟩
  | 5 => ⟨((457344977382059/18889465931478580854784), (706558301656405/18889465931478580854784)), (162179755/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-1174508378172075/1208925819614629174706176), (-583331810202965/1208925819614629174706176)), (10379504299/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1091537305163093/38685626227668133590597632), (-9411/4503599627370496)), (664288275115/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-781386263472811/1237940039285380274899124224), (1991/4503599627370496)), (10628612401835/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem A_maincorr1 : AnalyticAt ℂ F_maincorr1 c := by
  exact A_mainconstant.add A_gcorr1

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_maincorr1 : Sound J_maincorr1 F_maincorr1 c := by
  apply sound_round (sound_add A_mainconstant A_gcorr1 S_mainconstant S_gcorr1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr1, J_mainconstant, J_gcorr1, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_gcorr2 (s : ℂ) : ℂ := value ((-1/360), 0)*F_iw3 s

def J_gcorr2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-15596998117597/1180591620717411303424), (583773358115767/590295810358705651712)), (3/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-481161270656999/9444732965739290427392), (-434384967354343/4722366482869645213696)), (299/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((962561214373399/151115727451828646838272), (584684935082559/151115727451828646838272)), (10171/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-1063931808461917/2417851639229258349412352), (-56861465344993/4835703278458516698824704)), (20399/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((398834932056047/19342813113834066795298816), (-427960838308377/38685626227668133590597632)), (1305717/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-381227890626831/618970019642690137449562112), (1218245979799881/1237940039285380274899124224)), (41783173/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((43530056516717/19807040628566084398385987584), (-1085660299639365/19807040628566084398385987584)), (1337061839/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((730259552956743/633825300114114700748351602688), (1405871138741133/633825300114114700748351602688)), (10696494813/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-471820568761645/5070602400912917605986812821504), (-152075906540203/2535301200456458802993406410752)), (684575668269/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

theorem A_gcorr2 : AnalyticAt ℂ F_gcorr2 c := by
  exact analyticAt_const.mul A_iw3

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gcorr2 : Sound J_gcorr2 F_gcorr2 c := by
  apply sound_round (sound_scale A_iw3 S_iw3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gcorr1, J_maincorr1, J_gcorr2,
    J_iw3, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_maincorr2 (s : ℂ) : ℂ := F_maincorr1 s+F_gcorr2 s

def J_maincorr2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((283938844069113/17592186044416), (620114121979785/35184372088832)), (23/35184372088832), by norm_num⟩
  | 1 => ⟨((736290000265179/562949953421312), (302354234759013/1125899906842624)), (19/562949953421312), by norm_num⟩
  | 2 => ⟨((1131565677907849/144115188075855872), (-673524693165485/144115188075855872)), (2477/144115188075855872), by norm_num⟩
  | 3 => ⟨((-244907464410203/4611686018427387904), (451084333008521/4611686018427387904)), (79191/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-46451732338799/590295810358705651712), (-1199245459613119/590295810358705651712)), (2534069/147573952589676412928), by norm_num⟩
  | 5 => ⟨((457333343230123/18889465931478580854784), (706576890614837/18889465931478580854784)), (162180393/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-587252860654137/604462909807314587353088), (-145849518412247/302231454903657293676544)), (10379545103/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((1091581876669011/38685626227668133590597632), (-20188516720173/9671406556917033397649408)), (664290886565/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-195375363510339/309485009821345068724781056), (136801914227941/309485009821345068724781056)), (21257308370037/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem A_maincorr2 : AnalyticAt ℂ F_maincorr2 c := by
  exact A_maincorr1.add A_gcorr2

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_maincorr2 : Sound J_maincorr2 F_maincorr2 c := by
  apply sound_round (sound_add A_maincorr1 A_gcorr2 S_maincorr1 S_gcorr2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr2, J_maincorr1, J_gcorr2, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_gcorr3 (s : ℂ) : ℂ := value ((1/1260), 0)*F_iw5 s

def J_gcorr3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-45836248303477/37778931862957161709568), (-445474236251125/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((9499391146971/37778931862957161709568), (4061533238155/604462909807314587353088)), (529/2417851639229258349412352), by norm_num⟩
  | 2 => ⟨((-911622702205433/38685626227668133590597632), (244549049981841/19342813113834066795298816)), (9615/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((726148351278135/618970019642690137449562112), (-1160234257815121/618970019642690137449562112)), (77653/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((-62185694781231/9903520314283042199192993792), (775471346671523/4951760157141521099596496896)), (77703/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-365125191923703/79228162514264337593543950336), (-1405863033312295/158456325028528675187087900672)), (19892755/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((629169562740147/1267650600228229401496703205376), (811140267953423/2535301200456458802993406410752)), (636569515/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((-666034360585103/20282409603651670423947251286016), (-35621083929265/20282409603651670423947251286016)), (10185113355/40564819207303340847894502572032), by norm_num⟩
  | 8 => ⟨((1013728915714659/649037107316853453566312041152512), (-7960681221987/10141204801825835211973625643008)), (81480907301/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

theorem A_gcorr3 : AnalyticAt ℂ F_gcorr3 c := by
  exact analyticAt_const.mul A_iw5

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gcorr3 : Sound J_gcorr3 F_gcorr3 c := by
  apply sound_round (sound_scale A_iw5 S_iw5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gcorr2, J_maincorr2, J_gcorr3,
    J_iw5, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_maincorr3 (s : ℂ) : ℂ := F_maincorr2 s+F_gcorr3 s

def J_maincorr3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((283938844047769/17592186044416), (620114121953855/35184372088832)), (3/4398046511104), by norm_num⟩
  | 1 => ⟨((736290000406731/562949953421312), (151177117383289/562949953421312)), (39/1125899906842624), by norm_num⟩
  | 2 => ⟨((565782837255895/72057594037927936), (-673524691343453/144115188075855872)), (1239/72057594037927936), by norm_num⟩
  | 3 => ⟨((-30613432374997/576460752303423488), (225542162182051/2305843009213693952)), (158383/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-46451736045355/590295810358705651712), (-1199245367169731/590295810358705651712)), (10136277/590295810358705651712), by norm_num⟩
  | 5 => ⟨((228666628088747/9444732965739290427392), (88322090377863/2361183241434822606848)), (40545099/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-1174505121285421/1208925819614629174706176), (-18231177714599/37778931862957161709568)), (20759090511/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((272895151577321/9671406556917033397649408), (-40377067411259/19342813113834066795298816)), (664290896279/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-781499520506895/1237940039285380274899124224), (68400835643615/154742504910672534362390528)), (21257308680863/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem A_maincorr3 : AnalyticAt ℂ F_maincorr3 c := by
  exact A_maincorr2.add A_gcorr3

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_maincorr3 : Sound J_maincorr3 F_maincorr3 c := by
  apply sound_round (sound_add A_maincorr2 A_gcorr3 S_maincorr2 S_gcorr3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr3, J_maincorr2, J_gcorr3, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_gcorr4 (s : ℂ) : ℂ := value ((-1/1680), 0)*F_iw7 s

def J_gcorr4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1458596323525815/309485009821345068724781056), (-782556959943061/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | 1 => ⟨((-27230563172733/38685626227668133590597632), (696140554689575/618970019642690137449562112)), (269/154742504910672534362390528), by norm_num⟩
  | 2 => ⟨((37311417191365/4951760157141521099596496896), (-1861131231897921/9903520314283042199192993792)), (10337/4951760157141521099596496896), by norm_num⟩
  | 3 => ⟨((730250382793161/79228162514264337593543950336), (702931514417775/39614081257132168796771975168)), (168669/79228162514264337593543950336), by norm_num⟩
  | 4 => ⟨((-943754267802865/633825300114114700748351602688), (-608355135743291/633825300114114700748351602688)), (675837/316912650057057350374175801344), by norm_num⟩
  | 5 => ⟨((699335066012655/5070602400912917605986812821504), (74804855604749/10141204801825835211973625643008)), (21629617/10141204801825835211973625643008), by norm_num⟩
  | 6 => ⟨((-177405022423307/20282409603651670423947251286016), (713290077318867/162259276829213363391578010288128)), (346077011/162259276829213363391578010288128), by norm_num⟩
  | 7 => ⟨((115616690087747/324518553658426726783156020576256), (-43551005304341/81129638414606681695789005144064)), (692154413/324518553658426726783156020576256), by norm_num⟩
  | 8 => ⟨((-110770238202163/41538374868278621028243970633760768), (1656014010591957/41538374868278621028243970633760768)), (44297883925/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

theorem A_gcorr4 : AnalyticAt ℂ F_gcorr4 c := by
  exact analyticAt_const.mul A_iw7

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gcorr4 : Sound J_gcorr4 F_gcorr4 c := by
  apply sound_round (sound_scale A_iw7 S_iw7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gcorr3, J_maincorr3, J_gcorr4,
    J_iw7, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_maincorr4 (s : ℂ) : ℂ := F_maincorr3 s+F_gcorr4 s

def J_maincorr4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((70984711011963/4398046511104), (310057060976883/17592186044416)), (25/35184372088832), by norm_num⟩
  | 1 => ⟨((1472580000812669/1125899906842624), (75588558691961/281474976710656)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((282891418628219/36028797018963968), (-84190586421317/18014398509481984)), (2479/144115188075855872), by norm_num⟩
  | 3 => ⟨((-122453729478735/2305843009213693952), (225542162222967/2305843009213693952)), (9899/576460752303423488), by norm_num⟩
  | 4 => ⟨((-46451736924295/590295810358705651712), (-599622683868153/295147905179352825856)), (5068139/295147905179352825856), by norm_num⟩
  | 5 => ⟨((223307255265/9223372036854775808), (706576723162239/18889465931478580854784)), (324360793/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-9175821342653/9444732965739290427392), (-583397681552743/1208925819614629174706176)), (20759090515/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((1091580620091867/38685626227668133590597632), (-10094269448657/4835703278458516698824704)), (664290896363/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-781499523808105/1237940039285380274899124224), (547206734501983/1237940039285380274899124224)), (21257308683505/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem A_maincorr4 : AnalyticAt ℂ F_maincorr4 c := by
  exact A_maincorr3.add A_gcorr4

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_maincorr4 : Sound J_maincorr4 F_maincorr4 c := by
  apply sound_round (sound_add A_maincorr3 A_gcorr4 S_maincorr3 S_gcorr4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr4, J_maincorr3, J_gcorr4, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_gcorr5 (s : ℂ) : ℂ := value ((1/1188), 0)*F_iw9 s

def J_gcorr5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-60301280307515/39614081257132168796771975168), (187993053726889/4951760157141521099596496896)), (11/9903520314283042199192993792), by norm_num⟩
  | 1 => ⟨((-442575989573347/79228162514264337593543950336), (-53252387455737/4951760157141521099596496896)), (1949/79228162514264337593543950336), by norm_num⟩
  | 2 => ⟨((1143944566889061/633825300114114700748351602688), (737400164704627/633825300114114700748351602688)), (1235/39614081257132168796771975168), by norm_num⟩
  | 3 => ⟨((-1412798111619419/5070602400912917605986812821504), (-18890114987011/1267650600228229401496703205376)), (163175/5070602400912917605986812821504), by norm_num⟩
  | 4 => ⟨((134397740054531/5070602400912917605986812821504), (-270185629598389/20282409603651670423947251286016)), (1309967/40564819207303340847894502572032), by norm_num⟩
  | 5 => ⟨((-122623735076447/81129638414606681695789005144064), (184761748566093/81129638414606681695789005144064)), (5241559/162259276829213363391578010288128), by norm_num⟩
  | 6 => ⟨((39161158710309/2596148429267413814265248164610048), (-585461235072907/2596148429267413814265248164610048)), (20966789/649037107316853453566312041152512), by norm_num⟩
  | 7 => ⟨((608629505881/81129638414606681695789005144064), (1282473732658373/83076749736557242056487941267521536)), (2683754257/83076749736557242056487941267521536), by norm_num⟩
  | 8 => ⟨((-1335214745867909/1329227995784915872903807060280344576), (-912086460874197/1329227995784915872903807060280344576)), (42940073887/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

theorem A_gcorr5 : AnalyticAt ℂ F_gcorr5 c := by
  exact analyticAt_const.mul A_iw9

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gcorr5 : Sound J_gcorr5 F_gcorr5 c := by
  apply sound_round (sound_scale A_iw9 S_iw9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gcorr4, J_maincorr4, J_gcorr5,
    J_iw9, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_maincorr5 (s : ℂ) : ℂ := F_maincorr4 s+F_gcorr5 s

def J_maincorr5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((70984711011963/4398046511104), (620114121953767/35184372088832)), (13/17592186044416), by norm_num⟩
  | 1 => ⟨((1472580000812663/1125899906842624), (37794279345979/140737488355328)), (41/1125899906842624), by norm_num⟩
  | 2 => ⟨((70722854657071/9007199254740992), (-5261911651331/1125899906842624)), (155/9007199254740992), by norm_num⟩
  | 3 => ⟨((-244907458958755/4611686018427387904), (902168648891731/9223372036854775808)), (158385/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-46451736908649/590295810358705651712), (-1199245367744169/590295810358705651712)), (10136279/590295810358705651712), by norm_num⟩
  | 5 => ⟨((457333258754169/18889465931478580854784), (706576723205257/18889465931478580854784)), (162180397/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-293626282960337/302231454903657293676544), (-291698840912685/604462909807314587353088)), (5189772629/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((272895155095521/9671406556917033397649408), (-40377077496029/19342813113834066795298816)), (664290896365/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-781499525051621/1237940039285380274899124224), (68400841706567/154742504910672534362390528)), (10628654341773/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem A_maincorr5 : AnalyticAt ℂ F_maincorr5 c := by
  exact A_maincorr4.add A_gcorr5

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_maincorr5 : Sound J_maincorr5 F_maincorr5 c := by
  apply sound_round (sound_add A_maincorr4 A_gcorr5 S_maincorr4 S_gcorr5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr5, J_maincorr4, J_gcorr5, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_gcorr6 (s : ℂ) : ℂ := value ((-691/360360), 0)*F_iw11 s

def J_gcorr6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-926553196448545/2535301200456458802993406410752), (-597267122414329/2535301200456458802993406410752)), (31/1267650600228229401496703205376), by norm_num⟩
  | 1 => ⟨((1716472079345615/10141204801825835211973625643008), (45900903579585/5070602400912917605986812821504)), (5485/10141204801825835211973625643008), by norm_num⟩
  | 2 => ⟨((-653143478720065/20282409603651670423947251286016), (41032586817119/2535301200456458802993406410752)), (14659/20282409603651670423947251286016), by norm_num⟩
  | 3 => ⟨((496603668251565/162259276829213363391578010288128), (-748251242154369/162259276829213363391578010288128)), (30697/40564819207303340847894502572032), by norm_num⟩
  | 4 => ⟨((-118946636003939/2596148429267413814265248164610048), (1778258059856717/2596148429267413814265248164610048)), (1976521/2596148429267413814265248164610048), by norm_num⟩
  | 5 => ⟨((-331274151503175/10384593717069655257060992658440192), (-1363368049218225/20769187434139310514121985316880384)), (1977829/2596148429267413814265248164610048), by norm_num⟩
  | 6 => ⟨((946291375147691/166153499473114484112975882535043072), (323206244215223/83076749736557242056487941267521536)), (126588965/166153499473114484112975882535043072), by norm_num⟩
  | 7 => ⟨((-1573020861350295/2658455991569831745807614120560689152), (-126344948743881/2658455991569831745807614120560689152)), (2025434221/2658455991569831745807614120560689152), by norm_num⟩
  | 8 => ⟨((56949837929467/1329227995784915872903807060280344576), (-427859380553543/21267647932558653966460912964485513216)), (16203480519/21267647932558653966460912964485513216), by norm_num⟩
  | _ => zero

theorem A_gcorr6 : AnalyticAt ℂ F_gcorr6 c := by
  exact analyticAt_const.mul A_iw11

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gcorr6 : Sound J_gcorr6 F_gcorr6 c := by
  apply sound_round (sound_scale A_iw11 S_iw11)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gcorr5, J_maincorr5, J_gcorr6,
    J_iw11, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_maincorr6 (s : ℂ) : ℂ := F_maincorr5 s+F_gcorr6 s

def J_maincorr6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((70984711011963/4398046511104), (620114121953767/35184372088832)), (27/35184372088832), by norm_num⟩
  | 1 => ⟨((1472580000812663/1125899906842624), (37794279345979/140737488355328)), (21/562949953421312), by norm_num⟩
  | 2 => ⟨((1131565674513131/144115188075855872), (-336762345685183/72057594037927936)), (2481/144115188075855872), by norm_num⟩
  | 3 => ⟨((-244907458958741/4611686018427387904), (112771081111461/1152921504606846976)), (79193/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-11612934227169/147573952589676412928), (-1199245367743765/590295810358705651712)), (1267035/73786976294838206464), by norm_num⟩
  | 5 => ⟨((228666629376783/9444732965739290427392), (706576723204017/18889465931478580854784)), (324360795/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-1174505131834463/1208925819614629174706176), (-583397681820667/1208925819614629174706176)), (20759090517/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((545790310179597/19342813113834066795298816), (-80754154993897/38685626227668133590597632)), (332145448183/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-390749762499291/618970019642690137449562112), (547206733627631/1237940039285380274899124224)), (5314327170887/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem A_maincorr6 : AnalyticAt ℂ F_maincorr6 c := by
  exact A_maincorr5.add A_gcorr6

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_maincorr6 : Sound J_maincorr6 F_maincorr6 c := by
  apply sound_round (sound_add A_maincorr5 A_gcorr6 S_maincorr5 S_gcorr6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr6, J_maincorr5, J_gcorr6, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def expGammaMainValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((802499995162219/5070602400912917605986812821504), (-398876795153/2535301200456458802993406410752)), (1/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((903634236811691/316912650057057350374175801344), (-972480409073/316912650057057350374175801344)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((480457365372503/9903520314283042199192993792), (-2192411272303/39614081257132168796771975168)), (3/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((961817424843549/1237940039285380274899124224), (-291667886101/309485009821345068724781056)), (1/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1805329010097155/154742504910672534362390528), (-2337723930143/154742504910672534362390528)), (1/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1581587806800633/9671406556917033397649408), (-549070508817/2417851639229258349412352)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1286848527137297/604462909807314587353088), (-60200803969/18889465931478580854784)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((483361302330147/18889465931478580854784), (-3139242764501/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((166478546800283/590295810358705651712), (-2362160950315/4722366482869645213696)), (3/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((208584413493699/73786976294838206464), (-815145881653/147573952589676412928)), (3/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1882628893901753/73786976294838206464), (-255921286025/4611686018427387904)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1889371473684901/9223372036854775808), (-2316437604809/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1660828469535653/1152921504606846976), (-72905770741/18014398509481984)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((1253303937988991/144115188075855872), (-4120271403953/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((1580197326253615/36028797018963968), (-1564076083515/9007199254740992)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((1600796782596199/9007199254740992), (-3977511313651/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((306696855435193/562949953421312), (-4080340810467/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 1 => ⟨((1280512566145451/1125899906842624), (-6384170035511/562949953421312)), (5/562949953421312), by norm_num⟩
  | 0 => ⟨((1448585898327515/1125899906842624), (-27726886992159/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | _ => zero

def expGammaMainValueSquares : ℕ → Disk
  | 0 => ⟨((1448585898327515/1125899906842624), (-27726886992159/1125899906842624)), (72483543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((931535881574711/562949953421312), (-35673488608767/562949953421312)), (51/1125899906842624), by norm_num⟩
  | 2 => ⟨((769594611035677/281474976710656), (-59030353334345/281474976710656)), (11/70368744177664), by norm_num⟩
  | 3 => ⟨((1045903422039589/140737488355328), (-40349449837901/35184372088832)), (65/70368744177664), by norm_num⟩
  | 4 => ⟨((948454398218407/17592186044416), (-149930299865543/8796093022208)), (35/2199023255552), by norm_num⟩
  | 5 => ⟨((719113094608263/274877906944), (-252601588239683/137438953472)), (311/137438953472), by norm_num⟩
  | 6 => ⟨((232608060201961/67108864), (-161336819301639/16777216)), (2707/134217728), by norm_num⟩
  | _ => zero

def expGammaMainValue : CertifiedScalarExp.Data :=
  ⟨⟨((70984711011963/4398046511104), (620114121953767/35184372088832)), (27/35184372088832), by norm_num⟩, 3, expGammaMainValuePoly, expGammaMainValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem expGammaMainValue_checks : CertifiedScalarExp.Checks expGammaMainValue := by
  constructor
  · norm_num [expGammaMainValue, CertifiedScalarExp.reduced, expGammaMainValuePoly, expGammaMainValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [expGammaMainValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        expGammaMainValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [expGammaMainValue, expGammaMainValueSquares, expGammaMainValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [expGammaMainValue, CertifiedScalarExp.roundingCheck, expGammaMainValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_expGammaMain (s : ℂ) : ℂ := Complex.exp (F_maincorr6 s)

def J_expGammaMain : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((232608060201961/67108864), (-161336819301639/16777216)), (2707/134217728), by norm_num⟩
  | 1 => ⟨((119383938210877/16777216), (-781592978738109/67108864)), (2167/67108864), by norm_num⟩
  | 2 => ⟨((832088799721205/134217728), (-453162555785403/67108864)), (441/16777216), by norm_num⟩
  | 3 => ⟨((444126865772103/134217728), (-331691619136995/134217728)), (3943/268435456), by norm_num⟩
  | 4 => ⟨((674844878279321/536870912), (-336040437917515/536870912)), (1769/268435456), by norm_num⟩
  | 5 => ⟨((1582175567724699/4294967296), (-235361010143135/2147483648)), (379/134217728), by norm_num⟩
  | 6 => ⟨((5875079314883/67108864), (-92601353076659/8589934592)), (6337/4294967296), by norm_num⟩
  | 7 => ⟨((599438169519003/34359738368), (46030022644383/68719476736)), (18485/17179869184), by norm_num⟩
  | 8 => ⟨((1641071474813629/549755813888), (322252174969745/549755813888)), (66793/68719476736), by norm_num⟩
  | _ => zero

theorem A_expGammaMain : AnalyticAt ℂ F_expGammaMain c := by
  exact A_maincorr6.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_expGammaMain : Sound J_expGammaMain F_expGammaMain c := by
  apply exp_sound A_maincorr6 S_maincorr6 expGammaMainValue expGammaMainValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [expGammaMainValue, J_maincorr6]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_expGammaMain, J_maincorr6, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_halfVariable (s : ℂ) : ℂ := value ((1/2), 0)*F_variable s

def J_halfVariable : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_halfVariable : AnalyticAt ℂ F_halfVariable c := by
  exact analyticAt_const.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale A_variable S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_maincorr6, J_expGammaMain, J_halfVariable,
    J_variable, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

theorem V_gammaInv0 : F_halfVariable c = value ((1/4), 7) := by
  have h := centre_contains S_halfVariable
  have he : J_halfVariable ⟨0,by omega⟩ = exact ((1/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_halfVariable, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv0 : F_halfVariable c ≠ 0 := by
  rw [V_gammaInv0]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv0 (s : ℂ) : ℂ := (F_halfVariable s)⁻¹

def J_gammaInv0 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((4/785), (-112/785)), 0, by norm_num⟩
  | 1 => ⟨((1464947929907357/144115188075855872), (13096597074523/18014398509481984)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-179305403295817/2305843009213693952), (833911220602493/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-948172697079109/18446744073709551616), (-136323541064721/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 4 => ⟨((194251489300027/295147905179352825856), (-1076688386329695/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 5 => ⟨((1221014963686377/4722366482869645213696), (265609379331687/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-88235185579349/18889465931478580854784), (1382840646273095/75557863725914323419136)), (3/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-1563988681919155/1208925819614629174706176), (-114804396750677/302231454903657293676544)), (1/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((293953245717095/9671406556917033397649408), (-883209488035335/9671406556917033397649408)), (3/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem A_gammaInv0 : AnalyticAt ℂ F_gammaInv0 c := by
  exact A_halfVariable.inv N_gammaInv0

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv0 : Sound J_gammaInv0 F_gammaInv0 c := by
  apply inv_coefficients_sound A_halfVariable N_gammaInv0 S_halfVariable
  · rw [V_gammaInv0]
    have hv : (value ((1/4), 7))⁻¹ = value ((4/785), (-112/785)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv0] using contains_exact ((4/785), (-112/785))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv0, J_halfVariable, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_q1 (s : ℂ) : ℂ := value (1, 0)

def J_q1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q1 : AnalyticAt ℂ F_q1 c := by
  exact analyticAt_const

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (c := c) (contains_exact (1, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift1 (s : ℂ) : ℂ := F_halfVariable s+F_q1 s

def J_shift1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((5/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift1 : AnalyticAt ℂ F_shift1 c := by
  exact A_halfVariable.add A_q1

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift1 : Sound J_shift1 F_shift1 c := by
  apply sound_round (sound_add A_halfVariable A_q1 S_halfVariable S_q1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift1, J_halfVariable, J_q1, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv1 : F_shift1 c = value ((5/4), 7) := by
  have h := centre_contains S_shift1
  have he : J_shift1 ⟨0,by omega⟩ = exact ((5/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift1, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv1 : F_shift1 c ≠ 0 := by
  rw [V_gammaInv1]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv1 (s : ℂ) : ℂ := (F_shift1 s)⁻¹

def J_gammaInv1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((20/809), (-112/809)), 0, by norm_num⟩
  | 1 => ⟨((334260055676405/36028797018963968), (493242769904577/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-405359677050309/1152921504606846976), (691637327787085/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-685846103052137/18446744073709551616), (-292870360372689/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 4 => ⟨((392187306722003/147573952589676412928), (-643757222516013/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 5 => ⟨((69732159027087/590295810358705651712), (249011374922247/1180591620717411303424)), (3/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-4740197829477/295147905179352825856), (3287940705693/590295810358705651712)), (1/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-113058615920359/604462909807314587353088), (-1427224527795685/1208925819614629174706176)), (11/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((406357210753847/4835703278458516698824704), (31835457006213/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem A_gammaInv1 : AnalyticAt ℂ F_gammaInv1 c := by
  exact A_shift1.inv N_gammaInv1

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv1 : Sound J_gammaInv1 F_gammaInv1 c := by
  apply inv_coefficients_sound A_shift1 N_gammaInv1 S_shift1
  · rw [V_gammaInv1]
    have hv : (value ((5/4), 7))⁻¹ = value ((20/809), (-112/809)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv1] using contains_exact ((20/809), (-112/809))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv1, J_shift1, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd1 (s : ℂ) : ℂ := F_gammaInv0 s*F_gammaInv1 s

def J_gammaInvProd1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1414226657253563/72057594037927936), (-152496841090243/36028797018963968)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((511630828806949/576460752303423488), (-776939986616785/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((631413950804801/2305843009213693952), (569095571261633/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-524653188053945/36893488147419103232), (898834359361313/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-295061562071989/147573952589676412928), (-432931163813683/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 5 => ⟨((663157691469683/4722366482869645213696), (-182609030089325/1180591620717411303424)), (3/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((860549902028715/75557863725914323419136), (961984235944393/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-668935725039219/604462909807314587353088), (60500433799561/75557863725914323419136)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-259380587895299/4835703278458516698824704), (-899127216538443/9671406556917033397649408)), (5/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd1 : AnalyticAt ℂ F_gammaInvProd1 c := by
  exact A_gammaInv0.mul A_gammaInv1

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd1 : Sound J_gammaInvProd1 F_gammaInvProd1 c := by
  apply sound_round (sound_mul A_gammaInv0 A_gammaInv1 S_gammaInv0 S_gammaInv1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift1, J_gammaInv1, J_gammaInvProd1,
    J_gammaInv0, J_gammaInv1, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q2 (s : ℂ) : ℂ := value (2, 0)

def J_q2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q2 : AnalyticAt ℂ F_q2 c := by
  exact analyticAt_const

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (c := c) (contains_exact (2, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift2 (s : ℂ) : ℂ := F_halfVariable s+F_q2 s

def J_shift2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((9/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift2 : AnalyticAt ℂ F_shift2 c := by
  exact A_halfVariable.add A_q2

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift2 : Sound J_shift2 F_shift2 c := by
  apply sound_round (sound_add A_halfVariable A_q2 S_halfVariable S_q2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift2, J_halfVariable, J_q2, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv2 : F_shift2 c = value ((9/4), 7) := by
  have h := centre_contains S_shift2
  have he : J_shift2 ⟨0,by omega⟩ = exact ((9/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift2, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv2 : F_shift2 c ≠ 0 := by
  rw [V_gammaInv2]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv2 (s : ℂ) : ℂ := (F_shift2 s)⁻¹

def J_gammaInv2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((36/865), (-112/865)), 0, by norm_num⟩
  | 1 => ⟨((270808853532899/36028797018963968), (776601207286379/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-582547098843061/1152921504606846976), (431744383447071/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-15828714096949/1152921504606846976), (-186793232079809/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 4 => ⟨((1716544874757865/590295810358705651712), (-13566060043839/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-271707829093471/4722366482869645213696), (446774063112225/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-835106666263801/75557863725914323419136), (-578950375977331/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((877745961571865/1208925819614629174706176), (-672274988081959/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((404124338021663/19342813113834066795298816), (1133035350446237/19342813113834066795298816)), (19/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem A_gammaInv2 : AnalyticAt ℂ F_gammaInv2 c := by
  exact A_shift2.inv N_gammaInv2

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv2 : Sound J_gammaInv2 F_gammaInv2 c := by
  apply inv_coefficients_sound A_shift2 N_gammaInv2 S_shift2
  · rw [V_gammaInv2]
    have hv : (value ((9/4), 7))⁻¹ = value ((36/865), (-112/865)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv2] using contains_exact ((36/865), (-112/865))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv2, J_shift2, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd2 (s : ℂ) : ℂ := F_gammaInvProd1 s*F_gammaInv2 s

def J_gammaInvProd2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-49174249748753/36028797018963968), (1363362895296199/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((-503588405489147/1152921504606846976), (-420446223706361/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((277039107219297/4611686018427387904), (-235238103049211/4611686018427387904)), (5/18446744073709551616), by norm_num⟩
  | 3 => ⟨((42565020868495/9223372036854775808), (575969944213597/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-516225300209051/590295810358705651712), (394519997316981/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-41601852460121/2361183241434822606848), (-1665866987643675/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((619466940055513/75557863725914323419136), (-18911275180821/75557863725914323419136)), (3/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-914094752601/9444732965739290427392), (1722956480506701/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-1129413428287461/19342813113834066795298816), (-174263634909215/9671406556917033397649408)), (17/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd2 : AnalyticAt ℂ F_gammaInvProd2 c := by
  exact A_gammaInvProd1.mul A_gammaInv2

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd2 : Sound J_gammaInvProd2 F_gammaInvProd2 c := by
  apply sound_round (sound_mul A_gammaInvProd1 A_gammaInv2 S_gammaInvProd1 S_gammaInv2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift2, J_gammaInv2, J_gammaInvProd2,
    J_gammaInvProd1, J_gammaInv2, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q3 (s : ℂ) : ℂ := value (3, 0)

def J_q3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q3 : AnalyticAt ℂ F_q3 c := by
  exact analyticAt_const

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (c := c) (contains_exact (3, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift3 (s : ℂ) : ℂ := F_halfVariable s+F_q3 s

def J_shift3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((13/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift3 : AnalyticAt ℂ F_shift3 c := by
  exact A_halfVariable.add A_q3

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift3 : Sound J_shift3 F_shift3 c := by
  apply sound_round (sound_add A_halfVariable A_q3 S_halfVariable S_q3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift3, J_halfVariable, J_q3, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv3 : F_shift3 c = value ((13/4), 7) := by
  have h := centre_contains S_shift3
  have he : J_shift3 ⟨0,by omega⟩ = exact ((13/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift3, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv3 : F_shift3 c ≠ 0 := by
  rw [V_gammaInv3]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv3 (s : ℂ) : ℂ := (F_shift3 s)⁻¹

def J_gammaInv3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((52/953), (-112/953)), 0, by norm_num⟩
  | 1 => ⟨((780708763437943/144115188075855872), (231039016171879/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-151209165733237/288230376151711744), (165302271317099/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 3 => ⟨((217211367639005/36893488147419103232), (-1281635666014343/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 4 => ⟨((1110163303054591/590295810358705651712), (381837262574247/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-1202602632322939/9444732965739290427392), (710406838483883/9444732965739290427392)), (3/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-142960999197499/151115727451828646838272), (-1440777757996483/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((1417008023956987/2417851639229258349412352), (247256291734301/1208925819614629174706176)), (3/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-1083482279909731/38685626227668133590597632), (279098099355331/9671406556917033397649408)), (17/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem A_gammaInv3 : AnalyticAt ℂ F_gammaInv3 c := by
  exact A_shift3.inv N_gammaInv3

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv3 : Sound J_gammaInv3 F_gammaInv3 c := by
  apply inv_coefficients_sound A_shift3 N_gammaInv3 S_shift3
  · rw [V_gammaInv3]
    have hv : (value ((13/4), 7))⁻¹ = value ((52/953), (-112/953)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv3] using contains_exact ((52/953), (-112/953))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv3, J_shift3, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd3 (s : ℂ) : ℂ := F_gammaInvProd2 s*F_gammaInv3 s

def J_gammaInvProd3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((234593218220801/1152921504606846976), (333714850168243/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-823202765361683/9223372036854775808), (163690794955065/4611686018427387904)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-87350955163819/36893488147419103232), (-1184745426502901/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 3 => ⟨((1285235475222647/590295810358705651712), (107720902511339/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-185515587229983/2361183241434822606848), (144015946170859/590295810358705651712)), (11/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-55531585340221/2361183241434822606848), (-529448213738489/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((284563897176095/151115727451828646838272), (-597460555764511/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((346365628780033/2417851639229258349412352), (519458246801389/2417851639229258349412352)), (21/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-422377647265353/19342813113834066795298816), (326328168512913/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd3 : AnalyticAt ℂ F_gammaInvProd3 c := by
  exact A_gammaInvProd2.mul A_gammaInv3

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd3 : Sound J_gammaInvProd3 F_gammaInvProd3 c := by
  apply sound_round (sound_mul A_gammaInvProd2 A_gammaInv3 S_gammaInvProd2 S_gammaInv3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift3, J_gammaInv3, J_gammaInvProd3,
    J_gammaInvProd2, J_gammaInv3, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q4 (s : ℂ) : ℂ := value (4, 0)

def J_q4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q4 : AnalyticAt ℂ F_q4 c := by
  exact analyticAt_const

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (c := c) (contains_exact (4, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift4 (s : ℂ) : ℂ := F_halfVariable s+F_q4 s

def J_shift4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((17/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift4 : AnalyticAt ℂ F_shift4 c := by
  exact A_halfVariable.add A_q4

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift4 : Sound J_shift4 F_shift4 c := by
  apply sound_round (sound_add A_halfVariable A_q4 S_halfVariable S_q4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift4, J_halfVariable, J_q4, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv4 : F_shift4 c = value ((17/4), 7) := by
  have h := centre_contains S_shift4
  have he : J_shift4 ⟨0,by omega⟩ = exact ((17/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift4, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv4 : F_shift4 c ≠ 0 := by
  rw [V_gammaInv4]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv4 (s : ℂ) : ℂ := (F_shift4 s)⁻¹

def J_gammaInv4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((68/1073), (-112/1073)), 0, by norm_num⟩
  | 1 => ⟨((495684678124489/144115188075855872), (476658397550013/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-2094733109616673/4611686018427387904), (-138808695125577/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((294479823500463/18446744073709551616), (-419703852765197/18446744073709551616)), (3/36893488147419103232), by norm_num⟩
  | 4 => ⟨((201172067188597/295147905179352825856), (917377106730069/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-1940065417952163/18889465931478580854784), (-258253125180227/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((299811367084683/75557863725914323419136), (-372276075113489/75557863725914323419136)), (5/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((317729691719699/2417851639229258349412352), (878190437594807/2417851639229258349412352)), (7/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-447205770913543/19342813113834066795298816), (-179915931286789/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem A_gammaInv4 : AnalyticAt ℂ F_gammaInv4 c := by
  exact A_shift4.inv N_gammaInv4

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv4 : Sound J_gammaInv4 F_gammaInv4 c := by
  apply inv_coefficients_sound A_shift4 N_gammaInv4 S_shift4
  · rw [V_gammaInv4]
    have hv : (value ((17/4), 7))⁻¹ = value ((68/1073), (-112/1073)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv4] using contains_exact ((68/1073), (-112/1073))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv4, J_shift4, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd4 (s : ℂ) : ℂ := F_gammaInvProd3 s*F_gammaInv4 s

def J_gammaInvProd4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1590409008249251/36893488147419103232), (-6676291946485/2305843009213693952)), (9/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-58404542681763/18446744073709551616), (128270605456299/9223372036854775808)), (3/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-361777131612873/147573952589676412928), (-25388699275473/18446744073709551616)), (7/295147905179352825856), by norm_num⟩
  | 3 => ⟨((723798666905529/2361183241434822606848), (-708430659920725/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((499288322338703/18889465931478580854784), (928756390771639/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-960629586111189/151115727451828646838272), (104892786439743/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((50743468642617/1208925819614629174706176), (-843338540017485/1208925819614629174706176)), (31/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((643934937606927/9671406556917033397649408), (222033549182825/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-294884010598577/77371252455336267181195264), (860569512698619/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd4 : AnalyticAt ℂ F_gammaInvProd4 c := by
  exact A_gammaInvProd3.mul A_gammaInv4

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd4 : Sound J_gammaInvProd4 F_gammaInvProd4 c := by
  apply sound_round (sound_mul A_gammaInvProd3 A_gammaInv4 S_gammaInvProd3 S_gammaInv4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift4, J_gammaInv4, J_gammaInvProd4,
    J_gammaInvProd3, J_gammaInv4, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q5 (s : ℂ) : ℂ := value (5, 0)

def J_q5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q5 : AnalyticAt ℂ F_q5 c := by
  exact analyticAt_const

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (c := c) (contains_exact (5, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift5 (s : ℂ) : ℂ := F_halfVariable s+F_q5 s

def J_shift5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((21/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift5 : AnalyticAt ℂ F_shift5 c := by
  exact A_halfVariable.add A_q5

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift5 : Sound J_shift5 F_shift5 c := by
  apply sound_round (sound_add A_halfVariable A_q5 S_halfVariable S_q5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift5, J_halfVariable, J_q5, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv5 : F_shift5 c = value ((21/4), 7) := by
  have h := centre_contains S_shift5
  have he : J_shift5 ⟨0,by omega⟩ = exact ((21/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift5, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv5 : F_shift5 c ≠ 0 := by
  rw [V_gammaInv5]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv5 (s : ℂ) : ℂ := (F_shift5 s)⁻¹

def J_gammaInv5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((12/175), (-16/175)), 0, by norm_num⟩
  | 1 => ⟨((65881228834677/36028797018963968), (451756997723499/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 2 => ⟨((-1610836380454077/4611686018427387904), (-605784621709225/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 3 => ⟨((663373497435349/36893488147419103232), (-105736952152883/9223372036854775808)), (5/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-109103271445913/1180591620717411303424), (1434454826267791/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-989350306876969/18889465931478580854784), (-433351091619385/9444732965739290427392)), (5/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((588330025470719/151115727451828646838272), (-62047756699043/75557863725914323419136)), (7/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-14498377403655/151115727451828646838272), (124599160780669/604462909807314587353088)), (19/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-474574430030725/77371252455336267181195264), (-886157196142427/77371252455336267181195264)), (25/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem A_gammaInv5 : AnalyticAt ℂ F_gammaInv5 c := by
  exact A_shift5.inv N_gammaInv5

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv5 : Sound J_gammaInv5 F_gammaInv5 c := by
  apply inv_coefficients_sound A_shift5 N_gammaInv5 S_shift5
  · rw [V_gammaInv5]
    have hv : (value ((21/4), 7))⁻¹ = value ((12/175), (-16/175)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv5] using contains_exact ((12/175), (-16/175))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv5, J_shift5, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd5 (s : ℂ) : ℂ := F_gammaInvProd4 s*F_gammaInv5 s

def J_gammaInvProd5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((794321250774439/295147905179352825856), (-305467339265293/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 1 => ⟨((339828029431825/295147905179352825856), (222552175915179/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-475016255187745/1180591620717411303424), (308582220580277/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((26616262479793/18889465931478580854784), (-1350111999818183/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((1439669053443537/151115727451828646838272), (262172928699151/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-960172207867891/1208925819614629174706176), (600200629382659/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-47790490969953/604462909807314587353088), (-1180148260298365/9671406556917033397649408)), (9/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((1156975051598205/77371252455336267181195264), (-38141998250747/9671406556917033397649408)), (9/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-13197879395833/154742504910672534362390528), (479272630276353/309485009821345068724781056)), (69/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd5 : AnalyticAt ℂ F_gammaInvProd5 c := by
  exact A_gammaInvProd4.mul A_gammaInv5

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd5 : Sound J_gammaInvProd5 F_gammaInvProd5 c := by
  apply sound_round (sound_mul A_gammaInvProd4 A_gammaInv5 S_gammaInvProd4 S_gammaInv5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift5, J_gammaInv5, J_gammaInvProd5,
    J_gammaInvProd4, J_gammaInv5, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q6 (s : ℂ) : ℂ := value (6, 0)

def J_q6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q6 : AnalyticAt ℂ F_q6 c := by
  exact analyticAt_const

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (c := c) (contains_exact (6, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift6 (s : ℂ) : ℂ := F_halfVariable s+F_q6 s

def J_shift6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((25/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift6 : AnalyticAt ℂ F_shift6 c := by
  exact A_halfVariable.add A_q6

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift6 : Sound J_shift6 F_shift6 c := by
  apply sound_round (sound_add A_halfVariable A_q6 S_halfVariable S_q6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift6, J_halfVariable, J_q6, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv6 : F_shift6 c = value ((25/4), 7) := by
  have h := centre_contains S_shift6
  have he : J_shift6 ⟨0,by omega⟩ = exact ((25/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift6, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv6 : F_shift6 c ≠ 0 := by
  rw [V_gammaInv6]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv6 (s : ℂ) : ℂ := (F_shift6 s)⁻¹

def J_gammaInv6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((100/1409), (-112/1409)), 0, by norm_num⟩
  | 1 => ⟨((184673624774013/288230376151711744), (406514268370469/72057594037927936)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-569441461199067/2305843009213693952), (-805804180970891/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((1159053856684475/73786976294838206464), (-8334717745121/2305843009213693952)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-488481233612115/1180591620717411303424), (888489020485725/1180591620717411303424)), (5/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-287651650436847/18889465931478580854784), (-815096097732459/18889465931478580854784)), (13/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((340825913384585/151115727451828646838272), (279872959116077/302231454903657293676544)), (17/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-1130003737094877/9671406556917033397649408), (549129410209105/9671406556917033397649408)), (11/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((73098480860281/38685626227668133590597632), (-1030366839321713/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem A_gammaInv6 : AnalyticAt ℂ F_gammaInv6 c := by
  exact A_shift6.inv N_gammaInv6

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv6 : Sound J_gammaInv6 F_gammaInv6 c := by
  apply inv_coefficients_sound A_shift6 N_gammaInv6 S_shift6
  · rw [V_gammaInv6]
    have hv : (value ((25/4), 7))⁻¹ = value ((100/1409), (-112/1409)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv6] using contains_exact ((100/1409), (-112/1409))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv6, J_shift6, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd6 (s : ℂ) : ℂ := F_gammaInvProd5 s*F_gammaInv6 s

def J_gammaInvProd6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-163001399328339/1180591620717411303424), (-1198869642542821/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((535211329099143/2361183241434822606848), (132412906310487/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-516168460832981/18889465931478580854784), (930721788456337/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-992834150992551/151115727451828646838272), (-1211831055267673/151115727451828646838272)), (1/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((56812968065575/37778931862957161709568), (-36840137664317/75557863725914323419136)), (3/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-110513926829045/9671406556917033397649408), (2037532218950743/9671406556917033397649408)), (15/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-900546482967015/38685626227668133590597632), (-398693135732135/38685626227668133590597632)), (17/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((38365960650435/19342813113834066795298816), (-313820719515527/154742504910672534362390528)), (9/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((630167333168783/4951760157141521099596496896), (41391611322443/154742504910672534362390528)), (35/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd6 : AnalyticAt ℂ F_gammaInvProd6 c := by
  exact A_gammaInvProd5.mul A_gammaInv6

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd6 : Sound J_gammaInvProd6 F_gammaInvProd6 c := by
  apply sound_round (sound_mul A_gammaInvProd5 A_gammaInv6 S_gammaInvProd5 S_gammaInv6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift6, J_gammaInv6, J_gammaInvProd6,
    J_gammaInvProd5, J_gammaInv6, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q7 (s : ℂ) : ℂ := value (7, 0)

def J_q7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q7 : AnalyticAt ℂ F_q7 c := by
  exact analyticAt_const

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (c := c) (contains_exact (7, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift7 (s : ℂ) : ℂ := F_halfVariable s+F_q7 s

def J_shift7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((29/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift7 : AnalyticAt ℂ F_shift7 c := by
  exact A_halfVariable.add A_q7

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift7 : Sound J_shift7 F_shift7 c := by
  apply sound_round (sound_add A_halfVariable A_q7 S_halfVariable S_q7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift7, J_halfVariable, J_q7, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv7 : F_shift7 c = value ((29/4), 7) := by
  have h := centre_contains S_shift7
  have he : J_shift7 ⟨0,by omega⟩ = exact ((29/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift7, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv7 : F_shift7 c ≠ 0 := by
  rw [V_gammaInv7]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv7 (s : ℂ) : ℂ := (F_shift7 s)⁻¹

def J_gammaInv7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((116/1625), (-112/1625)), 0, by norm_num⟩
  | 1 => ⟨((-49773463299477/288230376151711744), (177263386838487/36028797018963968)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-11773405604965/72057594037927936), (-418646279078541/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((222993882738281/18446744073709551616), (62691275666867/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-543953646598161/1180591620717411303424), (456020044255475/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 5 => ⟨((118393876172539/37778931862957161709568), (-560350195951405/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((550324944034955/604462909807314587353088), (88160836672031/75557863725914323419136)), (3/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-1406324215790223/19342813113834066795298816), (-198664494274263/19342813113834066795298816)), (7/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((912659851768041/309485009821345068724781056), (-20686650897337/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem A_gammaInv7 : AnalyticAt ℂ F_gammaInv7 c := by
  exact A_shift7.inv N_gammaInv7

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv7 : Sound J_gammaInv7 F_gammaInv7 c := by
  apply inv_coefficients_sound A_shift7 N_gammaInv7 S_shift7
  · rw [V_gammaInv7]
    have hv : (value ((29/4), 7))⁻¹ = value ((116/1625), (-112/1625)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv7] using contains_exact ((116/1625), (-112/1625))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv7, J_shift7, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd7 (s : ℂ) : ℂ := F_gammaInvProd6 s*F_gammaInv7 s

def J_gammaInvProd7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-423605475960543/9444732965739290427392), (-31555866180129/1180591620717411303424)), (9/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((779580783679903/37778931862957161709568), (-268473681130577/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((2830152482083/2361183241434822606848), (1000242857958595/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-1562648446839575/1208925819614629174706176), (-380286999461895/1208925819614629174706176)), (45/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((632127735757587/4835703278458516698824704), (-830632960261463/4835703278458516698824704)), (35/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((289339159645191/19342813113834066795298816), (127964008307175/4835703278458516698824704)), (23/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-1181579034912637/309485009821345068724781056), (34022754920751/77371252455336267181195264)), (55/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((304353815229115/2475880078570760549798248448), (-1061513420356449/2475880078570760549798248448)), (15/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((375423269096073/9903520314283042199192993792), (591483332876341/19807040628566084398385987584)), (31/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd7 : AnalyticAt ℂ F_gammaInvProd7 c := by
  exact A_gammaInvProd6.mul A_gammaInv7

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd7 : Sound J_gammaInvProd7 F_gammaInvProd7 c := by
  apply sound_round (sound_mul A_gammaInvProd6 A_gammaInv7 S_gammaInvProd6 S_gammaInv7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift7, J_gammaInv7, J_gammaInvProd7,
    J_gammaInvProd6, J_gammaInv7, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q8 (s : ℂ) : ℂ := value (8, 0)

def J_q8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q8 : AnalyticAt ℂ F_q8 c := by
  exact analyticAt_const

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (c := c) (contains_exact (8, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift8 (s : ℂ) : ℂ := F_halfVariable s+F_q8 s

def J_shift8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((33/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift8 : AnalyticAt ℂ F_shift8 c := by
  exact A_halfVariable.add A_q8

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift8 : Sound J_shift8 F_shift8 c := by
  apply sound_round (sound_add A_halfVariable A_q8 S_halfVariable S_q8)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift8, J_halfVariable, J_q8, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv8 : F_shift8 c = value ((33/4), 7) := by
  have h := centre_contains S_shift8
  have he : J_shift8 ⟨0,by omega⟩ = exact ((33/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift8, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv8 : F_shift8 c ≠ 0 := by
  rw [V_gammaInv8]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv8 (s : ℂ) : ℂ := (F_shift8 s)⁻¹

def J_gammaInv8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((132/1873), (-112/1873)), 0, by norm_num⟩
  | 1 => ⟨((-50118034271985/72057594037927936), (1214663965044303/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-468040755960935/4611686018427387904), (-780730476197319/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((637365480495219/73786976294838206464), (108138511885577/36893488147419103232)), (5/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-925618964978009/2361183241434822606848), (365927318122133/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((346814068328535/37778931862957161709568), (-1298210187461045/75557863725914323419136)), (13/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((114982652337221/604462909807314587353088), (265937102029311/302231454903657293676544)), (7/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-638527461510551/19342813113834066795298816), (-61216591429759/2417851639229258349412352)), (1/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((594279512399175/309485009821345068724781056), (-29344816398745/309485009821345068724781056)), (35/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem A_gammaInv8 : AnalyticAt ℂ F_gammaInv8 c := by
  exact A_shift8.inv N_gammaInv8

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv8 : Sound J_gammaInv8 F_gammaInv8 c := by
  apply inv_coefficients_sound A_shift8 N_gammaInv8 S_shift8
  · rw [V_gammaInv8]
    have hv : (value ((33/4), 7))⁻¹ = value ((132/1873), (-112/1873)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv8] using contains_exact ((132/1873), (-112/1873))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv8, J_shift8, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd8 (s : ℂ) : ℂ := F_gammaInvProd7 s*F_gammaInv8 s

def J_gammaInvProd8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-359594143829951/75557863725914323419136), (241252640621285/302231454903657293676544)), (19/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((113068653784383/151115727451828646838272), (-90896460172443/37778931862957161709568)), (41/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((317852865325911/604462909807314587353088), (75853728967653/151115727451828646838272)), (15/604462909807314587353088), by norm_num⟩
  | 3 => ⟨((-1387296477194169/9671406556917033397649408), (514116365781713/9671406556917033397649408)), (29/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((23273352991177/9671406556917033397649408), (-2018169769068627/77371252455336267181195264)), (93/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((515549125325809/154742504910672534362390528), (607072523058803/309485009821345068724781056)), (65/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((-518472577123911/1237940039285380274899124224), (717461108480433/2475880078570760549798248448)), (5/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-215501297871765/19807040628566084398385987584), (-1194356692323753/19807040628566084398385987584)), (91/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((526353308602627/79228162514264337593543950336), (129718006779937/79228162514264337593543950336)), (3/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd8 : AnalyticAt ℂ F_gammaInvProd8 c := by
  exact A_gammaInvProd7.mul A_gammaInv8

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd8 : Sound J_gammaInvProd8 F_gammaInvProd8 c := by
  apply sound_round (sound_mul A_gammaInvProd7 A_gammaInv8 S_gammaInvProd7 S_gammaInv8)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift8, J_gammaInv8, J_gammaInvProd8,
    J_gammaInvProd7, J_gammaInv8, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q9 (s : ℂ) : ℂ := value (9, 0)

def J_q9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q9 : AnalyticAt ℂ F_q9 c := by
  exact analyticAt_const

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (c := c) (contains_exact (9, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift9 (s : ℂ) : ℂ := F_halfVariable s+F_q9 s

def J_shift9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((37/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift9 : AnalyticAt ℂ F_shift9 c := by
  exact A_halfVariable.add A_q9

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift9 : Sound J_shift9 F_shift9 c := by
  apply sound_round (sound_add A_halfVariable A_q9 S_halfVariable S_q9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift9, J_halfVariable, J_q9, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv9 : F_shift9 c = value ((37/4), 7) := by
  have h := centre_contains S_shift9
  have he : J_shift9 ⟨0,by omega⟩ = exact ((37/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift9, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv9 : F_shift9 c ≠ 0 := by
  rw [V_gammaInv9]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv9 (s : ℂ) : ℂ := (F_shift9 s)⁻¹

def J_gammaInv9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((148/2153), (-112/2153)), 0, by norm_num⟩
  | 1 => ⟨((-36375381341485/36028797018963968), (257674496203613/72057594037927936)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-537814939458619/9223372036854775808), (-1375833857386043/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 3 => ⟨((868332570616303/147573952589676412928), (532793823218835/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-1398503510649121/4722366482869645213696), (68368832596891/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((356087136227341/37778931862957161709568), (-657202294998165/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-118142629943329/1208925819614629174706176), (1315592815046189/2417851639229258349412352)), (5/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-417561270123355/38685626227668133590597632), (-102727211209541/4835703278458516698824704)), (21/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((571640127160261/618970019642690137449562112), (556337432927307/1237940039285380274899124224)), (21/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem A_gammaInv9 : AnalyticAt ℂ F_gammaInv9 c := by
  exact A_shift9.inv N_gammaInv9

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv9 : Sound J_gammaInv9 F_gammaInv9 c := by
  apply inv_coefficients_sound A_shift9 N_gammaInv9 S_shift9
  · rw [V_gammaInv9]
    have hv : (value ((37/4), 7))⁻¹ = value ((148/2153), (-112/2153)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv9] using contains_exact ((148/2153), (-112/2153))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv9, J_shift9, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd9 (s : ℂ) : ℂ := F_gammaInvProd8 s*F_gammaInv9 s

def J_gammaInvProd9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-345303181417087/1208925819614629174706176), (731271963763189/2417851639229258349412352)), (37/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((-347092999048455/4835703278458516698824704), (-537100966080903/2417851639229258349412352)), (43/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((681874358844955/9671406556917033397649408), (249885421443657/19342813113834066795298816)), (33/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((-23826560614507/2417851639229258349412352), (967601044434157/77371252455336267181195264)), (67/77371252455336267181195264), by norm_num⟩
  | 4 => ⟨((-11393620944455/9671406556917033397649408), (-806022710657827/309485009821345068724781056)), (57/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((1087643399432729/2475880078570760549798248448), (25252282760683/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-581239594634789/19807040628566084398385987584), (1038524083048813/19807040628566084398385987584)), (13/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-671835616434893/158456325028528675187087900672), (-973632492512543/158456325028528675187087900672)), (61/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((1074209635158265/1267650600228229401496703205376), (-167508039738237/1267650600228229401496703205376)), (133/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd9 : AnalyticAt ℂ F_gammaInvProd9 c := by
  exact A_gammaInvProd8.mul A_gammaInv9

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd9 : Sound J_gammaInvProd9 F_gammaInvProd9 c := by
  apply sound_round (sound_mul A_gammaInvProd8 A_gammaInv9 S_gammaInvProd8 S_gammaInv9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift9, J_gammaInv9, J_gammaInvProd9,
    J_gammaInvProd8, J_gammaInv9, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q10 (s : ℂ) : ℂ := value (10, 0)

def J_q10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q10 : AnalyticAt ℂ F_q10 c := by
  exact analyticAt_const

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (c := c) (contains_exact (10, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift10 (s : ℂ) : ℂ := F_halfVariable s+F_q10 s

def J_shift10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((41/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift10 : AnalyticAt ℂ F_shift10 c := by
  exact A_halfVariable.add A_q10

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift10 : Sound J_shift10 F_shift10 c := by
  apply sound_round (sound_add A_halfVariable A_q10 S_halfVariable S_q10)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift10, J_halfVariable, J_q10, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv10 : F_shift10 c = value ((41/4), 7) := by
  have h := centre_contains S_shift10
  have he : J_shift10 ⟨0,by omega⟩ = exact ((41/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift10, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv10 : F_shift10 c ≠ 0 := by
  rw [V_gammaInv10]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv10 (s : ℂ) : ℂ := (F_shift10 s)⁻¹

def J_gammaInv10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((164/2465), (-112/2465)), 0, by norm_num⟩
  | 1 => ⟨((-340399043693195/288230376151711744), (871300116298301/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-271059926067185/9223372036854775808), (-587482067234269/4611686018427387904)), (3/9223372036854775808), by norm_num⟩
  | 3 => ⟨((1142716825544793/295147905179352825856), (526849188911369/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-495610186946033/2361183241434822606848), (-72733873431095/2361183241434822606848)), (7/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((1160908910129747/151115727451828646838272), (-565744236206165/151115727451828646838272)), (7/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-412253815192497/2417851639229258349412352), (361547833951063/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-21707243997515/19342813113834066795298816), (-1069436863854009/77371252455336267181195264)), (13/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((434943223737181/1237940039285380274899124224), (1075296067253035/2475880078570760549798248448)), (3/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem A_gammaInv10 : AnalyticAt ℂ F_gammaInv10 c := by
  exact A_shift10.inv N_gammaInv10

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv10 : Sound J_gammaInv10 F_gammaInv10 c := by
  apply inv_coefficients_sound A_shift10 N_gammaInv10 S_shift10
  · rw [V_gammaInv10]
    have hv : (value ((41/4), 7))⁻¹ = value ((164/2465), (-112/2465)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv10] using contains_exact ((164/2465), (-112/2465))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv10, J_shift10, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd10 (s : ℂ) : ℂ := F_gammaInvProd9 s*F_gammaInv10 s

def J_gammaInvProd10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-101767086615261/19342813113834066795298816), (1280496647104847/38685626227668133590597632)), (67/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((-597520874645647/38685626227668133590597632), (-492801722763643/38685626227668133590597632)), (83/77371252455336267181195264), by norm_num⟩
  | 2 => ⟨((470488861664403/77371252455336267181195264), (-351429975241473/154742504910672534362390528)), (33/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-294753885455753/1237940039285380274899124224), (924420185858667/618970019642690137449562112)), (141/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-137857668853855/618970019642690137449562112), (-865757527623807/4951760157141521099596496896)), (125/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((411340454365747/9903520314283042199192993792), (-11046386529579/618970019642690137449562112)), (93/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-86566510583741/158456325028528675187087900672), (251904773518605/39614081257132168796771975168)), (61/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((-435790824595583/633825300114114700748351602688), (-278949501076091/633825300114114700748351602688)), (147/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((844207769799499/10141204801825835211973625643008), (-489553433940845/10141204801825835211973625643008)), (165/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd10 : AnalyticAt ℂ F_gammaInvProd10 c := by
  exact A_gammaInvProd9.mul A_gammaInv10

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd10 : Sound J_gammaInvProd10 F_gammaInvProd10 c := by
  apply sound_round (sound_mul A_gammaInvProd9 A_gammaInv10 S_gammaInvProd9 S_gammaInv10)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift10, J_gammaInv10, J_gammaInvProd10,
    J_gammaInvProd9, J_gammaInv10, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_q11 (s : ℂ) : ℂ := value (11, 0)

def J_q11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q11 : AnalyticAt ℂ F_q11 c := by
  exact analyticAt_const

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (c := c) (contains_exact (11, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_shift11 (s : ℂ) : ℂ := F_halfVariable s+F_q11 s

def J_shift11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((45/4), 7), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_shift11 : AnalyticAt ℂ F_shift11 c := by
  exact A_halfVariable.add A_q11

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_shift11 : Sound J_shift11 F_shift11 c := by
  apply sound_round (sound_add A_halfVariable A_q11 S_halfVariable S_q11)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift11, J_halfVariable, J_q11, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_gammaInv11 : F_shift11 c = value ((45/4), 7) := by
  have h := centre_contains S_shift11
  have he : J_shift11 ⟨0,by omega⟩ = exact ((45/4), 7) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift11, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_gammaInv11 : F_shift11 c ≠ 0 := by
  rw [V_gammaInv11]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_gammaInv11 (s : ℂ) : ℂ := (F_shift11 s)⁻¹

def J_gammaInv11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((180/2809), (-112/2809)), 0, by norm_num⟩
  | 1 => ⟨((-725317296736205/576460752303423488), (368211037021603/144115188075855872)), (1/576460752303423488), by norm_num⟩
  | 2 => ⟨((-97974884081627/9223372036854775808), (-123299211067999/1152921504606846976)), (3/18446744073709551616), by norm_num⟩
  | 3 => ⟨((729720596662841/295147905179352825856), (237205663112533/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-1353465828259031/9444732965739290427392), (-507280145901235/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((1711294982855473/302231454903657293676544), (-85835167679301/75557863725914323419136)), (13/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-383878877598659/2417851639229258349412352), (721869302410565/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((81661849861921/38685626227668133590597632), (-1229905834195807/154742504910672534362390528)), (21/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((449714042174993/4951760157141521099596496896), (734688668973687/2475880078570760549798248448)), (9/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem A_gammaInv11 : AnalyticAt ℂ F_gammaInv11 c := by
  exact A_shift11.inv N_gammaInv11

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_gammaInv11 : Sound J_gammaInv11 F_gammaInv11 c := by
  apply inv_coefficients_sound A_shift11 N_gammaInv11 S_shift11
  · rw [V_gammaInv11]
    have hv : (value ((45/4), 7))⁻¹ = value ((180/2809), (-112/2809)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInv11] using contains_exact ((180/2809), (-112/2809))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv11, J_shift11, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_gammaInvProd11 (s : ℂ) : ℂ := F_gammaInvProd10 s*F_gammaInv11 s

def J_gammaInvProd11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((304106723515127/309485009821345068724781056), (721353432198479/309485009821345068724781056)), (7/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((-121906888608529/77371252455336267181195264), (-79084232637295/309485009821345068724781056)), (37/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((219542088195827/618970019642690137449562112), (-1018108546026449/2475880078570760549798248448)), (61/1237940039285380274899124224), by norm_num⟩
  | 3 => ⟨((203636718638373/4951760157141521099596496896), (155289177831715/1237940039285380274899124224)), (17/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-992785950174939/39614081257132168796771975168), (-218772036895407/39614081257132168796771975168)), (125/39614081257132168796771975168), by norm_num⟩
  | 5 => ⟨((453665501005629/158456325028528675187087900672), (-61844326498009/19807040628566084398385987584)), (3/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((479303551794165/2535301200456458802993406410752), (1486650447867035/2535301200456458802993406410752)), (259/2535301200456458802993406410752), by norm_num⟩
  | 7 => ⟨((-1609479572610715/20282409603651670423947251286016), (-80147307058401/5070602400912917605986812821504)), (5/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((1016905621192215/162259276829213363391578010288128), (-151875970871829/20282409603651670423947251286016)), (23/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

theorem A_gammaInvProd11 : AnalyticAt ℂ F_gammaInvProd11 c := by
  exact A_gammaInvProd10.mul A_gammaInv11

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaInvProd11 : Sound J_gammaInvProd11 F_gammaInvProd11 c := by
  apply sound_round (sound_mul A_gammaInvProd10 A_gammaInv11 S_gammaInvProd10 S_gammaInv11)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_shift11, J_gammaInv11, J_gammaInvProd11,
    J_gammaInvProd10, J_gammaInv11, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_gammaFinite (s : ℂ) : ℂ := F_expGammaMain s*F_gammaInvProd11 s

def J_gammaFinite : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((952591158707819/36893488147419103232), (-50558354688553/36893488147419103232)), (5107/73786976294838206464), by norm_num⟩
  | 1 => ⟨((967339483560789/36893488147419103232), (716010111686851/36893488147419103232)), (2747/18446744073709551616), by norm_num⟩
  | 2 => ⟨((362893446279681/73786976294838206464), (1439641379515101/73786976294838206464)), (3079/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-501520099020983/147573952589676412928), (1080529889421981/147573952589676412928)), (9489/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-1248681189653191/590295810358705651712), (77780794471501/73786976294838206464)), (45353/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-1242799021874395/2361183241434822606848), (-252859615309843/2361183241434822606848)), (23023/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-153704900126947/2361183241434822606848), (-696893187622705/9444732965739290427392)), (178195/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-55620119927291/37778931862957161709568), (-1120585109575699/75557863725914323419136)), (387367/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((542450578632463/604462909807314587353088), (-1014567176530271/604462909807314587353088)), (4309645/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem A_gammaFinite : AnalyticAt ℂ F_gammaFinite c := by
  exact A_expGammaMain.mul A_gammaInvProd11

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul A_expGammaMain A_gammaInvProd11 S_expGammaMain S_gammaInvProd11)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInv11, J_gammaInvProd11, J_gammaFinite,
    J_expGammaMain, J_gammaInvProd11, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_negLog2 (s : ℂ) : ℂ := value (-1, 0)*F_log2 s

def J_negLog2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1560828692041339/2251799813685248), 0), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog2 : AnalyticAt ℂ F_negLog2 c := by
  exact analyticAt_const.mul A_log2

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale A_log2 S_log2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaInvProd11, J_gammaFinite, J_negLog2,
    J_log2, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg2 (s : ℂ) : ℂ := F_negLog2 s*F_variable s

def J_arg2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-12193974156573/35184372088832), (-341431276384043/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-1560828692041339/2251799813685248), 0), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg2 : AnalyticAt ℂ F_arg2 c := by
  exact A_negLog2.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul A_negLog2 A_variable S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_gammaFinite, J_negLog2, J_arg2,
    J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395881079077225/2535301200456458802993406410752), (1864239233137/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781426371031523/633825300114114700748351602688), (4425044365871/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473182684998691/9903520314283042199192993792), (4977989322933/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946345761669895/1237940039285380274899124224), (5288922898947/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887178270175551/77371252455336267181195264), (5288708043875/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24258126611637/151115727451828646838272), (4957935249995/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630691608726287/302231454903657293676544), (16945173879/2361183241434822606848)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1892005708016127/75557863725914323419136), (7048762660831/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325174388235851/1180591620717411303424), (2643097708411/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625787011874463/590295810358705651712), (7267905604643/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457223251425095/18446744073709551616), (4541980174299/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914372685188765/4611686018427387904), (638636552323/576460752303423488)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599984862700437/1152921504606846976), (10216591731061/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199819753069981/144115188075855872), (2234429692339/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((749737812187867/18014398509481984), (6701481648311/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1499020023885047/9007199254740992), (16747340199341/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((140460409823905/281474976710656), (8368859274299/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((1122483129586171/1125899906842624), (25082258837149/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((559349826775127/562949953421312), (50065655238523/1125899906842624)), (1/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((559349826775127/562949953421312), (50065655238523/1125899906842624)), (3816844749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((138664895679041/140737488355328), (99490959773089/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 2 => ⟨((67761938267125/70368744177664), (196051581126867/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((1009888997879017/1125899906842624), (377577724108591/1125899906842624)), (7/281474976710656), by norm_num⟩
  | 4 => ⟨((779208564599953/1125899906842624), (677345449811399/1125899906842624)), (35/562949953421312), by norm_num⟩
  | 5 => ⟨((131778258319415/1125899906842624), (937549372689705/1125899906842624)), (363/2251799813685248), by norm_num⟩
  | 6 => ⟨((-191321029433569/281474976710656), (438932884426569/2251799813685248)), (691/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12193974156573/35184372088832), (-341431276384043/35184372088832)), (1/35184372088832), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term2 (s : ℂ) : ℂ := Complex.exp (F_arg2 s)

def J_term2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-191321029433569/281474976710656), (438932884426569/2251799813685248)), (691/2251799813685248), by norm_num⟩
  | 1 => ⟨((1060909057069637/2251799813685248), (-38030636411915/281474976710656)), (483/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1470732243476657/9007199254740992), (105443313615277/2251799813685248)), (337/4503599627370496), by norm_num⟩
  | 3 => ⟨((679622605282965/18014398509481984), (-97450314055103/9007199254740992)), (627/36028797018963968), by norm_num⟩
  | 4 => ⟨((-942156985393383/144115188075855872), (270189641727903/144115188075855872)), (219/72057594037927936), by norm_num⟩
  | 5 => ⟨((1044885532912449/1152921504606846976), (-74912475352079/288230376151711744)), (489/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-482839640764093/4611686018427387904), (276935312421653/9223372036854775808)), (455/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1529960848723235/147573952589676412928), (-219379349717207/73786976294838206464)), (363/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1060488048659611/1180591620717411303424), (38015544432389/147573952589676412928)), (507/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem A_term2 : AnalyticAt ℂ F_term2 c := by
  exact A_arg2.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound A_arg2 S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term2, J_arg2, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log3 (s : ℂ) : ℂ := (Real.log (3 : ℝ) : ℂ)

def J_log3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log3 : AnalyticAt ℂ F_log3 c := by
  exact analyticAt_const

theorem S_log3 : Sound J_log3 F_log3 c := by
  have hlog : Contains ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (3 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_3 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog3 (s : ℂ) : ℂ := value (-1, 0)*F_log3 s

def J_negLog3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1236927473467587/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog3 : AnalyticAt ℂ F_negLog3 c := by
  exact analyticAt_const.mul A_log3

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale A_log3 S_log3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term2, J_log3, J_negLog3,
    J_log3, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg3 (s : ℂ) : ℂ := F_negLog3 s*F_variable s

def J_arg3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-19326991772931/35184372088832), (-2164623078568277/140737488355328)), (7/70368744177664), by norm_num⟩
  | 1 => ⟨((-1236927473467587/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg3 : AnalyticAt ℂ F_arg3 c := by
  exact A_negLog3.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul A_negLog3 A_variable S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log3, J_negLog3, J_arg3,
    J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583260234522037/10141204801825835211973625643008), (-1832905782941/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890556676171073/316912650057057350374175801344), (-2174609159413/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946189317799019/19807040628566084398385987584), (-1223150069691/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946158728008965/1237940039285380274899124224), (-5198092891913/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221747815267013/19342813113834066795298816), (-2598880439789/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552169513294739/9671406556917033397649408), (-4872547835225/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261076503617057/604462909807314587353088), (-133222691003/18889465931478580854784)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891507396185017/75557863725914323419136), (-1731729264971/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300323905073157/4722366482869645213696), (-5194607241613/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406318346508391/147573952589676412928), (-3570820272985/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228531397970621/9223372036854775808), (-8925632295311/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((914011805296953/4611686018427387904), (-2509845793747/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49976983320137/36028797018963968), (-10036937419237/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599594470616823/72057594037927936), (-4389781423291/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498530230040445/36028797018963968), (-13163814694685/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((187229966168629/1125899906842624), (-16445058388591/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122505171399877/2251799813685248), (-8215213539309/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((560360744362611/562949953421312), (-24608830629795/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1115198759872015/1125899906842624), (-12267258714703/281474976710656)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1115198759872015/1125899906842624), (-12267258714703/281474976710656)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102460792735109/1125899906842624), (-97205313705231/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((1071117351708033/1125899906842624), (-190363364548201/1125899906842624)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((123351792177031/140737488355328), (-362201829235253/1125899906842624)), (37/1125899906842624), by norm_num⟩
  | 4 => ⟨((187097531118875/281474976710656), (-634916045299397/1125899906842624)), (89/1125899906842624), by norm_num⟩
  | 5 => ⟨((278833656313233/2251799813685248), (-211015604178181/281474976710656)), (439/2251799813685248), by norm_num⟩
  | 6 => ⟨((-615511474085715/1125899906842624), (-26129433040433/140737488355328)), (3/8796093022208), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19326991772931/35184372088832), (-2164623078568277/140737488355328)), (7/70368744177664), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term3 (s : ℂ) : ℂ := Complex.exp (F_arg3 s)

def J_term3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-615511474085715/1125899906842624), (-26129433040433/140737488355328)), (3/8796093022208), by norm_num⟩
  | 1 => ⟨((1352416938493579/2251799813685248), (114824464936601/562949953421312)), (855/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1485781868031949/4503599627370496), (-504590272876361/4503599627370496)), (119/562949953421312), by norm_num⟩
  | 3 => ⟨((8501553221355/70368744177664), (184783024841455/4503599627370496)), (707/9007199254740992), by norm_num⟩
  | 4 => ⟨((-149438573467945/4503599627370496), (-203004901828087/18014398509481984)), (787/36028797018963968), by norm_num⟩
  | 5 => ⟨((525360170281333/72057594037927936), (356837887693119/144115188075855872)), (701/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1539112370794249/1152921504606846976), (-522701984642709/1152921504606846976)), (65/72057594037927936), by norm_num⟩
  | 7 => ⟨((966221579540383/4611686018427387904), (328141042079823/4611686018427387904)), (661/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-66343931303711/2305843009213693952), (-360499781245253/36893488147419103232)), (735/36893488147419103232), by norm_num⟩
  | _ => zero

theorem A_term3 : AnalyticAt ℂ F_term3 c := by
  exact A_arg3.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound A_arg3 S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term3, J_arg3, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log4 (s : ℂ) : ℂ := (Real.log (4 : ℝ) : ℂ)

def J_log4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log4 : AnalyticAt ℂ F_log4 c := by
  exact analyticAt_const

theorem S_log4 : Sound J_log4 F_log4 c := by
  have hlog : Contains ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (4 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_4 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog4 (s : ℂ) : ℂ := value (-1, 0)*F_log4 s

def J_negLog4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1560828692041339/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog4 : AnalyticAt ℂ F_negLog4 c := by
  exact analyticAt_const.mul A_log4

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale A_log4 S_log4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term3, J_log4, J_negLog4,
    J_log4, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg4 (s : ℂ) : ℂ := F_negLog4 s*F_variable s

def J_arg4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-12193974156573/17592186044416), (-341431276384043/17592186044416)), (7/70368744177664), by norm_num⟩
  | 1 => ⟨((-1560828692041339/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg4 : AnalyticAt ℂ F_arg4 c := by
  exact A_negLog4.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul A_negLog4 A_variable S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log4, J_negLog4, J_arg4,
    J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791536432756209/5070602400912917605986812821504), (-363796725669/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780900756644253/633825300114114700748351602688), (-215758051301/158456325028528675187087900672)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946070034442853/19807040628566084398385987584), (-60678153179/2475880078570760549798248448)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946032356005763/1237940039285380274899124224), (-1031455594859/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886865301414905/77371252455336267181195264), (-515686732973/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96995888440159/604462909807314587353088), (-966825369617/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157608936697403/75557863725914323419136), (-845884951877/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891175896897587/75557863725914323419136), (-1374399476903/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650038358514189/2361183241434822606848), (-1030656501377/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624935835998577/590295810358705651712), (-1416920174201/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827832745360019/73786976294838206464), (-221350187739/9223372036854775808)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827557676831817/9223372036854775808), (-1991672297907/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799401770737459/576460752303423488), (-1991073197011/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599396631652873/72057594037927936), (-435378812419/36028797018963968)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497950215945503/36028797018963968), (-2610925756011/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497138319771037/9007199254740992), (-815325202615/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((2243678260136949/4503599627370496), (-6515536757397/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2239621387030869/2251799813685248), (-9755657987551/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((2227458619617207/2251799813685248), (-2430102175079/281474976710656)), (5/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2227458619617207/2251799813685248), (-2430102175079/281474976710656)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2203212704155261/2251799813685248), (-38461337485033/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((2155017029390471/2251799813685248), (-9407864194991/281474976710656)), (23/2251799813685248), by norm_num⟩
  | 3 => ⟨((1029939220754761/1125899906842624), (-72028099219773/1125899906842624)), (47/2251799813685248), by norm_num⟩
  | 4 => ⟨((937549372689715/1125899906842624), (-131778258319421/1125899906842624)), (93/2251799813685248), by norm_num⟩
  | 5 => ⟨((765284117734291/1125899906842624), (-438932884426593/2251799813685248)), (89/1125899906842624), by norm_num⟩
  | 6 => ⟨((954781607729043/2251799813685248), (-298346560970029/1125899906842624)), (39/281474976710656), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12193974156573/17592186044416), (-341431276384043/17592186044416)), (7/70368744177664), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term4 (s : ℂ) : ℂ := Complex.exp (F_arg4 s)

def J_term4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((954781607729043/2251799813685248), (-298346560970029/1125899906842624)), (39/281474976710656), by norm_num⟩
  | 1 => ⟨((-1323608358895755/2251799813685248), (827192310264525/2251799813685248)), (443/2251799813685248), by norm_num⟩
  | 2 => ⟨((114681925266771/281474976710656), (-573366017640723/2251799813685248)), (315/2251799813685248), by norm_num⟩
  | 3 => ⟨((-211977208426263/1125899906842624), (529902718075401/4503599627370496)), (149/2251799813685248), by norm_num⟩
  | 4 => ⟨((9183212772727/140737488355328), (-734601150010031/18014398509481984)), (211/9007199254740992), by norm_num⟩
  | 5 => ⟨((-325904283745167/18014398509481984), (407349372772437/36028797018963968)), (239/36028797018963968), by norm_num⟩
  | 6 => ⟨((602399027760989/144115188075855872), (-376470758986769/144115188075855872)), (113/72057594037927936), by norm_num⟩
  | 7 => ⟨((-954402714661901/1152921504606846976), (596456331782723/1152921504606846976)), (183/576460752303423488), by norm_num⟩
  | 8 => ⟨((1323083101573309/9223372036854775808), (-826864049404643/9223372036854775808)), (259/4611686018427387904), by norm_num⟩
  | _ => zero

theorem A_term4 : AnalyticAt ℂ F_term4 c := by
  exact A_arg4.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound A_arg4 S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term4, J_arg4, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log5 (s : ℂ) : ℂ := (Real.log (5 : ℝ) : ℂ)

def J_log5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log5 : AnalyticAt ℂ F_log5 c := by
  exact analyticAt_const

theorem S_log5 : Sound J_log5 F_log5 c := by
  have hlog : Contains ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (5 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_5 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog5 (s : ℂ) : ℂ := value (-1, 0)*F_log5 s

def J_negLog5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-453016498919635/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog5 : AnalyticAt ℂ F_negLog5 c := by
  exact analyticAt_const.mul A_log5

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale A_log5 S_log5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term4, J_log5, J_negLog5,
    J_log5, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg5 (s : ℂ) : ℂ := F_negLog5 s*F_variable s

def J_arg5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-28313531182477/35184372088832), (-792778873109361/35184372088832)), (9/70368744177664), by norm_num⟩
  | 1 => ⟨((-453016498919635/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg5 : AnalyticAt ℂ F_arg5 c := by
  exact A_negLog5.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul A_negLog5 A_variable S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log5, J_negLog5, J_arg5,
    J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582927530817571/10141204801825835211973625643008), (846896369209/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445180044464069/158456325028528675187087900672), (4017433429037/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891936437377707/39614081257132168796771975168), (1129816066037/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891847762671855/2475880078570760549798248448), (2400660615693/1237940039285380274899124224)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773512988896813/154742504910672534362390528), (2400437185539/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551729496029203/9671406556917033397649408), (4500344790775/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157586457336615/75557863725914323419136), (3937326599009/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236360292794389/9444732965739290427392), (6397264582665/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299855394054239/4722366482869645213696), (4797168347605/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624629637478289/590295810358705651712), (6594838193347/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827447179469897/73786976294838206464), (4120822098475/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1827120043099577/9223372036854775808), (9269230533043/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399590267760289/288230376151711744), (9265953829003/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149800083138307/18014398509481984), (8104019576069/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((748675228656043/18014398509481984), (1518580000171/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1496369640722601/9007199254740992), (948302981603/562949953421312)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1121042033085721/2251799813685248), (7576688776371/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((279636047400447/281474976710656), (22681245477869/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((277728497035449/281474976710656), (22583169416169/562949953421312)), (1/281474976710656), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((277728497035449/281474976710656), (22583169416169/562949953421312)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((547157826107633/562949953421312), (44565167202745/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((528280765875561/562949953421312), (86630009856411/562949953421312)), (11/562949953421312), by norm_num⟩
  | 3 => ⟨((964831091417109/1125899906842624), (325179655325429/1125899906842624)), (25/562949953421312), by norm_num⟩
  | 4 => ⟨((732886841639027/1125899906842624), (557320308577177/1125899906842624)), (29/281474976710656), by norm_num⟩
  | 5 => ⟨((201187685440257/1125899906842624), (725557784048219/1125899906842624)), (133/562949953421312), by norm_num⟩
  | 6 => ⟨((-431617064951121/1125899906842624), (518601308477511/2251799813685248)), (877/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28313531182477/35184372088832), (-792778873109361/35184372088832)), (9/70368744177664), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term5 (s : ℂ) : ℂ := Complex.exp (F_arg5 s)

def J_term5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-431617064951121/1125899906842624), (518601308477511/2251799813685248)), (877/2251799813685248), by norm_num⟩
  | 1 => ⟨((1389321735971731/2251799813685248), (-417328303650819/1125899906842624)), (711/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1118013537220831/2251799813685248), (335831996913719/1125899906842624)), (1153/2251799813685248), by norm_num⟩
  | 3 => ⟨((299895562236293/1125899906842624), (-180166916013797/1125899906842624)), (623/2251799813685248), by norm_num⟩
  | 4 => ⟨((-241331643816915/2251799813685248), (289967465198935/4503599627370496)), (505/4503599627370496), by norm_num⟩
  | 5 => ⟨((1242906550492753/36028797018963968), (-373347705490865/18014398509481984)), (655/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1333587282650483/144115188075855872), (400586634491519/72057594037927936)), (177/18014398509481984), by norm_num⟩
  | 7 => ⟨((1226471961278661/576460752303423488), (-368411038151447/288230376151711744)), (41/18014398509481984), by norm_num⟩
  | 8 => ⟨((-493482618254821/1152921504606846976), (37058418260009/144115188075855872)), (133/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_term5 : AnalyticAt ℂ F_term5 c := by
  exact A_arg5.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound A_arg5 S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term5, J_arg5, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log6 (s : ℂ) : ℂ := (Real.log (6 : ℝ) : ℂ)

def J_log6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log6 : AnalyticAt ℂ F_log6 c := by
  exact analyticAt_const

theorem S_log6 : Sound J_log6 F_log6 c := by
  have hlog : Contains ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (6 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_6 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog6 (s : ℂ) : ℂ := value (-1, 0)*F_log6 s

def J_negLog6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-2017341819488257/1125899906842624), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog6 : AnalyticAt ℂ F_negLog6 c := by
  exact analyticAt_const.mul A_log6

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale A_log6 S_log6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term5, J_log6, J_negLog6,
    J_log6, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg6 (s : ℂ) : ℂ := F_negLog6 s*F_variable s

def J_arg6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-985030185297/1099511627776), (-1765174092052225/70368744177664)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-2017341819488257/1125899906842624), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg6 : AnalyticAt ℂ F_arg6 c := by
  exact A_negLog6.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul A_negLog6 A_variable S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log6, J_negLog6, J_arg6,
    J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582808783725555/10141204801825835211973625643008), (7833362549/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780587963259249/633825300114114700748351602688), (18576822965/158456325028528675187087900672)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472947056320845/9903520314283042199192993792), (83588993831/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891690937678145/2475880078570760549798248448), (88805185487/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886678447707963/77371252455336267181195264), (22199012813/38685626227668133590597632)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551583935432175/9671406556917033397649408), (41618297127/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260565069997003/604462909807314587353088), (72822317673/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890678091817329/75557863725914323419136), (118318077585/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649851739887843/2361183241434822606848), (11090330789/590295810358705651712)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624422824129125/590295810358705651712), (30491946959/147573952589676412928)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827191764460081/73786976294838206464), (76210484475/36893488147419103232)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913418481791063/4611686018427387904), (171420303959/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1598083315828029/1152921504606846976), (85676860853/576460752303423488)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198163614107771/144115188075855872), (18732454543/18014398509481984)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497006837859785/36028797018963968), (112319900695/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1495961012916193/9007199254740992), (280538054783/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120664693359991/2251799813685248), (560291802155/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((559028100821615/562949953421312), (838479674057/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((555124452934763/562949953421312), (417285911417/562949953421312)), (5/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((555124452934763/562949953421312), (417285911417/562949953421312)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1094814848978089/1125899906842624), (3291882155917/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((2129171229407383/2251799813685248), (6401992652243/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((1006601277581393/1125899906842624), (12106705474609/2251799813685248)), (43/2251799813685248), by norm_num⟩
  | 4 => ⟨((449955401360005/562949953421312), (21647795019751/2251799813685248)), (39/1125899906842624), by norm_num⟩
  | 5 => ⟨((719177869341497/1125899906842624), (34605357856319/2251799813685248)), (127/2251799813685248), by norm_num⟩
  | 6 => ⟨((918229803397147/2251799813685248), (44208916582469/2251799813685248)), (333/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-985030185297/1099511627776), (-1765174092052225/70368744177664)), (1/8796093022208), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term6 (s : ℂ) : ℂ := Complex.exp (F_arg6 s)

def J_term6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((918229803397147/2251799813685248), (44208916582469/2251799813685248)), (333/4503599627370496), by norm_num⟩
  | 1 => ⟨((-822623472582127/1125899906842624), (-9901468113869/281474976710656)), (153/1125899906842624), by norm_num⟩
  | 2 => ⟨((368485849152073/562949953421312), (35482098504569/1125899906842624)), (281/2251799813685248), by norm_num⟩
  | 3 => ⟨((-1760634691986047/4503599627370496), (-42383590655763/2251799813685248)), (43/562949953421312), by norm_num⟩
  | 4 => ⟨((788658470304355/4503599627370496), (75941199897349/9007199254740992)), (79/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1130469025723793/18014398509481984), (-27213672804123/9007199254740992)), (29/2251799813685248), by norm_num⟩
  | 6 => ⟨((168794048459135/9007199254740992), (65013807919015/72057594037927936)), (71/18014398509481984), by norm_num⟩
  | 7 => ⟨((-1382575244233117/288230376151711744), (-66565203411125/288230376151711744)), (297/288230376151711744), by norm_num⟩
  | 8 => ⟨((1238621142887489/1152921504606846976), (59634416766487/1152921504606846976)), (273/1152921504606846976), by norm_num⟩
  | _ => zero

theorem A_term6 : AnalyticAt ℂ F_term6 c := by
  exact A_arg6.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound A_arg6 S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term6, J_arg6, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log7 (s : ℂ) : ℂ := (Real.log (7 : ℝ) : ℂ)

def J_log7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log7 : AnalyticAt ℂ F_log7 c := by
  exact analyticAt_const

theorem S_log7 : Sound J_log7 F_log7 c := by
  have hlog : Contains ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (7 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_7 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog7 (s : ℂ) : ℂ := value (-1, 0)*F_log7 s

def J_negLog7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-2190900055545493/1125899906842624), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog7 : AnalyticAt ℂ F_negLog7 c := by
  exact analyticAt_const.mul A_log7

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale A_log7 S_log7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term6, J_log7, J_negLog7,
    J_log7, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg7 (s : ℂ) : ℂ := F_negLog7 s*F_variable s

def J_arg7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-68465626735797/70368744177664), (-958518774301153/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-2190900055545493/1125899906842624), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg7 : AnalyticAt ℂ F_arg7 c := by
  exact A_negLog7.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul A_negLog7 A_variable S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log7, J_negLog7, J_arg7,
    J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582708384489811/10141204801825835211973625643008), (-1374255850219/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780463261903483/633825300114114700748351602688), (-1629317319785/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891647609813889/39614081257132168796771975168), (-3665633305903/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891541129205449/2475880078570760549798248448), (-3894347249337/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773206631969775/154742504910672534362390528), (-243369408005/9671406556917033397649408)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775721290094693/4835703278458516698824704), (-3650077065389/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630220450531575/302231454903657293676544), (-798338333599/151115727451828646838272)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890475411845941/75557863725914323419136), (-5188328893439/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299550677876877/4722366482869645213696), (-3890485088089/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624211435307535/590295810358705651712), (-2674089627147/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456731400067845/18446744073709551616), (-3341683578143/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826534879523139/9223372036854775808), (-3758117156433/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99861120181175/72057594037927936), (-3756520707761/576460752303423488)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((9358536536587/1125899906842624), (-410644889713/9007199254740992)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((187074125520825/4503599627370496), (-2462072217961/9007199254740992)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((747715372160949/4503599627370496), (-12297775704371/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((560057501763927/1125899906842624), (-12278886603147/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117183265920705/1125899906842624), (-18371068855743/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((277077585699703/281474976710656), (-36552866016107/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((277077585699703/281474976710656), (-36552866016107/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((544904434436701/562949953421312), (-35981812609079/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((525137536709057/562949953421312), (-69656810985057/562949953421312)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((481245907380853/562949953421312), (-259912313081409/1125899906842624)), (35/1125899906842624), by norm_num⟩
  | 4 => ⟨((762799674973239/1125899906842624), (-444379597824419/1125899906842624)), (77/1125899906842624), by norm_num⟩
  | 5 => ⟨((682814013644671/2251799813685248), (-1204272638180745/2251799813685248)), (331/2251799813685248), by norm_num⟩
  | 6 => ⟨((-6828132572143/35184372088832), (-22823249778943/70368744177664)), (139/562949953421312), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-68465626735797/70368744177664), (-958518774301153/35184372088832)), (1/8796093022208), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term7 (s : ℂ) : ℂ := Complex.exp (F_arg7 s)

def J_term7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-6828132572143/35184372088832), (-22823249778943/70368744177664)), (139/562949953421312), by norm_num⟩
  | 1 => ⟨((425181839079303/1125899906842624), (355295947034157/562949953421312)), (273/562949953421312), by norm_num⟩
  | 2 => ⟨((-413682827929209/1125899906842624), (-691373989251985/1125899906842624)), (67/140737488355328), by norm_num⟩
  | 3 => ⟨((268329871119117/1125899906842624), (56056319269929/140737488355328)), (351/1125899906842624), by norm_num⟩
  | 4 => ⟨((-261072909752697/2251799813685248), (-436322242344159/2251799813685248)), (689/4503599627370496), by norm_num⟩
  | 5 => ⟨((101604884946235/2251799813685248), (1358470207417713/18014398509481984)), (1081/18014398509481984), by norm_num⟩
  | 6 => ⟨((-527237271494603/36028797018963968), (-440576827300567/18014398509481984)), (707/36028797018963968), by norm_num⟩
  | 7 => ⟨((293130387874737/72057594037927936), (489898811247293/72057594037927936)), (793/144115188075855872), by norm_num⟩
  | 8 => ⟨((-570405396761971/576460752303423488), (-59581191801015/36028797018963968)), (389/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_term7 : AnalyticAt ℂ F_term7 c := by
  exact A_arg7.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound A_arg7 S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term7, J_arg7, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log8 (s : ℂ) : ℂ := (Real.log (8 : ℝ) : ℂ)

def J_log8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log8 : AnalyticAt ℂ F_log8 c := by
  exact analyticAt_const

theorem S_log8 : Sound J_log8 F_log8 c := by
  have hlog : Contains ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (8 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_8 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog8 (s : ℂ) : ℂ := value (-1, 0)*F_log8 s

def J_negLog8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1170621519031005/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog8 : AnalyticAt ℂ F_negLog8 c := by
  exact analyticAt_const.mul A_log8

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale A_log8 S_log8)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term7, J_log8, J_negLog8,
    J_log8, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg8 (s : ℂ) : ℂ := F_negLog8 s*F_variable s

def J_arg8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-36581922469719/35184372088832), (-2048587658304259/70368744177664)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1170621519031005/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg8 : AnalyticAt ℂ F_arg8 c := by
  exact A_negLog8.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul A_negLog8 A_variable S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log8, J_negLog8, J_arg8,
    J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49456919209873/316912650057057350374175801344), (375110626867/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445089767108017/158456325028528675187087900672), (889364261035/158456325028528675187087900672)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472882584755927/9903520314283042199192993792), (4001752397797/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891416461462835/2475880078570760549798248448), (4251408950891/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886540944145617/77371252455336267181195264), (4250899265383/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551325552347525/9671406556917033397649408), (3984676466843/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315084605275447/151115727451828646838272), (1743025126871/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472577182719163/18889465931478580854784), (5663815931733/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649712767544633/2361183241434822606848), (16589738503/18446744073709551616)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((203004893693663/73786976294838206464), (2919071632183/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913354960869463/36893488147419103232), (1823877907435/18446744073709551616)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826291799831693/9223372036854775808), (8204469661511/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597534292268359/1152921504606846976), (8200742495927/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197678881091251/144115188075855872), (7171455233903/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((374067768934589/9007199254740992), (10748790491885/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495026178180431/9007199254740992), (13421293739801/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((559853607702345/1125899906842624), (3349809193151/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((1116563568770779/1125899906842624), (10021829612681/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1107039128511659/1125899906842624), (39866216824173/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1107039128511659/1125899906842624), (39866216824173/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1087082705463855/1125899906842624), (78396776945925/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((261036249034753/281474976710656), (151387845161151/1125899906842624)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((947971029052397/1125899906842624), (70197563762379/281474976710656)), (35/1125899906842624), by norm_num⟩
  | 4 => ⟨((728133912801255/1125899906842624), (472832487878305/1125899906842624)), (77/1125899906842624), by norm_num⟩
  | 5 => ⟨((544645987648945/2251799813685248), (1223147341627787/2251799813685248)), (329/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1065325754251691/4503599627370496), (1183377470541287/4503599627370496)), (517/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-36581922469719/35184372088832), (-2048587658304259/70368744177664)), (1/8796093022208), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term8 (s : ℂ) : ℂ := Complex.exp (F_arg8 s)

def J_term8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1065325754251691/4503599627370496), (1183377470541287/4503599627370496)), (517/2251799813685248), by norm_num⟩
  | 1 => ⟨((553820657203093/1125899906842624), (-307595533966445/562949953421312)), (543/1125899906842624), by norm_num⟩
  | 2 => ⟨((-287909420307135/562949953421312), (639626931365017/1125899906842624)), (285/562949953421312), by norm_num⟩
  | 3 => ⟨((199563602942539/562949953421312), (-443355604085871/1125899906842624)), (797/2251799813685248), by norm_num⟩
  | 4 => ⟨((-50656841573/274877906944), (921932060872719/4503599627370496)), (835/4503599627370496), by norm_num⟩
  | 5 => ⟨((690342728415251/9007199254740992), (-383420765197047/4503599627370496)), (701/9007199254740992), by norm_num⟩
  | 6 => ⟨((-957018231642183/36028797018963968), (132883511182235/4503599627370496)), (245/9007199254740992), by norm_num⟩
  | 7 => ⟨((568589562006209/72057594037927936), (-631596556243695/72057594037927936)), (587/72057594037927936), by norm_num⟩
  | 8 => ⟨((-591174377700627/288230376151711744), (164171014579383/72057594037927936)), (615/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_term8 : AnalyticAt ℂ F_term8 c := by
  exact A_arg8.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound A_arg8 S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term8, J_arg8, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log9 (s : ℂ) : ℂ := (Real.log (9 : ℝ) : ℂ)

def J_log9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log9 : AnalyticAt ℂ F_log9 c := by
  exact analyticAt_const

theorem S_log9 : Sound J_log9 F_log9 c := by
  have hlog : Contains ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (9 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_9 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog9 (s : ℂ) : ℂ := value (-1, 0)*F_log9 s

def J_negLog9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1236927473467587/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog9 : AnalyticAt ℂ F_negLog9 c := by
  exact analyticAt_const.mul A_log9

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale A_log9 S_log9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term8, J_log9, J_negLog9,
    J_log9, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg9 (s : ℂ) : ℂ := F_negLog9 s*F_variable s

def J_arg9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-19326991772931/17592186044416), (-2164623078568277/70368744177664)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1236927473467587/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg9 : AnalyticAt ℂ F_arg9 c := by
  exact A_negLog9.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul A_negLog9 A_variable S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log9, J_negLog9, J_arg9,
    J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395636175484673/2535301200456458802993406410752), (426463626061/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780274338053403/633825300114114700748351602688), (1011020962753/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891435396165249/39614081257132168796771975168), (1137286795283/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945658027388721/1237940039285380274899124224), (1208231710453/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221622751289669/19342813113834066795298816), (302019821265/38685626227668133590597632)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551232478326179/9671406556917033397649408), (283103100447/2417851639229258349412352)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260257542713475/604462909807314587353088), (123837368829/75557863725914323419136)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890178355661383/75557863725914323419136), (1609582287947/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324832168475103/1180591620717411303424), (603460602445/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623907459984345/590295810358705651712), (1659085308849/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826547550251373/73786976294838206464), (1036604901265/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228264026287575/1152921504606846976), (582867984403/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597358547350061/1152921504606846976), (2330361033479/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((598764712416611/72057594037927936), (254727095945/18014398509481984)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496055520833815/36028797018963968), (1527114226597/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494771810028771/9007199254740992), (3813419887227/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((139934426031265/281474976710656), (951719612091/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2232544155598143/2251799813685248), (2846994416625/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((1106679929559127/1125899906842624), (11322810678531/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1106679929559127/1125899906842624), (11322810678531/1125899906842624)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((543837091114755/562949953421312), (44518086369749/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((1050306207948217/1125899906842624), (86013282161871/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((978145173105015/1125899906842624), (40119145437163/562949953421312)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((211015604178179/281474976710656), (278833656313247/2251799813685248)), (21/562949953421312), by norm_num⟩
  | 5 => ⟨((615511474085701/1125899906842624), (418070928646945/2251799813685248)), (37/562949953421312), by norm_num⟩
  | 6 => ⟨((1190722362971367/4503599627370496), (914210764207223/4503599627370496)), (217/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19326991772931/17592186044416), (-2164623078568277/70368744177664)), (1/8796093022208), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term9 (s : ℂ) : ℂ := Complex.exp (F_arg9 s)

def J_term9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1190722362971367/4503599627370496), (914210764207223/4503599627370496)), (217/2251799813685248), by norm_num⟩
  | 1 => ⟨((-654071110176137/1125899906842624), (-15693174687355/35184372088832)), (243/1125899906842624), by norm_num⟩
  | 2 => ⟨((718570559302297/1125899906842624), (551702865911793/1125899906842624)), (17/70368744177664), by norm_num⟩
  | 3 => ⟨((-65785870560385/140737488355328), (-404071698789407/1125899906842624)), (203/1125899906842624), by norm_num⟩
  | 4 => ⟨((578185326546949/2251799813685248), (887836267586083/4503599627370496)), (227/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1016322407795299/9007199254740992), (-780310267116239/9007199254740992)), (203/4503599627370496), by norm_num⟩
  | 6 => ⟨((372181428817559/9007199254740992), (571505632285197/18014398509481984)), (303/18014398509481984), by norm_num⟩
  | 7 => ⟨((-467294961500601/36028797018963968), (-179389460191873/18014398509481984)), (387/72057594037927936), by norm_num⟩
  | 8 => ⟨((1026751974274503/288230376151711744), (394158930848661/144115188075855872)), (27/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_term9 : AnalyticAt ℂ F_term9 c := by
  exact A_arg9.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound A_arg9 S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term9, J_arg9, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log10 (s : ℂ) : ℂ := (Real.log (10 : ℝ) : ℂ)

def J_log10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log10 : AnalyticAt ℂ F_log10 c := by
  exact analyticAt_const

theorem S_log10 : Sound J_log10 F_log10 c := by
  have hlog : Contains ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (10 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_10 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog10 (s : ℂ) : ℂ := value (-1, 0)*F_log10 s

def J_negLog10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-648120085424803/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog10 : AnalyticAt ℂ F_negLog10 c := by
  exact analyticAt_const.mul A_log10

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale A_log10 S_log10)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term9, J_log10, J_negLog10,
    J_log10, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg10 (s : ℂ) : ℂ := F_negLog10 s*F_variable s

def J_arg10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-20253752669525/17592186044416), (-1134210149493405/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-648120085424803/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg10 : AnalyticAt ℂ F_arg10 c := by
  exact A_negLog10.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul A_negLog10 A_variable S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log10, J_negLog10, J_arg10,
    J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582476080021089/10141204801825835211973625643008), (-133560805097/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890096344896329/316912650057057350374175801344), (-633212515153/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59104485399111/1237940039285380274899124224), (-356145340445/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891218438174751/2475880078570760549798248448), (-1513439795377/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443221095127055/38685626227668133590597632), (-1513239685277/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551140936356417/9671406556917033397649408), (-709224809563/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260177429475391/604462909807314587353088), (-1240930865965/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890048145391687/75557863725914323419136), (-2016114198973/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299230993242005/4722366482869645213696), (-377934268187/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811886555905883/295147905179352825856), (-519518044459/147573952589676412928)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826379559198497/73786976294838206464), (-2596741020739/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456480785923391/2305843009213693952), (-1460083196489/4611686018427387904)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597169385057529/1152921504606846976), (-2918707918803/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197363800394285/144115188075855872), (-2552229463387/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495806869841951/36028797018963968), (-1912533153929/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494460622402009/9007199254740992), (-4775601178789/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2238327324365027/4503599627370496), (-9534025614973/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2231606141884839/2251799813685248), (-27847970373/4398046511104)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((34554262961677/35184372088832), (-28345196492619/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((34554262961677/35184372088832), (-28345196492619/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((542877812222049/562949953421312), (-13918784323243/562949953421312)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((523177210791135/562949953421312), (-107380048777269/2251799813685248)), (27/2251799813685248), by norm_num⟩
  | 3 => ⟨((969868591523517/1125899906842624), (-199587171372811/2251799813685248)), (27/1125899906842624), by norm_num⟩
  | 4 => ⟨((413307754722885/562949953421312), (-21490956657101/140737488355328)), (103/2251799813685248), by norm_num⟩
  | 5 => ⟨((290316252150323/562949953421312), (-63113099051245/281474976710656)), (23/281474976710656), by norm_num⟩
  | 6 => ⟨((971318644008091/4503599627370496), (-520764114587267/2251799813685248)), (273/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20253752669525/17592186044416), (-1134210149493405/35184372088832)), (5/35184372088832), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term10 (s : ℂ) : ℂ := Complex.exp (F_arg10 s)

def J_term10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((971318644008091/4503599627370496), (-520764114587267/2251799813685248)), (273/2251799813685248), by norm_num⟩
  | 1 => ⟨((-559135957560055/1125899906842624), (299775921803721/562949953421312)), (319/1125899906842624), by norm_num⟩
  | 2 => ⟨((643729060417367/1125899906842624), (-690259568783797/1125899906842624)), (93/281474976710656), by norm_num⟩
  | 3 => ⟨((-247040156407349/562949953421312), (264896898896345/562949953421312)), (289/1125899906842624), by norm_num⟩
  | 4 => ⟨((35551936344655/140737488355328), (-609947650579075/2251799813685248)), (337/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1047825390774731/9007199254740992), (35111409193253/281474976710656)), (157/2251799813685248), by norm_num⟩
  | 6 => ⟨((402117854143093/9007199254740992), (-862368078958917/18014398509481984)), (61/2251799813685248), by norm_num⟩
  | 7 => ⟨((-1058183516087589/72057594037927936), (70916995831597/4503599627370496)), (325/36028797018963968), by norm_num⟩
  | 8 => ⟨((609139397448827/144115188075855872), (-653169669767025/144115188075855872)), (379/144115188075855872), by norm_num⟩
  | _ => zero

theorem A_term10 : AnalyticAt ℂ F_term10 c := by
  exact A_arg10.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound A_arg10 S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term10, J_arg10, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log11 (s : ℂ) : ℂ := (Real.log (11 : ℝ) : ℂ)

def J_log11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log11 : AnalyticAt ℂ F_log11 c := by
  exact analyticAt_const

theorem S_log11 : Sound J_log11 F_log11 c := by
  have hlog : Contains ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (11 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_11 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog11 (s : ℂ) : ℂ := value (-1, 0)*F_log11 s

def J_negLog11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1349895032131027/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog11 : AnalyticAt ℂ F_negLog11 c := by
  exact analyticAt_const.mul A_log11

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale A_log11 S_log11)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term10, J_log11, J_negLog11,
    J_log11, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg11 (s : ℂ) : ℂ := F_negLog11 s*F_variable s

def J_arg11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-42184219754095/35184372088832), (-1181158153114649/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1349895032131027/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg11 : AnalyticAt ℂ F_arg11 c := by
  exact A_negLog11.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul A_negLog11 A_variable S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log11, J_negLog11, J_arg11,
    J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582414003945773/10141204801825835211973625643008), (-350827068703/1267650600228229401496703205376)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890057033700735/316912650057057350374175801344), (-1663142456927/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891254793501615/39614081257132168796771975168), (-935414720033/9903520314283042199192993792)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891123790690445/2475880078570760549798248448), (-3975024706587/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221598665739411/19342813113834066795298816), (-3974475826687/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193881423785711/1208925819614629174706176), (-465685986931/1208925819614629174706176)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260098644457001/604462909807314587353088), (-3259218708343/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889919309739181/75557863725914323419136), (-5295136883653/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299133658144211/4722366482869645213696), (-3970395818089/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623638125700063/590295810358705651712), (-1364434836479/147573952589676412928)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913104551154033/36893488147419103232), (-6819841772177/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825729010922489/9223372036854775808), (-7669114842677/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49905384201161/36028797018963968), (-7665105775613/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197188022799043/144115188075855872), (-3351228590173/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495536567535021/36028797018963968), (-5022332301139/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((747055577855425/4503599627370496), (-12540042788821/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((559398430167049/1125899906842624), (-12516359076021/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115209698329079/1125899906842624), (-9357661736935/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1104377997402517/1125899906842624), (-9298438459219/281474976710656)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1104377997402517/1125899906842624), (-9298438459219/281474976710656)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082038801511867/1125899906842624), (-72965568481911/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((1035157731793167/1125899906842624), (-140246172491841/1125899906842624)), (15/1125899906842624), by norm_num⟩
  | 3 => ⟨((934259372791291/1125899906842624), (-32235749582849/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((179042422748491/281474976710656), (-427981933437559/1125899906842624)), (17/281474976710656), by norm_num⟩
  | 5 => ⟨((292859506378419/1125899906842624), (-1088934059442351/2251799813685248)), (277/2251799813685248), by norm_num⟩
  | 6 => ⟨((-748477390207783/4503599627370496), (-566488529200155/2251799813685248)), (825/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-42184219754095/35184372088832), (-1181158153114649/35184372088832)), (5/35184372088832), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term11 (s : ℂ) : ℂ := Complex.exp (F_arg11 s)

def J_term11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-748477390207783/4503599627370496), (-566488529200155/2251799813685248)), (825/4503599627370496), by norm_num⟩
  | 1 => ⟨((224346299471963/562949953421312), (679190083131777/1125899906842624)), (499/1125899906842624), by norm_num⟩
  | 2 => ⟨((-134489732743407/281474976710656), (-407156672418305/562949953421312)), (603/1125899906842624), by norm_num⟩
  | 3 => ⟨((429989725847109/1125899906842624), (650879373386779/1125899906842624)), (971/2251799813685248), by norm_num⟩
  | 4 => ⟨((-515535165480325/2251799813685248), (-780370286303061/2251799813685248)), (587/2251799813685248), by norm_num⟩
  | 5 => ⟨((494479734506639/4503599627370496), (93562311027921/562949953421312)), (71/562949953421312), by norm_num⟩
  | 6 => ⟨((-790473745245375/18014398509481984), (-1196547324405027/18014398509481984)), (915/18014398509481984), by norm_num⟩
  | 7 => ⟨((67695473464111/4503599627370496), (819770049391529/36028797018963968)), (79/4503599627370496), by norm_num⟩
  | 8 => ⟨((-649306623237757/144115188075855872), (-982861363108817/144115188075855872)), (763/144115188075855872), by norm_num⟩
  | _ => zero

theorem A_term11 : AnalyticAt ℂ F_term11 c := by
  exact A_arg11.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound A_arg11 S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term11, J_arg11, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log12 (s : ℂ) : ℂ := (Real.log (12 : ℝ) : ℂ)

def J_log12 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log12 : AnalyticAt ℂ F_log12 c := by
  exact analyticAt_const

theorem S_log12 : Sound J_log12 F_log12 c := by
  have hlog : Contains ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (12 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_12 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog12 (s : ℂ) : ℂ := value (-1, 0)*F_log12 s

def J_negLog12 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1398878082754463/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog12 : AnalyticAt ℂ F_negLog12 c := by
  exact analyticAt_const.mul A_log12

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale A_log12 S_log12)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term11, J_log12, J_negLog12,
    J_log12, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg12 (s : ℂ) : ℂ := F_negLog12 s*F_variable s

def J_arg12 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-43714940086077/35184372088832), (-1224018322410155/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1398878082754463/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg12 : AnalyticAt ℂ F_arg12 c := by
  exact A_negLog12.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul A_negLog12 A_variable S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log12, J_negLog12, J_arg12,
    J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582357332929073/10141204801825835211973625643008), (1895572683333/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780042035893933/633825300114114700748351602688), (561598159611/79228162514264337593543950336)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891173480375535/39614081257132168796771975168), (2526897282231/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891037046386625/2475880078570760549798248448), (5368972310009/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110793886812133/9671406556917033397649408), (5368202120871/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550969282435937/9671406556917033397649408), (5031871036553/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630013191646521/302231454903657293676544), (4402068563713/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944900552130843/37778931862957161709568), (893978281671/9444732965739290427392)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299044320991201/4722366482869645213696), (1340631530721/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623514177926999/590295810358705651712), (3685644780611/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826052505140919/73786976294838206464), (2302708796233/18446744073709551616)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825550555402379/9223372036854775808), (10357682440283/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596790987528139/1152921504606846976), (10352046135373/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((598513087952055/72057594037927936), (282865508391/4503599627370496)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((373821850413615/9007199254740992), (6782424046355/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493788531290033/9007199254740992), (16933823413619/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118457535575065/2251799813685248), (16900432261293/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((557329568192025/562949953421312), (3158380644471/140737488355328)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1103111631342587/1125899906842624), (12549733287965/281474976710656)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1103111631342587/1125899906842624), (12549733287965/281474976710656)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((134818305221187/140737488355328), (98365808015909/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((1024590718816237/1125899906842624), (94228706817159/562949953421312)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((900852676304919/1125899906842624), (342999791950111/1125899906842624)), (35/1125899906842624), by norm_num⟩
  | 4 => ⟨((616295181224227/1125899906842624), (548880550877385/1125899906842624)), (39/562949953421312), by norm_num⟩
  | 5 => ⟨((69766318294687/1125899906842624), (150223139960129/281474976710656)), (81/562949953421312), by norm_num⟩
  | 6 => ⟨((-1265492703706501/4503599627370496), (297874163313897/4503599627370496)), (773/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-43714940086077/35184372088832), (-1224018322410155/35184372088832)), (1/8796093022208), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term12 (s : ℂ) : ℂ := Complex.exp (F_arg12 s)

def J_term12 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1265492703706501/4503599627370496), (297874163313897/4503599627370496)), (773/4503599627370496), by norm_num⟩
  | 1 => ⟨((196539452168655/281474976710656), (-185047372304685/1125899906842624)), (967/2251799813685248), by norm_num⟩
  | 2 => ⟨((-976764383279163/1125899906842624), (114956361491427/562949953421312)), (605/1125899906842624), by norm_num⟩
  | 3 => ⟨((1618112207524311/2251799813685248), (-11902326129395/70368744177664)), (1009/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1005214446145075/2251799813685248), (236609354775033/2251799813685248)), (631/2251799813685248), by norm_num⟩
  | 5 => ⟨((999145624675543/4503599627370496), (-235180863633011/4503599627370496)), (79/562949953421312), by norm_num⟩
  | 6 => ⟨((-1655189071241895/18014398509481984), (389601661296369/18014398509481984)), (527/9007199254740992), by norm_num⟩
  | 7 => ⟨((587570047112201/18014398509481984), (-276606788263943/36028797018963968)), (377/18014398509481984), by norm_num⟩
  | 8 => ⟨((-1460056717285357/144115188075855872), (343671023766787/144115188075855872)), (943/144115188075855872), by norm_num⟩
  | _ => zero

theorem A_term12 : AnalyticAt ℂ F_term12 c := by
  exact A_arg12.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound A_arg12 S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term12, J_arg12, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log13 (s : ℂ) : ℂ := (Real.log (13 : ℝ) : ℂ)

def J_log13 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log13 : AnalyticAt ℂ F_log13 c := by
  exact analyticAt_const

theorem S_log13 : Sound J_log13 F_log13 c := by
  have hlog : Contains ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (13 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_13 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog13 (s : ℂ) : ℂ := value (-1, 0)*F_log13 s

def J_negLog13 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-360984530327749/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog13 : AnalyticAt ℂ F_negLog13 c := by
  exact analyticAt_const.mul A_log13

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale A_log13 S_log13)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term12, J_log13, J_negLog13,
    J_log13, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg13 (s : ℂ) : ℂ := F_negLog13 s*F_variable s

def J_arg13 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-45123066290969/35184372088832), (-631722928073561/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-360984530327749/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg13 : AnalyticAt ℂ F_arg13 c := by
  exact A_negLog13.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul A_negLog13 A_variable S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log13, J_negLog13, J_arg13,
    J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582305200647293/10141204801825835211973625643008), (72857546151/316912650057057350374175801344)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779986957508795/633825300114114700748351602688), (2762746881357/633825300114114700748351602688)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59097247494921/1237940039285380274899124224), (3107729097749/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890972142096533/2475880078570760549798248448), (3301529236723/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772637851286303/154742504910672534362390528), (3301042204609/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550909567603795/9671406556917033397649408), (1547104815679/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314993683582839/151115727451828646838272), (676729008155/151115727451828646838272)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889718302005635/75557863725914323419136), (2198884262077/37778931862957161709568)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298983205155821/4722366482869645213696), (824369426091/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811715872331991/295147905179352825856), (4532652886603/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825951863316563/73786976294838206464), (5663747957257/73786976294838206464)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912720315074655/4611686018427387904), (3184436603449/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798342589489445/576460752303423488), (795664980683/144115188075855872)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((598469109403909/72057594037927936), (2782829145041/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((747582351002867/18014398509481984), (4170248341271/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((373412821617833/2251799813685248), (2602910610361/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118344418841221/2251799813685248), (649417854091/140737488355328)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((278637387130587/281474976710656), (15533674643213/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1103131405768445/1125899906842624), (15429081743889/562949953421312)), (1/281474976710656), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1103131405768445/1125899906842624), (15429081743889/562949953421312)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((539988796849945/562949953421312), (60468269090039/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((516340388812901/562949953421312), (58001937250525/562949953421312)), (19/1125899906842624), by norm_num⟩
  | 3 => ⟨((467613809708645/562949953421312), (26599827080387/140737488355328)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((368313135046579/562949953421312), (353521911581849/1125899906842624)), (41/562949953421312), by norm_num⟩
  | 5 => ⟨((741878593798037/2251799813685248), (925174699960751/2251799813685248)), (319/2251799813685248), by norm_num⟩
  | 6 => ⟨((-135697842967503/2251799813685248), (609616628665679/2251799813685248)), (473/2251799813685248), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45123066290969/35184372088832), (-631722928073561/17592186044416)), (5/35184372088832), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term13 (s : ℂ) : ℂ := Complex.exp (F_arg13 s)

def J_term13 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-135697842967503/2251799813685248), (609616628665679/2251799813685248)), (473/2251799813685248), by norm_num⟩
  | 1 => ⟨((348058095128413/2251799813685248), (-1563635779993901/2251799813685248)), (305/562949953421312), by norm_num⟩
  | 2 => ⟨((-223187846864727/1125899906842624), (501330823649903/562949953421312)), (787/1125899906842624), by norm_num⟩
  | 3 => ⟨((190821841469635/1125899906842624), (-857258782664321/1125899906842624)), (169/281474976710656), by norm_num⟩
  | 4 => ⟨((-15295261239599/140737488355328), (549706340943277/1125899906842624)), (109/281474976710656), by norm_num⟩
  | 5 => ⟨((251082051127781/4503599627370496), (-140996892599499/562949953421312)), (225/1125899906842624), by norm_num⟩
  | 6 => ⟨((-214670915236775/9007199254740992), (964399704205755/9007199254740992)), (387/4503599627370496), by norm_num⟩
  | 7 => ⟨((314640014915569/36028797018963968), (-353376628805521/9007199254740992)), (285/9007199254740992), by norm_num⟩
  | 8 => ⟨((-25219865752793/9007199254740992), (906393156996645/72057594037927936)), (1469/144115188075855872), by norm_num⟩
  | _ => zero

theorem A_term13 : AnalyticAt ℂ F_term13 c := by
  exact A_arg13.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound A_arg13 S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term13, J_arg13, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log14 (s : ℂ) : ℂ := (Real.log (14 : ℝ) : ℂ)

def J_log14 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log14 : AnalyticAt ℂ F_log14 c := by
  exact analyticAt_const

theorem S_log14 : Sound J_log14 F_log14 c := by
  have hlog : Contains ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (14 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_14 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog14 (s : ℂ) : ℂ := value (-1, 0)*F_log14 s

def J_negLog14 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-742828600391541/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog14 : AnalyticAt ℂ F_negLog14 c := by
  exact analyticAt_const.mul A_log14

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale A_log14 S_log14)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term13, J_log14, J_negLog14,
    J_log14, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg14 (s : ℂ) : ℂ := F_negLog14 s*F_variable s

def J_arg14 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-46426787524471/35184372088832), (-1299950050685197/35184372088832)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-742828600391541/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg14 : AnalyticAt ℂ F_arg14 c := by
  exact A_negLog14.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul A_negLog14 A_variable S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log14, J_negLog14, J_arg14,
    J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582256933693329/10141204801825835211973625643008), (244991691459/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779933118250253/633825300114114700748351602688), (580592479873/316912650057057350374175801344)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891051555269389/39614081257132168796771975168), (1306179584051/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945454130640735/1237940039285380274899124224), (346907225373/618970019642690137449562112)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772574258959097/154742504910672534362390528), (1387418670927/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775425128098721/4835703278458516698824704), (162560209283/1208925819614629174706176)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157490392889819/75557863725914323419136), (1137698180523/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889635040255057/75557863725914323419136), (231042622647/9444732965739290427392)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298921260785103/4722366482869645213696), (692944795071/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623347386282257/590295810358705651712), (1905003379875/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228230954638449/9223372036854775808), (2380362330345/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912662527047429/4611686018427387904), (669170444745/2305843009213693952)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596571698712881/1152921504606846976), (1337575121883/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196841278245241/144115188075855872), (2339034541829/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495023992777895/36028797018963968), (3505110607439/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493483610399141/9007199254740992), (2187686040277/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118189023767873/2251799813685248), (272897478951/140737488355328)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((557173518568951/562949953421312), (13054099765799/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((2205695963125609/2251799813685248), (12964389536455/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2205695963125609/2251799813685248), (12964389536455/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((270029686398021/281474976710656), (50795814958609/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((2071252415580975/2251799813685248), (761411932593/17592186044416)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((950481465904521/1125899906842624), (89646408959847/1125899906842624)), (51/2251799813685248), by norm_num⟩
  | 4 => ⟨((1590511790518809/2251799813685248), (75679240830723/562949953421312)), (95/2251799813685248), by norm_num⟩
  | 5 => ⟨((1082729548638601/2251799813685248), (213817807617249/1125899906842624)), (5/70368744177664), by norm_num⟩
  | 6 => ⟨((878791311789727/4503599627370496), (51404848895835/281474976710656)), (215/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46426787524471/35184372088832), (-1299950050685197/35184372088832)), (5/35184372088832), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term14 (s : ℂ) : ℂ := Complex.exp (F_arg14 s)

def J_term14 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((878791311789727/4503599627370496), (51404848895835/281474976710656)), (215/2251799813685248), by norm_num⟩
  | 1 => ⟨((-289897581572611/562949953421312), (-542641373025273/1125899906842624)), (575/2251799813685248), by norm_num⟩
  | 2 => ⟨((95632042185867/140737488355328), (716030846417417/1125899906842624)), (385/1125899906842624), by norm_num⟩
  | 3 => ⟨((-673009178337835/1125899906842624), (-629882151156167/1125899906842624)), (43/140737488355328), by norm_num⟩
  | 4 => ⟨((888054902495403/2251799813685248), (415573776950627/1125899906842624)), (115/562949953421312), by norm_num⟩
  | 5 => ⟨((-937451119812503/4503599627370496), (-877378417645959/4503599627370496)), (491/4503599627370496), by norm_num⟩
  | 6 => ⟨((824662416299073/9007199254740992), (771817314644935/9007199254740992)), (437/9007199254740992), by norm_num⟩
  | 7 => ⟨((-155452242442307/4503599627370496), (-145490724381263/4503599627370496)), (333/18014398509481984), by norm_num⟩
  | 8 => ⟨((820494759644997/72057594037927936), (767916725138811/72057594037927936)), (111/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_term14 : AnalyticAt ℂ F_term14 c := by
  exact A_arg14.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound A_arg14 S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term14, J_arg14, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log15 (s : ℂ) : ℂ := (Real.log (15 : ℝ) : ℂ)

def J_log15 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log15 : AnalyticAt ℂ F_log15 c := by
  exact analyticAt_const

theorem S_log15 : Sound J_log15 F_log15 c := by
  have hlog : Contains ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (15 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_15 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog15 (s : ℂ) : ℂ := value (-1, 0)*F_log15 s

def J_negLog15 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-190562091821633/70368744177664), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog15 : AnalyticAt ℂ F_negLog15 c := by
  exact analyticAt_const.mul A_log15

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale A_log15 S_log15)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term14, J_log15, J_negLog15,
    J_log15, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg15 (s : ℂ) : ℂ := F_negLog15 s*F_variable s

def J_arg15 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-2977532684713/2199023255552), (-1333934642751431/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-190562091821633/70368744177664), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg15 : AnalyticAt ℂ F_arg15 c := by
  exact A_negLog15.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul A_negLog15 A_variable S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log15, J_negLog15, J_arg15,
    J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791105999117113/5070602400912917605986812821504), (-139113044523/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889940268319735/316912650057057350374175801344), (-82414422379/158456325028528675187087900672)), (1/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945496223438715/19807040628566084398385987584), (-370820361043/39614081257132168796771975168)), (1/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945422758054239/1237940039285380274899124224), (-393942202505/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443127894609583/38685626227668133590597632), (-393880981177/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550791561876565/9671406556917033397649408), (-184599192779/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629935927113131/302231454903657293676544), (-322983568103/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944775912220463/37778931862957161709568), (-524726418997/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((20294671272181/73786976294838206464), (-393438201907/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25363467302255/9223372036854775808), (-540804342419/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912870531134387/36893488147419103232), (-337872877461/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825205533596169/9223372036854775808), (-94982136729/1152921504606846976)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99778290498059/72057594037927936), (-379705624109/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((299184409161657/36028797018963968), (-663983616219/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((747434792153481/18014398509481984), (-248743461895/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((746646220206345/4503599627370496), (-620983258769/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((139750075894577/281474976710656), (-154918032479/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((139258908670497/140737488355328), (-3704948961535/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((137790464655431/140737488355328), (-3678863574209/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((137790464655431/140737488355328), (-3678863574209/1125899906842624)), (19082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2158458378361089/2251799813685248), (-14407314702515/2251799813685248)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((64652935788393/70368744177664), (-27620207569371/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 3 => ⟨((475126524872281/562949953421312), (-50753428310049/2251799813685248)), (21/1125899906842624), by norm_num⟩
  | 4 => ⟨((1602872289878717/2251799813685248), (-42835601764871/1125899906842624)), (37/1125899906842624), by norm_num⟩
  | 5 => ⟨((1137694393159275/2251799813685248), (-30491164743825/562949953421312)), (7/140737488355328), by norm_num⟩
  | 6 => ⟨((35512513879207/140737488355328), (-123242312959155/2251799813685248)), (63/1125899906842624), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2977532684713/2199023255552), (-1333934642751431/35184372088832)), (1/8796093022208), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term15 (s : ℂ) : ℂ := Complex.exp (F_arg15 s)

def J_term15 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((35512513879207/140737488355328), (-123242312959155/2251799813685248)), (63/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1538714725635705/2251799813685248), (333746370393341/2251799813685248)), (347/2251799813685248), by norm_num⟩
  | 2 => ⟨((130216147568647/140737488355328), (-225950481365205/1125899906842624)), (239/1125899906842624), by norm_num⟩
  | 3 => ⟨((-940351638960079/1125899906842624), (203961748833395/1125899906842624)), (219/1125899906842624), by norm_num⟩
  | 4 => ⟨((636629861248159/1125899906842624), (-276169327472717/2251799813685248)), (151/1125899906842624), by norm_num⟩
  | 5 => ⟨((-1379220499024599/4503599627370496), (299152161120301/4503599627370496)), (333/4503599627370496), by norm_num⟩
  | 6 => ⟨((77812465619747/562949953421312), (-270039690027331/9007199254740992)), (153/4503599627370496), by norm_num⟩
  | 7 => ⟨((-240822929336931/4503599627370496), (208937439109741/18014398509481984)), (241/18014398509481984), by norm_num⟩
  | 8 => ⟨((1304321164441799/72057594037927936), (-282906536999457/72057594037927936)), (83/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_term15 : AnalyticAt ℂ F_term15 c := by
  exact A_arg15.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound A_arg15 S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term15, J_arg15, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log16 (s : ℂ) : ℂ := (Real.log (16 : ℝ) : ℂ)

def J_log16 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log16 : AnalyticAt ℂ F_log16 c := by
  exact analyticAt_const

theorem S_log16 : Sound J_log16 F_log16 c := by
  have hlog : Contains ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (16 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_16 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog16 (s : ℂ) : ℂ := value (-1, 0)*F_log16 s

def J_negLog16 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-390207173010335/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog16 : AnalyticAt ℂ F_negLog16 c := by
  exact analyticAt_const.mul A_log16

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale A_log16 S_log16)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term15, J_log16, J_negLog16,
    J_log16, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg16 (s : ℂ) : ℂ := F_negLog16 s*F_variable s

def J_arg16 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-12193974156573/8796093022208), (-341431276384043/8796093022208)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-390207173010335/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg16 : AnalyticAt ℂ F_arg16 c := by
  exact A_negLog16.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul A_negLog16 A_variable S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log16, J_negLog16, J_arg16,
    J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791084981959727/5070602400912917605986812821504), (-363796725669/2535301200456458802993406410752)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779829203879639/633825300114114700748351602688), (-862047186943/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890934614951057/39614081257132168796771975168), (-1939366185267/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236347995656539/309485009821345068724781056), (-2060284923137/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772449910153957/154742504910672534362390528), (-514989218015/38685626227668133590597632)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550733623147715/9671406556917033397649408), (-965430535667/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629910516594201/302231454903657293676544), (-844577503243/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944734503333705/37778931862957161709568), (-686055929067/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298796643832749/4722366482869645213696), (-2057596402793/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623175888992519/590295810358705651712), (-11047917243/2305843009213693952)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825633042256581/73786976294838206464), (-3533941613279/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825083328310065/9223372036854775808), (-3973771185439/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596329590269899/1152921504606846976), (-248211305127/72057594037927936)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598314501820685/72057594037927936), (-3472270704137/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494704723372963/36028797018963968), (-2601517364397/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((746541513681931/4503599627370496), (-6494402152011/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235572409976367/4503599627370496), (-12960664764377/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227474499804539/2251799813685248), (-19370768044029/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203212704155261/2251799813685248), (-19230668742517/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2203212704155261/2251799813685248), (-19230668742517/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2155017029390471/2251799813685248), (-37631456779965/1125899906842624)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1029939220754761/1125899906842624), (-72028099219775/1125899906842624)), (13/1125899906842624), by norm_num⟩
  | 3 => ⟨((937549372689715/1125899906842624), (-263556516638849/2251799813685248)), (13/562949953421312), by norm_num⟩
  | 4 => ⟨((1530568235468581/2251799813685248), (-438932884426605/2251799813685248)), (25/562949953421312), by norm_num⟩
  | 5 => ⟨((954781607729037/2251799813685248), (-298346560970037/1125899906842624)), (11/140737488355328), by norm_num⟩
  | 6 => ⟨((61680131745129/562949953421312), (-506005564814773/2251799813685248)), (243/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12193974156573/8796093022208), (-341431276384043/8796093022208)), (5/35184372088832), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term16 (s : ℂ) : ℂ := Complex.exp (F_arg16 s)

def J_term16 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((61680131745129/562949953421312), (-506005564814773/2251799813685248)), (243/2251799813685248), by norm_num⟩
  | 1 => ⟨((-342027275325617/1125899906842624), (701472661198005/1125899906842624)), (85/281474976710656), by norm_num⟩
  | 2 => ⟨((474150483133103/1125899906842624), (-486223797349279/562949953421312)), (119/281474976710656), by norm_num⟩
  | 3 => ⟨((-438208094059795/1125899906842624), (898732411343475/1125899906842624)), (111/281474976710656), by norm_num⟩
  | 4 => ⟨((607485409792189/2251799813685248), (-622953837000571/1125899906842624)), (311/1125899906842624), by norm_num⟩
  | 5 => ⟨((-336861439223007/2251799813685248), (690877913177513/2251799813685248)), (87/562949953421312), by norm_num⟩
  | 6 => ⟨((622652151564781/9007199254740992), (-638506770173509/4503599627370496)), (649/9007199254740992), by norm_num⟩
  | 7 => ⟨((-493245238087671/18014398509481984), (505804762873377/9007199254740992)), (519/18014398509481984), by norm_num⟩
  | 8 => ⟨((1335513851973/140737488355328), (-350597145299473/18014398509481984)), (363/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_term16 : AnalyticAt ℂ F_term16 c := by
  exact A_arg16.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound A_arg16 S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term16, J_arg16, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log17 (s : ℂ) : ℂ := (Real.log (17 : ℝ) : ℂ)

def J_log17 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log17 : AnalyticAt ℂ F_log17 c := by
  exact analyticAt_const

theorem S_log17 : Sound J_log17 F_log17 c := by
  have hlog : Contains ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (17 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_17 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog17 (s : ℂ) : ℂ := value (-1, 0)*F_log17 s

def J_negLog17 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-797478660034543/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog17 : AnalyticAt ℂ F_negLog17 c := by
  exact analyticAt_const.mul A_log17

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale A_log17 S_log17)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term16, J_log17, J_negLog17,
    J_log17, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg17 (s : ℂ) : ℂ := F_negLog17 s*F_variable s

def J_arg17 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-49842416252159/35184372088832), (-697793827530225/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-797478660034543/281474976710656), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg17 : AnalyticAt ℂ F_arg17 c := by
  exact A_negLog17.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul A_negLog17 A_variable S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log17, J_negLog17, J_arg17,
    J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582130478750109/10141204801825835211973625643008), (-1280385822169/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779779094683881/633825300114114700748351602688), (-1516915579649/316912650057057350374175801344)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472719513638665/9903520314283042199192993792), (-1706311247807/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890723632499761/2475880078570760549798248448), (-3625386232411/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772389310531837/154742504910672534362390528), (-3624795434577/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24229320743437/151115727451828646838272), (-1698809023363/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259770791287327/604462909807314587353088), (-1486144086667/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889386832732677/75557863725914323419136), (-4828791617079/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162341818649375/590295810358705651712), (-1810282124855/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623089755130363/590295810358705651712), (-2488301594025/295147905179352825856)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825524245319865/73786976294838206464), (-6218245391435/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824959380158175/9223372036854775808), (-1748019345637/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99762731565041/72057594037927936), (-873470935063/144115188075855872)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196516678179615/144115188075855872), (-3054724608053/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494531891716653/36028797018963968), (-9154482448193/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492859405410061/9007199254740992), (-5713075278167/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((558775623387077/1125899906842624), (-11400736653315/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113356602347451/1125899906842624), (-17037622408297/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((1100732997049875/1125899906842624), (-33821629246719/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1100732997049875/1125899906842624), (-33821629246719/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((537556323094489/562949953421312), (-66131248612057/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((255682999206747/281474976710656), (-126296380804351/1125899906842624)), (15/1125899906842624), by norm_num⟩
  | 3 => ⟨((914850383474999/1125899906842624), (-229447305123741/1125899906842624)), (31/1125899906842624), by norm_num⟩
  | 4 => ⟨((696602916075589/1125899906842624), (-186437492182065/562949953421312)), (127/2251799813685248), by norm_num⟩
  | 5 => ⟨((615010031737853/2251799813685248), (-922802461785795/2251799813685248)), (121/1125899906842624), by norm_num⟩
  | 6 => ⟨((-420398866242991/4503599627370496), (-1008140719901453/4503599627370496)), (331/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-49842416252159/35184372088832), (-697793827530225/17592186044416)), (1/8796093022208), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term17 (s : ℂ) : ℂ := Complex.exp (F_arg17 s)

def J_term17 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-420398866242991/4503599627370496), (-1008140719901453/4503599627370496)), (331/2251799813685248), by norm_num⟩
  | 1 => ⟨((595539838832873/2251799813685248), (714069435077809/1125899906842624)), (943/2251799813685248), by norm_num⟩
  | 2 => ⟨((-105455713643649/281474976710656), (-505777763011283/562949953421312)), (21/35184372088832), by norm_num⟩
  | 3 => ⟨((199185690068105/562949953421312), (477658769096823/562949953421312)), (639/1125899906842624), by norm_num⟩
  | 4 => ⟨((-564335555046001/2251799813685248), (-1353309198510585/2251799813685248)), (911/2251799813685248), by norm_num⟩
  | 5 => ⟨((79944151254085/562949953421312), (383421367985421/1125899906842624)), (1039/4503599627370496), by norm_num⟩
  | 6 => ⟨((-603996896299525/9007199254740992), (-362104845390861/2251799813685248)), (247/2251799813685248), by norm_num⟩
  | 7 => ⟨((244464580909193/9007199254740992), (293120079973943/4503599627370496)), (805/18014398509481984), by norm_num⟩
  | 8 => ⟨((-173155078195259/18014398509481984), (-103808965249125/4503599627370496)), (287/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_term17 : AnalyticAt ℂ F_term17 c := by
  exact A_arg17.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound A_arg17 S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term17, J_arg17, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log18 (s : ℂ) : ℂ := (Real.log (18 : ℝ) : ℂ)

def J_log18 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log18 : AnalyticAt ℂ F_log18 c := by
  exact analyticAt_const

theorem S_log18 : Sound J_log18 F_log18 c := by
  have hlog : Contains ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (18 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_18 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog18 (s : ℂ) : ℂ := value (-1, 0)*F_log18 s

def J_negLog18 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1627134646477921/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog18 : AnalyticAt ℂ F_negLog18 c := by
  exact analyticAt_const.mul A_log18

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale A_log18 S_log18)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term17, J_log18, J_negLog18,
    J_log18, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg18 (s : ℂ) : ℂ := F_negLog18 s*F_variable s

def J_arg18 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-50847957702435/35184372088832), (-1423742815668181/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-1627134646477921/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg18 : AnalyticAt ℂ F_arg18 c := by
  exact A_negLog18.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul A_negLog18 A_variable S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log18, J_negLog18, J_arg18,
    J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791046625571105/5070602400912917605986812821504), (-1801572332745/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55616567939675/19807040628566084398385987584), (-4268563950835/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890822744899621/39614081257132168796771975168), (-1200373509325/9903520314283042199192993792)), (1/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945332259388933/1237940039285380274899124224), (-5100832097511/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221541225795201/19342813113834066795298816), (-1274995556783/38685626227668133590597632)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550620327760061/9671406556917033397649408), (-4780330309227/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259721201999273/604462909807314587353088), (-1045471486291/151115727451828646838272)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889305473510197/75557863725914323419136), (-6793871295629/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298672850683569/4722366482869645213696), (-1273480419667/1180591620717411303424)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623003817003679/590295810358705651712), (-7001734210753/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57044224067119/2305843009213693952), (-4374277648807/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824834400814845/9223372036854775808), (-4918578526559/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399018973031453/288230376151711744), (-9830946713789/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598200829562519/72057594037927936), (-4297545347825/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((747176505079601/18014398509481984), (-6439329048031/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492624713948525/9007199254740992), (-2009231932923/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117299977410945/2251799813685248), (-16037143425243/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((556469225388723/562949953421312), (-11981948177315/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((549866443315149/562949953421312), (-47560292417455/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((549866443315149/562949953421312), (-47560292417455/1125899906842624)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((134020621325323/140737488355328), (-46454944486055/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((1013327623338993/1125899906842624), (-2764864125939/17592186044416)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((55262522791937/70368744177664), (-318517913182519/1125899906842624)), (35/1125899906842624), by norm_num⟩
  | 4 => ⟨((302139035508983/562949953421312), (-1000563738494359/2251799813685248)), (75/1125899906842624), by norm_num⟩
  | 5 => ⟨((204050178381973/2251799813685248), (-134252326106731/281474976710656)), (295/2251799813685248), by norm_num⟩
  | 6 => ⟨((-987547374423983/4503599627370496), (-389295153841449/4503599627370496)), (671/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50847957702435/35184372088832), (-1423742815668181/35184372088832)), (1/8796093022208), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term18 (s : ℂ) : ℂ := Complex.exp (F_arg18 s)

def J_term18 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-987547374423983/4503599627370496), (-389295153841449/4503599627370496)), (671/4503599627370496), by norm_num⟩
  | 1 => ⟨((713594760154897/1125899906842624), (562603859074583/2251799813685248)), (61/140737488355328), by norm_num⟩
  | 2 => ⟨((-16113704229175/17592186044416), (-203266788144071/562949953421312)), (355/562949953421312), by norm_num⟩
  | 3 => ⟨((496795686603727/562949953421312), (391677722513257/1125899906842624)), (43/70368744177664), by norm_num⟩
  | 4 => ⟨((-717962111002023/1125899906842624), (-35377944604669/140737488355328)), (125/281474976710656), by norm_num⟩
  | 5 => ⟨((830070963551903/2251799813685248), (327217318200801/2251799813685248)), (291/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1599475780066717/9007199254740992), (-630519796814745/9007199254740992)), (141/1125899906842624), by norm_num⟩
  | 7 => ⟨((660439946020539/9007199254740992), (520696175287933/18014398509481984)), (937/18014398509481984), by norm_num⟩
  | 8 => ⟨((-238614620970529/9007199254740992), (-188125689937099/18014398509481984)), (681/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_term18 : AnalyticAt ℂ F_term18 c := by
  exact A_arg18.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound A_arg18 S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term18, J_arg18, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log19 (s : ℂ) : ℂ := (Real.log (19 : ℝ) : ℂ)

def J_log19 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log19 : AnalyticAt ℂ F_log19 c := by
  exact analyticAt_const

theorem S_log19 : Sound J_log19 F_log19 c := by
  have hlog : Contains ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (19 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_19 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog19 (s : ℂ) : ℂ := value (-1, 0)*F_log19 s

def J_negLog19 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1657571786173643/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog19 : AnalyticAt ℂ F_negLog19 c := by
  exact analyticAt_const.mul A_log19

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale A_log19 S_log19)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term18, J_log19, J_negLog19,
    J_log19, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg19 (s : ℂ) : ℂ := F_negLog19 s*F_variable s

def J_arg19 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-25899559158963/17592186044416), (-725187656450969/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-1657571786173643/562949953421312), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg19 : AnalyticAt ℂ F_arg19 c := by
  exact A_negLog19.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul A_negLog19 A_variable S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log19, J_negLog19, J_arg19,
    J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197757254605755/1267650600228229401496703205376), (3595405425619/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889844249592985/316912650057057350374175801344), (8318760959/1237940039285380274899124224)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945387934956343/19807040628566084398385987584), (4790956339549/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890614724693183/2475880078570760549798248448), (636202930225/309485009821345068724781056)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221535003024531/19342813113834066795298816), (2544379841633/77371252455336267181195264)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193821708705963/1208925819614629174706176), (596224303357/1208925819614629174706176)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259680388822445/604462909807314587353088), (521581538791/75557863725914323419136)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118077448491561/4722366482869645213696), (847354878301/9444732965739290427392)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324655787063491/1180591620717411303424), (5082623336403/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811467754992543/295147905179352825856), (6986159800857/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825329837134113/73786976294838206464), (8729028569187/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912369235505773/4611686018427387904), (9815108859323/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595980049682779/1152921504606846976), (9808797904975/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((149539736919395/18014398509481984), (4287798761693/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((747113780728777/18014398509481984), (1606149122099/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492468248226209/9007199254740992), (8018315480465/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117144030386791/2251799813685248), (3999832955785/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112705830334745/1125899906842624), (11952860071023/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 0 => ⟨((549636432971999/562949953421312), (47438158358333/1125899906842624)), (1/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((549636432971999/562949953421312), (47438158358333/1125899906842624)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((535638402491179/562949953421312), (46316266638575/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((1011682477056179/1125899906842624), (22034615085113/140737488355328)), (19/1125899906842624), by norm_num⟩
  | 3 => ⟨((881453027561627/1125899906842624), (158394428029045/562949953421312)), (41/1125899906842624), by norm_num⟩
  | 4 => ⟨((1201890605662053/2251799813685248), (31001256702877/70368744177664)), (175/2251799813685248), by norm_num⟩
  | 5 => ⟨((204457446888123/2251799813685248), (529498140549913/1125899906842624)), (171/1125899906842624), by norm_num⟩
  | 6 => ⟨((-958939839353025/4503599627370496), (384616207145583/4503599627370496)), (769/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-25899559158963/17592186044416), (-725187656450969/17592186044416)), (5/35184372088832), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term19 (s : ℂ) : ℂ := Complex.exp (F_arg19 s)

def J_term19 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-958939839353025/4503599627370496), (384616207145583/4503599627370496)), (769/4503599627370496), by norm_num⟩
  | 1 => ⟨((705884960416663/1125899906842624), (-70779934521163/281474976710656)), (569/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1039217596129091/1125899906842624), (416814396293921/1125899906842624)), (421/562949953421312), by norm_num⟩
  | 3 => ⟨((7968522911141/8796093022208), (-204547425920925/562949953421312)), (831/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1501621085820441/2251799813685248), (602277413969731/2251799813685248)), (615/1125899906842624), by norm_num⟩
  | 5 => ⟨((221071582851397/562949953421312), (-44334227349101/281474976710656)), (91/281474976710656), by norm_num⟩
  | 6 => ⟨((-433954523822451/2251799813685248), (1359785699145/17592186044416)), (359/2251799813685248), by norm_num⟩
  | 7 => ⟨((1460288703003927/18014398509481984), (-292849811446903/9007199254740992)), (607/9007199254740992), by norm_num⟩
  | 8 => ⟨((-268733186122573/9007199254740992), (215569599966451/18014398509481984)), (449/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_term19 : AnalyticAt ℂ F_term19 c := by
  exact A_arg19.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound A_arg19 S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term19, J_arg19, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log20 (s : ℂ) : ℂ := (Real.log (20 : ℝ) : ℂ)

def J_log20 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log20 : AnalyticAt ℂ F_log20 c := by
  exact analyticAt_const

theorem S_log20 : Sound J_log20 F_log20 c := by
  have hlog : Contains ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (20 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_20 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog20 (s : ℂ) : ℂ := value (-1, 0)*F_log20 s

def J_negLog20 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-421611835964985/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog20 : AnalyticAt ℂ F_negLog20 c := by
  exact analyticAt_const.mul A_log20

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale A_log20 S_log20)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term19, J_log20, J_negLog20,
    J_log20, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg20 (s : ℂ) : ℂ := F_negLog20 s*F_variable s

def J_arg20 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-52701479495623/35184372088832), (-184455178234681/4398046511104)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-421611835964985/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg20 : AnalyticAt ℂ F_arg20 c := by
  exact A_negLog20.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul A_negLog20 A_variable S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log20, J_negLog20, J_arg20,
    J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582024629224607/10141204801825835211973625643008), (2659992025497/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779653311290497/633825300114114700748351602688), (98467458467/19807040628566084398385987584)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890736545025775/39614081257132168796771975168), (1772174317453/19807040628566084398385987584)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945286636216837/1237940039285380274899124224), (3765293705345/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772238943524571/154742504910672534362390528), (3764644920021/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775267775578087/4835703278458516698824704), (220541583697/604462909807314587353088)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259647429585107/604462909807314587353088), (1543446483491/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889186356269213/75557863725914323419136), (5014908958247/75557863725914323419136)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162323022488901/590295810358705651712), (1880025632845/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811441489030315/295147905179352825856), (5168233778127/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456316436296611/18446744073709551616), (6457537634193/73786976294838206464)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824668528173845/9223372036854775808), (3630471529961/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99744550267441/72057594037927936), (7256210759165/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((598131042837547/72057594037927936), (6343862190485/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((373537473905605/9007199254740992), (9505152882009/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492381725458583/9007199254740992), (1482853689383/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117073295572279/2251799813685248), (369841575715/70368744177664)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112639018358061/1125899906842624), (8841356071753/562949953421312)), (1/562949953421312), by norm_num⟩
  | 0 => ⟨((549647662736611/562949953421312), (35087077579985/1125899906842624)), (1/281474976710656), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((549647662736611/562949953421312), (35087077579985/1125899906842624)), (3815771007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1072225960991145/1125899906842624), (68515966887961/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 2 => ⟨((1016941263380737/1125899906842624), (130499341892121/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 3 => ⟨((225850328424067/281474976710656), (235740610346597/1125899906842624)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((337756621880539/562949953421312), (378307833199677/1125899906842624)), (163/2251799813685248), by norm_num⟩
  | 5 => ⟨((278178658629339/1125899906842624), (453951456948933/1125899906842624)), (153/1125899906842624), by norm_num⟩
  | 6 => ⟨((-457193604394635/4503599627370496), (112158822120357/562949953421312)), (797/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-52701479495623/35184372088832), (-184455178234681/4398046511104)), (5/35184372088832), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term20 (s : ℂ) : ℂ := Complex.exp (F_arg20 s)

def J_term20 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-457193604394635/4503599627370496), (112158822120357/562949953421312)), (797/4503599627370496), by norm_num⟩
  | 1 => ⟨((342407408986871/1125899906842624), (-1343991212759019/2251799813685248)), (75/140737488355328), by norm_num⟩
  | 2 => ⟨((-512880462902985/1125899906842624), (503279731429395/562949953421312)), (903/1125899906842624), by norm_num⟩
  | 3 => ⟨((512150851731261/1125899906842624), (-1005127556045749/1125899906842624)), (453/562949953421312), by norm_num⟩
  | 4 => ⟨((-95891677216219/281474976710656), (376386632335587/562949953421312)), (341/562949953421312), by norm_num⟩
  | 5 => ⟨((459625267522959/2251799813685248), (-451021432728807/1125899906842624)), (411/1125899906842624), by norm_num⟩
  | 6 => ⟨((-57371426985809/562949953421312), (450379820696749/2251799813685248)), (825/4503599627370496), by norm_num⟩
  | 7 => ⟨((196422211887125/4503599627370496), (-96372668872765/1125899906842624)), (355/4503599627370496), by norm_num⟩
  | 8 => ⟨((-588428359393121/36028797018963968), (1154826857722697/36028797018963968)), (1069/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_term20 : AnalyticAt ℂ F_term20 c := by
  exact A_arg20.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound A_arg20 S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term20, J_arg20, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_log21 (s : ℂ) : ℂ := (Real.log (21 : ℝ) : ℂ)

def J_log21 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_log21 : AnalyticAt ℂ F_log21 c := by
  exact analyticAt_const

theorem S_log21 : Sound J_log21 F_log21 c := by
  have hlog : Contains ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩ (Real.log (21 : ℝ) : ℂ) := by
    apply CertifiedScalarExp.contains_real
    convert HardTileLogInputs.log_21 using 1 <;> norm_num
  have h := constant_sound (c := c) hlog
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_negLog21 (s : ℂ) : ℂ := value (-1, 0)*F_log21 s

def J_negLog21 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-428478441126635/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLog21 : AnalyticAt ℂ F_negLog21 c := by
  exact analyticAt_const.mul A_log21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale A_log21 S_log21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term20, J_log21, J_negLog21,
    J_log21, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_arg21 (s : ℂ) : ℂ := F_negLog21 s*F_variable s

def J_arg21 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-53559805140829/35184372088832), (-749837271971611/17592186044416)), (5/35184372088832), by norm_num⟩
  | 1 => ⟨((-428478441126635/140737488355328), 0), (1/140737488355328), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_arg21 : AnalyticAt ℂ F_arg21 c := by
  exact A_negLog21.mul A_variable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul A_negLog21 A_variable S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_log21, J_negLog21, J_arg21,
    J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790996425953233/5070602400912917605986812821504), (885113558783/5070602400912917605986812821504)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222452328079813/79228162514264337593543950336), (2096881522247/633825300114114700748351602688)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945348850045873/19807040628566084398385987584), (2358671382155/39614081257132168796771975168)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945266112186125/1237940039285380274899124224), (2505698789483/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772198148108537/154742504910672534362390528), (2505260612907/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550497573769145/9671406556917033397649408), (1174108170925/4835703278458516698824704)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259614467551767/604462909807314587353088), (1027111953093/302231454903657293676544)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889133295515909/75557863725914323419136), (417155178331/9444732965739290427392)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649272411895557/2361183241434822606848), (2502167892523/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202853697119405/73786976294838206464), (1719620523301/295147905179352825856)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825200063202809/73786976294838206464), (1074298056457/18446744073709551616)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912298052417671/4611686018427387904), (4831786032825/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398960553691019/288230376151711744), (4828593531677/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299050594937531/36028797018963968), (4221429873411/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494064448664655/36028797018963968), (3162485558841/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492282094942327/9007199254740992), (3946835862225/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116984396973139/2251799813685248), (3937441017409/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 1 => ⟨((556266188340951/562949953421312), (23530862561641/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 0 => ⟨((1099188126950287/1125899906842624), (46687579741181/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1099188126950287/1125899906842624), (46687579741181/2251799813685248)), (11448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((536313041045381/562949953421312), (91159850028701/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 2 => ⟨((1020027779945089/1125899906842624), (21711617566093/281474976710656)), (27/2251799813685248), by norm_num⟩
  | 3 => ⟨((1834824492274703/2251799813685248), (314720026963167/2251799813685248)), (27/1125899906842624), by norm_num⟩
  | 4 => ⟨((1451075802662871/2251799813685248), (16027624052433/70368744177664)), (13/281474976710656), by norm_num⟩
  | 5 => ⟨((409132953898257/1125899906842624), (330506074940657/1125899906842624)), (183/2251799813685248), by norm_num⟩
  | 6 => ⟨((206609870164819/4503599627370496), (960802472049165/4503599627370496)), (241/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53559805140829/35184372088832), (-749837271971611/17592186044416)), (5/35184372088832), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_term21 (s : ℂ) : ℂ := Complex.exp (F_arg21 s)

def J_term21 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((206609870164819/4503599627370496), (960802472049165/4503599627370496)), (241/2251799813685248), by norm_num⟩
  | 1 => ⟨((-314514192785957/2251799813685248), (-1462592342186907/2251799813685248)), (739/2251799813685248), by norm_num⟩
  | 2 => ⟨((239386379229829/1125899906842624), (1113223800757623/1125899906842624)), (283/562949953421312), by norm_num⟩
  | 3 => ⟨((-242939067616861/1125899906842624), (-1129744946538111/1125899906842624)), (579/1125899906842624), by norm_num⟩
  | 4 => ⟨((369816721179571/2251799813685248), (429941729829991/562949953421312)), (111/281474976710656), by norm_num⟩
  | 5 => ⟨((-112591530547651/1125899906842624), (-1047173794704823/2251799813685248)), (545/2251799813685248), by norm_num⟩
  | 6 => ⟨((57131240174991/1125899906842624), (531357352362469/2251799813685248)), (557/4503599627370496), by norm_num⟩
  | 7 => ⟨((-397571068817659/18014398509481984), (-1848833579104969/18014398509481984)), (975/18014398509481984), by norm_num⟩
  | 8 => ⟨((302603509901261/36028797018963968), (1407203828800395/36028797018963968)), (747/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_term21 : AnalyticAt ℂ F_term21 c := by
  exact A_arg21.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound A_arg21 S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_term21, J_arg21, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_initial2 (s : ℂ) : ℂ := F_q1 s+F_term2 s

def J_initial2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((90153947277087/281474976710656), (438932884426569/2251799813685248)), (691/2251799813685248), by norm_num⟩
  | 1 => ⟨((1060909057069637/2251799813685248), (-38030636411915/281474976710656)), (483/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1470732243476657/9007199254740992), (105443313615277/2251799813685248)), (337/4503599627370496), by norm_num⟩
  | 3 => ⟨((679622605282965/18014398509481984), (-97450314055103/9007199254740992)), (627/36028797018963968), by norm_num⟩
  | 4 => ⟨((-942156985393383/144115188075855872), (270189641727903/144115188075855872)), (219/72057594037927936), by norm_num⟩
  | 5 => ⟨((1044885532912449/1152921504606846976), (-74912475352079/288230376151711744)), (489/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-482839640764093/4611686018427387904), (276935312421653/9223372036854775808)), (455/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1529960848723235/147573952589676412928), (-219379349717207/73786976294838206464)), (363/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1060488048659611/1180591620717411303424), (38015544432389/147573952589676412928)), (507/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem A_initial2 : AnalyticAt ℂ F_initial2 c := by
  exact A_q1.add A_term2

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial2 : Sound J_initial2 F_initial2 c := by
  apply sound_round (sound_add A_q1 A_term2 S_q1 S_term2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial2, J_q1, J_term2, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial3 (s : ℂ) : ℂ := F_initial2 s+F_term3 s

def J_initial3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-254895684977367/1125899906842624), (20861955779641/2251799813685248)), (1459/2251799813685248), by norm_num⟩
  | 1 => ⟨((150832874722701/140737488355328), (38763192112771/562949953421312)), (669/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1110573994885139/2251799813685248), (-18356477852863/281474976710656)), (323/1125899906842624), by norm_num⟩
  | 3 => ⟨((714005057487461/4503599627370496), (272115735627807/9007199254740992)), (865/9007199254740992), by norm_num⟩
  | 4 => ⟨((-715523917045953/18014398509481984), (-169231196612099/18014398509481984)), (897/36028797018963968), by norm_num⟩
  | 5 => ⟨((590665516088361/72057594037927936), (39922706252135/18014398509481984)), (763/144115188075855872), by norm_num⟩
  | 6 => ⟨((-207477785123159/144115188075855872), (-244042535295001/576460752303423488)), (549/576460752303423488), by norm_num⟩
  | 7 => ⟨((126754107007873/576460752303423488), (157214916361249/2305843009213693952)), (685/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-1094643152379989/36893488147419103232), (-87748973784289/9223372036854775808)), (47/2305843009213693952), by norm_num⟩
  | _ => zero

theorem A_initial3 : AnalyticAt ℂ F_initial3 c := by
  exact A_initial2.add A_term3

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial3 : Sound J_initial3 F_initial3 c := by
  apply sound_round (sound_add A_initial2 A_term3 S_initial2 S_term3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial3, J_initial2, J_term3, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial4 (s : ℂ) : ℂ := F_initial3 s+F_term4 s

def J_initial4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((444990237774309/2251799813685248), (-575831166160417/2251799813685248)), (1771/2251799813685248), by norm_num⟩
  | 1 => ⟨((1089717636667461/2251799813685248), (982245078715609/2251799813685248)), (1781/2251799813685248), by norm_num⟩
  | 2 => ⟨((-193118592750971/2251799813685248), (-720217840463627/2251799813685248)), (961/2251799813685248), by norm_num⟩
  | 3 => ⟨((-133903776217591/4503599627370496), (1331921171778609/9007199254740992)), (1461/9007199254740992), by norm_num⟩
  | 4 => ⟨((459927317863103/18014398509481984), (-451916173311065/9007199254740992)), (871/18014398509481984), by norm_num⟩
  | 5 => ⟨((-712951618892307/72057594037927936), (487194785276707/36028797018963968)), (215/18014398509481984), by norm_num⟩
  | 6 => ⟨((197460621318915/72057594037927936), (-437481392810519/144115188075855872)), (727/288230376151711744), by norm_num⟩
  | 7 => ⟨((-700894500646155/1152921504606846976), (168765947490837/288230376151711744)), (269/576460752303423488), by norm_num⟩
  | 8 => ⟨((131177789184789/1152921504606846976), (-228653255797233/2305843009213693952)), (707/9223372036854775808), by norm_num⟩
  | _ => zero

theorem A_initial4 : AnalyticAt ℂ F_initial4 c := by
  exact A_initial3.add A_term4

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial4 : Sound J_initial4 F_initial4 c := by
  apply sound_round (sound_add A_initial3 A_term4 S_initial3 S_term4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial4, J_initial3, J_term4, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial5 (s : ℂ) : ℂ := F_initial4 s+F_term5 s

def J_initial5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-418243892127933/2251799813685248), (-28614928841453/1125899906842624)), (331/281474976710656), by norm_num⟩
  | 1 => ⟨((309879921579899/281474976710656), (36897117853493/562949953421312)), (801/562949953421312), by norm_num⟩
  | 2 => ⟨((-655566064985901/1125899906842624), (-48553846636189/2251799813685248)), (1057/1125899906842624), by norm_num⟩
  | 3 => ⟨((1065678472727581/4503599627370496), (-109414156331767/9007199254740992)), (3953/9007199254740992), by norm_num⟩
  | 4 => ⟨((-1470725832672217/18014398509481984), (128018757086805/9007199254740992)), (2891/18014398509481984), by norm_num⟩
  | 5 => ⟨((110803842630825/4503599627370496), (-259500625705023/36028797018963968)), (1741/36028797018963968), by norm_num⟩
  | 6 => ⟨((-938666040012653/144115188075855872), (363691876172519/144115188075855872)), (445/36028797018963968), by norm_num⟩
  | 7 => ⟨((13687886108681/9007199254740992), (-99822545330305/144115188075855872)), (791/288230376151711744), by norm_num⟩
  | 8 => ⟨((-22644051816877/72057594037927936), (364281436362911/2305843009213693952)), (1241/2305843009213693952), by norm_num⟩
  | _ => zero

theorem A_initial5 : AnalyticAt ℂ F_initial5 c := by
  exact A_initial4.add A_term5

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial5 : Sound J_initial5 F_initial5 c := by
  apply sound_round (sound_add A_initial4 A_term5 S_initial4 S_term5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial5, J_initial4, J_term5, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial6 (s : ℂ) : ℂ := F_initial5 s+F_term6 s

def J_initial6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((249992955634607/1125899906842624), (-13020941100437/2251799813685248)), (5629/4503599627370496), by norm_num⟩
  | 1 => ⟨((416896213737469/1125899906842624), (17094181625755/562949953421312)), (1755/1125899906842624), by norm_num⟩
  | 2 => ⟨((81405633318245/1125899906842624), (22410350372949/2251799813685248)), (2395/2251799813685248), by norm_num⟩
  | 3 => ⟨((-347478109629233/2251799813685248), (-278948518954819/9007199254740992)), (4641/9007199254740992), by norm_num⟩
  | 4 => ⟨((1683908048545203/18014398509481984), (101979978492077/4503599627370496)), (3523/18014398509481984), by norm_num⟩
  | 5 => ⟨((-687253655200493/18014398509481984), (-368355316921515/36028797018963968)), (2205/36028797018963968), by norm_num⟩
  | 6 => ⟨((440509683833377/36028797018963968), (123429873002637/36028797018963968)), (1175/72057594037927936), by norm_num⟩
  | 7 => ⟨((-944562888755325/288230376151711744), (-266210294071735/288230376151711744)), (17/4503599627370496), by norm_num⟩
  | 8 => ⟨((876316313817457/1152921504606846976), (483550269895885/2305843009213693952)), (1787/2305843009213693952), by norm_num⟩
  | _ => zero

theorem A_initial6 : AnalyticAt ℂ F_initial6 c := by
  exact A_initial5.add A_term6

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial6 : Sound J_initial6 F_initial6 c := by
  apply sound_round (sound_add A_initial5 A_term6 S_initial5 S_term6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial6, J_initial5, J_term6, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial7 (s : ℂ) : ℂ := F_initial6 s+F_term7 s

def J_initial7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((31492713326031/1125899906842624), (-743364934026613/2251799813685248)), (6741/4503599627370496), by norm_num⟩
  | 1 => ⟨((210519513204193/281474976710656), (46548766082489/70368744177664)), (2301/1125899906842624), by norm_num⟩
  | 2 => ⟨((-83069298652741/281474976710656), (-1360337628131021/2251799813685248)), (3467/2251799813685248), by norm_num⟩
  | 3 => ⟨((189181632609001/2251799813685248), (827163978580159/2251799813685248)), (3725/4503599627370496), by norm_num⟩
  | 4 => ⟨((-101168807369093/4503599627370496), (-770664506196241/4503599627370496)), (785/2251799813685248), by norm_num⟩
  | 5 => ⟨((125585424369387/18014398509481984), (293573137239239/4503599627370496)), (273/2251799813685248), by norm_num⟩
  | 6 => ⟨((-43363793830613/18014398509481984), (-757723781598497/36028797018963968)), (2589/72057594037927936), by norm_num⟩
  | 7 => ⟨((227958662743623/288230376151711744), (1693384950917437/288230376151711744)), (1337/144115188075855872), by norm_num⟩
  | 8 => ⟨((-264494479706485/1152921504606846976), (-832411501342269/576460752303423488)), (1225/576460752303423488), by norm_num⟩
  | _ => zero

theorem A_initial7 : AnalyticAt ℂ F_initial7 c := by
  exact A_initial6.add A_term7

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial7 : Sound J_initial7 F_initial7 c := by
  apply sound_round (sound_add A_initial6 A_term7 S_initial6 S_term7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial7, J_initial6, J_term7, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial8 (s : ℂ) : ℂ := F_initial7 s+F_term8 s

def J_initial8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-939354900947567/4503599627370496), (-303352397511939/4503599627370496)), (7775/4503599627370496), by norm_num⟩
  | 1 => ⟨((1395898710019865/1125899906842624), (64794594693467/562949953421312)), (711/281474976710656), by norm_num⟩
  | 2 => ⟨((-454048017612617/562949953421312), (-81083765400987/2251799813685248)), (4607/2251799813685248), by norm_num⟩
  | 3 => ⟨((987436044379157/2251799813685248), (-59547229591583/2251799813685248)), (5319/4503599627370496), by norm_num⟩
  | 4 => ⟨((-931130499701125/4503599627370496), (75633777338239/2251799813685248)), (2405/4503599627370496), by norm_num⟩
  | 5 => ⟨((1506270881199889/18014398509481984), (-5615476747363/281474976710656)), (1793/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1043745819303409/36028797018963968), (305344307859383/36028797018963968)), (2275/36028797018963968), by norm_num⟩
  | 7 => ⟨((625579227692115/72057594037927936), (-6507822453573/2251799813685248)), (157/9007199254740992), by norm_num⟩
  | 8 => ⟨((-41081124851703/18014398509481984), (480956615292795/576460752303423488)), (307/72057594037927936), by norm_num⟩
  | _ => zero

theorem A_initial8 : AnalyticAt ℂ F_initial8 c := by
  exact A_initial7.add A_term8

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial8 : Sound J_initial8 F_initial8 c := by
  apply sound_round (sound_add A_initial7 A_term8 S_initial7 S_term8)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial8, J_initial7, J_term8, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial9 (s : ℂ) : ℂ := F_initial8 s+F_term9 s

def J_initial9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((31420932752975/562949953421312), (152714591673821/1125899906842624)), (8209/4503599627370496), by norm_num⟩
  | 1 => ⟨((46364224990233/70368744177664), (-186296200304213/562949953421312)), (3087/1125899906842624), by norm_num⟩
  | 2 => ⟨((-189525475922937/1125899906842624), (1022321966422599/2251799813685248)), (5151/2251799813685248), by norm_num⟩
  | 3 => ⟨((-65137884587003/2251799813685248), (-867690627170397/2251799813685248)), (6131/4503599627370496), by norm_num⟩
  | 4 => ⟨((225240153392773/4503599627370496), (1039103822262561/4503599627370496)), (2859/4503599627370496), by norm_num⟩
  | 5 => ⟨((-131593483597677/4503599627370496), (-960005523031855/9007199254740992)), (275/1125899906842624), by norm_num⟩
  | 6 => ⟨((444979895966827/36028797018963968), (1448355572429777/36028797018963968)), (2881/36028797018963968), by norm_num⟩
  | 7 => ⟨((-309010695309087/72057594037927936), (-231452039820457/18014398509481984)), (1643/72057594037927936), by norm_num⟩
  | 8 => ⟨((369453976647255/288230376151711744), (128599521167965/36028797018963968)), (1661/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_initial9 : AnalyticAt ℂ F_initial9 c := by
  exact A_initial8.add A_term9

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial9 : Sound J_initial9 F_initial9 c := by
  apply sound_round (sound_add A_initial8 A_term9 S_initial8 S_term9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial9, J_initial8, J_term9, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial10 (s : ℂ) : ℂ := F_initial9 s+F_term10 s

def J_initial10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1222686106031891/4503599627370496), (-215334931239625/2251799813685248)), (8755/4503599627370496), by norm_num⟩
  | 1 => ⟨((182691642283673/1125899906842624), (28369930374877/140737488355328)), (1703/562949953421312), by norm_num⟩
  | 2 => ⟨((227101792247215/562949953421312), (-358197171144995/2251799813685248)), (5895/2251799813685248), by norm_num⟩
  | 3 => ⟨((-1053298510216399/2251799813685248), (191896968414983/2251799813685248)), (911/562949953421312), by norm_num⟩
  | 4 => ⟨((1362902116421733/4503599627370496), (-180791478895589/4503599627370496)), (3533/4503599627370496), by norm_num⟩
  | 5 => ⟨((-1311012357970085/9007199254740992), (163559571152241/9007199254740992)), (707/2251799813685248), by norm_num⟩
  | 6 => ⟨((32085176758425/562949953421312), (-34547573186007/4503599627370496)), (965/9007199254740992), by norm_num⟩
  | 7 => ⟨((-341798552849169/18014398509481984), (52215943505931/18014398509481984)), (2293/72057594037927936), by norm_num⟩
  | 8 => ⟨((1587732771544909/288230376151711744), (-138771585095165/144115188075855872)), (2419/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_initial10 : AnalyticAt ℂ F_initial10 c := by
  exact A_initial9.add A_term10

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial10 : Sound J_initial10 F_initial10 c := by
  apply sound_round (sound_add A_initial9 A_term10 S_initial9 S_term10)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial10, J_initial9, J_term10, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial11 (s : ℂ) : ℂ := F_initial10 s+F_term11 s

def J_initial11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((118552178956027/1125899906842624), (-195455865109945/562949953421312)), (2395/1125899906842624), by norm_num⟩
  | 1 => ⟨((631384241227599/1125899906842624), (906149526130793/1125899906842624)), (3905/1125899906842624), by norm_num⟩
  | 2 => ⟨((-41877673239599/562949953421312), (-1986823860818215/2251799813685248)), (7101/2251799813685248), by norm_num⟩
  | 3 => ⟨((-193319058522181/2251799813685248), (1493655715188541/2251799813685248)), (4615/2251799813685248), by norm_num⟩
  | 4 => ⟨((331831785461083/4503599627370496), (-1741532051501711/4503599627370496)), (4707/4503599627370496), by norm_num⟩
  | 5 => ⟨((-322052888956807/9007199254740992), (1660556547598977/9007199254740992)), (991/2251799813685248), by norm_num⟩
  | 6 => ⟨((236251911024225/18014398509481984), (-1334737617149055/18014398509481984)), (2845/18014398509481984), by norm_num⟩
  | 7 => ⟨((-71016658992725/18014398509481984), (924201936403391/36028797018963968)), (3557/72057594037927936), by norm_num⟩
  | 8 => ⟨((72279881267349/72057594037927936), (-560816474101991/72057594037927936)), (1973/144115188075855872), by norm_num⟩
  | _ => zero

theorem A_initial11 : AnalyticAt ℂ F_initial11 c := by
  exact A_initial10.add A_term11

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial11 : Sound J_initial11 F_initial11 c := by
  apply sound_round (sound_add A_initial10 A_term11 S_initial10 S_term11)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial11, J_initial10, J_term11, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial12 (s : ℂ) : ℂ := F_initial11 s+F_term12 s

def J_initial12 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-791283987882393/4503599627370496), (-1265772757565663/4503599627370496)), (10353/4503599627370496), by norm_num⟩
  | 1 => ⟨((1417542049902219/1125899906842624), (180275538456527/281474976710656)), (4389/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1060519729758361/1125899906842624), (-381749603713127/562949953421312)), (1039/281474976710656), by norm_num⟩
  | 3 => ⟨((712396574501065/1125899906842624), (278195319761975/562949953421312)), (2813/1125899906842624), by norm_num⟩
  | 4 => ⟨((-419649276707267/1125899906842624), (-317078335487911/1125899906842624)), (1493/1125899906842624), by norm_num⟩
  | 5 => ⟨((209529795049285/1125899906842624), (297548705083239/2251799813685248)), (2615/4503599627370496), by norm_num⟩
  | 6 => ⟨((-709468580108835/9007199254740992), (-472567977926343/9007199254740992)), (975/4503599627370496), by norm_num⟩
  | 7 => ⟨((129138347029869/4503599627370496), (80949393517431/4503599627370496)), (2533/36028797018963968), by norm_num⟩
  | 8 => ⟨((-1315496954750659/144115188075855872), (-777961924437195/144115188075855872)), (729/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_initial12 : AnalyticAt ℂ F_initial12 c := by
  exact A_initial11.add A_term12

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial12 : Sound J_initial12 F_initial12 c := by
  apply sound_round (sound_add A_initial11 A_term12 S_initial11 S_term12)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial12, J_initial11, J_term12, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial13 (s : ℂ) : ℂ := F_initial12 s+F_term13 s

def J_initial13 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1062679673817399/4503599627370496), (-46539500234305/4503599627370496)), (11299/4503599627370496), by norm_num⟩
  | 1 => ⟨((795785548733213/562949953421312), (-30357868085421/562949953421312)), (625/140737488355328), by norm_num⟩
  | 2 => ⟨((-80231723538943/70368744177664), (14947652492097/70368744177664)), (4943/1125899906842624), by norm_num⟩
  | 3 => ⟨((225804603992675/281474976710656), (-300868143140371/1125899906842624)), (3489/1125899906842624), by norm_num⟩
  | 4 => ⟨((-542011366624059/1125899906842624), (116314002727683/562949953421312)), (1929/1125899906842624), by norm_num⟩
  | 5 => ⟨((1089201231324921/4503599627370496), (-266438865314757/2251799813685248)), (3515/4503599627370496), by norm_num⟩
  | 6 => ⟨((-462069747672805/4503599627370496), (122957931569853/2251799813685248)), (681/2251799813685248), by norm_num⟩
  | 7 => ⟨((1347746791154521/36028797018963968), (-191477841770659/9007199254740992)), (3673/36028797018963968), by norm_num⟩
  | 8 => ⟨((-429753701698837/36028797018963968), (8084565543407/1125899906842624)), (1097/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_initial13 : AnalyticAt ℂ F_initial13 c := by
  exact A_initial12.add A_term13

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial13 : Sound J_initial13 F_initial13 c := by
  apply sound_round (sound_add A_initial12 A_term13 S_initial12 S_term13)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial13, J_initial12, J_term13, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial14 (s : ℂ) : ℂ := F_initial13 s+F_term14 s

def J_initial14 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-22986045253459/562949953421312), (775938082099055/4503599627370496)), (11729/4503599627370496), by norm_num⟩
  | 1 => ⟨((252943983580301/281474976710656), (-603357109196115/1125899906842624)), (661/140737488355328), by norm_num⟩
  | 2 => ⟨((-64831404892019/140737488355328), (955193286290969/1125899906842624)), (333/70368744177664), by norm_num⟩
  | 3 => ⟨((230209237632865/1125899906842624), (-465375147148269/562949953421312)), (3833/1125899906842624), by norm_num⟩
  | 4 => ⟨((-195967830752715/2251799813685248), (648201782405993/1125899906842624)), (2159/1125899906842624), by norm_num⟩
  | 5 => ⟨((75875055756209/2251799813685248), (-1410256148275473/4503599627370496)), (2003/2251799813685248), by norm_num⟩
  | 6 => ⟨((-99477079046537/9007199254740992), (1263649040924347/9007199254740992)), (3161/9007199254740992), by norm_num⟩
  | 7 => ⟨((104128851616065/36028797018963968), (-482459290533185/9007199254740992)), (4339/36028797018963968), by norm_num⟩
  | 8 => ⟨((-39012643752677/72057594037927936), (1285328919916859/72057594037927936)), (1319/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_initial14 : AnalyticAt ℂ F_initial14 c := by
  exact A_initial13.add A_term14

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial14 : Sound J_initial14 F_initial14 c := by
  apply sound_round (sound_add A_initial13 A_term14 S_initial13 S_term14)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial14, J_initial13, J_term14, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial15 (s : ℂ) : ℂ := F_initial14 s+F_term15 s

def J_initial15 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((119064010263369/562949953421312), (529453456180745/4503599627370496)), (11981/4503599627370496), by norm_num⟩
  | 1 => ⟨((484837143006703/2251799813685248), (-872967847998889/2251799813685248)), (10923/2251799813685248), by norm_num⟩
  | 2 => ⟨((16346185669157/35184372088832), (182310701231441/281474976710656)), (5567/1125899906842624), by norm_num⟩
  | 3 => ⟨((-355071200663607/562949953421312), (-726788545463143/1125899906842624)), (1013/281474976710656), by norm_num⟩
  | 4 => ⟨((1077291891743603/2251799813685248), (1020234237339269/2251799813685248)), (1155/562949953421312), by norm_num⟩
  | 5 => ⟨((-306867596878045/1125899906842624), (-277775996788793/1125899906842624)), (1085/1125899906842624), by norm_num⟩
  | 6 => ⟨((1145522370869415/9007199254740992), (124201168862127/1125899906842624)), (3467/9007199254740992), by norm_num⟩
  | 7 => ⟨((-227806822884923/4503599627370496), (-755981141956629/18014398509481984)), (2411/18014398509481984), by norm_num⟩
  | 8 => ⟨((632654260344561/36028797018963968), (501211191458701/36028797018963968)), (1485/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_initial15 : AnalyticAt ℂ F_initial15 c := by
  exact A_initial14.add A_term15

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial15 : Sound J_initial15 F_initial15 c := by
  apply sound_round (sound_add A_initial14 A_term15 S_initial14 S_term15)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial15, J_initial14, J_term15, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial16 (s : ℂ) : ℂ := F_initial15 s+F_term16 s

def J_initial16 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((90372071004249/281474976710656), (-482557673448801/4503599627370496)), (12467/4503599627370496), by norm_num⟩
  | 1 => ⟨((-199217407644531/2251799813685248), (529977474397121/2251799813685248)), (11603/2251799813685248), by norm_num⟩
  | 2 => ⟨((997228424546127/1125899906842624), (-121602394886397/562949953421312)), (6043/1125899906842624), by norm_num⟩
  | 3 => ⟨((-1148350495387009/1125899906842624), (42985966470083/281474976710656)), (281/70368744177664), by norm_num⟩
  | 4 => ⟨((105298581345987/140737488355328), (-225673436661873/2251799813685248)), (2621/1125899906842624), by norm_num⟩
  | 5 => ⟨((-950596632979097/2251799813685248), (135325919599927/2251799813685248)), (1259/1125899906842624), by norm_num⟩
  | 6 => ⟨((442043630608549/2251799813685248), (-141702094725001/4503599627370496)), (1029/2251799813685248), by norm_num⟩
  | 7 => ⟨((-1404472529627363/18014398509481984), (255628383790125/18014398509481984)), (1465/9007199254740992), by norm_num⟩
  | 8 => ⟨((974545806449649/36028797018963968), (-199983099140245/36028797018963968)), (231/4503599627370496), by norm_num⟩
  | _ => zero

theorem A_initial16 : AnalyticAt ℂ F_initial16 c := by
  exact A_initial15.add A_term16

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial16 : Sound J_initial16 F_initial16 c := by
  apply sound_round (sound_add A_initial15 A_term16 S_initial15 S_term16)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial16, J_initial15, J_term16, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial17 (s : ℂ) : ℂ := F_initial16 s+F_term17 s

def J_initial17 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((32048570932031/140737488355328), (-745349196675127/2251799813685248)), (6565/2251799813685248), by norm_num⟩
  | 1 => ⟨((198161215594171/1125899906842624), (489529086138185/562949953421312)), (3137/562949953421312), by norm_num⟩
  | 2 => ⟨((575405569971531/1125899906842624), (-39211259868605/35184372088832)), (6715/1125899906842624), by norm_num⟩
  | 3 => ⟨((-749979115250799/1125899906842624), (563630702036989/562949953421312)), (5135/1125899906842624), by norm_num⟩
  | 4 => ⟨((17506902288903/35184372088832), (-789491317586229/1125899906842624)), (3077/1125899906842624), by norm_num⟩
  | 5 => ⟨((-630820027962757/2251799813685248), (902168655570769/2251799813685248)), (1519/1125899906842624), by norm_num⟩
  | 6 => ⟨((72761101633417/562949953421312), (-865911785506723/4503599627370496)), (2553/4503599627370496), by norm_num⟩
  | 7 => ⟨((-57221460488061/1125899906842624), (178513587960737/2251799813685248)), (1869/9007199254740992), by norm_num⟩
  | 8 => ⟨((628235650059131/36028797018963968), (-1030454821133245/36028797018963968)), (1211/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_initial17 : AnalyticAt ℂ F_initial17 c := by
  exact A_initial16.add A_term17

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial17 : Sound J_initial17 F_initial17 c := by
  apply sound_round (sound_add A_initial16 A_term17 S_initial16 S_term17)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial17, J_initial16, J_term17, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial18 (s : ℂ) : ℂ := F_initial17 s+F_term18 s

def J_initial18 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((38006895401009/4503599627370496), (-1879993547191703/4503599627370496)), (13801/4503599627370496), by norm_num⟩
  | 1 => ⟨((227938993937267/281474976710656), (630180050906831/562949953421312)), (6763/1125899906842624), by norm_num⟩
  | 2 => ⟨((-455871500695669/1125899906842624), (-830646946041751/562949953421312)), (7425/1125899906842624), by norm_num⟩
  | 3 => ⟨((243612257956655/1125899906842624), (1518939126587235/1125899906842624)), (5823/1125899906842624), by norm_num⟩
  | 4 => ⟨((-157741237757127/1125899906842624), (-1072514874423581/1125899906842624)), (3577/1125899906842624), by norm_num⟩
  | 5 => ⟨((99625467794573/1125899906842624), (614692986885785/1125899906842624)), (905/562949953421312), by norm_num⟩
  | 6 => ⟨((-108824538483011/2251799813685248), (-73823230244631/281474976710656)), (1559/2251799813685248), by norm_num⟩
  | 7 => ⟨((202668262116051/9007199254740992), (487201219743457/4503599627370496)), (1169/4503599627370496), by norm_num⟩
  | 8 => ⟨((-326222833822985/36028797018963968), (-1406706201007443/36028797018963968)), (3103/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_initial18 : AnalyticAt ℂ F_initial18 c := by
  exact A_initial17.add A_term18

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial18 : Sound J_initial18 F_initial18 c := by
  apply sound_round (sound_add A_initial17 A_term18 S_initial17 S_term18)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial18, J_initial17, J_term18, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial19 (s : ℂ) : ℂ := F_initial18 s+F_term19 s

def J_initial19 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-57558308997001/281474976710656), (-186922167505765/562949953421312)), (7285/2251799813685248), by norm_num⟩
  | 1 => ⟨((404410234041433/281474976710656), (488620181864505/562949953421312)), (3667/562949953421312), by norm_num⟩
  | 2 => ⟨((-186886137103095/140737488355328), (-311119873947395/281474976710656)), (2067/281474976710656), by norm_num⟩
  | 3 => ⟨((78973949411419/70368744177664), (138730534343173/140737488355328)), (13/2199023255552), by norm_num⟩
  | 4 => ⟨((-227137945166837/281474976710656), (-192844041859679/281474976710656)), (4193/1125899906842624), by norm_num⟩
  | 5 => ⟨((541768633497367/1125899906842624), (437356077489381/1125899906842624)), (1087/562949953421312), by norm_num⟩
  | 6 => ⟨((-271389531152731/1125899906842624), (-52066659058311/281474976710656)), (959/1125899906842624), by norm_num⟩
  | 7 => ⟨((466406306809007/4503599627370496), (681552628040011/9007199254740992)), (1473/4503599627370496), by norm_num⟩
  | 8 => ⟨((-350288894578319/9007199254740992), (-243891750268635/9007199254740992)), (1001/9007199254740992), by norm_num⟩
  | _ => zero

theorem A_initial19 : AnalyticAt ℂ F_initial19 c := by
  exact A_initial18.add A_term19

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial19 : Sound J_initial19 F_initial19 c := by
  apply sound_round (sound_add A_initial18 A_term19 S_initial18 S_term19)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial19, J_initial18, J_term19, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_initial20 (s : ℂ) : ℂ := F_initial19 s+F_term20 s

def J_initial20 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1378126548346651/4503599627370496), (-1168177271647/8796093022208)), (15367/4503599627370496), by norm_num⟩
  | 1 => ⟨((490012086288151/281474976710656), (76311189337375/281474976710656)), (31/4398046511104), by norm_num⟩
  | 2 => ⟨((-2007969559727745/1125899906842624), (-118960016465395/562949953421312)), (9171/1125899906842624), by norm_num⟩
  | 3 => ⟨((1775734042313965/1125899906842624), (104716718699635/1125899906842624)), (3781/562949953421312), by norm_num⟩
  | 4 => ⟨((-20189351398941/17592186044416), (-9301451383771/562949953421312)), (4875/1125899906842624), by norm_num⟩
  | 5 => ⟨((1543162534517693/2251799813685248), (-6832677619713/562949953421312)), (2585/1125899906842624), by norm_num⟩
  | 6 => ⟨((-386132385124349/1125899906842624), (33846548230261/2251799813685248)), (4661/4503599627370496), by norm_num⟩
  | 7 => ⟨((165707129674033/1125899906842624), (-89428722942109/9007199254740992)), (457/1125899906842624), by norm_num⟩
  | 8 => ⟨((-1989583937706397/36028797018963968), (179259856648157/36028797018963968)), (5073/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_initial20 : AnalyticAt ℂ F_initial20 c := by
  exact A_initial19.add A_term20

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_initial20 : Sound J_initial20 F_initial20 c := by
  apply sound_round (sound_add A_initial19 A_term20 S_initial19 S_term20)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_initial20, J_initial19, J_term20, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_q12 (s : ℂ) : ℂ := value (-1, 0)

def J_q12 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨(-1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_q12 : AnalyticAt ℂ F_q12 c := by
  exact analyticAt_const

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (c := c) (contains_exact (-1, 0))
  convert h using 1
  funext k
  fin_cases k <;> rfl

def F_sminusone (s : ℂ) : ℂ := F_variable s+F_q12 s

def J_sminusone : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_sminusone : AnalyticAt ℂ F_sminusone c := by
  exact A_variable.add A_q12

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_sminusone : Sound J_sminusone F_sminusone c := by
  apply sound_round (sound_add A_variable A_q12 S_variable S_q12)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_sminusone, J_variable, J_q12, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem V_sminusoneInv : F_sminusone c = value ((-1/2), 14) := by
  have h := centre_contains S_sminusone
  have he : J_sminusone ⟨0,by omega⟩ = exact ((-1/2), 14) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_sminusone, exact]
  rw [he] at h
  exact value_eq_of_exact h

theorem N_sminusoneInv : F_sminusone c ≠ 0 := by
  rw [V_sminusoneInv]
  intro h
  have hi := congrArg Complex.im h
  norm_num [value] at hi

def F_sminusoneInv (s : ℂ) : ℂ := (F_sminusone s)⁻¹

def J_sminusoneInv : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-2/785), (-56/785)), 0, by norm_num⟩
  | 1 => ⟨((1464947929907357/288230376151711744), (-13096597074523/36028797018963968)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((179305403295817/4611686018427387904), (833911220602493/2305843009213693952)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-948172697079109/36893488147419103232), (136323541064721/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-194251489300027/590295810358705651712), (-1076688386329695/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 5 => ⟨((1221014963686377/9444732965739290427392), (-265609379331687/9444732965739290427392)), (1/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((88235185579349/37778931862957161709568), (1382840646273095/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-1563988681919155/2417851639229258349412352), (114804396750677/604462909807314587353088)), (1/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-293953245717095/19342813113834066795298816), (-883209488035335/19342813113834066795298816)), (3/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem A_sminusoneInv : AnalyticAt ℂ F_sminusoneInv c := by
  exact A_sminusone.inv N_sminusoneInv

set_option maxHeartbeats 5000000 in
-- One exact inverse and eight outward-rounded reciprocal recurrence checks.
theorem S_sminusoneInv : Sound J_sminusoneInv F_sminusoneInv c := by
  apply inv_coefficients_sound A_sminusone N_sminusoneInv S_sminusone
  · rw [V_sminusoneInv]
    have hv : (value ((-1/2), 14))⁻¹ = value ((-2/785), (-56/785)) := by
      apply Complex.ext <;> norm_num [value, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
    rw [hv]
    simpa [J_sminusoneInv] using contains_exact ((-2/785), (-56/785))
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_sminusoneInv, J_sminusone, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_emIntegralProduct (s : ℂ) : ℂ := F_term21 s*F_sminusoneInv s

def J_emIntegralProduct : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1088238852370417/72057594037927936), (-137495619600797/36028797018963968)), (571/72057594037927936), by norm_num⟩
  | 1 => ⟨((-411347226395001/9007199254740992), (457074354539323/36028797018963968)), (895/36028797018963968), by norm_num⟩
  | 2 => ⟨((1242477312752605/18014398509481984), (-376722512631683/18014398509481984)), (703/18014398509481984), by norm_num⟩
  | 3 => ⟨((-624774526497789/9007199254740992), (102754945020003/4503599627370496)), (737/18014398509481984), by norm_num⟩
  | 4 => ⟨((941429689842037/18014398509481984), (-334199833382369/18014398509481984)), (145/4503599627370496), by norm_num⟩
  | 5 => ⟨((-566793478982343/18014398509481984), (432327274013661/36028797018963968)), (731/36028797018963968), by norm_num⟩
  | 6 => ⟨((568104824311947/36028797018963968), (-463691293674339/72057594037927936)), (767/72057594037927936), by norm_num⟩
  | 7 => ⟨((-487540154682753/72057594037927936), (424323428747987/144115188075855872)), (345/72057594037927936), by norm_num⟩
  | 8 => ⟨((731415431703083/288230376151711744), (-169167729064023/144115188075855872)), (17/9007199254740992), by norm_num⟩
  | _ => zero

theorem A_emIntegralProduct : AnalyticAt ℂ F_emIntegralProduct c := by
  exact A_term21.mul A_sminusoneInv

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emIntegralProduct : Sound J_emIntegralProduct F_emIntegralProduct c := by
  apply sound_round (sound_mul A_term21 A_sminusoneInv S_term21 S_sminusoneInv)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_sminusone, J_sminusoneInv, J_emIntegralProduct,
    J_term21, J_sminusoneInv, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emIntegral (s : ℂ) : ℂ := value (21, 0)*F_emIntegralProduct s

def J_emIntegral : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((357078373434043/1125899906842624), (-90231500363023/1125899906842624)), (375/2251799813685248), by norm_num⟩
  | 1 => ⟨((-539893234643439/562949953421312), (299955045166431/1125899906842624)), (147/281474976710656), by norm_num⟩
  | 2 => ⟨((815375736493897/562949953421312), (-123612074457271/281474976710656)), (923/1125899906842624), by norm_num⟩
  | 3 => ⟨((-205004141507087/140737488355328), (67432932669377/140737488355328)), (121/140737488355328), by norm_num⟩
  | 4 => ⟨((617813233958837/562949953421312), (-438637281314359/1125899906842624)), (381/562949953421312), by norm_num⟩
  | 5 => ⟨((-743916441164325/1125899906842624), (283714773571465/1125899906842624)), (15/35184372088832), by norm_num⟩
  | 6 => ⟨((1491275163818861/4503599627370496), (-304297411473785/2251799813685248)), (1007/4503599627370496), by norm_num⟩
  | 7 => ⟨((-1279792906042227/9007199254740992), (556924500231733/9007199254740992)), (907/9007199254740992), by norm_num⟩
  | 8 => ⟨((119997844263787/2251799813685248), (-111016322198265/4503599627370496)), (715/18014398509481984), by norm_num⟩
  | _ => zero

theorem A_emIntegral : AnalyticAt ℂ F_emIntegral c := by
  exact analyticAt_const.mul A_emIntegralProduct

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emIntegral : Sound J_emIntegral F_emIntegral c := by
  apply sound_round (sound_scale A_emIntegralProduct S_emIntegralProduct)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_sminusoneInv, J_emIntegralProduct, J_emIntegral,
    J_emIntegralProduct, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emHalf (s : ℂ) : ℂ := value ((1/2), 0)*F_term21 s

def J_emHalf : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((206609870164819/9007199254740992), (960802472049165/9007199254740992)), (241/4503599627370496), by norm_num⟩
  | 1 => ⟨((-314514192785957/4503599627370496), (-1462592342186907/4503599627370496)), (739/4503599627370496), by norm_num⟩
  | 2 => ⟨((239386379229829/2251799813685248), (1113223800757623/2251799813685248)), (283/1125899906842624), by norm_num⟩
  | 3 => ⟨((-242939067616861/2251799813685248), (-1129744946538111/2251799813685248)), (579/2251799813685248), by norm_num⟩
  | 4 => ⟨((369816721179571/4503599627370496), (429941729829991/1125899906842624)), (111/562949953421312), by norm_num⟩
  | 5 => ⟨((-112591530547651/2251799813685248), (-1047173794704823/4503599627370496)), (545/4503599627370496), by norm_num⟩
  | 6 => ⟨((57131240174991/2251799813685248), (531357352362469/4503599627370496)), (557/9007199254740992), by norm_num⟩
  | 7 => ⟨((-397571068817659/36028797018963968), (-1848833579104969/36028797018963968)), (975/36028797018963968), by norm_num⟩
  | 8 => ⟨((302603509901261/72057594037927936), (1407203828800395/72057594037927936)), (747/72057594037927936), by norm_num⟩
  | _ => zero

theorem A_emHalf : AnalyticAt ℂ F_emHalf c := by
  exact analyticAt_const.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emHalf : Sound J_emHalf F_emHalf c := by
  apply sound_round (sound_scale A_term21 S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emIntegralProduct, J_emIntegral, J_emHalf,
    J_term21, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emInitialIntegral (s : ℂ) : ℂ := F_initial20 s+F_emIntegral s

def J_emInitialIntegral : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((50186945389521/4503599627370496), (-239758191133839/1125899906842624)), (16117/4503599627370496), by norm_num⟩
  | 1 => ⟨((440130937932863/562949953421312), (605199802515931/1125899906842624)), (2131/281474976710656), by norm_num⟩
  | 2 => ⟨((-377218086739951/1125899906842624), (-366184165379937/562949953421312)), (5047/562949953421312), by norm_num⟩
  | 3 => ⟨((135700910257269/1125899906842624), (644180180054651/1125899906842624)), (4265/562949953421312), by norm_num⟩
  | 4 => ⟨((-28246010807275/562949953421312), (-457240184081901/1125899906842624)), (5637/1125899906842624), by norm_num⟩
  | 5 => ⟨((55329652189043/2251799813685248), (270049418332039/1125899906842624)), (3065/1125899906842624), by norm_num⟩
  | 6 => ⟨((-53254376678535/4503599627370496), (-67612715810881/562949953421312)), (1417/1125899906842624), by norm_num⟩
  | 7 => ⟨((45864131350037/9007199254740992), (58436972161203/1125899906842624)), (4563/9007199254740992), by norm_num⟩
  | 8 => ⟨((-69618429485805/36028797018963968), (-708870720937963/36028797018963968)), (6503/36028797018963968), by norm_num⟩
  | _ => zero

theorem A_emInitialIntegral : AnalyticAt ℂ F_emInitialIntegral c := by
  exact A_initial20.add A_emIntegral

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emInitialIntegral : Sound J_emInitialIntegral F_emInitialIntegral c := by
  apply sound_round (sound_add A_initial20 A_emIntegral S_initial20 S_emIntegral)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emInitialIntegral, J_initial20, J_emIntegral, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_emInitialHalf (s : ℂ) : ℂ := F_emInitialIntegral s+F_emHalf s

def J_emInitialHalf : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((306983760943861/9007199254740992), (-957263057021547/9007199254740992)), (8179/2251799813685248), by norm_num⟩
  | 1 => ⟨((801633327669237/1125899906842624), (59887929242301/281474976710656)), (17419/2251799813685248), by norm_num⟩
  | 2 => ⟨((-515049794250073/2251799813685248), (-351512860762125/2251799813685248)), (10377/1125899906842624), by norm_num⟩
  | 3 => ⟨((28462752897677/2251799813685248), (158615413571191/2251799813685248)), (17639/2251799813685248), by norm_num⟩
  | 4 => ⟨((143848634721371/4503599627370496), (-13649227125955/562949953421312)), (5859/1125899906842624), by norm_num⟩
  | 5 => ⟨((-3578867397413/140737488355328), (33023878623333/4503599627370496)), (12805/4503599627370496), by norm_num⟩
  | 6 => ⟨((61008103671447/4503599627370496), (-9544374124579/4503599627370496)), (11893/9007199254740992), by norm_num⟩
  | 7 => ⟨((-214114543417511/36028797018963968), (21149530053527/36028797018963968)), (19227/36028797018963968), by norm_num⟩
  | 8 => ⟨((163366650929651/72057594037927936), (-10537613075531/72057594037927936)), (13753/72057594037927936), by norm_num⟩
  | _ => zero

theorem A_emInitialHalf : AnalyticAt ℂ F_emInitialHalf c := by
  exact A_emInitialIntegral.add A_emHalf

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emInitialHalf : Sound J_emInitialHalf F_emInitialHalf c := by
  apply sound_round (sound_add A_emInitialIntegral A_emHalf S_emInitialIntegral S_emHalf)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emInitialHalf, J_emInitialIntegral, J_emHalf, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_factor1 (s : ℂ) : ℂ := F_variable s+F_q1 s

def J_factor1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((3/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor1 : AnalyticAt ℂ F_factor1 c := by
  exact A_variable.add A_q1

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor1 : Sound J_factor1 F_factor1 c := by
  apply sound_round (sound_add A_variable A_q1 S_variable S_q1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor1, J_variable, J_q1, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising2 (s : ℂ) : ℂ := F_variable s*F_factor1 s

def J_rising2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-781/4), 28), 0, by norm_num⟩
  | 1 => ⟨(2, 28), 0, by norm_num⟩
  | 2 => ⟨(1, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising2 : AnalyticAt ℂ F_rising2 c := by
  exact A_variable.mul A_factor1

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising2 : Sound J_rising2 F_rising2 c := by
  apply sound_round (sound_mul A_variable A_factor1 S_variable S_factor1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emInitialHalf, J_factor1, J_rising2,
    J_variable, J_factor1, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor2 (s : ℂ) : ℂ := F_variable s+F_q2 s

def J_factor2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((5/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor2 : AnalyticAt ℂ F_factor2 c := by
  exact A_variable.add A_q2

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor2 : Sound J_factor2 F_factor2 c := by
  apply sound_round (sound_add A_variable A_q2 S_variable S_q2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor2, J_variable, J_q2, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising3 (s : ℂ) : ℂ := F_rising2 s*F_factor2 s

def J_rising3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-7041/8), (-5327/2)), 0, by norm_num⟩
  | 1 => ⟨((-2329/4), 126), 0, by norm_num⟩
  | 2 => ⟨((9/2), 42), 0, by norm_num⟩
  | 3 => ⟨(1, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising3 : AnalyticAt ℂ F_rising3 c := by
  exact A_rising2.mul A_factor2

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising3 : Sound J_rising3 F_rising3 c := by
  apply sound_round (sound_mul A_rising2 A_factor2 S_rising2 S_factor2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising2, J_factor2, J_rising3,
    J_rising2, J_factor2, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor3 (s : ℂ) : ℂ := F_variable s+F_q3 s

def J_factor3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((7/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor3 : AnalyticAt ℂ F_factor3 c := by
  exact A_variable.add A_q3

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor3 : Sound J_factor3 F_factor3 c := by
  apply sound_round (sound_add A_variable A_q3 S_variable S_q3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor3, J_variable, J_q3, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising4 (s : ℂ) : ℂ := F_rising3 s*F_factor3 s

def J_rising4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((547337/16), -21644), 0, by norm_num⟩
  | 1 => ⟨(-4682, -10374), 0, by norm_num⟩
  | 2 => ⟨((-2309/2), 336), 0, by norm_num⟩
  | 3 => ⟨(8, 56), 0, by norm_num⟩
  | 4 => ⟨(1, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising4 : AnalyticAt ℂ F_rising4 c := by
  exact A_rising3.mul A_factor3

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising4 : Sound J_rising4 F_rising4 c := by
  apply sound_round (sound_mul A_rising3 A_factor3 S_rising3 S_factor3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising3, J_factor3, J_rising4,
    J_rising3, J_factor3, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor4 (s : ℂ) : ℂ := F_variable s+F_q4 s

def J_factor4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((9/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor4 : AnalyticAt ℂ F_factor4 c := by
  exact A_variable.add A_q4

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor4 : Sound J_factor4 F_factor4 c := by
  apply sound_round (sound_add A_variable A_q4 S_variable S_q4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor4, J_variable, J_q4, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising5 (s : ℂ) : ℂ := F_rising4 s*F_factor4 s

def J_rising5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((14622545/32), (3052175/8)), 0, by norm_num⟩
  | 1 => ⟨((2534009/16), -133875), 0, by norm_num⟩
  | 2 => ⟨((-58325/4), -25025), 0, by norm_num⟩
  | 3 => ⟨((-3805/2), 700), 0, by norm_num⟩
  | 4 => ⟨((25/2), 70), 0, by norm_num⟩
  | 5 => ⟨(1, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising5 : AnalyticAt ℂ F_rising5 c := by
  exact A_rising4.mul A_factor4

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising5 : Sound J_rising5 F_rising5 c := by
  apply sound_round (sound_mul A_rising4 A_factor4 S_rising4 S_factor4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising4, J_factor4, J_rising5,
    J_rising4, J_factor4, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor5 (s : ℂ) : ℂ := F_variable s+F_q5 s

def J_factor5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((11/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor5 : AnalyticAt ℂ F_factor5 c := by
  exact A_variable.add A_q5

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor5 : Sound J_factor5 F_factor5 c := by
  apply sound_round (sound_add A_variable A_q5 S_variable S_q5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor5, J_variable, J_q5, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising6 (s : ℂ) : ℂ := F_rising5 s*F_factor5 s

def J_rising6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-180995605/64), (33982935/4)), 0, by norm_num⟩
  | 1 => ⟨((25618161/8), (7449869/4)), 0, by norm_num⟩
  | 2 => ⟨((6856459/16), -475650), 0, by norm_num⟩
  | 3 => ⟨(-34845, -47810), 0, by norm_num⟩
  | 4 => ⟨((-11255/4), 1260), 0, by norm_num⟩
  | 5 => ⟨(18, 84), 0, by norm_num⟩
  | 6 => ⟨(1, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising6 : AnalyticAt ℂ F_rising6 c := by
  exact A_rising5.mul A_factor5

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising6 : Sound J_rising6 F_rising6 c := by
  apply sound_round (sound_mul A_rising5 A_factor5 S_rising5 S_factor5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising5, J_factor5, J_rising6,
    J_rising5, J_factor5, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor6 (s : ℂ) : ℂ := F_variable s+F_q6 s

def J_factor6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((13/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor6 : AnalyticAt ℂ F_factor6 c := by
  exact A_variable.add A_q6

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor6 : Sound J_factor6 F_factor6 c := by
  apply sound_round (sound_add A_variable A_q6 S_variable S_q6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor6, J_variable, J_q6, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising7 (s : ℂ) : ℂ := F_rising6 s*F_factor6 s

def J_rising7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-17577297745/128), (500143385/32)), 0, by norm_num⟩
  | 1 => ⟨((-517621889/64), (523468421/8)), 0, by norm_num⟩
  | 2 => ⟨((404697811/32), (38161151/8)), 0, by norm_num⟩
  | 3 => ⟨((13942019/16), -1274245), 0, by norm_num⟩
  | 4 => ⟨((-566195/8), (-158025/2)), 0, by norm_num⟩
  | 5 => ⟨((-15491/4), 2058), 0, by norm_num⟩
  | 6 => ⟨((49/2), 98), 0, by norm_num⟩
  | 7 => ⟨(1, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising7 : AnalyticAt ℂ F_rising7 c := by
  exact A_rising6.mul A_factor6

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising7 : Sound J_rising7 F_rising7 c := by
  apply sound_round (sound_mul A_rising6 A_factor6 S_rising6 S_factor6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising6, J_factor6, J_rising7,
    J_rising6, J_factor6, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor7 (s : ℂ) : ℂ := F_variable s+F_q7 s

def J_factor7 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((15/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor7 : AnalyticAt ℂ F_factor7 c := by
  exact A_variable.add A_q7

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor7 : Sound J_factor7 F_factor7 c := by
  apply sound_round (sound_add A_variable A_q7 S_variable S_q7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor7, J_variable, J_q7, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising8 (s : ℂ) : ℂ := F_rising7 s*F_factor7 s

def J_rising8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-319675525295/256), -1805295835), 0, by norm_num⟩
  | 1 => ⟨((-2228102381/2), (1572605349/4)), 0, by norm_num⟩
  | 2 => ⟨((319699091/16), 278264924), 0, by norm_num⟩
  | 3 => ⟨(37021558, 7412573), 0, by norm_num⟩
  | 4 => ⟨((11573947/8), -2857680), 0, by norm_num⟩
  | 5 => ⟨(-128632, -117796), 0, by norm_num⟩
  | 6 => ⟨(-5061, 3136), 0, by norm_num⟩
  | 7 => ⟨(32, 112), 0, by norm_num⟩
  | 8 => ⟨(1, 0), 0, by norm_num⟩
  | _ => zero

theorem A_rising8 : AnalyticAt ℂ F_rising8 c := by
  exact A_rising7.mul A_factor7

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising8 : Sound J_rising8 F_rising8 c := by
  apply sound_round (sound_mul A_rising7 A_factor7 S_rising7 S_factor7)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising7, J_factor7, J_rising8,
    J_rising7, J_factor7, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor8 (s : ℂ) : ℂ := F_variable s+F_q8 s

def J_factor8 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((17/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor8 : AnalyticAt ℂ F_factor8 c := by
  exact A_variable.add A_q8

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor8 : Sound J_factor8 F_factor8 c := by
  apply sound_round (sound_add A_variable A_q8 S_variable S_q8)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor8, J_variable, J_q8, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising9 (s : ℂ) : ℂ := F_rising8 s*F_factor8 s

def J_rising9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((7505876615265/512), (-4201890545545/128)), 0, by norm_num⟩
  | 1 => ⟨((-4152905308527/256), (-112481809083/8)), 0, by norm_num⟩
  | 2 => ⟨((-154877439501/32), (24305119167/8)), 0, by norm_num⟩
  | 3 => ⟨((3694214627/16), (1719147213/2)), 0, by norm_num⟩
  | 4 => ⟨((1429222347/16), (13506801/4)), 0, by norm_num⟩
  | 5 => ⟨((16020123/8), -5659794), 0, by norm_num⟩
  | 6 => ⟨((-431109/2), -161994), 0, by norm_num⟩
  | 7 => ⟨(-6357, 4536), 0, by norm_num⟩
  | 8 => ⟨((81/2), 126), 0, by norm_num⟩
  | _ => zero

theorem A_rising9 : AnalyticAt ℂ F_rising9 c := by
  exact A_rising8.mul A_factor8

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising9 : Sound J_rising9 F_rising9 c := by
  apply sound_round (sound_mul A_rising8 A_factor8 S_rising8 S_factor8)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising8, J_factor8, J_rising9,
    J_rising8, J_factor8, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor9 (s : ℂ) : ℂ := F_variable s+F_q9 s

def J_factor9 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((19/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor9 : AnalyticAt ℂ F_factor9 c := by
  exact A_variable.add A_q9

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor9 : Sound J_factor9 F_factor9 c := by
  apply sound_round (sound_add A_variable A_q9 S_variable S_q9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor9, J_variable, J_q9, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising10 (s : ℂ) : ℂ := F_rising9 s*F_factor9 s

def J_rising10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((613223396791075/1024), (-6823696014625/64)), 0, by norm_num⟩
  | 1 => ⟨((7346094172905/128), (-25184731342925/64)), 0, by norm_num⟩
  | 2 => ⟨((-26812284097419/256), (-211827107625/4)), 0, by norm_num⟩
  | 3 => ⟨((-117444084325/8), (57746107825/4)), 0, by norm_num⟩
  | 4 => ⟨((33030892135/32), (4284443625/2)), 0, by norm_num⟩
  | 5 => ⟨((750349635/4), (-44712255/2)), 0, by norm_num⟩
  | 6 => ⟨((17781309/8), -10216500), 0, by norm_num⟩
  | 7 => ⟨(-339450, -207900), 0, by norm_num⟩
  | 8 => ⟨((-30945/4), 6300), 0, by norm_num⟩
  | _ => zero

theorem A_rising10 : AnalyticAt ℂ F_rising10 c := by
  exact A_rising9.mul A_factor9

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising10 : Sound J_rising10 F_rising10 c := by
  apply sound_round (sound_mul A_rising9 A_factor9 S_rising9 S_factor9)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising9, J_factor9, J_rising10,
    J_rising9, J_factor9, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_factor10 (s : ℂ) : ℂ := F_variable s+F_q10 s

def J_factor10 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((21/2), 14), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_factor10 : AnalyticAt ℂ F_factor10 c := by
  exact A_variable.add A_q10

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_factor10 : Sound J_factor10 F_factor10 c := by
  apply sound_round (sound_add A_variable A_q10 S_variable S_q10)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor10, J_variable, J_q10, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_rising11 (s : ℂ) : ℂ := F_rising10 s*F_factor10 s

def J_rising11 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((497959598348893/64), (116230416009657/16)), (1/128), by norm_num⟩
  | 1 => ⟨((858959391016287/128), (-439681431810005/128)), (1/128), by norm_num⟩
  | 2 => ⟨((-154079412490179/512), (-309229359529783/128)), 0, by norm_num⟩
  | 3 => ⟨((-118014009041819/256), (-855203131475/8)), 0, by norm_num⟩
  | 4 => ⟨((-2165334683765/64), (822093940745/16)), 0, by norm_num⟩
  | 5 => ⟨((106075806595/32), (18134824785/4)), 0, by norm_num⟩
  | 6 => ⟨((5663302029/16), (-394048347/4)), 0, by norm_num⟩
  | 7 => ⟨((12552309/8), -17151750), 0, by norm_num⟩
  | 8 => ⟨((-4071045/8), (-500115/2)), 0, by norm_num⟩
  | _ => zero

theorem A_rising11 : AnalyticAt ℂ F_rising11 c := by
  exact A_rising10.mul A_factor10

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_rising11 : Sound J_rising11 F_rising11 c := by
  apply sound_round (sound_mul A_rising10 A_factor10 S_rising10 S_factor10)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising10, J_factor10, J_rising11,
    J_rising10, J_factor10, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorrProduct1 (s : ℂ) : ℂ := F_variable s*F_term21 s

def J_emCorrProduct1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-834245604600369/281474976710656), (210808713645753/281474976710656)), (875/562949953421312), by norm_num⟩
  | 1 => ⟨((1276396289331633/140737488355328), (-290880852129517/140737488355328)), (343/70368744177664), by norm_num⟩
  | 2 => ⟨((-976418569836549/70368744177664), (198545314906435/70368744177664)), (537/70368744177664), by norm_num⟩
  | 3 => ⟨((995896631059685/70368744177664), (-89149863098359/35184372088832)), (561/70368744177664), by norm_num⟩
  | 4 => ⟨((-1523606665320215/140737488355328), (118057114471805/70368744177664)), (439/70368744177664), by norm_num⟩
  | 5 => ⟨((932353644781215/140737488355328), (-122273927085417/140737488355328)), (275/70368744177664), by norm_num⟩
  | 6 => ⟨((-1901763688498719/562949953421312), (25568112699255/70368744177664)), (1147/562949953421312), by norm_num⟩
  | 7 => ⟨((1662436525991287/1125899906842624), (-139972058381247/1125899906842624)), (1/1099511627776), by norm_num⟩
  | 8 => ⟨((-1271543374118139/2251799813685248), (77648993425495/2251799813685248)), (25/70368744177664), by norm_num⟩
  | _ => zero

theorem A_emCorrProduct1 : AnalyticAt ℂ F_emCorrProduct1 c := by
  exact A_variable.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorrProduct1 : Sound J_emCorrProduct1 F_emCorrProduct1 c := by
  apply sound_round (sound_mul A_variable A_term21 S_variable S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_factor10, J_rising11, J_emCorrProduct1,
    J_variable, J_term21, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorr1 (s : ℂ) : ℂ := value ((1/252), 0)*F_emCorrProduct1 s

def J_emCorr1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1694975196648369/144115188075855872), (107077441851811/36028797018963968)), (445/72057594037927936), by norm_num⟩
  | 1 => ⟨((1296656547892453/36028797018963968), (-295498008512525/36028797018963968)), (349/18014398509481984), by norm_num⟩
  | 2 => ⟨((-15498707457723/281474976710656), (100848413920729/9007199254740992)), (273/9007199254740992), by norm_num⟩
  | 3 => ⟨((505852257046189/9007199254740992), (-181129880580793/18014398509481984)), (571/18014398509481984), by norm_num⟩
  | 4 => ⟨((-386947724525769/9007199254740992), (239862073847477/36028797018963968)), (893/36028797018963968), by norm_num⟩
  | 5 => ⟨((1894305817968183/72057594037927936), (-31053695767725/9007199254740992)), (559/36028797018963968), by norm_num⟩
  | 6 => ⟨((-241493801714123/18014398509481984), (207791646063787/144115188075855872)), (583/72057594037927936), by norm_num⟩
  | 7 => ⟨((422206101839057/72057594037927936), (-142193837085711/288230376151711744)), (1041/288230376151711744), by norm_num⟩
  | 8 => ⟨((-161465825284843/72057594037927936), (39440758565331/288230376151711744)), (407/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_emCorr1 : AnalyticAt ℂ F_emCorr1 c := by
  exact analyticAt_const.mul A_emCorrProduct1

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorr1 : Sound J_emCorr1 F_emCorr1 c := by
  apply sound_round (sound_scale A_emCorrProduct1 S_emCorrProduct1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_rising11, J_emCorrProduct1, J_emCorr1,
    J_emCorrProduct1, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emAfterCorr1 (s : ℂ) : ℂ := F_emInitialHalf s+F_emCorr1 s

def J_emAfterCorr1 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((100523905576669/4503599627370496), (-465246848279297/4503599627370496)), (8193/2251799813685248), by norm_num⟩
  | 1 => ⟨((210538461197719/281474976710656), (460634808406375/2251799813685248)), (2183/281474976710656), by norm_num⟩
  | 2 => ⟨((-639039453911857/2251799813685248), (-326300757281943/2251799813685248)), (41645/4503599627370496), by norm_num⟩
  | 3 => ⟨((619703268636897/9007199254740992), (4249193078081/70368744177664)), (35421/4503599627370496), by norm_num⟩
  | 4 => ⟨((-99250455083027/9007199254740992), (-633688462213643/36028797018963968)), (188381/36028797018963968), by norm_num⟩
  | 5 => ⟨((61925710492727/72057594037927936), (34994061478941/9007199254740992)), (102999/36028797018963968), by norm_num⟩
  | 6 => ⟨((2538612971665/18014398509481984), (-97628325922741/144115188075855872)), (95727/72057594037927936), by norm_num⟩
  | 7 => ⟨((-6022984995965/72057594037927936), (27002403342505/288230376151711744)), (154857/288230376151711744), by norm_num⟩
  | 8 => ⟨((237603205601/9007199254740992), (-2709693736793/288230376151711744)), (55419/288230376151711744), by norm_num⟩
  | _ => zero

theorem A_emAfterCorr1 : AnalyticAt ℂ F_emAfterCorr1 c := by
  exact A_emInitialHalf.add A_emCorr1

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emAfterCorr1 : Sound J_emAfterCorr1 F_emAfterCorr1 c := by
  apply sound_round (sound_add A_emInitialHalf A_emCorr1 S_emInitialHalf S_emCorr1)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr1, J_emInitialHalf, J_emCorr1, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_emCorrProduct2 (s : ℂ) : ℂ := F_rising3 s*F_term21 s

def J_emCorrProduct2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((1160768980627021/2199023255552), (-340803629125065/1099511627776)), (835/2199023255552), by norm_num⟩
  | 1 => ⟨((-114119957082517/68719476736), (453680527294365/549755813888)), (341/274877906944), by norm_num⟩
  | 2 => ⟨((714900373139229/274877906944), (-589916313881357/549755813888)), (1111/549755813888), by norm_num⟩
  | 3 => ⟨((-743371435961987/274877906944), (494979332646867/549755813888)), (1207/549755813888), by norm_num⟩
  | 4 => ⟨((1155039473292147/549755813888), (-148386776587421/274877906944)), (491/274877906944), by norm_num⟩
  | 5 => ⟨((-357639609574195/274877906944), (262858104877613/1099511627776)), (639/549755813888), by norm_num⟩
  | 6 => ⟨((367849088001365/549755813888), (-165667349958901/2199023255552)), (1383/2199023255552), by norm_num⟩
  | 7 => ⟨((-1292870240982349/4398046511104), (13833471601023/1099511627776)), (1281/4398046511104), by norm_num⟩
  | 8 => ⟨((1981537052856795/17592186044416), (26017190070981/8796093022208)), (2073/17592186044416), by norm_num⟩
  | _ => zero

theorem A_emCorrProduct2 : AnalyticAt ℂ F_emCorrProduct2 c := by
  exact A_rising3.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorrProduct2 : Sound J_emCorrProduct2 F_emCorrProduct2 c := by
  apply sound_round (sound_mul A_rising3 A_term21 S_rising3 S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emCorr1, J_emAfterCorr1, J_emCorrProduct2,
    J_rising3, J_term21, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorr2 (s : ℂ) : ℂ := value ((-1/6667920), 0)*F_emCorrProduct2 s

def J_emCorr2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-730155427557595/9223372036854775808), (428749602530857/9223372036854775808)), (263/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1148553173933771/4611686018427387904), (-570754913182181/4611686018427387904)), (859/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-899383764250129/2305843009213693952), (185536745715143/1152921504606846976)), (175/576460752303423488), by norm_num⟩
  | 3 => ⟨((467600959120851/1152921504606846976), (-9729860449539/72057594037927936)), (95/288230376151711744), by norm_num⟩
  | 4 => ⟨((-1453102821565689/4611686018427387904), (46669669896139/576460752303423488)), (309/1152921504606846976), by norm_num⟩
  | 5 => ⟨((56241273327945/288230376151711744), (-41336233815065/1152921504606846976)), (1609/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-1851097075190437/18446744073709551616), (208418585886459/18446744073709551616)), (1741/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1626501464694607/36893488147419103232), (-17403263767429/9223372036854775808)), (1613/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-623220493568119/36893488147419103232), (-16365523939021/36893488147419103232)), (1305/73786976294838206464), by norm_num⟩
  | _ => zero

theorem A_emCorr2 : AnalyticAt ℂ F_emCorr2 c := by
  exact analyticAt_const.mul A_emCorrProduct2

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorr2 : Sound J_emCorr2 F_emCorr2 c := by
  apply sound_round (sound_scale A_emCorrProduct2 S_emCorrProduct2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr1, J_emCorrProduct2, J_emCorr2,
    J_emCorrProduct2, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emAfterCorr2 (s : ℂ) : ℂ := F_emAfterCorr1 s+F_emCorr2 s

def J_emAfterCorr2 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((100167384371807/4503599627370496), (-116259374471859/1125899906842624)), (16387/4503599627370496), by norm_num⟩
  | 1 => ⟨((421217126640303/562949953421312), (460356119483923/2251799813685248)), (17465/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1279835516738265/4503599627370496), (-81484595206367/562949953421312)), (41647/4503599627370496), by norm_num⟩
  | 3 => ⟨((623356401130029/9007199254740992), (16958765044943/281474976710656)), (35423/4503599627370496), by norm_num⟩
  | 4 => ⟨((-204177093062795/18014398509481984), (-1261543215690269/72057594037927936)), (188391/36028797018963968), by norm_num⟩
  | 5 => ⟨((303944115298853/288230376151711744), (554737954436173/144115188075855872)), (824043/288230376151711744), by norm_num⟩
  | 6 => ⟨((93555325974315/2305843009213693952), (-1536000891528049/2305843009213693952)), (3063483/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-91079178327467/2305843009213693952), (846673643192731/9223372036854775808)), (1238957/2305843009213693952), by norm_num⟩
  | 8 => ⟨((350002236573577/36893488147419103232), (-363206322248525/36893488147419103232)), (14188569/73786976294838206464), by norm_num⟩
  | _ => zero

theorem A_emAfterCorr2 : AnalyticAt ℂ F_emAfterCorr2 c := by
  exact A_emAfterCorr1.add A_emCorr2

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emAfterCorr2 : Sound J_emAfterCorr2 F_emAfterCorr2 c := by
  apply sound_round (sound_add A_emAfterCorr1 A_emCorr2 S_emAfterCorr1 S_emCorr2)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr2, J_emAfterCorr1, J_emCorr2, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_emCorrProduct3 (s : ℂ) : ℂ := F_rising5 s*F_term21 s

def J_emCorrProduct3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-259548038738293/4294967296), (246939291142395/2147483648)), (193/2147483648), by norm_num⟩
  | 1 => ⟨((236018648095753/1073741824), (-692442297823655/2147483648)), (659/2147483648), by norm_num⟩
  | 2 => ⟨((-825654285681041/2147483648), (954555746787541/2147483648)), (561/1073741824), by norm_num⟩
  | 3 => ⟨((467950821308775/1073741824), (-859243966613447/2147483648)), (1271/2147483648), by norm_num⟩
  | 4 => ⟨((-389220294235455/1073741824), (141209933497957/536870912)), (1079/2147483648), by norm_num⟩
  | 5 => ⟨((63609500869951/268435456), (-35810284710589/268435456)), (1461/4294967296), by norm_num⟩
  | 6 => ⟨((-546197812981081/4294967296), (459239430372759/8589934592)), (823/4294967296), by norm_num⟩
  | 7 => ⟨((991952910689097/17179869184), (-288970505788621/17179869184)), (1585/17179869184), by norm_num⟩
  | 8 => ⟨((-389451148951159/17179869184), (266393872947691/68719476736)), (2665/68719476736), by norm_num⟩
  | _ => zero

theorem A_emCorrProduct3 : AnalyticAt ℂ F_emCorrProduct3 c := by
  exact A_rising5.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorrProduct3 : Sound J_emCorrProduct3 F_emCorrProduct3 c := by
  apply sound_round (sound_mul A_rising5 A_term21 S_rising5 S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emCorr2, J_emAfterCorr2, J_emCorrProduct3,
    J_rising5, J_term21, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorr3 (s : ℂ) : ℂ := value ((1/123503214240), 0)*F_emCorrProduct3 s

def J_emCorr3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-577669351189205/1180591620717411303424), (274803194026801/295147905179352825856)), (215/295147905179352825856), by norm_num⟩
  | 1 => ⟨((262650297757599/147573952589676412928), (-385287724446151/147573952589676412928)), (367/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-114852335678039/36893488147419103232), (1062265008052499/295147905179352825856)), (625/147573952589676412928), by norm_num⟩
  | 3 => ⟨((1041506029665919/295147905179352825856), (-239049631775159/73786976294838206464)), (1415/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-216569383392045/73786976294838206464), (314287293642341/147573952589676412928)), (601/147573952589676412928), by norm_num⟩
  | 5 => ⟨((283148038996085/147573952589676412928), (-637616189595645/590295810358705651712)), (1627/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-303914583384591/295147905179352825856), (511058656180845/1180591620717411303424)), (1833/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((34496311183469/73786976294838206464), (-321577087238265/2361183241434822606848)), (1765/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1733582681866087/9444732965739290427392), (148226486794647/4722366482869645213696)), (2967/9444732965739290427392), by norm_num⟩
  | _ => zero

theorem A_emCorr3 : AnalyticAt ℂ F_emCorr3 c := by
  exact analyticAt_const.mul A_emCorrProduct3

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorr3 : Sound J_emCorr3 F_emCorr3 c := by
  apply sound_round (sound_scale A_emCorrProduct3 S_emCorrProduct3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr2, J_emCorrProduct3, J_emCorr3,
    J_emCorrProduct3, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emAfterCorr3 (s : ℂ) : ℂ := F_emAfterCorr2 s+F_emCorr3 s

def J_emAfterCorr3 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((200330361476225/9007199254740992), (-930066609446929/9007199254740992)), (32775/9007199254740992), by norm_num⟩
  | 1 => ⟨((1684872514286703/2251799813685248), (460350240459807/2251799813685248)), (8733/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1279849536798773/4503599627370496), (-325930276386625/2251799813685248)), (2603/281474976710656), by norm_num⟩
  | 3 => ⟨((623388185371657/9007199254740992), (271325650287461/4503599627370496)), (70847/9007199254740992), by norm_num⟩
  | 4 => ⟨((-816919865789649/72057594037927936), (-630694877548835/36028797018963968)), (376783/72057594037927936), by norm_num⟩
  | 5 => ⟨((304497138812517/288230376151711744), (554582286421135/144115188075855872)), (824045/288230376151711744), by norm_num⟩
  | 6 => ⟨((91180993291623/2305843009213693952), (-383750682522549/576460752303423488)), (3063487/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-180002337205967/4611686018427387904), (845417482695707/9223372036854775808)), (1238959/2305843009213693952), by norm_num⟩
  | 8 => ⟨((686460858445075/73786976294838206464), (-181024151410221/18446744073709551616)), (14188593/73786976294838206464), by norm_num⟩
  | _ => zero

theorem A_emAfterCorr3 : AnalyticAt ℂ F_emAfterCorr3 c := by
  exact A_emAfterCorr2.add A_emCorr3

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emAfterCorr3 : Sound J_emAfterCorr3 F_emAfterCorr3 c := by
  apply sound_round (sound_add A_emAfterCorr2 A_emCorr3 S_emAfterCorr2 S_emCorr3)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr3, J_emAfterCorr2, J_emCorr3, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_emCorrProduct4 (s : ℂ) : ℂ := F_rising7 s*F_term21 s

def J_emCorrProduct4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-40409207632845/4194304), (-479484817653011/16777216)), (275/16777216), by norm_num⟩
  | 1 => ⟨((15729853972299/1048576), (92576046356341/1048576)), (975/16777216), by norm_num⟩
  | 2 => ⟨((-6115641222517/4194304), (-1119229696900381/8388608)), (27/262144), by norm_num⟩
  | 3 => ⟨((-163236823751701/8388608), (551893023972873/4194304)), (1021/8388608), by norm_num⟩
  | 4 => ⟨((125617237270981/4194304), (-1597224313238951/16777216)), (903/8388608), by norm_num⟩
  | 5 => ⟨((-450306683086329/16777216), (451259572391767/8388608)), (639/8388608), by norm_num⟩
  | 6 => ⟨((295512648122419/16777216), (-826614302704299/33554432)), (1503/33554432), by norm_num⟩
  | 7 => ⟨((-309135359440877/33554432), (626997443757743/67108864)), (189/8388608), by norm_num⟩
  | 8 => ⟨((1078606590531975/268435456), (-198729231516347/67108864)), (2655/268435456), by norm_num⟩
  | _ => zero

theorem A_emCorrProduct4 : AnalyticAt ℂ F_emCorrProduct4 c := by
  exact A_rising7.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorrProduct4 : Sound J_emCorrProduct4 F_emCorrProduct4 c := by
  apply sound_round (sound_mul A_rising7 A_term21 S_rising7 S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emCorr3, J_emAfterCorr3, J_emCorrProduct4,
    J_rising7, J_term21, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorr4 (s : ℂ) : ℂ := value ((-1/2178596699193600), 0)*F_emCorrProduct4 s

def J_emCorr4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((167067996114177/37778931862957161709568), (495596006115131/37778931862957161709568)), (285/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-130067147378787/18889465931478580854784), (-95686697778477/2361183241434822606848)), (1009/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((6321133126901/9444732965739290427392), (578418489269755/9444732965739290427392)), (447/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((168721750770443/18889465931478580854784), (-285218601730257/4722366482869645213696)), (33/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-519352428262013/37778931862957161709568), (1650892711026459/37778931862957161709568)), (467/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((232718727943163/18889465931478580854784), (-932844726526565/37778931862957161709568)), (661/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-38180272548265/4722366482869645213696), (427194701412171/37778931862957161709568)), (1555/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((639045257940721/151115727451828646838272), (-81008151230871/18889465931478580854784)), (391/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-1114848893555469/604462909807314587353088), (821626961370065/604462909807314587353088)), (2745/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem A_emCorr4 : AnalyticAt ℂ F_emCorr4 c := by
  exact analyticAt_const.mul A_emCorrProduct4

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorr4 : Sound J_emCorr4 F_emCorr4 c := by
  apply sound_round (sound_scale A_emCorrProduct4 S_emCorrProduct4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr3, J_emCorrProduct4, J_emCorr4,
    J_emCorrProduct4, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emAfterCorr4 (s : ℂ) : ℂ := F_emAfterCorr3 s+F_emCorr4 s

def J_emAfterCorr4 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((200330401308339/9007199254740992), (-930066491287633/9007199254740992)), (4097/1125899906842624), by norm_num⟩
  | 1 => ⟨((1684872498781491/2251799813685248), (460350149205861/2251799813685248)), (17467/2251799813685248), by norm_num⟩
  | 2 => ⟨((-639924766892311/2251799813685248), (-651860276961821/4503599627370496)), (41649/4503599627370496), by norm_num⟩
  | 3 => ⟨((623388265824457/9007199254740992), (135662689140903/2251799813685248)), (1107/140737488355328), by norm_num⟩
  | 4 => ⟨((-816920856375793/72057594037927936), (-1261386606269715/72057594037927936)), (23549/4503599627370496), by norm_num⟩
  | 5 => ⟨((152250344909249/144115188075855872), (1109157455801815/288230376151711744)), (412023/144115188075855872), by norm_num⟩
  | 6 => ⟨((45581175290209/1152921504606846976), (-767488328097423/1152921504606846976)), (47867/36028797018963968), by norm_num⟩
  | 7 => ⟨((-359965670184765/9223372036854775808), (211344481983591/2305843009213693952)), (4955837/9223372036854775808), by norm_num⟩
  | 8 => ⟨((85790596061531/9223372036854775808), (-723996309380951/73786976294838206464)), (7094297/36893488147419103232), by norm_num⟩
  | _ => zero

theorem A_emAfterCorr4 : AnalyticAt ℂ F_emAfterCorr4 c := by
  exact A_emAfterCorr3.add A_emCorr4

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emAfterCorr4 : Sound J_emAfterCorr4 F_emAfterCorr4 c := by
  apply sound_round (sound_add A_emAfterCorr3 A_emCorr4 S_emAfterCorr3 S_emCorr4)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr4, J_emAfterCorr3, J_emCorr4, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_emCorrProduct5 (s : ℂ) : ℂ := F_rising9 s*F_term21 s

def J_emCorrProduct5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((503051054656443/65536), (212540758559231/131072)), (667/131072), by norm_num⟩
  | 1 => ⟨((-1383740373205971/65536), (-148156939248657/16384)), (1235/65536), by norm_num⟩
  | 2 => ⟨((912189873900037/32768), (626608589695187/32768)), (1137/32768), by norm_num⟩
  | 3 => ⟨((-759341542862563/32768), (-390723234471137/16384)), (1389/32768), by norm_num⟩
  | 4 => ⟨((438020836014199/32768), (339577531280291/16384)), (633/16384), by norm_num⟩
  | 5 => ⟨((-352249684706307/65536), (-896506797853679/65536)), (115/4096), by norm_num⟩
  | 6 => ⟨((336348127413365/262144), (1892018731603499/262144)), (1109/65536), by norm_num⟩
  | 7 => ⟨((9220427479117/131072), (-824832880797527/262144)), (1141/131072), by norm_num⟩
  | 8 => ⟨((-272067060541201/1048576), (1214860317247713/1048576)), (2047/524288), by norm_num⟩
  | _ => zero

theorem A_emCorrProduct5 : AnalyticAt ℂ F_emCorrProduct5 c := by
  exact A_rising9.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorrProduct5 : Sound J_emCorrProduct5 F_emCorrProduct5 c := by
  apply sound_round (sound_mul A_rising9 A_term21 S_rising9 S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emCorr4, J_emAfterCorr4, J_emCorrProduct5,
    J_rising9, J_term21, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorr5 (s : ℂ) : ℂ := value ((1/38046141316037352960), 0)*F_emCorrProduct5 s

def J_emCorr5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((60976315470299/302231454903657293676544), (206101583117527/4835703278458516698824704)), (81/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((-1341818310401443/2417851639229258349412352), (-574673393206807/2417851639229258349412352)), (599/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((442276997572167/604462909807314587353088), (151906184026379/302231454903657293676544)), (69/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-736336386356059/1208925819614629174706176), (-757771617370607/1208925819614629174706176)), (337/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((849500946105175/2417851639229258349412352), (1317158501972795/2417851639229258349412352)), (307/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-170788930468571/1208925819614629174706176), (-217336514141799/604462909807314587353088)), (1785/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((326158060263023/9671406556917033397649408), (458674442627937/2417851639229258349412352)), (4303/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((35764334584075/19342813113834066795298816), (-799843586200363/9671406556917033397649408)), (2213/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-263824464878095/38685626227668133590597632), (589027338447269/19342813113834066795298816)), (3971/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem A_emCorr5 : AnalyticAt ℂ F_emCorr5 c := by
  exact analyticAt_const.mul A_emCorrProduct5

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorr5 : Sound J_emCorr5 F_emCorr5 c := by
  apply sound_round (sound_scale A_emCorrProduct5 S_emCorrProduct5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr4, J_emCorrProduct5, J_emCorr5,
    J_emCorrProduct5, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emAfterCorr5 (s : ℂ) : ℂ := F_emAfterCorr4 s+F_emCorr5 s

def J_emAfterCorr5 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((200330403125575/9007199254740992), (-930066490903739/9007199254740992)), (32777/9007199254740992), by norm_num⟩
  | 1 => ⟨((1684872497531825/2251799813685248), (460350148670655/2251799813685248)), (4367/562949953421312), by norm_num⟩
  | 2 => ⟨((-639924765244701/2251799813685248), (-325930137349121/2251799813685248)), (20825/2251799813685248), by norm_num⟩
  | 3 => ⟨((623388260338323/9007199254740992), (542650750917773/9007199254740992)), (70849/9007199254740992), by norm_num⟩
  | 4 => ⟨((-204230207764673/18014398509481984), (-1261386567015333/72057594037927936)), (376785/72057594037927936), by norm_num⟩
  | 5 => ⟨((76125162274811/72057594037927936), (1109157352167689/288230376151711744)), (824047/288230376151711744), by norm_num⟩
  | 6 => ⟨((91162428342559/2305843009213693952), (-767488109384405/1152921504606846976)), (3063489/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-359965653131001/9223372036854775808), (845377165144079/9223372036854775808)), (2477919/4611686018427387904), by norm_num⟩
  | 8 => ⟨((85790533160877/9223372036854775808), (-361997031209987/36893488147419103232)), (14188595/73786976294838206464), by norm_num⟩
  | _ => zero

theorem A_emAfterCorr5 : AnalyticAt ℂ F_emAfterCorr5 c := by
  exact A_emAfterCorr4.add A_emCorr5

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emAfterCorr5 : Sound J_emAfterCorr5 F_emAfterCorr5 c := by
  apply sound_round (sound_add A_emAfterCorr4 A_emCorr5 S_emAfterCorr4 S_emCorr5)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr5, J_emAfterCorr4, J_emCorr5, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

def F_emCorrProduct6 (s : ℂ) : ℂ := F_rising11 s*F_term21 s

def J_emCorrProduct6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-610737267257617/512), (1020513838266727/512)), (413/256), by norm_num⟩
  | 1 => ⟨((149514762379331/32), (-306832075948209/64)), (773/128), by norm_num⟩
  | 2 => ⟨((-131121958048993/16), (331751133454411/64)), (717/64), by norm_num⟩
  | 3 => ⟨((285057149984659/32), (-24322322993461/8)), (1769/128), by norm_num⟩
  | 4 => ⟨((-1755602053408571/256), (164166213462637/256)), (815/64), by norm_num⟩
  | 5 => ⟨((1026935165638525/256), (147622437331971/256)), (2399/256), by norm_num⟩
  | 6 => ⟨((-59375707866369/32), (-94564743777349/128)), (367/64), by norm_num⟩
  | 7 => ⟨((709061381477037/1024), (500881637395691/1024)), (3075/1024), by norm_num⟩
  | 8 => ⟨((-427290020891863/2048), (-487230980993545/2048)), (1407/1024), by norm_num⟩
  | _ => zero

theorem A_emCorrProduct6 : AnalyticAt ℂ F_emCorrProduct6 c := by
  exact A_rising11.mul A_term21

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorrProduct6 : Sound J_emCorrProduct6 F_emCorrProduct6 c := by
  apply sound_round (sound_mul A_rising11 A_term21 S_rising11 S_term21)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emCorr5, J_emAfterCorr5, J_emCorrProduct6,
    J_rising11, J_term21, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emCorr6 (s : ℂ) : ℂ := value ((-691/458048909146168503491328000), 0)*F_emCorrProduct6 s

def J_emCorr6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((139229185279733/77371252455336267181195264), (-232645554620521/77371252455336267181195264)), (377/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((-545355776878409/77371252455336267181195264), (1119171394764445/154742504910672534362390528)), (1411/154742504910672534362390528), by norm_num⟩
  | 2 => ⟨((956535878593779/77371252455336267181195264), (-605031885267317/77371252455336267181195264)), (1309/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-519873626559431/38685626227668133590597632), (11089472989575/2417851639229258349412352)), (807/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((800445810910037/77371252455336267181195264), (-149699252862003/154742504910672534362390528)), (1487/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((-1872875347384347/309485009821345068724781056), (-269226756323931/309485009821345068724781056)), (547/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((54143291230695/19342813113834066795298816), (344925333708273/309485009821345068724781056)), (1339/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-1293152309498449/1237940039285380274899124224), (-228371006764729/309485009821345068724781056)), (5609/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((389635574420187/1237940039285380274899124224), (888588611353391/2475880078570760549798248448)), (5133/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem A_emCorr6 : AnalyticAt ℂ F_emCorr6 c := by
  exact analyticAt_const.mul A_emCorrProduct6

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_emCorr6 : Sound J_emCorr6 F_emCorr6 c := by
  apply sound_round (sound_scale A_emCorrProduct6 S_emCorrProduct6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr5, J_emCorrProduct6, J_emCorr6,
    J_emCorrProduct6, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_emAfterCorr6 (s : ℂ) : ℂ := F_emAfterCorr5 s+F_emCorr6 s

def J_emAfterCorr6 : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((200330403141783/9007199254740992), (-930066490930823/9007199254740992)), (16389/4503599627370496), by norm_num⟩
  | 1 => ⟨((1684872497515953/2251799813685248), (460350148686941/2251799813685248)), (17469/2251799813685248), by norm_num⟩
  | 2 => ⟨((-319962382608431/1125899906842624), (-651860274733459/4503599627370496)), (41651/4503599627370496), by norm_num⟩
  | 3 => ⟨((9740441565895/140737488355328), (542650750959085/9007199254740992)), (35425/4503599627370496), by norm_num⟩
  | 4 => ⟨((-816920830313219/72057594037927936), (-630693283542521/36028797018963968)), (188393/36028797018963968), by norm_num⟩
  | 5 => ⟨((304500647354993/288230376151711744), (138644668989619/36028797018963968)), (51503/18014398509481984), by norm_num⟩
  | 6 => ⟨((45581217398471/1152921504606846976), (-383744054049729/576460752303423488)), (1531745/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-359965662765737/9223372036854775808), (845377158338093/9223372036854775808)), (4955839/9223372036854775808), by norm_num⟩
  | 8 => ⟨((343162144255553/36893488147419103232), (-361997017968985/36893488147419103232)), (3547149/18446744073709551616), by norm_num⟩
  | _ => zero

theorem A_emAfterCorr6 : AnalyticAt ℂ F_emAfterCorr6 c := by
  exact A_emAfterCorr5.add A_emCorr6

set_option maxHeartbeats 5000000 in
-- Nine outward-rounded additions.
theorem S_emAfterCorr6 : Sound J_emAfterCorr6 F_emAfterCorr6 c := by
  apply sound_round (sound_add A_emAfterCorr5 A_emCorr6 S_emAfterCorr5 S_emCorr6)
  intro k
  fin_cases k <;> norm_num [HardTileGammaLogJet.logJet, HardTileGammaLog.gammaLogDisk, HardTileGammaLogJet.affineJet, HardTileGammaLogJet.inverseJet, HardTileGammaLogJet.inverseTable, J_emAfterCorr6, J_emAfterCorr5, J_emCorr6, jetAdd,
    CertifiedTaylorModel.add, exact, zero, qadd, size]

theorem gammaMain_identity (s : ℂ) :
    F_maincorr6 s = StirlingGamma.mainTerm (s/2+12) := by
  rw [HardTileFiniteIdentities.stirlingMain_eq]
  simp only [F_maincorr6, F_maincorr5, F_maincorr4, F_maincorr3, F_maincorr2, F_maincorr1, F_mainconstant, F_mainbase, F_wlog, F_wmhalf, F_shift, F_q0, F_shiftlog, F_negw, F_halfLog2pi, F_log2pi, F_log2, F_logpi, F_gcorr1, F_shiftinv, F_gcorr2, F_iw3, F_iw2, F_gcorr3, F_iw5, F_iw4, F_gcorr4, F_iw7, F_iw6, F_gcorr5, F_iw9, F_iw8, F_gcorr6, F_iw11, F_iw10, HardTileFiniteIdentities.stirlingMain,
    HardTileGammaLogJet.shifted, value, Rat.cast_zero, zero_mul, add_zero,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_add]
  simp only [show (12 : ℂ)+(1/2)*s = s/2+12 by ring]
  ring

theorem gammaFinite_identity (s : ℂ) :
    F_gammaFinite s = StirlingAnalytic.gammaApprox s := by
  simp only [F_gammaFinite, F_expGammaMain, gammaMain_identity,
    StirlingAnalytic.gammaApprox, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [F_gammaInvProd11, F_gammaInvProd10, F_gammaInvProd9, F_gammaInvProd8, F_gammaInvProd7, F_gammaInvProd6, F_gammaInvProd5, F_gammaInvProd4, F_gammaInvProd3, F_gammaInvProd2, F_gammaInvProd1, F_gammaInv0, F_halfVariable, F_variable, F_gammaInv1, F_shift1, F_q1, F_gammaInv2, F_shift2, F_q2, F_gammaInv3, F_shift3, F_q3, F_gammaInv4, F_shift4, F_q4, F_gammaInv5, F_shift5, F_q5, F_gammaInv6, F_shift6, F_q6, F_gammaInv7, F_shift7, F_q7, F_gammaInv8, F_shift8, F_q8, F_gammaInv9, F_shift9, F_q9, F_gammaInv10, F_shift10, F_q10, F_gammaInv11, F_shift11, F_q11, value, Rat.cast_zero, zero_mul, add_zero,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat,
    Finset.prod_range_succ, Finset.prod_range_zero, mul_one, one_mul]
  simp only [show (1/2 : ℂ)*s = s/2 by ring]
  ring

theorem term1_identity (s : ℂ) :
    F_q1 s = HardTileFiniteIdentities.dirichletTerm s 1 := by
  simp [HardTileFiniteIdentities.dirichletTerm, F_q1, value]

theorem term2_identity (s : ℂ) :
    F_term2 s = HardTileFiniteIdentities.dirichletTerm s 2 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term2, F_arg2, F_negLog2, F_log2, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term3_identity (s : ℂ) :
    F_term3 s = HardTileFiniteIdentities.dirichletTerm s 3 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term3, F_arg3, F_negLog3, F_log3, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term4_identity (s : ℂ) :
    F_term4 s = HardTileFiniteIdentities.dirichletTerm s 4 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term4, F_arg4, F_negLog4, F_log4, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term5_identity (s : ℂ) :
    F_term5 s = HardTileFiniteIdentities.dirichletTerm s 5 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term5, F_arg5, F_negLog5, F_log5, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term6_identity (s : ℂ) :
    F_term6 s = HardTileFiniteIdentities.dirichletTerm s 6 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term6, F_arg6, F_negLog6, F_log6, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term7_identity (s : ℂ) :
    F_term7 s = HardTileFiniteIdentities.dirichletTerm s 7 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term7, F_arg7, F_negLog7, F_log7, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term8_identity (s : ℂ) :
    F_term8 s = HardTileFiniteIdentities.dirichletTerm s 8 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term8, F_arg8, F_negLog8, F_log8, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term9_identity (s : ℂ) :
    F_term9 s = HardTileFiniteIdentities.dirichletTerm s 9 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term9, F_arg9, F_negLog9, F_log9, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term10_identity (s : ℂ) :
    F_term10 s = HardTileFiniteIdentities.dirichletTerm s 10 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term10, F_arg10, F_negLog10, F_log10, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term11_identity (s : ℂ) :
    F_term11 s = HardTileFiniteIdentities.dirichletTerm s 11 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term11, F_arg11, F_negLog11, F_log11, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term12_identity (s : ℂ) :
    F_term12 s = HardTileFiniteIdentities.dirichletTerm s 12 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term12, F_arg12, F_negLog12, F_log12, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term13_identity (s : ℂ) :
    F_term13 s = HardTileFiniteIdentities.dirichletTerm s 13 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term13, F_arg13, F_negLog13, F_log13, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term14_identity (s : ℂ) :
    F_term14 s = HardTileFiniteIdentities.dirichletTerm s 14 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term14, F_arg14, F_negLog14, F_log14, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term15_identity (s : ℂ) :
    F_term15 s = HardTileFiniteIdentities.dirichletTerm s 15 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term15, F_arg15, F_negLog15, F_log15, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term16_identity (s : ℂ) :
    F_term16 s = HardTileFiniteIdentities.dirichletTerm s 16 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term16, F_arg16, F_negLog16, F_log16, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term17_identity (s : ℂ) :
    F_term17 s = HardTileFiniteIdentities.dirichletTerm s 17 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term17, F_arg17, F_negLog17, F_log17, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term18_identity (s : ℂ) :
    F_term18 s = HardTileFiniteIdentities.dirichletTerm s 18 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term18, F_arg18, F_negLog18, F_log18, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term19_identity (s : ℂ) :
    F_term19 s = HardTileFiniteIdentities.dirichletTerm s 19 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term19, F_arg19, F_negLog19, F_log19, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term20_identity (s : ℂ) :
    F_term20 s = HardTileFiniteIdentities.dirichletTerm s 20 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term20, F_arg20, F_negLog20, F_log20, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem term21_identity (s : ℂ) :
    F_term21 s = HardTileFiniteIdentities.dirichletTerm s 21 := by
  unfold HardTileFiniteIdentities.dirichletTerm
  simp only [F_term21, F_arg21, F_negLog21, F_log21, F_variable, value, Rat.cast_neg, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero]
  congr 1
  ring

theorem rising1_identity (s : ℂ) :
    F_variable s = HardTileFiniteIdentities.rising s 1 := by
  simp [F_variable, HardTileFiniteIdentities.rising, Finset.prod_range_succ]

theorem rising2_identity (s : ℂ) :
    F_rising2 s = HardTileFiniteIdentities.rising s 2 := by
  simp only [F_rising2, rising1_identity,
    F_factor1, F_variable, F_q1, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising3_identity (s : ℂ) :
    F_rising3 s = HardTileFiniteIdentities.rising s 3 := by
  simp only [F_rising3, rising2_identity,
    F_factor2, F_variable, F_q2, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising4_identity (s : ℂ) :
    F_rising4 s = HardTileFiniteIdentities.rising s 4 := by
  simp only [F_rising4, rising3_identity,
    F_factor3, F_variable, F_q3, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising5_identity (s : ℂ) :
    F_rising5 s = HardTileFiniteIdentities.rising s 5 := by
  simp only [F_rising5, rising4_identity,
    F_factor4, F_variable, F_q4, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising6_identity (s : ℂ) :
    F_rising6 s = HardTileFiniteIdentities.rising s 6 := by
  simp only [F_rising6, rising5_identity,
    F_factor5, F_variable, F_q5, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising7_identity (s : ℂ) :
    F_rising7 s = HardTileFiniteIdentities.rising s 7 := by
  simp only [F_rising7, rising6_identity,
    F_factor6, F_variable, F_q6, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising8_identity (s : ℂ) :
    F_rising8 s = HardTileFiniteIdentities.rising s 8 := by
  simp only [F_rising8, rising7_identity,
    F_factor7, F_variable, F_q7, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising9_identity (s : ℂ) :
    F_rising9 s = HardTileFiniteIdentities.rising s 9 := by
  simp only [F_rising9, rising8_identity,
    F_factor8, F_variable, F_q8, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising10_identity (s : ℂ) :
    F_rising10 s = HardTileFiniteIdentities.rising s 10 := by
  simp only [F_rising10, rising9_identity,
    F_factor9, F_variable, F_q9, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem rising11_identity (s : ℂ) :
    F_rising11 s = HardTileFiniteIdentities.rising s 11 := by
  simp only [F_rising11, rising10_identity,
    F_factor10, F_variable, F_q10, HardTileFiniteIdentities.rising, Finset.prod_range_succ,
    value, Rat.cast_zero, zero_mul, add_zero, Rat.cast_ofNat]
  first | rfl | (simp only [Finset.prod_range_zero, Nat.cast_zero, add_zero, one_mul] <;> rfl)

theorem zetaFinite_identity (s : ℂ) :
    F_emAfterCorr6 s = EulerMaclaurinZeta.finiteModel s 21 := by
  rw [HardTileFiniteIdentities.emFinite_eq]
  simp only [F_emAfterCorr6, F_emAfterCorr5, F_emAfterCorr4, F_emAfterCorr3, F_emAfterCorr2, F_emAfterCorr1, F_emInitialHalf, F_emInitialIntegral, F_initial20, F_initial19, F_initial18, F_initial17, F_initial16, F_initial15, F_initial14, F_initial13, F_initial12, F_initial11, F_initial10, F_initial9, F_initial8, F_initial7, F_initial6, F_initial5, F_initial4, F_initial3, F_initial2, F_emIntegral, F_emIntegralProduct, F_sminusoneInv, F_sminusone, F_q12, F_emHalf, F_emCorr1, F_emCorrProduct1, F_emCorr2, F_emCorrProduct2, F_emCorr3, F_emCorrProduct3, F_emCorr4, F_emCorrProduct4, F_emCorr5, F_emCorrProduct5, F_emCorr6, F_emCorrProduct6, term1_identity, term2_identity, term3_identity, term4_identity, term5_identity, term6_identity, term7_identity, term8_identity, term9_identity, term10_identity, term11_identity, term12_identity, term13_identity, term14_identity, term15_identity, term16_identity, term17_identity, term18_identity, term19_identity, term20_identity, term21_identity, rising1_identity, rising2_identity, rising3_identity, rising4_identity, rising5_identity, rising6_identity, rising7_identity, rising8_identity, rising9_identity, rising10_identity, rising11_identity,
    HardTileFiniteIdentities.emFinite, Finset.sum_range_succ, Finset.sum_range_zero,
    value, Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_zero,
    zero_mul, add_zero, Rat.cast_ofNat, Nat.cast_ofNat]
  simp only [show HardTileFiniteIdentities.rising s 1 = s by
    simp [HardTileFiniteIdentities.rising], show s+(-1 : ℂ) = s-1 by ring]
  ring

end Reinmann.HardTileFiniteJets

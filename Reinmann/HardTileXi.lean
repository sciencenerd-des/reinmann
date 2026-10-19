/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
import Reinmann.HardTileFiniteJets
import Reinmann.ZetaJetRemainder
import Reinmann.TaylorDerivativeTail
import Reinmann.XiLocalCauchy
import Reinmann.XiAdaptiveTiles
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Complete degree-eight ordinary Taylor jet and nonvanishing certificate for
the actual completed Xi function on the hard tile `‖z - (1/2 + 14i)‖ ≤ 1/16`. -/
noncomputable section
namespace Reinmann.HardTileXi
open Finset Metric Filter
open CertifiedTaylorModel CertifiedTaylorComposition CertifiedTaylorInputs
open HardTileFiniteJets
open scoped Topology
set_option maxRecDepth 20000

def F_negLogPi (s : ℂ) : ℂ := value (-1, 0)*F_logpi s

def J_negLogPi : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-1288851271837807/1125899906842624), 0), (7/1125899906842624), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_negLogPi : AnalyticAt ℂ F_negLogPi c := by
  exact analyticAt_const.mul A_logpi

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_negLogPi : Sound J_negLogPi F_negLogPi c := by
  apply sound_round (sound_scale A_logpi S_logpi)
  intro k
  fin_cases k <;> norm_num [J_negLogPi, J_logpi, jetScale, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_piArg (s : ℂ) : ℂ := F_negLogPi s*F_halfVariable s

def J_piArg : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-40276602244931/140737488355328), (-1127744862858081/140737488355328)), (7/140737488355328), by norm_num⟩
  | 1 => ⟨((-1288851271837807/2251799813685248), 0), (7/2251799813685248), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_piArg : AnalyticAt ℂ F_piArg c := by
  exact A_negLogPi.mul A_halfVariable

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_piArg : Sound J_piArg F_piArg c := by
  apply sound_round (sound_mul A_negLogPi A_halfVariable S_negLogPi S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_piArg, J_negLogPi, J_halfVariable, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def piPowerValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583602982483863/10141204801825835211973625643008), (-2253419018637/10141204801825835211973625643008)), (1/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890763176780593/316912650057057350374175801344), (-668668883939/158456325028528675187087900672)), (1/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236605452922001/4951760157141521099596496896), (-376115669085/4951760157141521099596496896)), (1/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892811948299703/2475880078570760549798248448), (-3196888974167/2475880078570760549798248448)), (1/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774477512477955/154742504910672534362390528), (-3196782931819/154742504910672534362390528)), (1/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552634095808589/9671406556917033397649408), (-2996871273971/9671406556917033397649408)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261483542249609/604462909807314587353088), (-2622149578699/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1892169825424199/75557863725914323419136), (-4260781461101/75557863725914323419136)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((650410797121505/2361183241434822606848), (-3195400811617/4722366482869645213696)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625959117367171/590295810358705651712), (-4393374784583/590295810358705651712)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914555230036261/36893488147419103232), (-2745633027897/36893488147419103232)), (1/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228624149886585/1152921504606846976), (-6177051533449/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((800118340372875/576460752303423488), (-6176272017133/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((300011144997507/36028797018963968), (-5403359626783/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499821832334339/36028797018963968), (-8103279084755/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((749734233256729/4503599627370496), (-10126010186375/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((1124155223957481/2251799813685248), (-5060680549901/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((70203108091383/70368744177664), (-3792590675961/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 0 => ⟨((560233563135645/562949953421312), (-15146836357589/562949953421312)), (1/562949953421312), by norm_num⟩
  | _ => zero

def piPowerValueSquares : ℕ → Disk
  | 0 => ⟨((560233563135645/562949953421312), (-15146836357589/562949953421312)), (3816844749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((557122736587731/562949953421312), (-60294994617355/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 2 => ⟨((1099482716529911/1125899906842624), (-59670868075591/562949953421312)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((530517760371125/562949953421312), (-116541599711881/562949953421312)), (27/1125899906842624), by norm_num⟩
  | 4 => ⟨((951655286505791/1125899906842624), (-439310017478187/1125899906842624)), (63/1125899906842624), by norm_num⟩
  | 5 => ⟨((158241085319085/281474976710656), (-371322262314127/562949953421312)), (39/281474976710656), by norm_num⟩
  | 6 => ⟨((-33501431103241/281474976710656), (-835007622750445/1125899906842624)), (763/2251799813685248), by norm_num⟩
  | _ => zero

def piPowerValue : CertifiedScalarExp.Data :=
  ⟨⟨((-40276602244931/140737488355328), (-1127744862858081/140737488355328)), (7/140737488355328), by norm_num⟩, -1, piPowerValuePoly, piPowerValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem piPowerValue_checks : CertifiedScalarExp.Checks piPowerValue := by
  constructor
  · norm_num [piPowerValue, CertifiedScalarExp.reduced, piPowerValuePoly, piPowerValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        piPowerValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, piPowerValueSquares, piPowerValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [piPowerValue, CertifiedScalarExp.roundingCheck, piPowerValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

def F_piPower (s : ℂ) : ℂ := Complex.exp (F_piArg s)

def J_piPower : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-33501431103241/281474976710656), (-835007622750445/1125899906842624)), (763/2251799813685248), by norm_num⟩
  | 1 => ⟨((306800715220837/4503599627370496), (1911716361348991/4503599627370496)), (887/4503599627370496), by norm_num⟩
  | 2 => ⟨((-175601973856631/9007199254740992), (-547099713025865/4503599627370496)), (129/2251799813685248), by norm_num⟩
  | 3 => ⟨((268022436650441/72057594037927936), (104380232006723/4503599627370496)), (799/72057594037927936), by norm_num⟩
  | 4 => ⟨((-306813293311937/576460752303423488), (-955897368559919/288230376151711744)), (29/18014398509481984), by norm_num⟩
  | 5 => ⟨((140487338492021/2305843009213693952), (1750790856952541/4611686018427387904)), (431/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-214426739940343/36893488147419103232), (-668060872608485/18446744073709551616)), (667/36893488147419103232), by norm_num⟩
  | 7 => ⟨((280526511468535/590295810358705651712), (218499784697589/73786976294838206464)), (885/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-160563540725553/4722366482869645213696), (-500246467189979/2361183241434822606848)), (257/2361183241434822606848), by norm_num⟩
  | _ => zero

theorem A_piPower : AnalyticAt ℂ F_piPower c := by
  exact A_piArg.cexp'

set_option maxHeartbeats 5000000 in
-- The constant exp certificate and eight ordinary-coefficient recurrence checks.
theorem S_piPower : Sound J_piPower F_piPower c := by
  apply exp_sound A_piArg S_piArg piPowerValue piPowerValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [piPowerValue, J_piArg]
  · rfl
  · intro n hn
    have hlt : n < 8 := by omega
    interval_cases n <;> norm_num [J_piPower, J_piArg, CertifiedTaylorModel.get, sum,
      CertifiedTaylorModel.mul, CertifiedTaylorModel.add, zero, exact, qmul, qadd, size]

def F_polyPrefactor (s : ℂ) : ℂ := F_halfVariable s*F_sminusone s

def J_polyPrefactor : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((-785/8), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 14), 0, by norm_num⟩
  | 2 => ⟨((1/2), 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem A_polyPrefactor : AnalyticAt ℂ F_polyPrefactor c := by
  exact A_halfVariable.mul A_sminusone

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_polyPrefactor : Sound J_polyPrefactor F_polyPrefactor c := by
  apply sound_round (sound_mul A_halfVariable A_sminusone S_halfVariable S_sminusone)
  intro k
  fin_cases k <;> norm_num [J_polyPrefactor, J_halfVariable, J_sminusone, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_prefactor (s : ℂ) : ℂ := F_polyPrefactor s*F_piPower s

def J_prefactor : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((205457995437845/17592186044416), (1280236296599803/17592186044416)), (293/8796093022208), by norm_num⟩
  | 1 => ⟨((130121927288909/35184372088832), (-1524152254097623/35184372088832)), (53/2199023255552), by norm_num⟩
  | 2 => ⟨((-287758885396419/70368744177664), (439916828970733/35184372088832)), (603/70368744177664), by norm_num⟩
  | 3 => ⟨((771133123775281/562949953421312), (-657229118873851/281474976710656)), (35/17592186044416), by norm_num⟩
  | 4 => ⟨((-635010095754789/2251799813685248), (356638652052887/1125899906842624)), (385/1125899906842624), by norm_num⟩
  | 5 => ⟨((762215188871785/18014398509481984), (-18642182971431/562949953421312)), (419/9007199254740992), by norm_num⟩
  | 6 => ⟨((-722132724640705/144115188075855872), (792177175654633/288230376151711744)), (1499/288230376151711744), by norm_num⟩
  | 7 => ⟨((1131824165303633/2305843009213693952), (-209967394315003/1152921504606846976)), (1139/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1513623601652553/36893488147419103232), (344379271692369/36893488147419103232)), (1503/36893488147419103232), by norm_num⟩
  | _ => zero

theorem A_prefactor : AnalyticAt ℂ F_prefactor c := by
  exact A_polyPrefactor.mul A_piPower

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_prefactor : Sound J_prefactor F_prefactor c := by
  apply sound_round (sound_mul A_polyPrefactor A_piPower S_polyPrefactor S_piPower)
  intro k
  fin_cases k <;> norm_num [J_prefactor, J_polyPrefactor, J_piPower, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_gammaActual (s : ℂ) : ℂ := Complex.Gamma (s / 2)

def J_gammaActual : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((952591158707819/36893488147419103232), (-50558354688553/36893488147419103232)), (2956587/73786976294838206464), by norm_num⟩
  | 1 => ⟨((967339483560789/36893488147419103232), (716010111686851/36893488147419103232)), (740617/18446744073709551616), by norm_num⟩
  | 2 => ⟨((362893446279681/73786976294838206464), (1439641379515101/73786976294838206464)), (740949/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-501520099020983/147573952589676412928), (1080529889421981/147573952589676412928)), (5921937/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-1248681189653191/590295810358705651712), (77780794471501/73786976294838206464)), (11828593/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-1242799021874395/2361183241434822606848), (-252859615309843/2361183241434822606848)), (47269711/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-153704900126947/2361183241434822606848), (-696893187622705/9444732965739290427392)), (188983757/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-55620119927291/37778931862957161709568), (-1120585109575699/75557863725914323419136)), (755772321/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((542450578632463/604462909807314587353088), (-1014567176530271/604462909807314587353088)), (12091413019/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem A_gammaActual : AnalyticAt ℂ F_gammaActual c := by
  apply DifferentiableOn.analyticAt (s := Metric.ball EulerMaclaurinAnalytic.hardCentre 1)
    _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  intro z hz
  exact (StirlingAnalytic.gamma_factor_differentiableAt
    (mem_ball_iff_norm.mp hz).le).differentiableWithinAt

theorem S_gammaApprox : Sound J_gammaFinite StirlingAnalytic.gammaApprox c :=
  sound_congr S_gammaFinite (Eventually.of_forall gammaFinite_identity)

theorem S_gammaPerturb :
    Sound (fun k => inflate (J_gammaFinite k) (4 / 10 ^ 14) (by norm_num)) F_gammaActual c := by
  apply sound_perturb (by norm_num) S_gammaApprox
  intro k
  simpa only [coefficient, F_gammaActual, c, HardTileGammaLogJet.centre,
    EulerMaclaurinAnalytic.hardCentre, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using
    StirlingAnalytic.gamma_coefficient_error_le k.val

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round S_gammaPerturb
  intro k
  fin_cases k <;> norm_num [J_gammaActual, J_gammaFinite, inflate, zero, size]

def F_zetaActual (s : ℂ) : ℂ := riemannZeta s

def J_zetaActual : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((200330403141783/9007199254740992), (-930066490930823/9007199254740992)), (14074261/140737488355328), by norm_num⟩
  | 1 => ⟨((1684872497515953/2251799813685248), (460350148686941/2251799813685248)), (225197451/2251799813685248), by norm_num⟩
  | 2 => ⟨((-319962382608431/1125899906842624), (-651860274733459/4503599627370496)), (225200807/2251799813685248), by norm_num⟩
  | 3 => ⟨((9740441565895/140737488355328), (542650750959085/9007199254740992)), (112598847/1125899906842624), by norm_num⟩
  | 4 => ⟨((-816920830313219/72057594037927936), (-630693283542521/36028797018963968)), (3603068095/36028797018963968), by norm_num⟩
  | 5 => ⟨((304500647354993/288230376151711744), (138644668989619/36028797018963968)), (900745677/9007199254740992), by norm_num⟩
  | 6 => ⟨((45581217398471/1152921504606846976), (-383744054049729/576460752303423488)), (57646841103/576460752303423488), by norm_num⟩
  | 7 => ⟨((-359965662765737/9223372036854775808), (845377158338093/9223372036854775808)), (922342159525/9223372036854775808), by norm_num⟩
  | 8 => ⟨((343162144255553/36893488147419103232), (-361997017968985/36893488147419103232)), (230584744315/2305843009213693952), by norm_num⟩
  | _ => zero

theorem A_zetaActual : AnalyticAt ℂ F_zetaActual c := by
  apply DifferentiableOn.analyticAt (s := Metric.ball EulerMaclaurinAnalytic.hardCentre 1)
    _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  intro z hz
  exact (differentiableAt_riemannZeta
    (ZetaJetRemainder.hard_disk_ne_one (mem_ball_iff_norm.mp hz).le)).differentiableWithinAt

theorem S_zetaApprox :
    Sound J_emAfterCorr6 (fun s => EulerMaclaurinZeta.finiteModel s 21) c :=
  sound_congr S_emAfterCorr6 (Eventually.of_forall zetaFinite_identity)

theorem S_zetaPerturb :
    Sound (fun k => inflate (J_emAfterCorr6 k) (1 / 10 ^ 7) (by norm_num)) F_zetaActual c := by
  apply sound_perturb (by norm_num) S_zetaApprox
  intro k
  simpa only [coefficient, F_zetaActual, c, HardTileGammaLogJet.centre,
    EulerMaclaurinAnalytic.hardCentre, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_pow] using ZetaJetRemainder.zeta_coefficient_error_le k.val

set_option maxHeartbeats 5000000 in
theorem S_zetaActual : Sound J_zetaActual F_zetaActual c := by
  apply sound_round S_zetaPerturb
  intro k
  fin_cases k <;> norm_num [J_zetaActual, J_emAfterCorr6, inflate, zero, size]

def F_prefactorGamma (s : ℂ) : ℂ := F_prefactor s*F_gammaActual s

def J_prefactorGamma : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((231320838669347/576460752303423488), (1073944630106343/576460752303423488)), (1951223/576460752303423488), by norm_num⟩
  | 1 => ⟨((-616810885833985/576460752303423488), (36431788923637/36028797018963968)), (3041855/576460752303423488), by norm_num⟩
  | 2 => ⟨((-591667247148079/1152921504606846976), (-345490134643631/2305843009213693952)), (13712535/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-247757222460643/9223372036854775808), (-536758517606269/4611686018427387904)), (28101251/4611686018427387904), by norm_num⟩
  | 4 => ⟨((498809136207327/36893488147419103232), (-863238306747073/73786976294838206464)), (450925599/73786976294838206464), by norm_num⟩
  | 5 => ⟨((965251450548391/590295810358705651712), (417769334638585/590295810358705651712)), (3605311169/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-50496537839221/9444732965739290427392), (1847784012880783/18889465931478580854784)), (115288198711/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((615235668857797/604462909807314587353088), (-90369385662547/37778931862957161709568)), (28810026671/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((1016844806814533/1208925819614629174706176), (345984395155115/604462909807314587353088)), (7373927308383/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem A_prefactorGamma : AnalyticAt ℂ F_prefactorGamma c := by
  exact A_prefactor.mul A_gammaActual

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_prefactorGamma : Sound J_prefactorGamma F_prefactorGamma c := by
  apply sound_round (sound_mul A_prefactor A_gammaActual S_prefactor S_gammaActual)
  intro k
  fin_cases k <;> norm_num [J_prefactorGamma, J_prefactor, J_gammaActual, jetMul, sum, CertifiedTaylorModel.get,
    CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def F_xiProduct (s : ℂ) : ℂ := F_prefactorGamma s*F_zetaActual s

def J_xiProduct : Jet8 := fun k =>
  match k.val with
  | 0 => ⟨((56659349003/281474976710656), 0), (255423/1125899906842624), by norm_num⟩
  | 1 => ⟨((57/576460752303423488), (927507278751715/576460752303423488)), (505507227/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-2025910014910213/2305843009213693952), (117/288230376151711744)), (585813855/1152921504606846976), by norm_num⟩
  | 3 => ⟨((817/4611686018427387904), (-904880593116505/4611686018427387904)), (2418126017/4611686018427387904), by norm_num⟩
  | 4 => ⟨((738961161842581/36893488147419103232), (17975/73786976294838206464)), (2433282903/4611686018427387904), by norm_num⟩
  | 5 => ⟨((73629/4722366482869645213696), (739274208252307/2361183241434822606848)), (2493854295833/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((641709312338621/4722366482869645213696), (318381/9444732965739290427392)), (4988215421815/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((593231/75557863725914323419136), (1805848854216189/151115727451828646838272)), (79811296129927/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((92123689133617/2417851639229258349412352), (931333/75557863725914323419136)), (159620601643983/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem A_xiProduct : AnalyticAt ℂ F_xiProduct c := by
  exact A_prefactorGamma.mul A_zetaActual

set_option maxHeartbeats 5000000 in
-- Nine finite rational convolution/rounding checks.
theorem S_xiProduct : Sound J_xiProduct F_xiProduct c := by
  apply sound_round (sound_mul A_prefactorGamma A_zetaActual S_prefactorGamma S_zetaActual)
  intro k
  fin_cases k <;> norm_num [J_xiProduct, J_prefactorGamma, J_zetaActual, jetMul, sum,
    CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
    exact, zero, qmul, qadd, size]

/-! ## Identification with `xiCompleted` and hard-tile nonvanishing -/

theorem piPower_eq (s : ℂ) : (Real.pi : ℂ) ^ (-s / 2) = F_piPower s := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.cpow_def_of_ne_zero hpi0, ← Complex.ofReal_log Real.pi_pos.le]
  unfold F_piPower F_piArg F_negLogPi F_logpi F_halfVariable F_variable
  simp only [value, Rat.cast_neg, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_zero, zero_mul, add_zero]
  congr 1
  ring

theorem xiProduct_eq_xiCompleted {s : ℂ} (hr : 0 < s.re) (h1 : s ≠ 1) :
    F_xiProduct s = xiCompleted s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hgamma : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have heq : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp
  rw [xiCompleted_eq_product h0 h1, heq, Complex.Gammaℝ_def, piPower_eq]
  unfold F_xiProduct F_prefactorGamma F_prefactor F_polyPrefactor
    F_halfVariable F_sminusone F_q12 F_variable F_gammaActual F_zetaActual
  simp only [value, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_neg,
    Rat.cast_zero, zero_mul, add_zero]
  ring

theorem quarter_ball_domain {s : ℂ} (hs : s ∈ Metric.ball c (1 / 4)) :
    0 < s.re ∧ s ≠ 1 := by
  have hn : ‖c - s‖ < 1 / 4 := by
    rw [norm_sub_rev]
    exact mem_ball_iff_norm.mp hs
  have hr := (Complex.re_le_norm (c - s)).trans_lt hn
  have hi := (Complex.im_le_norm (c - s)).trans_lt hn
  norm_num [c, HardTileGammaLogJet.centre, Complex.sub_re, Complex.sub_im] at hr hi
  refine ⟨by linarith, ?_⟩
  intro h1
  rw [h1] at hi
  norm_num at hi

theorem xiProduct_eventuallyEq : F_xiProduct =ᶠ[𝓝 c] xiCompleted := by
  filter_upwards [Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 4)] with s hs
  exact xiProduct_eq_xiCompleted (quarter_ball_domain hs).1 (quarter_ball_domain hs).2

/-- Certified degree-eight ordinary Taylor jet for the actual completed Xi
function at the hard centre `1/2 + 14i`. -/
theorem xiCompleted_sound : Sound J_xiProduct xiCompleted c :=
  sound_congr S_xiProduct xiProduct_eventuallyEq

/-- All nine ordinary coefficient disks meet the requested `1e-7` budget. -/
theorem xiCompleted_coefficient_error_budget (k : Fin 9) :
    ‖coefficient xiCompleted c k.val - value (J_xiProduct k).centre‖ ≤ (1 / 10 ^ 7 : ℝ) := by
  have h : ‖coefficient xiCompleted c k.val - value (J_xiProduct k).centre‖ ≤
      ((J_xiProduct k).radius : ℝ) := xiCompleted_sound k
  apply h.trans
  fin_cases k <;> norm_num [J_xiProduct]

theorem hard_centre_value :
    value (J_xiProduct ⟨0, by omega⟩).centre =
      (56659349003 / 281474976710656 : ℂ) := by
  norm_num [J_xiProduct, value]

/-- Certified value enclosure for `xiCompleted (1/2 + 14i)`. -/
theorem hard_centre_enclosure :
    ‖xiCompleted c - (56659349003 / 281474976710656 : ℂ)‖ ≤
      (255423 / 1125899906842624 : ℝ) := by
  have h := centre_contains xiCompleted_sound
  unfold Contains at h
  rw [hard_centre_value] at h
  simpa [J_xiProduct] using h

theorem xiCompleted_coeff_le_thousand (n : ℕ) :
    ‖coefficient xiCompleted c n‖ ≤ 1000 := by
  unfold coefficient
  apply XiLocalCauchy.taylor_coefficient_bound
  · norm_num [c, HardTileGammaLogJet.centre]
  · norm_num [c, HardTileGammaLogJet.centre]
  · norm_num [c, HardTileGammaLogJet.centre]

theorem xiCompleted_coeff_norm_le (k : Fin 9) :
    ‖coefficient xiCompleted c k.val‖ ≤
      ((size (J_xiProduct k).centre + (J_xiProduct k).radius : ℚ) : ℝ) :=
  norm_le_of_contains (xiCompleted_sound k)

def coeffBound (m : ℕ) : ℚ :=
  size (CertifiedTaylorModel.get J_xiProduct m).centre +
    (CertifiedTaylorModel.get J_xiProduct m).radius

theorem xiCompleted_coeff_le_bound {n : ℕ} (hn : n ∈ range 8) :
    ‖coefficient xiCompleted c (n + 1)‖ ≤ (coeffBound (n + 1) : ℝ) := by
  have hlt : n + 1 < 8 + 1 := Nat.succ_lt_succ (mem_range.mp hn)
  simpa [coeffBound, CertifiedTaylorModel.get, hlt] using
    xiCompleted_coeff_norm_le ⟨n + 1, hlt⟩

set_option maxHeartbeats 5000000 in
/-- Uniform derivative bound on the closed hard tile `‖z - (1/2 + 14i)‖ ≤ 1/16`,
combining the eight certified nonconstant Taylor coefficients and the proved
unit-circle Cauchy majorant `1000`. -/
theorem hard_tile_deriv_le {z : ℂ} (hz : ‖z - c‖ ≤ 1 / 16) :
    ‖deriv xiCompleted z‖ ≤ (9 / 5000 : ℝ) := by
  have h := TaylorDerivativeTail.derivative_bound differentiable_xiCompleted
    (r := (1 / 16 : ℝ)) (M := 1000) (by norm_num) (by norm_num) hz
    xiCompleted_coeff_le_thousand
  have hsum :
      (∑ n ∈ range 8, ((n + 1 : ℕ) : ℝ) * ‖coefficient xiCompleted c (n + 1)‖ * (1 / 16 : ℝ) ^ n) ≤
        ∑ n ∈ range 8, ((n + 1 : ℕ) : ℝ) * (coeffBound (n + 1) : ℝ) * (1 / 16 : ℝ) ^ n := by
    apply Finset.sum_le_sum
    intro n hn
    have hc := xiCompleted_coeff_le_bound hn
    gcongr
  apply h.trans ((add_le_add hsum le_rfl).trans _)
  norm_num [Finset.sum_range_succ, coeffBound, CertifiedTaylorModel.get, J_xiProduct, size]

/-- Complete hard-tile certificate: `xiCompleted z ≠ 0` throughout the closed
complex disk `‖z - (1/2 + 14i)‖ ≤ 1/16`. -/
theorem hard_tile_nonzero {z : ℂ} (hz : ‖z - c‖ ≤ 1 / 16) :
    xiCompleted z ≠ 0 := by
  have hcover := XiAdaptiveTiles.adaptive_cover_nonzero (n := 1)
    (f := xiCompleted) (S := Metric.closedBall c (1 / 16))
    (fun _ => Metric.closedBall c (1 / 16)) (fun _ => c)
    (fun _ => (56659349003 / 281474976710656 : ℂ))
    (fun _ => (1 / 16 : ℝ)) (fun _ => (9 / 5000 : ℝ))
    (fun _ => (255423 / 1125899906842624 : ℝ))
    (fun _ => convex_closedBall c (1 / 16)) (fun _ => by simp)
    (fun _ w _ => differentiable_xiCompleted w) (fun _ => by norm_num)
    (fun _ _ hw => hard_tile_deriv_le (mem_closedBall_iff_norm.mp hw))
    (fun _ => hard_centre_enclosure)
    (fun w hw => ⟨⟨0, by omega⟩, hw, mem_closedBall_iff_norm.mp hw⟩)
    (fun _ => by norm_num)
  exact hcover z (mem_closedBall_iff_norm.mpr hz)

/-- Consequence for the Riemann zeta function on the hard tile
`‖z - (1/2 + 14i)‖ ≤ 1/16`. -/
theorem hard_tile_zeta_nonzero {z : ℂ} (hz : ‖z - c‖ ≤ 1 / 16) :
    riemannZeta z ≠ 0 := by
  intro hzeta
  have hball : z ∈ Metric.ball c (1 / 4) :=
    mem_ball_iff_norm.mpr (hz.trans_lt (by norm_num))
  have hd := quarter_ball_domain hball
  have hxi : xiCompleted z = 0 := by
    rw [← xiProduct_eq_xiCompleted hd.1 hd.2]
    simp [F_xiProduct, F_zetaActual, hzeta]
  exact hard_tile_nonzero hz hxi

end Reinmann.HardTileXi

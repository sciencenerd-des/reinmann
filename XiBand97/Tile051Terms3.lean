/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile051Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨51,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (76371/2560)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 16 ((69/80), (76371/2560))
  have he : value ((69/80), (76371/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-715655399/268435456), (-24753314537/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term22 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-280098890283119/9007199254740992), (1120246641566765/18014398509481984)), (28082651/18014398509481984), by norm_num⟩
  | 1 => ⟨((6605511177/68719476736), (-13209266385/68719476736)), (333/68719476736), by norm_num⟩
  | 2 => ⟨((-10208957737/68719476736), (20415201587/68719476736)), (517/68719476736), by norm_num⟩
  | 3 => ⟨((10518773923/68719476736), (-21034751599/68719476736)), (535/68719476736), by norm_num⟩
  | 4 => ⟨((-2032123547/17179869184), (16254827547/68719476736)), (415/68719476736), by norm_num⟩
  | 5 => ⟨((10050208247/137438953472), (-2512218101/17179869184)), (129/34359738368), by norm_num⟩
  | 6 => ⟨((-10355206785/274877906944), (10353830403/137438953472)), (267/137438953472), by norm_num⟩
  | 7 => ⟨((4572626255/274877906944), (-18288073903/549755813888)), (473/549755813888), by norm_num⟩
  | 8 => ⟨((-7067090939/1099511627776), (7066151603/549755813888)), (367/1099511627776), by norm_num⟩
  | 9 => ⟨((2427186457/1099511627776), (-19414910743/4398046511104)), (507/4398046511104), by norm_num⟩
  | 10 => ⟨((-6002029105/8796093022208), (12002462667/8796093022208)), (315/8796093022208), by norm_num⟩
  | 11 => ⟨((6746373371/35184372088832), (-13490953327/35184372088832)), (89/8796093022208), by norm_num⟩
  | 12 => ⟨((-217222151/4398046511104), (13900369823/140737488355328)), (23/8796093022208), by norm_num⟩
  | 13 => ⟨((6611129999/562949953421312), (-13220502535/562949953421312)), (11/17592186044416), by norm_num⟩
  | 14 => ⟨((-2919326213/1125899906842624), (2918938185/562949953421312)), (39/281474976710656), by norm_num⟩
  | 15 => ⟨((9625345343/18014398509481984), (-19248131943/18014398509481984)), (517/18014398509481984), by norm_num⟩
  | 16 => ⟨((-7438087771/72057594037927936), (7437099123/36028797018963968)), (401/72057594037927936), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (1325079818127/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777852571214307/633825300114114700748351602688), (3133264979187/633825300114114700748351602688)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888711100088661/39614081257132168796771975168), (3524104057621/39614081257132168796771975168)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472105424760373/618970019642690137449562112), (1871670861823/1237940039285380274899124224)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770087889791699/154742504910672534362390528), (3742195943863/154742504910672534362390528)), (13831/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548519490403007/9671406556917033397649408), (109596615859/302231454903657293676544)), (12971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628941964264569/302231454903657293676544), (3067488705273/604462909807314587353088)), (11353/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886321702207185/75557863725914323419136), (4982389094185/75557863725914323419136)), (9227/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296436595084715/4722366482869645213696), (3734797733261/4722366482869645213696)), (13847/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404982880161039/147573952589676412928), (5132108286883/590295810358705651712)), (2381/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821578630862887/73786976294838206464), (6410280605137/73786976294838206464)), (23823/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910261779790393/4611686018427387904), (7204895496543/9223372036854775808)), (6705/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795885814564613/576460752303423488), (7196565414639/1152921504606846976)), (6711/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192642824576945/144115188075855872), (3143816952625/72057594037927936)), (5879/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488729537103345/36028797018963968), (9412755445849/36028797018963968)), (35327/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485621207546919/9007199254740992), (2933321587079/2251799813685248)), (44251/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220670334762381/4503599627370496), (23368834580699/4503599627370496)), (5549/281474976710656), by norm_num⟩
  | 1 => ⟨((551293889963933/562949953421312), (17404865226091/1125899906842624)), (66941/1125899906842624), by norm_num⟩
  | 0 => ⟨((2158833071244819/2251799813685248), (34325154053509/1125899906842624)), (135301/1125899906842624), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2158833071244819/2251799813685248), (34325154053509/1125899906842624)), (516132359031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2067611577370853/2251799813685248), (32908021972439/562949953421312)), (535361/2251799813685248), by norm_num⟩
  | 2 => ⟨((1890794466914767/2251799813685248), (120865108532423/1125899906842624)), (1045733/2251799813685248), by norm_num⟩
  | 3 => ⟨((390428824634057/562949953421312), (50744093028889/281474976710656)), (1980685/2251799813685248), by norm_num⟩
  | 4 => ⟨((1009928604360035/2251799813685248), (563089673687227/2251799813685248)), (1730763/1125899906842624), by norm_num⟩
  | 5 => ⟨((78036000471673/562949953421312), (505089630810297/2251799813685248)), (4836171/2251799813685248), by norm_num⟩
  | 6 => ⟨((-280098890283119/9007199254740992), (1120246641566765/18014398509481984)), (28082651/18014398509481984), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-24753314537/268435456)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-725947119/268435456), (-12554643899/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term23 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((915387045799237/18014398509481984), (784247716543895/18014398509481984)), (8257309/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2737227237/17179869184), (-4690178259/34359738368)), (199/68719476736), by norm_num⟩
  | 2 => ⟨((8582560169/34359738368), (14706026803/68719476736)), (157/34359738368), by norm_num⟩
  | 3 => ⟨((-1121273657/4294967296), (-3842555165/17179869184)), (331/68719476736), by norm_num⟩
  | 4 => ⟨((1757873533/8589934592), (6024154747/34359738368)), (261/68719476736), by norm_num⟩
  | 5 => ⟨((-1102360459/8589934592), (-3777740473/34359738368)), (329/137438953472), by norm_num⟩
  | 6 => ⟨((1152148281/17179869184), (1974180567/34359738368)), (173/137438953472), by norm_num⟩
  | 7 => ⟨((-8257266905/274877906944), (-7074321999/274877906944)), (39/68719476736), by norm_num⟩
  | 8 => ⟨((6472653155/549755813888), (11090747855/1099511627776)), (247/1099511627776), by norm_num⟩
  | 9 => ⟨((-2254996281/549755813888), (-15455544777/4398046511104)), (173/2199023255552), by norm_num⟩
  | 10 => ⟨((11312844473/8796093022208), (4846077125/4398046511104)), (219/8796093022208), by norm_num⟩
  | 11 => ⟨((-6449337893/17592186044416), (-11050797669/35184372088832)), (63/8796093022208), by norm_num⟩
  | 12 => ⟨((13481241107/140737488355328), (11549904057/140737488355328)), (133/70368744177664), by norm_num⟩
  | 13 => ⟨((-3251565655/140737488355328), (-11142971497/562949953421312)), (259/562949953421312), by norm_num⟩
  | 14 => ⟨((182058309/35184372088832), (9982492193/2251799813685248)), (117/1125899906842624), by norm_num⟩
  | 15 => ⟨((-9742383357/9007199254740992), (-8346679075/9007199254740992)), (197/9007199254740992), by norm_num⟩
  | 16 => ⟨((3818398333/18014398509481984), (13085481981/72057594037927936)), (311/72057594037927936), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (922761460233/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888899077209723/316912650057057350374175801344), (1090905244473/633825300114114700748351602688)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888650149654525/39614081257132168796771975168), (19171603785/618970019642690137449562112)), (12983/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888357297589173/2475880078570760549798248448), (1303309610963/2475880078570760549798248448)), (13795/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27656623297985/2417851639229258349412352), (1302905440699/154742504910672534362390528)), (3449/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((12097343118477/75557863725914323419136), (1221044593139/9671406556917033397649408)), (12935/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157229028859515/75557863725914323419136), (533992478319/302231454903657293676544)), (1415/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((58944952927241/2361183241434822606848), (108416967319/4722366482869645213696)), (4599/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296374888003443/4722366482869645213696), (1300300454321/4722366482869645213696)), (13799/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619847808282759/590295810358705651712), (1786771276431/590295810358705651712)), (18977/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821475690066643/73786976294838206464), (2231752680441/73786976294838206464)), (23725/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820410083898087/9223372036854775808), (2508370773385/9223372036854775808)), (13349/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397915265719297/288230376151711744), (2505435335313/1152921504606846976)), (13353/576460752303423488), by norm_num⟩
  | 5 => ⟨((298137335836837/36028797018963968), (1094479042687/72057594037927936)), (23377/144115188075855872), by norm_num⟩
  | 4 => ⟨((186074477701753/4503599627370496), (3276852782455/36028797018963968)), (8771/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485465399643801/9007199254740992), (255285549921/562949953421312)), (2743/562949953421312), by norm_num⟩
  | 2 => ⟨((34693633285803/70368744177664), (8134747534195/4503599627370496)), (43937/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102421345544723/1125899906842624), (3029125071129/562949953421312)), (132061/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158498564967803/2251799813685248), (2986579151457/281474976710656)), (265131/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2158498564967803/2251799813685248), (2986579151457/281474976710656)), (1011394509322356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1034404827803543/1125899906842624), (45805327975633/2251799813685248)), (256959/1125899906842624), by norm_num⟩
  | 2 => ⟨((1899758245410401/2251799813685248), (84166011754973/2251799813685248)), (965219/2251799813685248), by norm_num⟩
  | 3 => ⟨((399902052968811/562949953421312), (142015354866859/2251799813685248)), (212599/281474976710656), by norm_num⟩
  | 4 => ⟨((1127355129462495/2251799813685248), (201766539349361/2251799813685248)), (2630909/2251799813685248), by norm_num⟩
  | 5 => ⟨((136581840451331/562949953421312), (404054644124227/4503599627370496)), (3105781/2251799813685248), by norm_num⟩
  | 6 => ⟨((915387045799237/18014398509481984), (784247716543895/18014398509481984)), (8257309/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-12554643899/134217728)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-735800759/268435456), (-12725054293/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term24 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((491844022148435/9007199254740992), (-38653430001543/1125899906842624)), (14456539/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2981389577/17179869184), (3748861123/34359738368)), (177/68719476736), by norm_num⟩
  | 2 => ⟨((9475016565/34359738368), (-2978520613/17179869184)), (71/17179869184), by norm_num⟩
  | 3 => ⟨((-627335681/2147483648), (12621198457/68719476736)), (303/68719476736), by norm_num⟩
  | 4 => ⟨((498426641/2147483648), (-10027712025/68719476736)), (243/68719476736), by norm_num⟩
  | 5 => ⟨((-2534442713/17179869184), (3186860861/34359738368)), (311/137438953472), by norm_num⟩
  | 6 => ⟨((671216281/8589934592), (-1688002561/34359738368)), (83/68719476736), by norm_num⟩
  | 7 => ⟨((-19503190609/549755813888), (1532732287/68719476736)), (19/34359738368), by norm_num⟩
  | 8 => ⟨((15495547405/1099511627776), (-9742211431/1099511627776)), (243/1099511627776), by norm_num⟩
  | 9 => ⟨((-10943485285/2199023255552), (3440141373/1099511627776)), (87/1099511627776), by norm_num⟩
  | 10 => ⟨((13911594131/8796093022208), (-4373181787/4398046511104)), (223/8796093022208), by norm_num⟩
  | 11 => ⟨((-16077016369/35184372088832), (10107787003/35184372088832)), (259/35184372088832), by norm_num⟩
  | 12 => ⟨((8515603909/70368744177664), (-10707697067/140737488355328)), (277/140737488355328), by norm_num⟩
  | 13 => ⟨((-16654183151/562949953421312), (10470657747/562949953421312)), (273/562949953421312), by norm_num⟩
  | 14 => ⟨((3780563611/562949953421312), (-4753759137/1125899906842624)), (125/1125899906842624), by norm_num⟩
  | 15 => ⟨((-12815823643/9007199254740992), (4028720649/4503599627370496)), (107/4503599627370496), by norm_num⟩
  | 16 => ⟨((20364688709/72057594037927936), (-6401745545/36028797018963968)), (171/36028797018963968), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (-731107726141/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888870932509275/316912650057057350374175801344), (-54017270385/39614081257132168796771975168)), (11537/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888586851968885/39614081257132168796771975168), (-486040866087/19807040628566084398385987584)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944145039981525/1237940039285380274899124224), (-516274112119/1237940039285380274899124224)), (13791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221244589261995/19342813113834066795298816), (-258055925659/38685626227668133590597632)), (431/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774198491958259/4835703278458516698824704), (-120920632423/1208925819614629174706176)), (12931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257777205669821/604462909807314587353088), (-846099925373/604462909807314587353088)), (2829/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1886149158529307/75557863725914323419136), (-1374266778597/75557863725914323419136)), (18389/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296307957299799/4722366482869645213696), (-515067761983/2361183241434822606848)), (6897/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619755893259661/590295810358705651712), (-707759786397/295147905179352825856)), (18969/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821360968124899/73786976294838206464), (-221003177677/9223372036854775808)), (23715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820281257657777/9223372036854775808), (-993570548535/4611686018427387904)), (6671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((795766265534953/576460752303423488), (-1984784430553/1152921504606846976)), (13345/576460752303423488), by norm_num⟩
  | 5 => ⟨((298109302142665/36028797018963968), (-1734038849851/144115188075855872)), (11681/72057594037927936), by norm_num⟩
  | 4 => ⟨((744214139427769/18014398509481984), (-2595772514327/36028797018963968)), (35057/36028797018963968), by norm_num⟩
  | 3 => ⟨((92828570083439/562949953421312), (-808871608371/2251799813685248)), (5481/1125899906842624), by norm_num⟩
  | 2 => ⟨((1109989704424677/2251799813685248), (-3221684265757/2251799813685248)), (43887/2251799813685248), by norm_num⟩
  | 1 => ⟨((2204231543723031/2251799813685248), (-9596332618641/2251799813685248)), (131861/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157310092215139/2251799813685248), (-18919521583525/2251799813685248)), (16533/140737488355328), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2157310092215139/2251799813685248), (-18919521583525/2251799813685248)), (63068390429449037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1033313187387717/1125899906842624), (-18125623158847/1125899906842624)), (255651/1125899906842624), by norm_num⟩
  | 2 => ⟨((1896096799595289/2251799813685248), (-8317544626227/281474976710656)), (954975/2251799813685248), by norm_num⟩
  | 3 => ⟨((1594615752475771/2251799813685248), (-28014692337095/562949953421312)), (1664687/2251799813685248), by norm_num⟩
  | 4 => ⟨((1123653272763645/2251799813685248), (-79354602358517/1125899906842624)), (1261693/1125899906842624), by norm_num⟩
  | 5 => ⟨((1099039140344737/4503599627370496), (-39598128620091/562949953421312)), (2874053/2251799813685248), by norm_num⟩
  | 6 => ⟨((491844022148435/9007199254740992), (-38653430001543/1125899906842624)), (14456539/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-12725054293/134217728)), (1/134217728), by norm_num⟩, -15, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-745252095/268435456), (-12888507187/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term25 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-231958940567559/18014398509481984), (-548753269688391/9007199254740992)), (376185/281474976710656), by norm_num⟩
  | 1 => ⟨((2848232369/68719476736), (26952646387/137438953472)), (593/137438953472), by norm_num⟩
  | 2 => ⟨((-2292026579/34359738368), (-5422326367/17179869184)), (479/68719476736), by norm_num⟩
  | 3 => ⟨((4918499297/68719476736), (23271727009/68719476736)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((-989502405/17179869184), (-4681799967/17179869184)), (417/68719476736), by norm_num⟩
  | 5 => ⟨((318508537/8589934592), (24112212369/137438953472)), (539/137438953472), by norm_num⟩
  | 6 => ⟨((-5467943625/274877906944), (-12935702913/137438953472)), (145/68719476736), by norm_num⟩
  | 7 => ⟨((2514375935/274877906944), (743543239/17179869184)), (535/549755813888), by norm_num⟩
  | 8 => ⟨((-1011682989/274877906944), (-9573493427/549755813888)), (27/68719476736), by norm_num⟩
  | 9 => ⟨((5789301183/4398046511104), (27391899157/4398046511104)), (155/1099511627776), by norm_num⟩
  | 10 => ⟨((-931752081/2199023255552), (-8817112199/4398046511104)), (401/8796093022208), by norm_num⟩
  | 11 => ⟨((4362464361/35184372088832), (20640864947/35184372088832)), (471/35184372088832), by norm_num⟩
  | 12 => ⟨((-4680743689/140737488355328), (-22146793727/140737488355328)), (507/140737488355328), by norm_num⟩
  | 13 => ⟨((4635917755/562949953421312), (2741837651/70368744177664)), (63/70368744177664), by norm_num⟩
  | 14 => ⟨((-4263555311/2251799813685248), (-20172879841/2251799813685248)), (465/2251799813685248), by norm_num⟩
  | 15 => ⟨((1829847349/4503599627370496), (17315732063/9007199254740992)), (401/9007199254740992), by norm_num⟩
  | 16 => ⟨((-5890051395/72057594037927936), (-27868595663/72057594037927936)), (81/9007199254740992), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (-2317452892447/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222210502938723/79228162514264337593543950336), (-2739409100715/633825300114114700748351602688)), (1445/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888521597649267/39614081257132168796771975168), (-3081093959465/39614081257132168796771975168)), (13007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888220499924685/2475880078570760549798248448), (-3272735088379/2475880078570760549798248448)), (6911/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442471714044373/38685626227668133590597632), (-1635846193095/77371252455336267181195264)), (13825/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548331197131203/9671406556917033397649408), (-3066104147535/9671406556917033397649408)), (3241/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628859673769853/302231454903657293676544), (-2681734121919/604462909807314587353088)), (11347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943027293571179/37778931862957161709568), (-1088935820287/18889465931478580854784)), (18443/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296236546448001/4722366482869645213696), (-3264993098317/4722366482869645213696)), (6919/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619656920749497/590295810358705651712), (-4486418990879/590295810358705651712)), (19035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227654510080541/9223372036854775808), (-5603607142535/73786976294838206464)), (23805/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820139151269649/9223372036854775808), (-3148995192297/4611686018427387904)), (26797/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795694209837793/576460752303423488), (-6290413568481/1152921504606846976)), (26817/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18629825973051/2251799813685248), (-171737456165/4503599627370496)), (23489/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488231278740475/36028797018963968), (-8226397924327/36028797018963968)), (35279/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485003068113887/9007199254740992), (-10253307178071/9007199254740992)), (44181/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109724022526477/2251799813685248), (-20417782170741/4503599627370496)), (88609/4503599627370496), by norm_num⟩
  | 1 => ⟨((275422110487043/281474976710656), (-30405425753989/2251799813685248)), (133531/2251799813685248), by norm_num⟩
  | 0 => ⟨((538843368265775/562949953421312), (-59930845069603/2251799813685248)), (16847/140737488355328), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((538843368265775/562949953421312), (-59930845069603/2251799813685248)), (64266205370855287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2061481253342971/2251799813685248), (-57364492570001/1125899906842624)), (8287/35184372088832), by norm_num⟩
  | 2 => ⟨((940701343011441/1125899906842624), (-210064545386127/2251799813685248)), (512565/1125899906842624), by norm_num⟩
  | 3 => ⟨((1552335572861201/2251799813685248), (-87755580563983/562949953421312)), (952139/1125899906842624), by norm_num⟩
  | 4 => ⟨((1015422883576085/2251799813685248), (-241986181184753/1125899906842624)), (3219223/2251799813685248), by norm_num⟩
  | 5 => ⟨((707748868358183/4503599627370496), (-218241696611609/1125899906842624)), (2143569/1125899906842624), by norm_num⟩
  | 6 => ⟨((-231958940567559/18014398509481984), (-548753269688391/9007199254740992)), (376185/281474976710656), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-12888507187/134217728)), (1/134217728), by norm_num⟩, -15, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-754332693/268435456), (-13045548487/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term26 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1064416575571875/18014398509481984), (-25928380848659/2251799813685248)), (23360783/18014398509481984), by norm_num⟩
  | 1 => ⟨((26458526305/137438953472), (5156077141/137438953472)), (583/137438953472), by norm_num⟩
  | 2 => ⟨((-21551108239/68719476736), (-4199749271/68719476736)), (477/68719476736), by norm_num⟩
  | 3 => ⟨((2925649631/8589934592), (4561062853/68719476736)), (65/8589934592), by norm_num⟩
  | 4 => ⟨((-4766024467/17179869184), (-3715095773/68719476736)), (213/34359738368), by norm_num⟩
  | 5 => ⟨((12422534253/68719476736), (4841656271/137438953472)), (279/68719476736), by norm_num⟩
  | 6 => ⟨((-26982543895/274877906944), (-328637157/17179869184)), (19/8589934592), by norm_num⟩
  | 7 => ⟨((25117637957/549755813888), (4894772953/549755813888)), (71/68719476736), by norm_num⟩
  | 8 => ⟨((-10229461159/549755813888), (-3986910703/1099511627776)), (29/68719476736), by norm_num⟩
  | 9 => ⟨((14812698661/2199023255552), (180413055/137438953472)), (169/1099511627776), by norm_num⟩
  | 10 => ⟨((-9652240445/4398046511104), (-3761940159/8796093022208)), (443/8796093022208), by norm_num⟩
  | 11 => ⟨((22871222675/35184372088832), (4457005167/35184372088832)), (527/35184372088832), by norm_num⟩
  | 12 => ⟨((-12419441903/70368744177664), (-4840451035/140737488355328)), (287/70368744177664), by norm_num⟩
  | 13 => ⟨((778148859/17592186044416), (1213127443/140737488355328)), (577/562949953421312), by norm_num⟩
  | 14 => ⟨((-2897467547/281474976710656), (-4517127225/2251799813685248)), (539/2251799813685248), by norm_num⟩
  | 15 => ⟨((10069577583/4503599627370496), (981149105/2251799813685248)), (235/4503599627370496), by norm_num⟩
  | 16 => ⟨((-16403827931/36028797018963968), (-1598339251/18014398509481984)), (385/36028797018963968), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (-3841572172743/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777624899764949/633825300114114700748351602688), (-1135195628575/158456325028528675187087900672)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888454715972535/39614081257132168796771975168), (-5107117478615/39614081257132168796771975168)), (13033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944074470301591/1237940039285380274899124224), (-1356188589583/618970019642690137449562112)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221226842224521/19342813113834066795298816), (-1355750512047/38685626227668133590597632)), (433/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774131496336913/4835703278458516698824704), (-317637693865/604462909807314587353088)), (3249/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628829537878285/302231454903657293676544), (-555633371237/75557863725914323419136)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885955535096343/75557863725914323419136), (-3609873075401/37778931862957161709568)), (18495/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648080643535511/2361183241434822606848), (-676469889683/590295810358705651712)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619551864652939/590295810358705651712), (-7436214019271/590295810358705651712)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910551201479069/36893488147419103232), (-1160979922249/9223372036854775808)), (5973/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909992764449249/4611686018427387904), (-10438612107967/9223372036854775808)), (26905/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591230763591293/1152921504606846976), (-10425862882039/1152921504606846976)), (26939/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596083194504747/72057594037927936), (-4554150285545/72057594037927936)), (23611/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488008554732879/36028797018963968), (-13633825533541/36028797018963968)), (17747/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484708965359339/9007199254740992), (-16992263171853/9007199254740992)), (44503/9007199254740992), by norm_num⟩
  | 2 => ⟨((554703263306285/1125899906842624), (-8458693120903/1125899906842624)), (11177/562949953421312), by norm_num⟩
  | 1 => ⟨((68822140646039/70368744177664), (-12594708199549/562949953421312)), (67573/1125899906842624), by norm_num⟩
  | 0 => ⟨((1076389757746615/1125899906842624), (-24817679347181/562949953421312)), (68603/562949953421312), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076389757746615/1125899906842624), (-24817679347181/562949953421312)), (261699678661155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((256717145707763/281474976710656), (-189810804303259/2251799813685248)), (274443/1125899906842624), by norm_num⟩
  | 2 => ⟨((464273975285985/562949953421312), (-173115523357223/1125899906842624)), (546875/1125899906842624), by norm_num⟩
  | 3 => ⟨((739170779770291/1125899906842624), (-571084741897975/2251799813685248)), (535103/562949953421312), by norm_num⟩
  | 4 => ⟨((825719929869441/2251799813685248), (-749852009789083/2251799813685248)), (3896099/2251799813685248), by norm_num⟩
  | 5 => ⟨((53084366235575/2251799813685248), (-549931432778817/2251799813685248)), (10904317/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1064416575571875/18014398509481984), (-25928380848659/2251799813685248)), (23360783/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-13045548487/134217728)), (1/134217728), by norm_num⟩, -15, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-763070545/268435456), (-26393324531/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
private theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term27 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-312333323868395/9007199254740992), (210902602431563/4503599627370496)), (12008715/9007199254740992), by norm_num⟩
  | 1 => ⟨((3926848157/34359738368), (-10606393009/68719476736)), (303/68719476736), by norm_num⟩
  | 2 => ⟨((-12942250923/68719476736), (17478470547/68719476736)), (501/68719476736), by norm_num⟩
  | 3 => ⟨((14218515907/68719476736), (-9601031265/34359738368)), (69/8589934592), by norm_num⟩
  | 4 => ⟨((-11715477227/68719476736), (15821716397/68719476736)), (457/68719476736), by norm_num⟩
  | 5 => ⟨((3861230175/34359738368), (-10429159237/68719476736)), (303/68719476736), by norm_num⟩
  | 6 => ⟨((-8483989839/137438953472), (5728801249/68719476736)), (335/137438953472), by norm_num⟩
  | 7 => ⟨((7989098995/274877906944), (-10789253917/274877906944)), (317/274877906944), by norm_num⟩
  | 8 => ⟨((-13165383497/1099511627776), (2222476301/137438953472)), (131/274877906944), by norm_num⟩
  | 9 => ⟨((4821217365/1099511627776), (-13022078803/2199023255552)), (385/2199023255552), by norm_num⟩
  | 10 => ⟨((-12711956745/8796093022208), (4291864739/2199023255552)), (255/4398046511104), by norm_num⟩
  | 11 => ⟨((3808775971/8796093022208), (-5143740375/8796093022208)), (307/17592186044416), by norm_num⟩
  | 12 => ⟨((-8368736173/70368744177664), (11301952771/70368744177664)), (339/70368744177664), by norm_num⟩
  | 13 => ⟨((2121691477/70368744177664), (-11461351569/281474976710656)), (345/281474976710656), by norm_num⟩
  | 14 => ⟨((-7991713129/1125899906842624), (1349098037/140737488355328)), (327/1125899906842624), by norm_num⟩
  | 15 => ⟨((7023835401/4503599627370496), (-18971336731/9007199254740992)), (577/9007199254740992), by norm_num⟩
  | 16 => ⟨((-2893676957/9007199254740992), (15631607749/36028797018963968)), (477/36028797018963968), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (179774174381/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777579643304433/633825300114114700748351602688), (849934853869/158456325028528675187087900672)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((118025255031489/2475880078570760549798248448), (3823761847719/39614081257132168796771975168)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888095513677537/2475880078570760549798248448), (2030784120113/1237940039285380274899124224)), (13833/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769761730327995/154742504910672534362390528), (4060242683309/154742504910672534362390528)), (13837/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548213743474891/9671406556917033397649408), (1902534801017/4835703278458516698824704)), (811/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1257616427592623/604462909807314587353088), (416003567493/75557863725914323419136)), (5679/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((942943532551591/37778931862957161709568), (675676093257/9444732965739290427392)), (9231/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296110662804499/4722366482869645213696), (4051749803817/4722366482869645213696)), (13853/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101217714874877/36893488147419103232), (1391852424583/147573952589676412928)), (19057/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821018639305265/73786976294838206464), (6953646541649/73786976294838206464)), (23837/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819893723369145/9223372036854775808), (1953784293667/2305843009213693952)), (26837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591141986730029/1152921504606846976), (3902751273893/576460752303423488)), (13431/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192092106817597/144115188075855872), (6818988627083/144115188075855872)), (11767/72057594037927936), by norm_num⟩
  | 4 => ⟨((92993993899029/2251799813685248), (10206862842569/36028797018963968)), (17679/18014398509481984), by norm_num⟩
  | 3 => ⟨((185573743095731/1125899906842624), (3180203887283/2251799813685248)), (44299/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218610179916027/4503599627370496), (12664315198219/2251799813685248)), (11113/562949953421312), by norm_num⟩
  | 1 => ⟨((2202091354652601/2251799813685248), (294620713335/17592186044416)), (33531/562949953421312), by norm_num⟩
  | 0 => ⟨((269086170604417/281474976710656), (37151478647197/1125899906842624)), (271333/2251799813685248), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((269086170604417/281474976710656), (37151478647197/1125899906842624)), (1035053261763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2055489366276073/2251799813685248), (35516297890105/562949953421312)), (33543/140737488355328), by norm_num⟩
  | 2 => ⟨((233416287199801/281474976710656), (129680040292975/1125899906842624)), (1047519/2251799813685248), by norm_num⟩
  | 3 => ⟨((1518631793174755/2251799813685248), (430154522193601/2251799813685248)), (1978639/2251799813685248), by norm_num⟩
  | 4 => ⟨((235501574938631/562949953421312), (580199296057325/2251799813685248)), (3424767/2251799813685248), by norm_num⟩
  | 5 => ⟨((489159509015553/4503599627370496), (121358787907675/562949953421312)), (9260503/4503599627370496), by norm_num⟩
  | 6 => ⟨((-312333323868395/9007199254740992), (210902602431563/4503599627370496)), (12008715/9007199254740992), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-26393324531/268435456)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
private theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 16 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨51,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile051Terms3

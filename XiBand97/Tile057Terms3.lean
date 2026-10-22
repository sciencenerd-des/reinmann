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
namespace Reinmann.XiBand97.Tile057Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨57,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (78519/2560)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (78519/2560))
  have he : value ((69/80), (78519/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-715655399/268435456), (-25449522779/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((530902117547563/9007199254740992), (-10380291591387/281474976710656)), (7770585/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3130037277/17179869184), (979184631/8589934592)), (185/68719476736), by norm_num⟩
  | 2 => ⟨((19350156207/68719476736), (-189168829/1073741824)), (9/2147483648), by norm_num⟩
  | 3 => ⟨((-19937384771/68719476736), (6237108067/34359738368)), (299/68719476736), by norm_num⟩
  | 4 => ⟨((3851706421/17179869184), (-4819791455/34359738368)), (233/68719476736), by norm_num⟩
  | 5 => ⟨((-2381157613/17179869184), (11918544003/137438953472)), (145/68719476736), by norm_num⟩
  | 6 => ⟨((19627358053/274877906944), (-1535030229/34359738368)), (301/274877906944), by norm_num⟩
  | 7 => ⟨((-17333999139/549755813888), (10845356811/549755813888)), (67/137438953472), by norm_num⟩
  | 8 => ⟨((6697515903/549755813888), (-8380864581/1099511627776)), (13/68719476736), by norm_num⟩
  | 9 => ⟨((-18402049767/4398046511104), (11513603651/4398046511104)), (9/137438953472), by norm_num⟩
  | 10 => ⟨((2844075853/2199023255552), (-7117807535/8796093022208)), (45/2199023255552), by norm_num⟩
  | 11 => ⟨((-6393570329/17592186044416), (8000525551/35184372088832)), (51/8796093022208), by norm_num⟩
  | 12 => ⟨((6587599105/70368744177664), (-257603793/4398046511104)), (53/35184372088832), by norm_num⟩
  | 13 => ⟨((-3132699769/140737488355328), (7840140409/562949953421312)), (203/562949953421312), by norm_num⟩
  | 14 => ⟨((11066637691/2251799813685248), (-3462029549/1125899906842624)), (181/2251799813685248), by norm_num⟩
  | 15 => ⟨((-9121985845/9007199254740992), (5707349499/9007199254740992)), (75/4503599627370496), by norm_num⟩
  | 16 => ⟨((14098222753/72057594037927936), (-8820829799/72057594037927936)), (117/36028797018963968), by norm_num⟩
  | _ => zero

private def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790251486516269/5070602400912917605986812821504), (-728265035259/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27779022483927/9903520314283042199192993792), (-53813912267/39614081257132168796771975168)), (11537/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888716842529935/39614081257132168796771975168), (-60526750303/2475880078570760549798248448)), (12979/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472107039272243/618970019642690137449562112), (-514337541335/1237940039285380274899124224)), (13791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770094748666909/154742504910672534362390528), (-32136269105/4835703278458516698824704)), (431/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774263173064945/4835703278458516698824704), (-963754081485/9671406556917033397649408)), (12931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257890352429623/604462909807314587353088), (-842950980575/604462909807314587353088)), (2829/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943166468674883/37778931862957161709568), (-1369169712655/75557863725914323419136)), (18389/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648222858688197/2361183241434822606848), (-513165088973/2361183241434822606848)), (6897/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202493149141443/73786976294838206464), (-1410315546863/590295810358705651712)), (2371/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1821597412753673/73786976294838206464), (-880781405809/36893488147419103232)), (23715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455136752575181/2305843009213693952), (-989964443609/4611686018427387904)), (6671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198974746824463/144115188075855872), (-988822423137/576460752303423488)), (13345/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192669124363681/144115188075855872), (-1727873201707/144115188075855872)), (11681/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488775459121199/36028797018963968), (-1293343240165/18014398509481984)), (35057/36028797018963968), by norm_num⟩
  | 3 => ⟨((371422471445359/2251799813685248), (-3224411950699/9007199254740992)), (43847/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220841315487547/4503599627370496), (-6422063932727/4503599627370496)), (21943/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205515384352863/2251799813685248), (-4783234933787/1125899906842624)), (8241/140737488355328), by norm_num⟩
  | 0 => ⟨((539960478307125/562949953421312), (-9434036317747/1125899906842624)), (264515/2251799813685248), by norm_num⟩
  | _ => zero

private def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539960478307125/562949953421312), (-9434036317747/1125899906842624)), (1009044655806731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258935155870919/281474976710656), (-18097547505027/1125899906842624)), (511859/2251799813685248), by norm_num⟩
  | 2 => ⟨((476255087770675/562949953421312), (-8324170302557/281474976710656)), (958197/2251799813685248), by norm_num⟩
  | 3 => ⟨((804837943429069/1125899906842624), (-220069987681/4398046511104)), (838971/1125899906842624), by norm_num⟩
  | 4 => ⟨((1145022129216053/2251799813685248), (-161090316665319/2251799813685248)), (1283421/1125899906842624), by norm_num⟩
  | 5 => ⟨((570710406165245/2251799813685248), (-327652531567345/4503599627370496)), (5955387/4503599627370496), by norm_num⟩
  | 6 => ⟨((530902117547563/9007199254740992), (-10380291591387/281474976710656)), (7770585/9007199254740992), by norm_num⟩
  | _ => zero

private def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-715655399/268435456), (-25449522779/268435456)), (1/134217728), by norm_num⟩, -15, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-725947119/268435456), (-25815508093/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-415235817527225/18014398509481984), (-565808523345987/9007199254740992)), (13292655/9007199254740992), by norm_num⟩
  | 1 => ⟨((4966619507/68719476736), (6767613801/34359738368)), (319/68719476736), by norm_num⟩
  | 2 => ⟨((-973300421/8589934592), (-2652476741/8589934592)), (251/34359738368), by norm_num⟩
  | 3 => ⟨((8138074241/68719476736), (11089100639/34359738368)), (527/68719476736), by norm_num⟩
  | 4 => ⟨((-3189610589/34359738368), (-1086556591/4294967296)), (415/68719476736), by norm_num⟩
  | 5 => ⟨((4000402221/68719476736), (2725513525/17179869184)), (523/137438953472), by norm_num⟩
  | 6 => ⟨((-8362158683/274877906944), (-2848610631/34359738368)), (549/274877906944), by norm_num⟩
  | 7 => ⟨((7491285767/549755813888), (20415547787/549755813888)), (247/274877906944), by norm_num⟩
  | 8 => ⟨((-2936110399/549755813888), (-250050125/17179869184)), (389/1099511627776), by norm_num⟩
  | 9 => ⟨((8183250821/4398046511104), (22301318275/4398046511104)), (17/137438953472), by norm_num⟩
  | 10 => ⟨((-5131707123/8796093022208), (-3496282723/2199023255552)), (343/8796093022208), by norm_num⟩
  | 11 => ⟨((1462767091/8796093022208), (15945562553/35184372088832)), (393/35184372088832), by norm_num⟩
  | 12 => ⟨((-6115330337/140737488355328), (-8332869859/70368744177664)), (103/35184372088832), by norm_num⟩
  | 13 => ⟨((5899871661/562949953421312), (16078563227/562949953421312)), (25/35184372088832), by norm_num⟩
  | 14 => ⟨((-5285432419/2251799813685248), (-7202034571/1125899906842624)), (45/281474976710656), by norm_num⟩
  | 15 => ⟨((2209659037/4503599627370496), (376365629/281474976710656)), (151/4503599627370496), by norm_num⟩
  | 16 => ⟨((-3464186565/36028797018963968), (-18881476045/72057594037927936)), (119/18014398509481984), by norm_num⟩
  | _ => zero

private def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580453031364711/10141204801825835211973625643008), (-2504247765191/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777794091241953/633825300114114700748351602688), (-2960566883467/633825300114114700748351602688)), (5781/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888645356823567/39614081257132168796771975168), (-3329854608225/39614081257132168796771975168)), (6505/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118021994219537/154742504910672534362390528), (-884248540029/618970019642690137449562112)), (13825/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885009083242629/77371252455336267181195264), (-220993511241/9671406556917033397649408)), (3457/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548454197244479/9671406556917033397649408), (-3313736466671/9671406556917033397649408)), (1621/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314456717351487/151115727451828646838272), (-2898353658625/604462909807314587353088)), (5675/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943114558378233/37778931862957161709568), (-147113746101/2361183241434822606848)), (9225/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648183637280193/2361183241434822606848), (-1764409574607/2361183241434822606848)), (13843/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809918198693721/295147905179352825856), (-4849023149543/590295810358705651712)), (9521/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455365003783873/18446744073709551616), (-6056627314193/73786976294838206464)), (23815/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820390512786899/9223372036854775808), (-3403657430097/4611686018427387904)), (13405/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795819538175613/576460752303423488), (-3399666969681/576460752303423488)), (1677/72057594037927936), by norm_num⟩
  | 5 => ⟨((596263697742621/72057594037927936), (-5940449191621/144115188075855872)), (1469/9007199254740992), by norm_num⟩
  | 4 => ⟨((1488557499701245/36028797018963968), (-2223191019771/9007199254740992)), (17653/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485408090097591/9007199254740992), (-11084672222737/9007199254740992)), (11055/2251799813685248), by norm_num⟩
  | 2 => ⟨((555062465349861/1125899906842624), (-5518932984453/1125899906842624)), (88707/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102279580807275/1125899906842624), (-8220097890151/562949953421312)), (4179/70368744177664), by norm_num⟩
  | 0 => ⟨((1078828485972051/1125899906842624), (-32416447641819/1125899906842624)), (270141/2251799813685248), by norm_num⟩
  | _ => zero

private def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1078828485972051/1125899906842624), (-32416447641819/1125899906842624)), (1030506142623137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1032791697556797/1125899906842624), (-124244746508907/2251799813685248)), (533251/2251799813685248), by norm_num⟩
  | 2 => ⟨((943955581508047/1125899906842624), (-227940231417719/2251799813685248)), (32411/70368744177664), by norm_num⟩
  | 3 => ⟨((779876565624619/1125899906842624), (-382210625277309/2251799813685248)), (1949073/2251799813685248), by norm_num⟩
  | 4 => ⟨((253879680430439/562949953421312), (-529491312637919/2251799813685248)), (1680891/1125899906842624), by norm_num⟩
  | 5 => ⟨((666948473345353/4503599627370496), (-119395236136207/562949953421312)), (9226375/4503599627370496), by norm_num⟩
  | 6 => ⟨((-415235817527225/18014398509481984), (-565808523345987/9007199254740992)), (13292655/9007199254740992), by norm_num⟩
  | _ => zero

private def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-725947119/268435456), (-25815508093/268435456)), (1/134217728), by norm_num⟩, -15, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-735800759/268435456), (-26165914759/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1157630499516153/18014398509481984), (100101117421179/18014398509481984)), (24285875/18014398509481984), by norm_num⟩
  | 1 => ⟨((28068634363/137438953472), (-303389301/17179869184)), (591/137438953472), by norm_num⟩
  | 2 => ⟨((-11150453869/34359738368), (482093765/17179869184)), (471/68719476736), by norm_num⟩
  | 3 => ⟨((11812247543/34359738368), (-1021413291/34359738368)), (125/17179869184), by norm_num⟩
  | 4 => ⟨((-18769979275/68719476736), (1623053211/68719476736)), (399/68719476736), by norm_num⟩
  | 5 => ⟨((23860801813/137438953472), (-1031630095/68719476736)), (509/137438953472), by norm_num⟩
  | 6 => ⟨((-12638485433/137438953472), (2185717317/274877906944)), (541/274877906944), by norm_num⟩
  | 7 => ⟨((22951878309/549755813888), (-496166235/137438953472)), (493/549755813888), by norm_num⟩
  | 8 => ⟨((-9117788097/549755813888), (394210751/274877906944)), (197/549755813888), by norm_num⟩
  | 9 => ⟨((12878587283/2199023255552), (-1113620433/2199023255552)), (279/2199023255552), by norm_num⟩
  | 10 => ⟨((-8185768729/4398046511104), (1415658273/8796093022208)), (89/2199023255552), by norm_num⟩
  | 11 => ⟨((18919864483/35184372088832), (-818006945/17592186044416)), (413/35184372088832), by norm_num⟩
  | 12 => ⟨((-20042782597/140737488355328), (1733113403/140737488355328)), (439/140737488355328), by norm_num⟩
  | 13 => ⟨((19599089847/562949953421312), (-1694746981/562949953421312)), (431/562949953421312), by norm_num⟩
  | 14 => ⟨((-17796275017/2251799813685248), (384714081/562949953421312)), (393/2251799813685248), by norm_num⟩
  | 15 => ⟨((15082005329/9007199254740992), (-2608303059/18014398509481984)), (669/18014398509481984), by norm_num⟩
  | 16 => ⟨((-23965712403/72057594037927936), (1036165941/36028797018963968)), (533/72057594037927936), by norm_num⟩
  | _ => zero

private def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580405215526759/10141204801825835211973625643008), (1989958469001/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111108149422435/39614081257132168796771975168), (2352422130563/316912650057057350374175801344)), (181/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((236071664803683/4951760157141521099596496896), (661458527661/4951760157141521099596496896)), (3259/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888274860102483/2475880078570760549798248448), (1405205609449/618970019642690137449562112)), (13855/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110621284361577/9671406556917033397649408), (87797669227/2417851639229258349412352)), (13859/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548380827242041/9671406556917033397649408), (164561821519/302231454903657293676544)), (12999/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628881033448717/302231454903657293676544), (4605849662639/604462909807314587353088)), (11379/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471530670472363/18889465931478580854784), (7480979305617/75557863725914323419136)), (18499/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296286460219951/4722366482869645213696), (5607649998965/4722366482869645213696)), (3471/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((404930918551339/147573952589676412928), (7705508562007/590295810358705651712)), (19103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910658355031039/36893488147419103232), (9624374088013/73786976294838206464)), (5975/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820225999728489/9223372036854775808), (5408549168721/4611686018427387904)), (26915/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795735227350575/576460752303423488), (5402102069629/576460752303423488)), (26951/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192375243067597/144115188075855872), (4719592474603/72057594037927936)), (11811/72057594037927936), by norm_num⟩
  | 4 => ⟨((744160044149049/18014398509481984), (14129820847313/36028797018963968)), (35513/36028797018963968), by norm_num⟩
  | 3 => ⟨((742547666354167/4503599627370496), (4402917832297/2251799813685248)), (11133/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109788336653385/2251799813685248), (8767951456831/1125899906842624)), (5593/281474976710656), by norm_num⟩
  | 1 => ⟨((1101715631948797/1125899906842624), (3264364906235/140737488355328)), (33823/562949953421312), by norm_num⟩
  | 0 => ⟨((1077467545779431/1125899906842624), (25738508890427/562949953421312)), (137425/1125899906842624), by norm_num⟩
  | _ => zero

private def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077467545779431/1125899906842624), (25738508890427/562949953421312)), (524234776023482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257191252483655/281474976710656), (98525305269669/1125899906842624)), (137797/562949953421312), by norm_num⟩
  | 2 => ⟨((1862776972471809/2251799813685248), (360100879442493/2251799813685248)), (551869/1125899906842624), by norm_num⟩
  | 3 => ⟨((370843956187359/562949953421312), (148944773402065/562949953421312)), (544781/562949953421312), by norm_num⟩
  | 4 => ⟨((819544924843991/2251799813685248), (392470191612315/1125899906842624)), (4024103/2251799813685248), by norm_num⟩
  | 5 => ⟨((12328466829795/1125899906842624), (571359766056683/2251799813685248)), (2867313/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1157630499516153/18014398509481984), (100101117421179/18014398509481984)), (24285875/18014398509481984), by norm_num⟩
  | _ => zero

private def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-735800759/268435456), (-26165914759/268435456)), (1/134217728), by norm_num⟩, -16, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-745252095/268435456), (-26502015053/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-258429951258333/18014398509481984), (1091576618646907/18014398509481984)), (24203669/18014398509481984), by norm_num⟩
  | 1 => ⟨((6346541767/137438953472), (-26807018957/137438953472)), (597/137438953472), by norm_num⟩
  | 2 => ⟨((-2553591233/34359738368), (10786058157/34359738368)), (241/34359738368), by norm_num⟩
  | 3 => ⟨((5479795391/68719476736), (-11572993949/34359738368)), (519/68719476736), by norm_num⟩
  | 4 => ⟨((-4409695227/68719476736), (9313007611/34359738368)), (105/17179869184), by norm_num⟩
  | 5 => ⟨((177428267/4294967296), (-5995483011/34359738368)), (543/137438953472), by norm_num⟩
  | 6 => ⟨((-3045970983/137438953472), (12865810215/137438953472)), (585/274877906944), by norm_num⟩
  | 7 => ⟨((175082185/17179869184), (-11832412991/274877906944)), (135/137438953472), by norm_num⟩
  | 8 => ⟨((-4508542501/1099511627776), (19043534063/1099511627776)), (109/274877906944), by norm_num⟩
  | 9 => ⟨((3224986325/2199023255552), (-13621949203/2199023255552)), (313/2199023255552), by norm_num⟩
  | 10 => ⟨((-4152332207/8796093022208), (17538945191/8796093022208)), (405/8796093022208), by norm_num⟩
  | 11 => ⟨((2430153047/17592186044416), (-20529340607/35184372088832)), (119/8796093022208), by norm_num⟩
  | 12 => ⟨((-2607453631/70368744177664), (11013566363/70368744177664)), (513/140737488355328), by norm_num⟩
  | 13 => ⟨((1291241455/140737488355328), (-21816186161/562949953421312)), (255/281474976710656), by norm_num⟩
  | 14 => ⟨((-1187527401/562949953421312), (626996377/70368744177664)), (471/2251799813685248), by norm_num⟩
  | 15 => ⟨((509667099/1125899906842624), (-8611086849/4503599627370496)), (203/4503599627370496), by norm_num⟩
  | 16 => ⟨((-6562220415/72057594037927936), (6929504821/18014398509481984)), (41/4503599627370496), by norm_num⟩
  | _ => zero

private def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580359351911831/10141204801825835211973625643008), (1174477225853/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111105244581573/39614081257132168796771975168), (1388323193783/316912650057057350374175801344)), (1445/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944260733838825/19807040628566084398385987584), (780743909191/9903520314283042199192993792)), (13007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888220353758453/2475880078570760549798248448), (829305436041/618970019642690137449562112)), (6911/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769886700941887/154742504910672534362390528), (3316164839909/154742504910672534362390528)), (6913/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774165520984911/4835703278458516698824704), (3107781986987/9671406556917033397649408)), (3241/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((78607450134671/37778931862957161709568), (2718187149779/604462909807314587353088)), (11347/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943027166438111/37778931862957161709568), (2207475591169/37778931862957161709568)), (4611/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324059085001097/1180591620717411303424), (827343574449/1180591620717411303424)), (6919/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202457076417779/73786976294838206464), (2273701488343/295147905179352825856)), (19035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821235655628497/73786976294838206464), (5679776909239/73786976294838206464)), (11903/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820138620627993/9223372036854775808), (1595899655991/2305843009213693952)), (26799/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397846955891607/288230376151711744), (99623725703/18014398509481984)), (6705/288230376151711744), by norm_num⟩
  | 5 => ⟨((298077066810755/36028797018963968), (696287397569/18014398509481984)), (23491/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488230239853075/36028797018963968), (8338216680885/36028797018963968)), (8821/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485001514610779/9007199254740992), (10392674977321/9007199254740992)), (11047/2251799813685248), by norm_num⟩
  | 2 => ⟨((2219444178147959/4503599627370496), (20695303074577/4503599627370496)), (88625/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203369200464257/2251799813685248), (30818678238463/2251799813685248)), (133565/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077675336698383/1125899906842624), (60745281816393/2251799813685248)), (67413/562949953421312), by norm_num⟩
  | _ => zero

private def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1077675336698383/1125899906842624), (60745281816393/2251799813685248)), (257160188915061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((257674245054903/281474976710656), (116286877077555/2251799813685248)), (265377/1125899906842624), by norm_num⟩
  | 2 => ⟨((1881083032608747/2251799813685248), (13306748263609/140737488355328)), (1026569/2251799813685248), by norm_num⟩
  | 3 => ⟨((775633684154597/1125899906842624), (177856651204925/1125899906842624)), (1909253/2251799813685248), by norm_num⟩
  | 4 => ⟨((1012478320947357/2251799813685248), (122525642632243/562949953421312)), (3233777/2251799813685248), by norm_num⟩
  | 5 => ⟨((348570870278519/2251799813685248), (881460642612021/4503599627370496)), (2157835/1125899906842624), by norm_num⟩
  | 6 => ⟨((-258429951258333/18014398509481984), (1091576618646907/18014398509481984)), (24203669/18014398509481984), by norm_num⟩
  | _ => zero

private def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/268435456), (-26502015053/268435456)), (1/134217728), by norm_num⟩, -16, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-754332693/268435456), (-3353116437/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((894837839283443/18014398509481984), (612596006743703/18014398509481984)), (13872173/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2780407015/17179869184), (-7613742557/68719476736)), (87/34359738368), by norm_num⟩
  | 2 => ⟨((4529417235/17179869184), (12403154133/68719476736)), (143/34359738368), by norm_num⟩
  | 3 => ⟨((-19676371483/68719476736), (-6735112257/34359738368)), (313/68719476736), by norm_num⟩
  | 4 => ⟨((4006719863/17179869184), (2742955741/17179869184)), (257/68719476736), by norm_num⟩
  | 5 => ⟨((-2610856023/17179869184), (-7149451683/68719476736)), (169/68719476736), by norm_num⟩
  | 6 => ⟨((5670947313/68719476736), (121320853/2147483648)), (185/137438953472), by norm_num⟩
  | 7 => ⟨((-5278998231/137438953472), (-3613943325/137438953472)), (87/137438953472), by norm_num⟩
  | 8 => ⟨((17199485861/1099511627776), (2943644059/274877906944)), (143/549755813888), by norm_num⟩
  | 9 => ⟨((-6226398371/1099511627776), (-4262522897/1099511627776)), (209/2199023255552), by norm_num⟩
  | 10 => ⟨((8114482791/4398046511104), (11110168875/8796093022208)), (275/8796093022208), by norm_num⟩
  | 11 => ⟨((-19227467847/35184372088832), (-6581455045/17592186044416)), (41/4398046511104), by norm_num⟩
  | 12 => ⟨((10440824405/70368744177664), (3573835983/35184372088832)), (45/17592186044416), by norm_num⟩
  | 13 => ⟨((-5233417515/140737488355328), (-3582739275/140737488355328)), (91/140737488355328), by norm_num⟩
  | 14 => ⟨((4871708425/562949953421312), (13340469061/2251799813685248)), (341/2251799813685248), by norm_num⟩
  | 15 => ⟨((-16930662777/9007199254740992), (-5795271475/4503599627370496)), (149/4503599627370496), by norm_num⟩
  | 16 => ⟨((13790433445/36028797018963968), (9440776965/36028797018963968)), (61/9007199254740992), by norm_num⟩
  | _ => zero

private def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580315287342547/10141204801825835211973625643008), (781968007055/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777635505113949/633825300114114700748351602688), (924295182679/633825300114114700748351602688)), (11537/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888467222513403/39614081257132168796771975168), (1039581239405/39614081257132168796771975168)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888163005392311/2475880078570760549798248448), (552119322993/1237940039285380274899124224)), (431/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((884914837601007/77371252455336267181195264), (1103882866455/154742504910672534362390528)), (6897/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548277922846897/9671406556917033397649408), (517256165673/4835703278458516698824704)), (3233/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628836532556287/302231454903657293676544), (113102576731/75557863725914323419136)), (11317/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942990000557445/37778931862957161709568), (734812868439/37778931862957161709568)), (18391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648090575662411/2361183241434822606848), (1101600393895/4722366482869645213696)), (13795/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809790817937369/295147905179352825856), (1513695530205/590295810358705651712)), (18971/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910571648768441/36893488147419103232), (945306573243/36893488147419103232)), (23717/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910018292950515/4611686018427387904), (265608838047/1152921504606846976)), (417/144115188075855872), by norm_num⟩
  | 6 => ⟨((1591288118631263/1152921504606846976), (2122287390337/1152921504606846976)), (26695/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192223639075795/144115188075855872), (1854099416627/144115188075855872)), (11683/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488108506532311/36028797018963968), (693838863729/9007199254740992)), (35065/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484858422359707/9007199254740992), (1729539409443/4503599627370496)), (43859/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109592526239831/2251799813685248), (860988076073/562949953421312)), (87801/4503599627370496), by norm_num⟩
  | 1 => ⟨((2203047586213001/2251799813685248), (10256550492861/2251799813685248)), (131915/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154972324408135/2251799813685248), (10106912153727/1125899906842624)), (264693/2251799813685248), by norm_num⟩
  | _ => zero

private def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2154972324408135/2251799813685248), (10106912153727/1125899906842624)), (1009723671920012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2062126967082575/2251799813685248), (38689257977797/2251799813685248)), (511375/2251799813685248), by norm_num⟩
  | 2 => ⟨((117985365080295/140737488355328), (70860794754095/2251799813685248)), (954175/2251799813685248), by norm_num⟩
  | 3 => ⟨((1580353012581625/2251799813685248), (59405186469105/1125899906842624)), (1659893/2251799813685248), by norm_num⟩
  | 4 => ⟨((1102851028126617/2251799813685248), (41691612562033/562949953421312)), (1252523/1125899906842624), by norm_num⟩
  | 5 => ⟨((527786410714081/2251799813685248), (20419061010155/281474976710656)), (353101/281474976710656), by norm_num⟩
  | 6 => ⟨((894837839283443/18014398509481984), (612596006743703/18014398509481984)), (13872173/18014398509481984), by norm_num⟩
  | _ => zero

private def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-754332693/268435456), (-3353116437/33554432)), (1/134217728), by norm_num⟩, -16, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-763070545/268435456), (-27135659463/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((890903817592821/18014398509481984), (-69392152383183/2251799813685248)), (13044741/18014398509481984), by norm_num⟩
  | 1 => ⟨((-11200995049/68719476736), (6979529237/68719476736)), (165/68719476736), by norm_num⟩
  | 2 => ⟨((18458326209/68719476736), (-11501694883/68719476736)), (137/34359738368), by norm_num⟩
  | 3 => ⟨((-10139272001/34359738368), (12635903339/68719476736)), (303/68719476736), by norm_num⟩
  | 4 => ⟨((4177173307/17179869184), (-10411469015/68719476736)), (251/68719476736), by norm_num⟩
  | 5 => ⟨((-11013825425/68719476736), (3431450341/34359738368)), (167/68719476736), by norm_num⟩
  | 6 => ⟨((12099923957/137438953472), (-7539667025/137438953472)), (185/137438953472), by norm_num⟩
  | 7 => ⟨((-1424263409/34359738368), (7099860725/274877906944)), (11/17179869184), by norm_num⟩
  | 8 => ⟨((18776559401/1099511627776), (-11699991361/1099511627776)), (73/274877906944), by norm_num⟩
  | 9 => ⟨((-13752105931/2199023255552), (2142292381/549755813888)), (27/274877906944), by norm_num⟩
  | 10 => ⟨((18129879085/8796093022208), (-11297033931/8796093022208)), (287/8796093022208), by norm_num⟩
  | 11 => ⟨((-10864204339/17592186044416), (846208657/2199023255552)), (173/17592186044416), by norm_num⟩
  | 12 => ⟨((11935548393/70368744177664), (-7437241835/70368744177664)), (3/1099511627776), by norm_num⟩
  | 13 => ⟨((-12103883203/281474976710656), (7542134099/281474976710656)), (49/70368744177664), by norm_num⟩
  | 14 => ⟨((5698917783/562949953421312), (-7102183889/1125899906842624)), (93/562949953421312), by norm_num⟩
  | 15 => ⟨((-20034883547/9007199254740992), (12484074395/9007199254740992)), (329/9007199254740992), by norm_num⟩
  | 16 => ⟨((8253963475/18014398509481984), (-10286368157/36028797018963968)), (273/36028797018963968), by norm_num⟩
  | _ => zero

private def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580272885984747/10141204801825835211973625643008), (-362936279595/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888792725490239/316912650057057350374175801344), (-428971784773/316912650057057350374175801344)), (11537/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236051366094025/4951760157141521099596496896), (-964951201399/39614081257132168796771975168)), (12979/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888103215173837/2475880078570760549798248448), (-1024963554003/2475880078570760549798248448)), (13791/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769769909607215/154742504910672534362390528), (-1024629504955/154742504910672534362390528)), (431/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548221918751101/9671406556917033397649408), (-480117692957/4835703278458516698824704)), (12931/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314406021915769/151115727451828646838272), (-839851358945/604462909807314587353088)), (2829/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235737557716181/9444732965739290427392), (-42627935625/2361183241434822606848)), (18389/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296121539602643/4722366482869645213696), (-511244682487/2361183241434822606848)), (6897/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202437467409319/73786976294838206464), (-1404979286573/590295810358705651712)), (2371/73786976294838206464), by norm_num⟩
  | 8 => ⟨((56907532217471/2305843009213693952), (-1754809913629/73786976294838206464)), (11857/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1819921679068777/9223372036854775808), (-493054642127/2305843009213693952)), (6671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99448336898757/72057594037927936), (-1969793234745/1152921504606846976)), (13345/576460752303423488), by norm_num⟩
  | 5 => ⟨((298030863102891/36028797018963968), (-1720844557587/144115188075855872)), (11681/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487958626778043/36028797018963968), (-2575827719313/36028797018963968)), (2191/2251799813685248), by norm_num⟩
  | 3 => ⟨((371167942784897/2251799813685248), (-200643030667/562949953421312)), (43847/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218813837675257/4503599627370496), (-1598044369405/1125899906842624)), (21943/1125899906842624), by norm_num⟩
  | 1 => ⟨((2202495955953699/2251799813685248), (-2379394474421/562949953421312)), (131857/2251799813685248), by norm_num⟩
  | 0 => ⟨((538472417397315/562949953421312), (-2344282187985/281474976710656)), (132259/1125899906842624), by norm_num⟩
  | _ => zero

private def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538472417397315/562949953421312), (-2344282187985/281474976710656)), (504528049949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030040272318191/1125899906842624), (-35877613323287/2251799813685248)), (63805/281474976710656), by norm_num⟩
  | 2 => ⟨((942056354536271/1125899906842624), (-4102872108463/140737488355328)), (950229/2251799813685248), by norm_num⟩
  | 3 => ⟨((787274980595241/1125899906842624), (-109853793379307/2251799813685248)), (205693/281474976710656), by norm_num⟩
  | 4 => ⟨((547815065391505/1125899906842624), (-76814237682583/1125899906842624)), (2461819/2251799813685248), by norm_num⟩
  | 5 => ⟨((1045211628391281/4503599627370496), (-298996359327097/4503599627370496)), (5463095/4503599627370496), by norm_num⟩
  | 6 => ⟨((890903817592821/18014398509481984), (-69392152383183/2251799813685248)), (13044741/18014398509481984), by norm_num⟩
  | _ => zero

private def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-763070545/268435456), (-27135659463/268435456)), (1/134217728), by norm_num⟩, -16, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 16 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 16 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 16 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 16 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 16 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨57,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiBand97.Tile057Terms3

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile064Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨64,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (16205/512)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (16205/512))
  have he : value ((69/80), (16205/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_log2 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
private theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2567700857/4294967296), (-94224620441/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
private theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term2 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-309190727910529/562949953421312), (-65324067679451/2251799813685248)), (1548081/2251799813685248), by norm_num⟩
  | 1 => ⟨((104645840481/274877906944), (172726415/8589934592)), (133/274877906944), by norm_num⟩
  | 2 => ⟨((-72534969287/549755813888), (-1915597241/274877906944)), (47/274877906944), by norm_num⟩
  | 3 => ⟨((33518272969/1099511627776), (1770387769/1099511627776)), (89/2199023255552), by norm_num⟩
  | 4 => ⟨((-92932385623/17592186044416), (-2454278581/8796093022208)), (63/8796093022208), by norm_num⟩
  | 5 => ⟨((103065313723/140737488355328), (1360941023/35184372088832)), (71/70368744177664), by norm_num⟩
  | 6 => ⟨((-47626287747/562949953421312), (-5031106309/1125899906842624)), (133/1125899906842624), by norm_num⟩
  | 7 => ⟨((9432007735/1125899906842624), (3985482461/9007199254740992)), (107/9007199254740992), by norm_num⟩
  | 8 => ⟨((-13075539137/18014398509481984), (-2762525931/72057594037927936)), (75/72057594037927936), by norm_num⟩
  | 9 => ⟨((128899883905/2305843009213693952), (1702077387/576460752303423488)), (187/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-35738636441/9223372036854775808), (-1887664227/9223372036854775808)), (105/18446744073709551616), by norm_num⟩
  | 11 => ⟨((36032196489/147573952589676412928), (3806339307/295147905179352825856)), (107/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-33300820541/2361183241434822606848), (-3517804479/4722366482869645213696)), (101/4722366482869645213696), by norm_num⟩
  | 13 => ⟨((28409070607/37778931862957161709568), (1500526927/37778931862957161709568)), (175/151115727451828646838272), by norm_num⟩
  | 14 => ⟨((-22504762507/604462909807314587353088), (-4754678897/2417851639229258349412352)), (141/2417851639229258349412352), by norm_num⟩
  | 15 => ⟨((66556214105/38685626227668133590597632), (1757702545/19342813113834066795298816)), (53/19342813113834066795298816), by norm_num⟩
  | 16 => ⟨((-92266504311/1237940039285380274899124224), (-4873386253/1237940039285380274899124224)), (149/1237940039285380274899124224), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583197014481433/10141204801825835211973625643008), (-2011768480783/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1781036287197059/633825300114114700748351602688), (-2386626019077/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892291817835423/39614081257132168796771975168), (-1342395604059/9903520314283042199192993792)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892225064999931/2475880078570760549798248448), (-5704828650257/2475880078570760549798248448)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773889965593293/154742504910672534362390528), (-5704431569083/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388020641428177/2417851639229258349412352), (-5347482397555/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261000248712407/604462909807314587353088), (-1169656140637/151115727451828646838272)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472845788126935/18889465931478580854784), (-7601971944907/75557863725914323419136)), (579/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325057608538117/1180591620717411303424), (-5700784395403/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625144395464029/590295810358705651712), (-7837448538047/590295810358705651712)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828089243842095/73786976294838206464), (-9795113319959/73786976294838206464)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456960115982315/2305843009213693952), (-11017164818475/9223372036854775808)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399769778792159/288230376151711744), (-11014237029939/1152921504606846976)), (843/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199026280324071/144115188075855872), (-9634155801509/144115188075855872)), (739/72057594037927936), by norm_num⟩
  | 4 => ⟨((374570883589249/9007199254740992), (-14444610931113/36028797018963968)), (2221/36028797018963968), by norm_num⟩
  | 3 => ⟨((374381658554989/2251799813685248), (-9022064919491/4503599627370496)), (2785/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122185002098943/2251799813685248), (-18026591303785/2251799813685248)), (1399/1125899906842624), by norm_num⟩
  | 1 => ⟨((560111799481565/562949953421312), (-26995734014773/1125899906842624)), (2115/562949953421312), by norm_num⟩
  | 0 => ⟨((69633296033481/70368744177664), (-53813022176319/1125899906842624)), (8591/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((69633296033481/70368744177664), (-53813022176319/1125899906842624)), (32772068503951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((274979131301649/281474976710656), (-53250603623097/562949953421312)), (17825/1125899906842624), by norm_num⟩
  | 2 => ⟨((1064458614832425/1125899906842624), (-208086770578115/1125899906842624)), (38201/1125899906842624), by norm_num⟩
  | 3 => ⟨((483956003539159/562949953421312), (-393462605740305/1125899906842624)), (43177/562949953421312), by norm_num⟩
  | 4 => ⟨((694591789712031/1125899906842624), (-84562841269867/140737488355328)), (104415/562949953421312), by norm_num⟩
  | 5 => ⟨((22028432787085/1125899906842624), (-1669396148735453/2251799813685248)), (508617/1125899906842624), by norm_num⟩
  | 6 => ⟨((-309190727910529/562949953421312), (-65324067679451/2251799813685248)), (1548081/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/4294967296), (-94224620441/4294967296)), (1/2147483648), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log3 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
private theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1017427393/1073741824), (-37335622511/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
private theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term3 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1706170476559685/4503599627370496), (185389175296273/2251799813685248)), (4589417/4503599627370496), by norm_num⟩
  | 1 => ⟨((14300688569/34359738368), (-12431080699/137438953472)), (39/34359738368), by norm_num⟩
  | 2 => ⟨((-62843648793/274877906944), (13656938017/274877906944)), (87/137438953472), by norm_num⟩
  | 3 => ⟨((46027203219/549755813888), (-20004906575/1099511627776)), (257/1099511627776), by norm_num⟩
  | 4 => ⟨((-101132102139/4398046511104), (21977636197/4398046511104)), (285/4398046511104), by norm_num⟩
  | 5 => ⟨((88883976151/17592186044416), (-9657960481/8796093022208)), (253/17592186044416), by norm_num⟩
  | 6 => ⟨((-32549676155/35184372088832), (14147138757/70368744177664)), (187/70368744177664), by norm_num⟩
  | 7 => ⟨((81735941065/562949953421312), (-4440634425/140737488355328)), (237/562949953421312), by norm_num⟩
  | 8 => ⟨((-2806128415/140737488355328), (19514142195/4503599627370496)), (263/4503599627370496), by norm_num⟩
  | 9 => ⟨((43844937391/18014398509481984), (-19056423483/36028797018963968)), (259/36028797018963968), by norm_num⟩
  | 10 => ⟨((-38534869611/144115188075855872), (16748496813/288230376151711744)), (115/144115188075855872), by norm_num⟩
  | 11 => ⟨((61578009159/2305843009213693952), (-1672736765/288230376151711744)), (93/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-90200476765/36893488147419103232), (2450252221/4611686018427387904)), (275/36893488147419103232), by norm_num⟩
  | 13 => ⟨((60981755211/295147905179352825856), (-13252318525/295147905179352825856)), (47/73786976294838206464), by norm_num⟩
  | 14 => ⟨((-76566063611/4722366482869645213696), (16639039983/4722366482869645213696)), (119/2361183241434822606848), by norm_num⟩
  | 15 => ⟨((89724179603/75557863725914323419136), (-19498510717/75557863725914323419136)), (281/75557863725914323419136), by norm_num⟩
  | 16 => ⟨((-98572086303/1208925819614629174706176), (5355325871/302231454903657293676544)), (39/151115727451828646838272), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395685368349727/2535301200456458802993406410752), (3813530767701/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780497253525523/633825300114114700748351602688), (70648595699/9903520314283042199192993792)), (1449/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236460691657271/4951760157141521099596496896), (5086236411529/39614081257132168796771975168)), (815/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891581031213393/2475880078570760549798248448), (1350899951957/618970019642690137449562112)), (433/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886623046721639/77371252455336267181195264), (5403007367155/154742504910672534362390528)), (1733/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551479107385927/9671406556917033397649408), (5064689742609/9671406556917033397649408)), (1625/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260472394574663/604462909807314587353088), (1107743410117/151115727451828646838272)), (1423/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890525712022035/75557863725914323419136), (3599575332537/37778931862957161709568)), (2313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324896909036031/1180591620717411303424), (5398328718509/4722366482869645213696)), (217/590295810358705651712), by norm_num⟩
  | 9 => ⟨((101516312960363/36893488147419103232), (3710510203669/295147905179352825856)), (597/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826985698049341/73786976294838206464), (9273751608493/73786976294838206464)), (747/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826599923690433/9223372036854775808), (5214748856741/4611686018427387904)), (3363/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597839762323371/1152921504606846976), (325786029299/36028797018963968)), (421/144115188075855872), by norm_num⟩
  | 5 => ⟨((299485796087887/36028797018963968), (9117115843937/144115188075855872)), (369/18014398509481984), by norm_num⟩
  | 4 => ⟨((1496661570791907/36028797018963968), (13665875081687/36028797018963968)), (4437/36028797018963968), by norm_num⟩
  | 3 => ⟨((747751940674287/4503599627370496), (17065167584765/9007199254740992)), (5563/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120169323302213/2251799813685248), (8519673116377/1125899906842624)), (1397/562949953421312), by norm_num⟩
  | 1 => ⟨((139652230183483/140737488355328), (12747133745387/562949953421312)), (8445/1125899906842624), by norm_num⟩
  | 0 => ⟨((554096357003451/562949953421312), (50728343479041/1125899906842624)), (17141/1125899906842624), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554096357003451/562949953421312), (50728343479041/1125899906842624)), (65387730125045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((272119599419497/281474976710656), (99861062773799/1125899906842624)), (4411/140737488355328), by norm_num⟩
  | 2 => ⟨((1043443545215197/1125899906842624), (96541982939909/562949953421312)), (74491/1125899906842624), by norm_num⟩
  | 3 => ⟨((466956701826229/562949953421312), (357886552183557/1125899906842624)), (163621/1125899906842624), by norm_num⟩
  | 4 => ⟨((660903741767425/1125899906842624), (37107544600533/70368744177664)), (187731/562949953421312), by norm_num⟩
  | 5 => ⟨((149728176727073/2251799813685248), (1394057282726287/2251799813685248)), (418389/562949953421312), by norm_num⟩
  | 6 => ⟨((-1706170476559685/4503599627370496), (185389175296273/2251799813685248)), (4589417/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1017427393/1073741824), (-37335622511/1073741824)), (1/1073741824), by norm_num⟩, -6, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log4 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-2567700857/2147483648), (-94224620441/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term4 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((1354752102318587/4503599627370496), (143512551431139/4503599627370496)), (1431589/4503599627370496), by norm_num⟩
  | 1 => ⟨((-57314611821/137438953472), (-12142983447/274877906944)), (123/274877906944), by norm_num⟩
  | 2 => ⟨((79454923177/274877906944), (2104218685/68719476736)), (87/274877906944), by norm_num⟩
  | 3 => ⟨((-73431941309/549755813888), (-3889421997/274877906944)), (41/274877906944), by norm_num⟩
  | 4 => ⟨((101798286163/2199023255552), (10783767565/2199023255552)), (29/549755813888), by norm_num⟩
  | 5 => ⟨((-112897912063/8796093022208), (-5979790467/4398046511104)), (131/8796093022208), by norm_num⟩
  | 6 => ⟨((104339825917/35184372088832), (2763249935/8796093022208)), (123/35184372088832), by norm_num⟩
  | 7 => ⟨((-20663673187/35184372088832), (-8755834979/140737488355328)), (99/140737488355328), by norm_num⟩
  | 8 => ⟨((28645933619/281474976710656), (6069082329/562949953421312)), (35/281474976710656), by norm_num⟩
  | 9 => ⟨((-35299285551/2251799813685248), (-7478697431/4503599627370496)), (11/562949953421312), by norm_num⟩
  | 10 => ⟨((78296320817/36028797018963968), (4147070431/18014398509481984)), (25/9007199254740992), by norm_num⟩
  | 11 => ⟨((-78939453123/288230376151711744), (-8362269605/288230376151711744)), (103/288230376151711744), by norm_num⟩
  | 12 => ⟨((72955545823/2305843009213693952), (7728378133/2305843009213693952)), (97/2305843009213693952), by norm_num⟩
  | 13 => ⟨((-3889917761/1152921504606846976), (-412069501/1152921504606846976)), (85/18446744073709551616), by norm_num⟩
  | 14 => ⟨((98607013619/295147905179352825856), (652856715/18446744073709551616)), (17/36893488147419103232), by norm_num⟩
  | 15 => ⟨((-36452892519/1180591620717411303424), (-3861553419/1180591620717411303424)), (51/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((101068878691/37778931862957161709568), (2676624865/9444732965739290427392)), (143/37778931862957161709568), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261857485/10141204801825835211973625643008), (68738230377/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780125004971637/633825300114114700748351602688), (162932246947/633825300114114700748351602688)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59102107661667/1237940039285380274899124224), (22909909129/4951760157141521099596496896)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891137667032183/2475880078570760549798248448), (97355234445/1237940039285380274899124224)), (1723/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221600461282219/19342813113834066795298816), (97341872771/77371252455336267181195264)), (431/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((48470792973943/302231454903657293676544), (182487623071/9671406556917033397649408)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((315027849830421/151115727451828646838272), (79824143821/302231454903657293676544)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889941007363859/75557863725914323419136), (259375262531/75557863725914323419136)), (2297/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299150780504017/4722366482869645213696), (194484905003/4722366482869645213696)), (1723/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623663047942575/590295810358705651712), (267341137007/590295810358705651712)), (2369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((14267518141475/576460752303423488), (20878940675/4611686018427387904)), (2961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912884611442357/4611686018427387904), (375665113717/9223372036854775808)), (3331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597016052355667/1152921504606846976), (93867609887/288230376151711744)), (3331/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74826893447467/9007199254740992), (328317762039/144115188075855872)), (2915/144115188075855872), by norm_num⟩
  | 4 => ⟨((747803965948693/18014398509481984), (61504904673/4503599627370496)), (1093/9007199254740992), by norm_num⟩
  | 3 => ⟨((23347097744523/140737488355328), (614284349947/9007199254740992)), (2733/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237841491275933/4503599627370496), (153284707373/562949953421312)), (10933/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115447292613429/1125899906842624), (916849772543/1125899906842624)), (4101/562949953421312), by norm_num⟩
  | 0 => ⟨((1105059070275877/1125899906842624), (1822297578415/1125899906842624)), (32825/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1105059070275877/1125899906842624), (1822297578415/1125899906842624)), (125217446334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2169202112210871/2251799813685248), (447141538855/140737488355328)), (32271/1125899906842624), by norm_num⟩
  | 2 => ⟨((2089611426167183/2251799813685248), (6891840844087/1125899906842624)), (15595/281474976710656), by norm_num⟩
  | 3 => ⟨((484755116324239/562949953421312), (25581793350557/2251799813685248)), (233077/2251799813685248), by norm_num⟩
  | 4 => ⟨((834698074367733/1125899906842624), (44056865574163/2251799813685248)), (406701/2251799813685248), by norm_num⟩
  | 5 => ⟨((154595363955267/281474976710656), (65324067679441/2251799813685248)), (618939/2251799813685248), by norm_num⟩
  | 6 => ⟨((1354752102318587/4503599627370496), (143512551431139/4503599627370496)), (1431589/4503599627370496), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2567700857/2147483648), (-94224620441/2147483648)), (1/1073741824), by norm_num⟩, -7, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log5 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-745252095/536870912), (-109391396717/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term5 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((878179608461641/4503599627370496), (-701270308927331/4503599627370496)), (922153/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1347899967/4294967296), (34443695741/137438953472)), (23/34359738368), by norm_num⟩
  | 2 => ⟨((34709780945/137438953472), (-27717494885/137438953472)), (75/137438953472), by norm_num⟩
  | 3 => ⟨((-37242158257/274877906944), (29739724737/274877906944)), (163/549755813888), by norm_num⟩
  | 4 => ⟨((117068245/2147483648), (-47864240497/1099511627776)), (133/1099511627776), by norm_num⟩
  | 5 => ⟨((-19293600957/1099511627776), (15406904661/1099511627776)), (87/2199023255552), by norm_num⟩
  | 6 => ⟨((646913601/137438953472), (-16530970983/4398046511104)), (95/8796093022208), by norm_num⟩
  | 7 => ⟨((-76153949295/70368744177664), (7601591837/8796093022208)), (177/70368744177664), by norm_num⟩
  | 8 => ⟨((61282526589/281474976710656), (-48937160389/281474976710656)), (145/281474976710656), by norm_num⟩
  | 9 => ⟨((-43835742961/1125899906842624), (17502515835/562949953421312)), (105/1125899906842624), by norm_num⟩
  | 10 => ⟨((56440725313/9007199254740992), (-45070740077/9007199254740992)), (137/9007199254740992), by norm_num⟩
  | 11 => ⟨((-66063885909/72057594037927936), (52755314779/72057594037927936)), (163/72057594037927936), by norm_num⟩
  | 12 => ⟨((70883815083/576460752303423488), (-56604269125/576460752303423488)), (177/576460752303423488), by norm_num⟩
  | 13 => ⟨((-35102492115/2305843009213693952), (7007773595/576460752303423488)), (89/2305843009213693952), by norm_num⟩
  | 14 => ⟨((32283018075/18446744073709551616), (-51559206883/36893488147419103232)), (83/18446744073709551616), by norm_num⟩
  | 15 => ⟨((-6927668429/36893488147419103232), (22128357945/147573952589676412928)), (145/295147905179352825856), by norm_num⟩
  | 16 => ⟨((22299304429/1180591620717411303424), (-35614218217/2361183241434822606848)), (59/1180591620717411303424), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791083779754303/5070602400912917605986812821504), (-438886441239/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889913682529645/316912650057057350374175801344), (-64998466885/39614081257132168796771975168)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890932605692517/39614081257132168796771975168), (-1169828123739/39614081257132168796771975168)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890781905347857/2475880078570760549798248448), (-1242766304325/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772447934507821/154742504910672534362390528), (-1242568258645/154742504910672534362390528)), (863/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775365930233007/4835703278458516698824704), (-582348680075/4835703278458516698824704)), (809/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259819580285813/604462909807314587353088), (-1018899854155/604462909807314587353088)), (177/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944733406658707/37778931862957161709568), (-1655317981525/75557863725914323419136)), (575/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649397572697155/2361183241434822606848), (-1241143588303/4722366482869645213696)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623174066652779/590295810358705651712), (-853006079733/295147905179352825856)), (2373/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912815560527353/36893488147419103232), (-2131675110495/73786976294838206464)), (2967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912540828484843/4611686018427387904), (-2396979901559/9223372036854775808)), (1669/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596328530721515/1152921504606846976), (-2395537440615/1152921504606846976)), (3339/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598314381904847/72057594037927936), (-1047236786235/72057594037927936)), (2923/144115188075855872), by norm_num⟩
  | 4 => ⟨((747352867846091/18014398509481984), (-3138469682035/36028797018963968)), (2193/18014398509481984), by norm_num⟩
  | 3 => ⟨((746543344153739/4503599627370496), (-3917421987311/9007199254740992)), (5485/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235586896242937/4503599627370496), (-7817872880409/4503599627370496)), (10981/4503599627370496), by norm_num⟩
  | 1 => ⟨((278439257802067/281474976710656), (-5842233178077/1125899906842624)), (16501/2251799813685248), by norm_num⟩
  | 0 => ⟨((2203362697043685/2251799813685248), (-23200068608751/2251799813685248)), (33117/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203362697043685/2251799813685248), (-23200068608751/2251799813685248)), (126331337935637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1077864227103691/1125899906842624), (-45402051666145/2251799813685248)), (65493/2251799813685248), by norm_num⟩
  | 2 => ⟨((2062840485976315/2251799813685248), (-86930013992605/2251799813685248)), (16005/281474976710656), by norm_num⟩
  | 3 => ⟨((943190868352205/1125899906842624), (-79635299381679/1125899906842624)), (122239/1125899906842624), by norm_num⟩
  | 4 => ⟨((784498895387899/1125899906842624), (-133424448689989/1125899906842624)), (222097/1125899906842624), by norm_num⟩
  | 5 => ⟨((1061615565867779/2251799813685248), (-371867275159715/2251799813685248)), (362143/1125899906842624), by norm_num⟩
  | 6 => ⟨((878179608461641/4503599627370496), (-701270308927331/4503599627370496)), (922153/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-745252095/536870912), (-109391396717/2147483648)), (1/1073741824), by norm_num⟩, -8, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log6 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1659352607/1073741824), (-60891777621/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term6 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((473920706454953/2251799813685248), (-308296425147151/9007199254740992)), (2135543/9007199254740992), by norm_num⟩
  | 1 => ⟨((-103656239435/274877906944), (8428848863/137438953472)), (59/137438953472), by norm_num⟩
  | 2 => ⟨((23215881069/68719476736), (-15102469765/274877906944)), (107/274877906944), by norm_num⟩
  | 3 => ⟨((-55463032989/274877906944), (18039995473/549755813888)), (65/274877906944), by norm_num⟩
  | 4 => ⟨((49688207275/549755813888), (-16161666357/1099511627776)), (59/549755813888), by norm_num⟩
  | 5 => ⟨((-71223452715/2199023255552), (11583127493/2199023255552)), (43/1099511627776), by norm_num⟩
  | 6 => ⟨((85076863889/8796093022208), (-13836118913/8796093022208)), (105/8796093022208), by norm_num⟩
  | 7 => ⟨((-43553507567/17592186044416), (7083142023/17592186044416)), (55/17592186044416), by norm_num⟩
  | 8 => ⟨((78037409601/140737488355328), (-1586410849/17592186044416)), (25/35184372088832), by norm_num⟩
  | 9 => ⟨((-7768014867/70368744177664), (10106548127/562949953421312)), (81/562949953421312), by norm_num⟩
  | 10 => ⟨((2783682839/140737488355328), (-7243401323/2251799813685248)), (59/2251799813685248), by norm_num⟩
  | 11 => ⟨((-116077151095/36028797018963968), (4719430149/9007199254740992)), (39/9007199254740992), by norm_num⟩
  | 12 => ⟨((34663722439/72057594037927936), (-2818694553/36028797018963968)), (95/144115188075855872), by norm_num⟩
  | 13 => ⟨((-76441911285/1152921504606846976), (12431809615/1152921504606846976)), (107/1152921504606846976), by norm_num⟩
  | 14 => ⟨((78266010509/9223372036854775808), (-12728464341/9223372036854775808)), (111/9223372036854775808), by norm_num⟩
  | 15 => ⟨((-37395697453/36893488147419103232), (6081692403/36893488147419103232)), (27/18446744073709551616), by norm_num⟩
  | 16 => ⟨((16751023755/147573952589676412928), (-340529061/18446744073709551616)), (49/295147905179352825856), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581962720775263/10141204801825835211973625643008), (-210006193561/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779585250446973/633825300114114700748351602688), (-124374241875/316912650057057350374175801344)), (721/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945330147001839/19807040628566084398385987584), (-34975482125/4951760157141521099596496896)), (811/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890492657723739/2475880078570760549798248448), (-148622364401/1237940039285380274899124224)), (431/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886079390418749/77371252455336267181195264), (-297192014735/154742504910672534362390528)), (1723/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550460878694083/9671406556917033397649408), (-278561518311/9671406556917033397649408)), (101/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259582570993467/604462909807314587353088), (-243685347863/604462909807314587353088)), (707/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889081860187513/75557863725914323419136), (-197941879035/37778931862957161709568)), (1149/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298506594069539/4722366482869645213696), (-37102629299/590295810358705651712)), (431/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622777574162663/590295810358705651712), (-407979832105/590295810358705651712)), (2369/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912567951782165/36893488147419103232), (-31859453637/4611686018427387904)), (1481/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824525084305305/9223372036854775808), (-286581488441/4611686018427387904)), (3331/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595772641214193/1152921504606846976), (-143194810687/288230376151711744)), (833/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196143128206769/144115188075855872), (-250375241099/72057594037927936)), (729/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493978815632613/36028797018963968), (-750263876365/36028797018963968)), (2187/18014398509481984), by norm_num⟩
  | 3 => ⟨((746090358448107/4503599627370496), (-936323554091/9007199254740992)), (1367/2251799813685248), by norm_num⟩
  | 2 => ⟨((2233782970678269/4503599627370496), (-934067993411/2251799813685248)), (5469/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224828151784355/2251799813685248), (-348869158127/281474976710656)), (16413/2251799813685248), by norm_num⟩
  | 0 => ⟨((274758799388441/281474976710656), (-5537065827659/2251799813685248)), (32855/2251799813685248), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((274758799388441/281474976710656), (-5537065827659/2251799813685248)), (125331887252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2145609380277495/2251799813685248), (-5404947810001/1125899906842624)), (64305/2251799813685248), by norm_num⟩
  | 2 => ⟨((2044374784522889/2251799813685248), (-20600244569821/2251799813685248)), (123163/2251799813685248), by norm_num⟩
  | 3 => ⟨((1855868298824191/2251799813685248), (-37405297129519/2251799813685248)), (112945/1125899906842624), by norm_num⟩
  | 4 => ⟨((1528931641881947/2251799813685248), (-61656728745495/2251799813685248)), (379849/2251799813685248), by norm_num⟩
  | 5 => ⟨((1036428904187861/2251799813685248), (-83727623513425/2251799813685248)), (536623/2251799813685248), by norm_num⟩
  | 6 => ⟨((473920706454953/2251799813685248), (-308296425147151/9007199254740992)), (2135543/9007199254740992), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1659352607/1073741824), (-60891777621/1073741824)), (1/1073741824), by norm_num⟩, -9, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log7 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-901055955/536870912), (-132260975987/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
private theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term7 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((541307829733107/9007199254740992), (795985851541899/4503599627370496)), (3737847/9007199254740992), by norm_num⟩
  | 1 => ⟨((-8036318967/68719476736), (-94538387879/274877906944)), (7/8589934592), by norm_num⟩
  | 2 => ⟨((15637954639/137438953472), (718606283/2147483648)), (55/68719476736), by norm_num⟩
  | 3 => ⟨((-20286703095/274877906944), (-1864457679/8589934592)), (9/17179869184), by norm_num⟩
  | 4 => ⟨((9869025361/274877906944), (58049073921/549755813888)), (71/274877906944), by norm_num⟩
  | 5 => ⟨((-15363389289/1099511627776), (-90366625669/2199023255552)), (223/2199023255552), by norm_num⟩
  | 6 => ⟨((19930516761/4398046511104), (29307555671/2199023255552)), (73/2199023255552), by norm_num⟩
  | 7 => ⟨((-11080855669/8796093022208), (-65176994313/17592186044416)), (41/4398046511104), by norm_num⟩
  | 8 => ⟨((10781174753/35184372088832), (63414287359/70368744177664)), (161/70368744177664), by norm_num⟩
  | 9 => ⟨((-1165510965/17592186044416), (-54843780163/281474976710656)), (141/281474976710656), by norm_num⟩
  | 10 => ⟨((3628767385/281474976710656), (85376854745/2251799813685248)), (221/2251799813685248), by norm_num⟩
  | 11 => ⟨((-20541833551/9007199254740992), (-30206488753/4503599627370496)), (79/4503599627370496), by norm_num⟩
  | 12 => ⟨((26648374925/72057594037927936), (78372150709/72057594037927936)), (207/72057594037927936), by norm_num⟩
  | 13 => ⟨((-7977745111/144115188075855872), (-93849331365/576460752303423488)), (125/288230376151711744), by norm_num⟩
  | 14 => ⟨((8870842959/1152921504606846976), (52177818967/2305843009213693952)), (35/576460752303423488), by norm_num⟩
  | 15 => ⟨((-9206327117/9223372036854775808), (-27075559329/9223372036854775808)), (147/18446744073709551616), by norm_num⟩
  | 16 => ⟨((4478671343/36893488147419103232), (26343302845/73786976294838206464)), (145/147573952589676412928), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790894766046627/5070602400912917605986812821504), (809597065325/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222422275204461/79228162514264337593543950336), (958742637703/316912650057057350374175801344)), (1445/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236303410701829/4951760157141521099596496896), (269606232923/4951760157141521099596496896)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890244984353043/2475880078570760549798248448), (286407545619/309485009821345068724781056)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771910992853155/154742504910672534362390528), (2290818768571/154742504910672534362390528)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550228455757439/9671406556917033397649408), (1073586749003/4835703278458516698824704)), (405/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629689539653867/302231454903657293676544), (1878307824161/604462909807314587353088)), (709/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888750958348741/75557863725914323419136), (3051371100085/75557863725914323419136)), (2303/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298258218502949/4722366482869645213696), (2287759335799/4722366482869645213696)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((811217867208807/295147905179352825856), (786104980221/147573952589676412928)), (297/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824708119463873/73786976294838206464), (1964325962567/36893488147419103232)), (2971/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824043162077717/9223372036854775808), (1104289832299/2305843009213693952)), (209/576460752303423488), by norm_num⟩
  | 6 => ⟨((199411236129329/144115188075855872), (4413943603339/1152921504606846976)), (1673/576460752303423488), by norm_num⟩
  | 5 => ⟨((149464973541643/18014398509481984), (3858585548443/144115188075855872)), (1465/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493341947331073/36028797018963968), (5780654578059/36028797018963968)), (2199/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491381390260655/9007199254740992), (7213191204873/9007199254740992)), (5505/9007199254740992), by norm_num⟩
  | 2 => ⟨((558043659485495/1125899906842624), (14388559450937/4503599627370496)), (5515/2251799813685248), by norm_num⟩
  | 1 => ⟨((555597902172299/562949953421312), (10744242448611/1125899906842624)), (16599/2251799813685248), by norm_num⟩
  | 0 => ⟨((4283402456389/4398046511104), (10650192421767/562949953421312)), (33411/2251799813685248), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((4283402456389/4398046511104), (10650192421767/562949953421312)), (127452858931731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2135128433959279/2251799813685248), (82980587431689/2251799813685248)), (33173/1125899906842624), by norm_num⟩
  | 2 => ⟨((2021444190530139/2251799813685248), (78681155676127/1125899906842624)), (32677/562949953421312), by norm_num⟩
  | 3 => ⟨((901828327214177/1125899906842624), (70632195668143/562949953421312)), (252943/2251799813685248), by norm_num⟩
  | 4 => ⟨((176156578991795/281474976710656), (28287645500165/140737488355328)), (58585/281474976710656), by norm_num⟩
  | 5 => ⟨((790986881904715/2251799813685248), (566507749117785/2251799813685248)), (387519/1125899906842624), by norm_num⟩
  | 6 => ⟨((541307829733107/9007199254740992), (795985851541899/4503599627370496)), (3737847/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-901055955/536870912), (-132260975987/2147483648)), (1/1073741824), by norm_num⟩, -10, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_log8 : Jet 16 := fun k =>
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
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | 13 => ⟨(0, 0), 0, by norm_num⟩
  | 14 => ⟨(0, 0), 0, by norm_num⟩
  | 15 => ⟨(0, 0), 0, by norm_num⟩
  | 16 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

private theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=16) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  funext k
  fin_cases k <;> rfl

private def J_negLog8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_arg8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1925775643/1073741824), (-70668465331/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
private theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

private def J_term8 : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((-1479822780464253/9007199254740992), (-118122808661543/4503599627370496)), (3936509/4503599627370496), by norm_num⟩
  | 1 => ⟨((93908842897/274877906944), (117125261/2147483648)), (251/137438953472), by norm_num⟩
  | 2 => ⟨((-48819487263/137438953472), (-15587528531/274877906944)), (525/274877906944), by norm_num⟩
  | 3 => ⟨((33839089953/137438953472), (10804451453/274877906944)), (183/137438953472), by norm_num⟩
  | 4 => ⟨((-70366409381/549755813888), (-11233612593/549755813888)), (383/549755813888), by norm_num⟩
  | 5 => ⟨((117058267845/2199023255552), (18687712551/2199023255552)), (5/17179869184), by norm_num⟩
  | 6 => ⟨((-40569304159/2199023255552), (-6476667633/2199023255552)), (223/2199023255552), by norm_num⟩
  | 7 => ⟨((48206569363/8796093022208), (7695915273/8796093022208)), (533/17592186044416), by norm_num⟩
  | 8 => ⟨((-25060685729/17592186044416), (-500100185/2199023255552)), (557/70368744177664), by norm_num⟩
  | 9 => ⟨((46321983083/140737488355328), (14790102751/281474976710656)), (517/281474976710656), by norm_num⟩
  | 10 => ⟨((-77059084733/1125899906842624), (-12302061627/1125899906842624)), (27/70368744177664), by norm_num⟩
  | 11 => ⟨((7283630089/562949953421312), (18604667633/9007199254740992)), (41/562949953421312), by norm_num⟩
  | 12 => ⟨((-80778042567/36028797018963968), (-12895772915/36028797018963968)), (457/36028797018963968), by norm_num⟩
  | 13 => ⟨((51684066883/144115188075855872), (4125539371/72057594037927936)), (587/288230376151711744), by norm_num⟩
  | 14 => ⟨((-1919178495/36028797018963968), (-9804363371/1152921504606846976)), (351/1152921504606846976), by norm_num⟩
  | 15 => ⟨((4256874121/576460752303423488), (10873386925/9223372036854775808)), (49/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-8851920885/9223372036854775808), (-11305286235/73786976294838206464)), (205/36893488147419103232), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581639509233233/10141204801825835211973625643008), (-3886060501115/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889595601089869/316912650057057350374175801344), (-2300542054627/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890216406799541/39614081257132168796771975168), (-5175371606969/39614081257132168796771975168)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59063133592543/77371252455336267181195264), (-1374455626809/618970019642690137449562112)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442921387983477/38685626227668133590597632), (-343542896047/9671406556917033397649408)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96876020506011/604462909807314587353088), (-2575968144631/4835703278458516698824704)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259192691308907/604462909807314587353088), (-2253368567379/302231454903657293676544)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944223311684175/37778931862957161709568), (-7321184567919/75557863725914323419136)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649014347833285/2361183241434822606848), (-5488908130791/4722366482869645213696)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622118076173133/590295810358705651712), (-3772015417661/295147905179352825856)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824307953653003/73786976294838206464), (-4712606008109/36893488147419103232)), (2987/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823588728361751/9223372036854775808), (-2649181858745/2305843009213693952)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594830154896033/1152921504606846976), (-1323554115973/144115188075855872)), (6737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195311569736467/144115188075855872), (-9255548324781/144115188075855872)), (5905/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492717746338535/36028797018963968), (-6932331817753/18014398509481984)), (8875/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490580427083991/9007199254740992), (-17298181435001/9007199254740992)), (1391/1125899906842624), by norm_num⟩
  | 2 => ⟨((34851731865901/70368744177664), (-17249219296509/2251799813685248)), (2795/562949953421312), by norm_num⟩
  | 1 => ⟨((34683471122557/35184372088832), (-3218932483835/140737488355328)), (8449/562949953421312), by norm_num⟩
  | 0 => ⟨((1093596812516187/1125899906842624), (-12753417626709/281474976710656)), (34313/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093596812516187/1125899906842624), (-12753417626709/281474976710656)), (130893711570357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((529954566349293/562949953421312), (-49550041812753/562949953421312)), (69767/1125899906842624), by norm_num⟩
  | 2 => ⟨((989063535963985/1125899906842624), (-186583341996047/1125899906842624)), (71819/562949953421312), by norm_num⟩
  | 3 => ⟨((837937128273551/1125899906842624), (-327813829391111/1125899906842624)), (149985/562949953421312), by norm_num⟩
  | 4 => ⟨((528179033131747/1125899906842624), (-60992850505391/140737488355328)), (1242351/2251799813685248), by norm_num⟩
  | 5 => ⟨((36313095661559/1125899906842624), (-1831218969976283/4503599627370496)), (1121219/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1479822780464253/9007199254740992), (-118122808661543/4503599627370496)), (3936509/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1925775643/1073741824), (-70668465331/1073741824)), (1/536870912), by norm_num⟩, -10, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
private theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
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

set_option maxHeartbeats 5000000 in
private theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 16 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 16 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨64,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile064Terms0

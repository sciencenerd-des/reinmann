/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
import Reinmann.FiniteBandModel
import Reinmann.FiniteBandTileRules
import XiBand97.Data

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiBand97.Tile025Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (29683/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (29683/1280))
  have he : value ((69/80), (29683/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-20060163/33554432), (-539353095/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1156452238800277/2251799813685248), (221623525266267/1125899906842624)), (106767117/2251799813685248), by norm_num⟩
  | 1 => ⟨((1528914659/4294967296), (-586005103/4294967296)), (143/4294967296), by norm_num⟩
  | 2 => ⟨((-1059762885/8589934592), (406187785/8589934592)), (101/8589934592), by norm_num⟩
  | 3 => ⟨((489714437/17179869184), (-46924653/4294967296)), (95/34359738368), by norm_num⟩
  | 4 => ⟨((-1357776725/274877906944), (520411055/274877906944)), (67/137438953472), by norm_num⟩
  | 5 => ⟨((752911287/1099511627776), (-577154329/2199023255552)), (151/2199023255552), by norm_num⟩
  | 6 => ⟨((-695837781/8796093022208), (533403861/17592186044416)), (71/8796093022208), by norm_num⟩
  | 7 => ⟨((551220567/70368744177664), (-105636395/35184372088832)), (57/70368744177664), by norm_num⟩
  | 8 => ⟨((-191038491/281474976710656), (585772555/2251799813685248)), (5/70368744177664), by norm_num⟩
  | 9 => ⟨((235409407/4503599627370496), (-360912529/18014398509481984)), (25/4503599627370496), by norm_num⟩
  | 10 => ⟨((-1044309547/288230376151711744), (400264803/288230376151711744)), (113/288230376151711744), by norm_num⟩
  | 11 => ⟨((526443795/2305843009213693952), (-201776305/2305843009213693952)), (29/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-973074753/73786976294838206464), (372961805/73786976294838206464)), (109/73786976294838206464), by norm_num⟩
  | 13 => ⟨((207533545/295147905179352825856), (-318175291/1180591620717411303424)), (95/1180591620717411303424), by norm_num⟩
  | 14 => ⟨((-1315211809/37778931862957161709568), (504096699/37778931862957161709568)), (153/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((121551381/75557863725914323419136), (-372707419/604462909807314587353088)), (115/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((-1348047953/19342813113834066795298816), (516682193/19342813113834066795298816)), (81/9671406556917033397649408), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (3615504282611/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890519311990121/316912650057057350374175801344), (1072297418337/158456325028528675187087900672)), (46311/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892294588672771/39614081257132168796771975168), (4825051662729/39614081257132168796771975168)), (52113/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892228181902671/2475880078570760549798248448), (640787658259/309485009821345068724781056)), (27693/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773893276994779/154742504910672534362390528), (5125945390807/154742504910672534362390528)), (13851/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((194010734595959/1208925819614629174706176), (600649434447/1208925819614629174706176)), (6495/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1261003352457921/604462909807314587353088), (262760467239/37778931862957161709568)), (11371/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891388583324623/75557863725914323419136), (213470682339/2361183241434822606848)), (73945/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650117422999375/2361183241434822606848), (1280668587189/1180591620717411303424)), (27745/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((406287753005037/147573952589676412928), (7042665492069/590295810358705651712)), (76349/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914049169816139/36893488147419103232), (2200453152415/18446744073709551616)), (47755/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827851830700293/9223372036854775808), (4949973765767/4611686018427387904)), (3361/288230376151711744), by norm_num⟩
  | 6 => ⟨((1599091898698815/1152921504606846976), (9897328949687/1152921504606846976)), (107681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599519529366621/72057594037927936), (4328605706269/72057594037927936)), (47183/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498305885018043/36028797018963968), (12979900513165/36028797018963968)), (141839/36028797018963968), by norm_num⟩
  | 3 => ⟨((748780068510037/4503599627370496), (16214490645597/9007199254740992)), (177807/9007199254740992), by norm_num⟩
  | 2 => ⟨((561113419915797/1125899906842624), (16198851389267/2251799813685248)), (89285/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120307151399149/1125899906842624), (6064740816813/281474976710656)), (33721/140737488355328), by norm_num⟩
  | 0 => ⟨((557191386815695/562949953421312), (6044922645429/140737488355328)), (547201/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557191386815695/562949953421312), (6044922645429/140737488355328)), (2087406162742232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1100906331803379/1125899906842624), (95729400072747/1125899906842624)), (1130215/1125899906842624), by norm_num⟩
  | 2 => ⟨((133541026388793/140737488355328), (46802163335891/281474976710656)), (2402445/1125899906842624), by norm_num⟩
  | 3 => ⟨((982572322854051/1125899906842624), (88817968860025/281474976710656)), (2679065/562949953421312), by norm_num⟩
  | 4 => ⟨((372693104893109/562949953421312), (155022799884061/281474976710656)), (397923/35184372088832), by norm_num⟩
  | 5 => ⟨((303912461413997/2251799813685248), (1642090655252951/2251799813685248)), (30886149/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1156452238800277/2251799813685248), (221623525266267/1125899906842624)), (106767117/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-539353095/33554432)), (1/33554432), by norm_num⟩, -3, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-15897303/16777216), (-427427215/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1643756848122057/4503599627370496), (-588691523874773/4503599627370496)), (71849683/4503599627370496), by norm_num⟩
  | 1 => ⟨((-861097085/2147483648), (38548931/268435456)), (5/268435456), by norm_num⟩
  | 2 => ⟨((14781435/67108864), (-338802635/4294967296)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((-346433411/4294967296), (496283651/17179869184)), (35/8589934592), by norm_num⟩
  | 4 => ⟨((1522384011/68719476736), (-272611659/34359738368)), (5/4294967296), by norm_num⟩
  | 5 => ⟨((-669003913/137438953472), (239595615/137438953472)), (73/274877906944), by norm_num⟩
  | 6 => ⟨((489983947/549755813888), (-350963583/1099511627776)), (7/137438953472), by norm_num⟩
  | 7 => ⟨((-1230405453/8796093022208), (440654749/8796093022208)), (73/8796093022208), by norm_num⟩
  | 8 => ⟨((1351738551/70368744177664), (-242054361/35184372088832)), (83/70368744177664), by norm_num⟩
  | 9 => ⟨((-1320032519/562949953421312), (59094199/70368744177664)), (21/140737488355328), by norm_num⟩
  | 10 => ⟨((580081579/2251799813685248), (-415498325/4503599627370496)), (19/1125899906842624), by norm_num⟩
  | 11 => ⟨((-463479819/18014398509481984), (331979321/36028797018963968)), (63/36028797018963968), by norm_num⟩
  | 12 => ⟨((678912833/288230376151711744), (-486288749/576460752303423488)), (95/576460752303423488), by norm_num⟩
  | 13 => ⟨((-917983977/4611686018427387904), (328764797/4611686018427387904)), (33/2305843009213693952), by norm_num⟩
  | 14 => ⟨((576290559/36893488147419103232), (-206391455/36893488147419103232)), (85/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-675327883/590295810358705651712), (60465117/147573952589676412928)), (51/590295810358705651712), by norm_num⟩
  | 16 => ⟨((1483847023/18889465931478580854784), (-531421765/18889465931478580854784)), (115/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (-447976077835/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780508005914967/633825300114114700748351602688), (-132785631935/158456325028528675187087900672)), (46127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891698271871543/39614081257132168796771975168), (-9335697303/618970019642690137449562112)), (25947/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891595360253917/2475880078570760549798248448), (-634766020755/2475880078570760549798248448)), (13785/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886630657914733/77371252455336267181195264), (-634696960177/154742504910672534362390528)), (27571/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96968395454673/604462909807314587353088), (-74369379185/1208925819614629174706176)), (25849/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260486660566727/604462909807314587353088), (-520512299057/604462909807314587353088)), (45237/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890550672200035/75557863725914323419136), (-845694969221/75557863725914323419136)), (73515/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299607911311685/4722366482869645213696), (-634150924083/4722366482869645213696)), (55141/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812145705702933/295147905179352825856), (-871762074099/590295810358705651712)), (75825/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456756872361477/18446744073709551616), (-1089409502611/73786976294838206464)), (94789/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913326070846841/4611686018427387904), (-306295705311/2305843009213693952)), (106651/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399474619590253/288230376151711744), (-1224679429045/1152921504606846976)), (53333/576460752303423488), by norm_num⟩
  | 5 => ⟨((18718779122777/2251799813685248), (-1071028451233/144115188075855872)), (93351/144115188075855872), by norm_num⟩
  | 4 => ⟨((93547761106281/2251799813685248), (-1605411245769/36028797018963968)), (70031/18014398509481984), by norm_num⟩
  | 3 => ⟨((373914406794651/2251799813685248), (-1002392776653/4503599627370496)), (175141/9007199254740992), by norm_num⟩
  | 2 => ⟨((2240722434963057/4503599627370496), (-2001820796179/2251799813685248)), (175235/2251799813685248), by norm_num⟩
  | 1 => ⟨((2235201529605717/2251799813685248), (-5990659573873/2251799813685248)), (263089/1125899906842624), by norm_num⟩
  | 0 => ⟨((1109337154039609/1125899906842624), (-745139597113/140737488355328)), (1054255/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1109337154039609/1125899906842624), (-745139597113/140737488355328)), (4021663674361418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2185972978486943/2251799813685248), (-11746849395757/1125899906842624)), (2088657/2251799813685248), by norm_num⟩
  | 2 => ⟨((2121825341557657/2251799813685248), (-22806907794753/1125899906842624)), (4098783/2251799813685248), by norm_num⟩
  | 3 => ⟨((1998429048867771/2251799813685248), (-85961948530901/2251799813685248)), (986307/281474976710656), by norm_num⟩
  | 4 => ⟨((1770285787633747/2251799813685248), (-76289576896395/1125899906842624)), (7303845/1125899906842624), by norm_num⟩
  | 5 => ⟨((1381397828004577/2251799813685248), (-239904724928905/2251799813685248)), (24947703/2251799813685248), by norm_num⟩
  | 6 => ⟨((1643756848122057/4503599627370496), (-588691523874773/4503599627370496)), (71849683/4503599627370496), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-427427215/16777216)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-20060163/16777216), (-539353095/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1013335045048403/4503599627370496), (-455274967885413/2251799813685248)), (4623771/140737488355328), by norm_num⟩
  | 1 => ⟨((-669851617/2147483648), (150476723/536870912)), (25/536870912), by norm_num⟩
  | 2 => ⟨((928611519/4294967296), (-417210065/2147483648)), (141/4294967296), by norm_num⟩
  | 3 => ⟨((-858219275/8589934592), (771167947/8589934592)), (33/2147483648), by norm_num⟩
  | 4 => ⟨((594872271/17179869184), (-66816611/2147483648)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((-164933615/17179869184), (592815943/68719476736)), (105/68719476736), by norm_num⟩
  | 6 => ⟨((152431027/68719476736), (-273939133/137438953472)), (49/137438953472), by norm_num⟩
  | 7 => ⟨((-483004053/1099511627776), (868023487/2199023255552)), (157/2199023255552), by norm_num⟩
  | 8 => ⟨((669585795/8796093022208), (-601668033/8796093022208)), (111/8796093022208), by norm_num⟩
  | 9 => ⟨((-206276225/17592186044416), (370706223/35184372088832)), (139/70368744177664), by norm_num⟩
  | 10 => ⟨((114383827/70368744177664), (-822252715/562949953421312)), (39/140737488355328), by norm_num⟩
  | 11 => ⟨((-115323385/562949953421312), (829006765/4503599627370496)), (159/4503599627370496), by norm_num⟩
  | 12 => ⟨((852651511/36028797018963968), (-95770617/4503599627370496)), (149/36028797018963968), by norm_num⟩
  | 13 => ⟨((-181850151/72057594037927936), (326809271/144115188075855872)), (129/288230376151711744), by norm_num⟩
  | 14 => ⟨((36013977/144115188075855872), (-129443957/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 15 => ⟨((-852069943/36893488147419103232), (382821179/18446744073709551616)), (39/9223372036854775808), by norm_num⟩
  | 16 => ⟨((590609879/295147905179352825856), (-265351421/147573952589676412928)), (55/147573952589676412928), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-119192727333/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27814442773137/9903520314283042199192993792), (-1130104093603/633825300114114700748351602688)), (11539/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891266654866433/39614081257132168796771975168), (-1271231342237/39614081257132168796771975168)), (103857/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945568389039143/1237940039285380274899124224), (-1350518452443/2475880078570760549798248448)), (110357/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110800171619845/9671406556917033397649408), (-1350333027899/154742504910672534362390528)), (55183/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193883053877599/1208925819614629174706176), (-632870115825/4835703278458516698824704)), (51739/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260110514392319/604462909807314587353088), (-1107325756203/604462909807314587353088)), (90553/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889939459151139/75557863725914323419136), (-1799035154617/75557863725914323419136)), (147167/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299149522968807/4722366482869645213696), (-1348953392093/4722366482869645213696)), (13799/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623661162317753/590295810358705651712), (-1854286223013/590295810358705651712)), (151815/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826239730475797/73786976294838206464), (-144816936845/4611686018427387904)), (11863/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1825765984994153/9223372036854775808), (-1302811714973/4611686018427387904)), (53397/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798506205998481/576460752303423488), (-2604272241083/1152921504606846976)), (26707/144115188075855872), by norm_num⟩
  | 5 => ⟨((1197226657633821/144115188075855872), (-1138609475939/72057594037927936)), (93513/72057594037927936), by norm_num⟩
  | 4 => ⟨((46737549143631/1125899906842624), (-3412791979675/36028797018963968)), (280691/36028797018963968), by norm_num⟩
  | 3 => ⟨((747102364710713/4503599627370496), (-2130340422535/4503599627370496)), (351131/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237817720179493/4503599627370496), (-4252726453319/2251799813685248)), (351533/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230847176223259/2251799813685248), (-3179618114183/562949953421312)), (1056615/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209976577896063/2251799813685248), (-25278507136367/2251799813685248)), (1060655/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2209976577896063/2251799813685248), (-25278507136367/2251799813685248)), (4046077732566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2168646361123083/2251799813685248), (-49618006321905/2251799813685248)), (4211449/2251799813685248), by norm_num⟩
  | 2 => ⟨((1043735119013129/1125899906842624), (-2986608428795/70368744177664)), (8297459/2251799813685248), by norm_num⟩
  | 3 => ⟨((1931076671377901/2251799813685248), (-88596951396595/1125899906842624)), (16088197/2251799813685248), by norm_num⟩
  | 4 => ⟨((821045327626473/1125899906842624), (-151956230706999/1125899906842624)), (30125479/2251799813685248), by norm_num⟩
  | 5 => ⟨((1156452238800269/2251799813685248), (-221623525266267/1125899906842624)), (26034409/1125899906842624), by norm_num⟩
  | 6 => ⟨((1013335045048403/4503599627370496), (-455274967885413/2251799813685248)), (4623771/140737488355328), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-539353095/16777216)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-2911141/2097152), (-39135597/1048576)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1045108577304171/4503599627370496), (206595938876601/2251799813685248)), (23891413/2251799813685248), by norm_num⟩
  | 1 => ⟨((-401028959/1073741824), (-79274973/536870912)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((1290862421/4294967296), (127588147/1073741824)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((-1385041947/8589934592), (-547587203/8589934592)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((557284755/8589934592), (440653803/17179869184)), (29/8589934592), by norm_num⟩
  | 5 => ⟨((-1435064341/68719476736), (-283681975/34359738368)), (77/68719476736), by norm_num⟩
  | 6 => ⟨((769882319/137438953472), (304379017/137438953472)), (43/137438953472), by norm_num⟩
  | 7 => ⟨((-708044453/549755813888), (-559861863/1099511627776)), (81/1099511627776), by norm_num⟩
  | 8 => ⟨((1139553587/4398046511104), (225265727/2199023255552)), (67/4398046511104), by norm_num⟩
  | 9 => ⟨((-815129221/17592186044416), (-322267735/17592186044416)), (25/8796093022208), by norm_num⟩
  | 10 => ⟨((524759949/70368744177664), (414935929/140737488355328)), (67/140737488355328), by norm_num⟩
  | 11 => ⟨((-307115839/281474976710656), (-485682629/1125899906842624)), (81/1125899906842624), by norm_num⟩
  | 12 => ⟨((1318090333/9007199254740992), (260558679/4503599627370496)), (89/9007199254740992), by norm_num⟩
  | 13 => ⟨((-652733709/36028797018963968), (-516126789/72057594037927936)), (45/36028797018963968), by norm_num⟩
  | 14 => ⟨((600305359/288230376151711744), (237335435/288230376151711744)), (85/576460752303423488), by norm_num⟩
  | 15 => ⟨((-257641121/1152921504606846976), (-407441757/4611686018427387904)), (75/4611686018427387904), by norm_num⟩
  | 16 => ⟨((103664347/4611686018427387904), (327876105/36893488147419103232)), (31/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (490430846589/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779827762367321/633825300114114700748351602688), (36316060541/39614081257132168796771975168)), (46129/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((7386457327657/154742504910672534362390528), (653608623331/39614081257132168796771975168)), (51897/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890782434212363/2475880078570760549798248448), (43397550101/154742504910672534362390528)), (55143/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772448496307163/154742504910672534362390528), (347125085357/77371252455336267181195264)), (27573/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775366211065637/4835703278458516698824704), (650742014069/9671406556917033397649408)), (51701/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39369378334517/18889465931478580854784), (17790055273/18889465931478580854784)), (45241/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889467734265329/75557863725914323419136), (231215657989/18889465931478580854784)), (73521/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324698973349369/1180591620717411303424), (346727160101/2361183241434822606848)), (55145/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623175188190367/590295810358705651712), (953186736987/590295810358705651712)), (75831/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825632662409987/73786976294838206464), (297753545527/18446744073709551616)), (94799/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912541791262943/4611686018427387904), (669623030501/4611686018427387904)), (106663/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596330695408415/1152921504606846976), (669220204155/576460752303423488)), (13335/144115188075855872), by norm_num⟩
  | 5 => ⟨((299157731635767/36028797018963968), (1170229636483/144115188075855872)), (46683/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494709516083755/36028797018963968), (1753534608175/36028797018963968)), (140087/36028797018963968), by norm_num⟩
  | 3 => ⟨((373273087530121/2251799813685248), (2188754614291/9007199254740992)), (87589/4503599627370496), by norm_num⟩
  | 2 => ⟨((2235601020108143/4503599627370496), (2184016308263/2251799813685248)), (350563/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227542218319791/2251799813685248), (816050932623/281474976710656)), (526367/2251799813685248), by norm_num⟩
  | 0 => ⟨((137715419178451/140737488355328), (6481274437931/1125899906842624)), (527417/1125899906842624), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((137715419178451/140737488355328), (6481274437931/1125899906842624)), (2011936192039107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2156057271508577/2251799813685248), (25368405716513/2251799813685248)), (64891/70368744177664), by norm_num⟩
  | 2 => ⟨((2064099736472441/2251799813685248), (48579572019907/2251799813685248)), (4023233/2251799813685248), by norm_num⟩
  | 3 => ⟨((118187341782371/140737488355328), (44530193667673/1125899906842624)), (7549341/2251799813685248), by norm_num⟩
  | 4 => ⟨((1584483510330213/2251799813685248), (74790381441921/1125899906842624)), (13276609/2251799813685248), by norm_num⟩
  | 5 => ⟨((552494403534763/1125899906842624), (52626403735281/562949953421312)), (20448083/2251799813685248), by norm_num⟩
  | 6 => ⟨((1045108577304171/4503599627370496), (206595938876601/2251799813685248)), (23891413/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-39135597/1048576)), (1/33554432), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-51854769/33554432), (-1394207525/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-364151043857461/2251799813685248), (625892229364691/4503599627370496)), (10826139/562949953421312), by norm_num⟩
  | 1 => ⟨((38890307/134217728), (-267374117/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-1114913213/4294967296), (239535053/1073741824)), (69/2147483648), by norm_num⟩
  | 3 => ⟨((166471359/1073741824), (-286126133/2147483648)), (21/1073741824), by norm_num⟩
  | 4 => ⟨((-149138317/2147483648), (64083651/1073741824)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((427551987/17179869184), (-734863927/34359738368)), (113/34359738368), by norm_num⟩
  | 6 => ⟨((-1021427095/137438953472), (54862475/8589934592)), (137/137438953472), by norm_num⟩
  | 7 => ⟨((522900477/274877906944), (-224686535/137438953472)), (71/274877906944), by norm_num⟩
  | 8 => ⟨((-936911881/2199023255552), (402584227/1099511627776)), (129/2199023255552), by norm_num⟩
  | 9 => ⟨((93262263/1099511627776), (-160296467/2199023255552)), (105/8796093022208), by norm_num⟩
  | 10 => ⟨((-534731337/35184372088832), (919080681/70368744177664)), (153/70368744177664), by norm_num⟩
  | 11 => ⟨((696807227/281474976710656), (-598826005/281474976710656)), (101/281474976710656), by norm_num⟩
  | 12 => ⟨((-104042579/281474976710656), (715301443/2251799813685248)), (123/2251799813685248), by norm_num⟩
  | 13 => ⟨((229439109/4503599627370496), (-49294159/1125899906842624)), (69/9007199254740992), by norm_num⟩
  | 14 => ⟨((-939656449/144115188075855872), (807527097/144115188075855872)), (9/9007199254740992), by norm_num⟩
  | 15 => ⟨((28060639/36028797018963968), (-192919243/288230376151711744)), (35/288230376151711744), by norm_num⟩
  | 16 => ⟨((-402223325/4611686018427387904), (691329761/9223372036854775808)), (127/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (395941025597/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889788880817429/316912650057057350374175801344), (937969762713/158456325028528675187087900672)), (46285/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890651434945101/39614081257132168796771975168), (2110135084987/19807040628566084398385987584)), (52083/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890482693342125/2475880078570760549798248448), (4483328009871/2475880078570760549798248448)), (55351/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443037049047757/38685626227668133590597632), (1120632575621/38685626227668133590597632)), (27683/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775225148434905/4835703278458516698824704), (4201524631247/9671406556917033397649408)), (51923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157446581691403/75557863725914323419136), (1837743283125/302231454903657293676544)), (45449/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944532255311667/37778931862957161709568), (5971076721595/75557863725914323419136)), (73885/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298492503167363/4722366482869645213696), (4476917299311/4722366482869645213696)), (55441/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622756447639455/590295810358705651712), (6153502309219/590295810358705651712)), (38137/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825106870563707/73786976294838206464), (480530606975/4611686018427387904)), (95409/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824488816998883/9223372036854775808), (8644892660009/9223372036854775808)), (107425/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595731873403639/1152921504606846976), (8639070544001/1152921504606846976)), (107537/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196102401511229/144115188075855872), (1888159458871/36028797018963968)), (94223/144115188075855872), by norm_num⟩
  | 4 => ⟨((746953818182635/18014398509481984), (11315861463957/36028797018963968)), (141589/36028797018963968), by norm_num⟩
  | 3 => ⟨((746037066373835/4503599627370496), (1765239465785/1125899906842624)), (22179/1125899906842624), by norm_num⟩
  | 2 => ⟨((558379289069553/1125899906842624), (7043780245427/1125899906842624)), (89051/1125899906842624), by norm_num⟩
  | 1 => ⟨((139018653640543/140737488355328), (21045493134021/1125899906842624)), (268831/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098245486134695/1125899906842624), (41747842892167/1125899906842624)), (544391/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098245486134695/1125899906842624), (41747842892167/1125899906842624)), (2076686863425826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1069722324435215/1125899906842624), (40722429883451/562949953421312)), (275603/281474976710656), by norm_num⟩
  | 2 => ⟨((1010456239758487/1125899906842624), (154762220289141/1125899906842624)), (1127153/562949953421312), by norm_num⟩
  | 3 => ⟨((13837132379319/17592186044416), (138893741992199/562949953421312)), (2333031/562949953421312), by norm_num⟩
  | 4 => ⟨((1256026042268771/2251799813685248), (873974883963927/2251799813685248)), (19285297/2251799813685248), by norm_num⟩
  | 5 => ⟨((22586635924293/140737488355328), (487492364052997/1125899906842624)), (4560541/281474976710656), by norm_num⟩
  | 6 => ⟨((-364151043857461/2251799813685248), (625892229364691/4503599627370496)), (10826139/562949953421312), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1394207525/33554432)), (1/33554432), by norm_num⟩, -7, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-56315997/33554432), (-757077783/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((87188413884063/1125899906842624), (-1529990736099047/9007199254740992)), (114528727/4503599627370496), by norm_num⟩
  | 1 => ⟨((-80900583/536870912), (1419651271/4294967296)), (107/2147483648), by norm_num⟩
  | 2 => ⟨((314850531/2147483648), (-345314227/1073741824)), (105/2147483648), by norm_num⟩
  | 3 => ⟨((-408447229/4294967296), (895933945/4294967296)), (69/2147483648), by norm_num⟩
  | 4 => ⟨((99350201/2147483648), (-435851739/4294967296)), (17/1073741824), by norm_num⟩
  | 5 => ⟨((-309322503/17179869184), (339251329/8589934592)), (213/34359738368), by norm_num⟩
  | 6 => ⟨((401275865/68719476736), (-55012717/4294967296)), (35/17179869184), by norm_num⟩
  | 7 => ⟨((-446198159/274877906944), (244685267/68719476736)), (157/274877906944), by norm_num⟩
  | 8 => ⟨((434130763/1099511627776), (-952271089/1099511627776)), (77/549755813888), by norm_num⟩
  | 9 => ⟨((-375457537/4398046511104), (25736583/137438953472)), (135/4398046511104), by norm_num⟩
  | 10 => ⟨((584485305/35184372088832), (-1282075599/35184372088832)), (213/35184372088832), by norm_num⟩
  | 11 => ⟨((-413583959/140737488355328), (453600713/70368744177664)), (19/17592186044416), by norm_num⟩
  | 12 => ⟨((268265741/562949953421312), (-294222077/281474976710656)), (199/1125899906842624), by norm_num⟩
  | 13 => ⟨((-642487419/9007199254740992), (352325985/2251799813685248)), (15/562949953421312), by norm_num⟩
  | 14 => ⟨((357206511/36028797018963968), (-783536811/36028797018963968)), (135/36028797018963968), by norm_num⟩
  | 15 => ⟨((-370715613/288230376151711744), (813169191/288230376151711744)), (71/144115188075855872), by norm_num⟩
  | 16 => ⟨((360689637/2305843009213693952), (-791177091/2305843009213693952)), (139/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-1488956985343/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779378505118721/633825300114114700748351602688), (-881627792829/316912650057057350374175801344)), (46187/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890427644507999/39614081257132168796771975168), (-1983367626017/39614081257132168796771975168)), (25983/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890245388018277/2475880078570760549798248448), (-1053483553595/1237940039285380274899124224)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771911421636573/154742504910672534362390528), (-2106561079745/154742504910672534362390528)), (110455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775114442208111/4835703278458516698824704), (-1974469701879/9671406556917033397649408)), (103567/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259379481043035/604462909807314587353088), (-1727229784247/604462909807314587353088)), (90637/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472187915280285/18889465931478580854784), (-1402970057163/37778931862957161709568)), (9207/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((649129394628945/2361183241434822606848), (-525937015089/1180591620717411303424)), (55255/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622436590117063/590295810358705651712), (-2891505086715/590295810358705651712)), (18999/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912354647673855/36893488147419103232), (-3612659348715/73786976294838206464)), (190051/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456011157719797/2305843009213693952), (-4061875197501/9223372036854775808)), (213893/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595291539989475/1152921504606846976), (-4058918774737/1152921504606846976)), (213999/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195721437481531/144115188075855872), (-443528801449/18014398509481984)), (187369/144115188075855872), by norm_num⟩
  | 4 => ⟨((11666756478761/281474976710656), (-5315704729315/36028797018963968)), (281293/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491385705079501/9007199254740992), (-6633023172453/9007199254740992)), (352035/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232185396666593/4503599627370496), (-13231278335793/4503599627370496)), (352665/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222413041364073/2251799813685248), (-19760190479779/2251799813685248)), (33161/70368744177664), by norm_num⟩
  | 0 => ⟨((1096582966562655/1125899906842624), (-612103578313/35184372088832)), (266871/281474976710656), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096582966562655/1125899906842624), (-612103578313/35184372088832)), (1018032075048351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1067688639425231/1125899906842624), (-76309147260655/2251799813685248)), (2116519/1125899906842624), by norm_num⟩
  | 2 => ⟨((1011194025640795/1125899906842624), (-144727624754687/2251799813685248)), (8315263/2251799813685248), by norm_num⟩
  | 3 => ⟨((28235104147785/35184372088832), (-129982877347887/1125899906842624)), (16005097/2251799813685248), by norm_num⟩
  | 4 => ⟨((88757763847791/140737488355328), (-417239798405985/2251799813685248)), (7345843/562949953421312), by norm_num⟩
  | 5 => ⟨((818307091110861/2251799813685248), (-526274440841495/2251799813685248)), (23975467/1125899906842624), by norm_num⟩
  | 6 => ⟨((87188413884063/1125899906842624), (-1529990736099047/9007199254740992)), (114528727/4503599627370496), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-757077783/16777216)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-60180489/33554432), (-1618059285/33554432)), (3/33554432), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-682365282596485/9007199254740992), (166773848251431/1125899906842624)), (199069627/4503599627370496), by norm_num⟩
  | 1 => ⟨((676602705/4294967296), (-1322923539/4294967296)), (199/2147483648), by norm_num⟩
  | 2 => ⟨((-351738943/2147483648), (687735541/2147483648)), (13/134217728), by norm_num⟩
  | 3 => ⟨((487613713/4294967296), (-476701951/2147483648)), (291/4294967296), by norm_num⟩
  | 4 => ⟨((-253491053/4294967296), (61954615/536870912)), (305/8589934592), by norm_num⟩
  | 5 => ⟨((421695861/17179869184), (-824518401/17179869184)), (1/67108864), by norm_num⟩
  | 6 => ⟨((-292297297/34359738368), (571512605/34359738368)), (357/68719476736), by norm_num⟩
  | 7 => ⟨((694645877/274877906944), (-679101173/137438953472)), (427/274877906944), by norm_num⟩
  | 8 => ⟨((-722237747/1099511627776), (706075595/549755813888)), (447/1099511627776), by norm_num⟩
  | 9 => ⟨((667489411/4398046511104), (-1305104821/4398046511104)), (13/137438953472), by norm_num⟩
  | 10 => ⟨((-138800521/4398046511104), (135694459/2199023255552)), (87/4398046511104), by norm_num⟩
  | 11 => ⟨((419821919/70368744177664), (-410427193/35184372088832)), (265/70368744177664), by norm_num⟩
  | 12 => ⟨((-581996759/562949953421312), (1137945807/562949953421312)), (185/281474976710656), by norm_num⟩
  | 13 => ⟨((372377919/2251799813685248), (-182022445/562949953421312)), (239/2251799813685248), by norm_num⟩
  | 14 => ⟨((-221239461/9007199254740992), (865154363/18014398509481984)), (143/9007199254740992), by norm_num⟩
  | 15 => ⟨((122681207/36028797018963968), (-239871723/36028797018963968)), (319/144115188075855872), by norm_num⟩
  | 16 => ⟨((-127554199/288230376151711744), (997598451/1152921504606846976)), (167/576460752303423488), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (2661962463947/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889598605650455/316912650057057350374175801344), (3151755663271/633825300114114700748351602688)), (138765/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945111755528365/19807040628566084398385987584), (886289055011/9903520314283042199192993792)), (156141/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890028265313473/2475880078570760549798248448), (3766038165697/2475880078570760549798248448)), (82967/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885847019672455/77371252455336267181195264), (3765261650247/154742504910672534362390528)), (165973/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550024812876711/9671406556917033397649408), (3529107878893/9671406556917033397649408)), (155641/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259200642996061/604462909807314587353088), (3087144621323/604462909807314587353088)), (136227/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888460533232309/75557863725914323419136), (5015063870079/75557863725914323419136)), (221447/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81127499512029/295147905179352825856), (939986334939/1180591620717411303424)), (166153/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811067505897959/295147905179352825856), (2583863753863/295147905179352825856)), (114285/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456082806310569/18446744073709551616), (1614091099619/18446744073709551616)), (285879/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823617795515245/9223372036854775808), (453680062059/576460752303423488)), (321841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797431412371983/576460752303423488), (3626611137825/576460752303423488)), (161063/576460752303423488), by norm_num⟩
  | 5 => ⟨((298836050305579/36028797018963968), (1585051710349/36028797018963968)), (141091/72057594037927936), by norm_num⟩
  | 4 => ⟨((186596845644905/4503599627370496), (9497593484709/36028797018963968)), (211957/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490665782845005/9007199254740992), (5924878341131/4503599627370496)), (265509/4503599627370496), by norm_num⟩
  | 2 => ⟨((139420226598765/281474976710656), (1477055290601/281474976710656)), (133177/562949953421312), by norm_num⟩
  | 1 => ⟨((277520739510915/281474976710656), (4410378033837/281474976710656)), (803295/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094227944475033/1125899906842624), (17475613577755/562949953421312)), (1623575/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1094227944475033/1125899906842624), (17475613577755/562949953421312)), (6193447117332076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531180968628311/562949953421312), (16984018390455/281474976710656)), (3256609/1125899906842624), by norm_num⟩
  | 2 => ⟨((998310390479281/1125899906842624), (64102233493507/562949953421312)), (3269331/562949953421312), by norm_num⟩
  | 3 => ⟨((1741162326111603/2251799813685248), (454704190740763/2251799813685248)), (13084467/1125899906842624), by norm_num⟩
  | 4 => ⟨((156812915141533/281474976710656), (703183117461209/2251799813685248)), (25518915/1125899906842624), by norm_num⟩
  | 5 => ⟨((119827712868827/562949953421312), (97937830758535/281474976710656)), (88743297/2251799813685248), by norm_num⟩
  | 6 => ⟨((-682365282596485/9007199254740992), (166773848251431/1125899906842624)), (199069627/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1618059285/33554432)), (3/33554432), by norm_num⟩, -8, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile025Terms0

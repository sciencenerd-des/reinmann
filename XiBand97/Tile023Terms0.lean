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
namespace Reinmann.XiBand97.Tile023Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (28967/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (28967/1280))
  have he : value ((69/80), (28967/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1052686123/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1238194811572441/2251799813685248), (-13447462837597/1125899906842624)), (49025627/1125899906842624), by norm_num⟩
  | 1 => ⟨((818492167/2147483648), (4444633/536870912)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((-283667769/2147483648), (-24646279/8589934592)), (93/8589934592), by norm_num⟩
  | 3 => ⟨((1048658743/34359738368), (45555997/68719476736)), (87/34359738368), by norm_num⟩
  | 4 => ⟨((-726874851/137438953472), (-31577011/274877906944)), (61/137438953472), by norm_num⟩
  | 5 => ⟨((403065003/549755813888), (17510013/1099511627776)), (137/2199023255552), by norm_num⟩
  | 6 => ⟨((-745022321/8796093022208), (-505709/274877906944)), (129/17592186044416), by norm_num⟩
  | 7 => ⟨((147545749/17592186044416), (12819411/70368744177664)), (13/17592186044416), by norm_num⟩
  | 8 => ⟨((-1636334719/2251799813685248), (-17771477/1125899906842624)), (73/1125899906842624), by norm_num⟩
  | 9 => ⟨((126024533/2251799813685248), (43798219/36028797018963968)), (91/18014398509481984), by norm_num⟩
  | 10 => ⟨((-1118125437/288230376151711744), (-12143445/144115188075855872)), (103/288230376151711744), by norm_num⟩
  | 11 => ⟨((563654905/2305843009213693952), (1530399/288230376151711744)), (53/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-2083710977/147573952589676412928), (-1414389/4611686018427387904)), (99/73786976294838206464), by norm_num⟩
  | 13 => ⟨((222202829/295147905179352825856), (38611879/2361183241434822606848)), (171/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((-352044033/9444732965739290427392), (-30587103/37778931862957161709568)), (137/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((520572435/302231454903657293676544), (45229577/1208925819614629174706176)), (205/1208925819614629174706176), by norm_num⟩
  | 16 => ⟨((-721666631/9671406556917033397649408), (-15675377/9671406556917033397649408)), (9/1208925819614629174706176), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-4063985511617/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890518020973815/316912650057057350374175801344), (-4821237461369/633825300114114700748351602688)), (46337/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946145763515715/19807040628566084398385987584), (-5423561991599/39614081257132168796771975168)), (3259/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1892224737876469/2475880078570760549798248448), (-1440544578017/618970019642690137449562112)), (55421/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443472404514293/38685626227668133590597632), (-1440444282117/38685626227668133590597632)), (55441/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552082218213233/9671406556917033397649408), (-337577468171/604462909807314587353088)), (51997/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260999922970599/604462909807314587353088), (-4725657639205/604462909807314587353088)), (45519/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945691291268757/37778931862957161709568), (-7678392458549/75557863725914323419136)), (37003/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162528746390597/590295810358705651712), (-5758092550555/4722366482869645213696)), (13885/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812571850525279/295147905179352825856), (-494764716137/36893488147419103232)), (38211/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914044144615959/36893488147419103232), (-4946789601427/36893488147419103232)), (23903/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1827839270979503/9223372036854775808), (-11127914380857/9223372036854775808)), (3365/288230376151711744), by norm_num⟩
  | 6 => ⟨((1599077773531261/1152921504606846976), (-5562477854417/576460752303423488)), (107825/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1199024939226795/144115188075855872), (-2432749910617/36028797018963968)), (47255/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498281188655473/36028797018963968), (-14589806039231/36028797018963968)), (142091/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497523118114077/9007199254740992), (-9112749313309/4503599627370496)), (89093/4503599627370496), by norm_num⟩
  | 2 => ⟨((561090305634231/1125899906842624), (-18207769541611/2251799813685248)), (179045/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120214830291643/1125899906842624), (-1704188428533/70368744177664)), (270719/1125899906842624), by norm_num⟩
  | 0 => ⟨((278526624015293/281474976710656), (-54353577133409/1125899906842624)), (550065/1125899906842624), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278526624015293/281474976710656), (-54353577133409/1125899906842624)), (2098331455710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1099812661581105/1125899906842624), (-53784242276305/562949953421312)), (1141717/1125899906842624), by norm_num⟩
  | 2 => ⟨((532026383706161/562949953421312), (-210152217935281/1125899906842624)), (2448687/1125899906842624), by norm_num⟩
  | 3 => ⟨((966377499919971/1125899906842624), (-198608284548983/562949953421312)), (86601/17592186044416), by norm_num⟩
  | 4 => ⟨((689319241318755/1125899906842624), (-681874388014025/1125899906842624)), (6712561/562949953421312), by norm_num⟩
  | 5 => ⟨((18133646447117/2251799813685248), (-1669878940264333/2251799813685248)), (16349981/562949953421312), by norm_num⟩
  | 6 => ⟨((-1238194811572441/2251799813685248), (-13447462837597/1125899906842624)), (49025627/1125899906842624), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1052686123/67108864)), (1/33554432), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1668468031/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((1682444189047051/4503599627370496), (58346464756349/562949953421312)), (33835161/2251799813685248), by norm_num⟩
  | 1 => ⟨((-881363803/2147483648), (-244522641/2147483648)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((968277105/4294967296), (134317789/2147483648)), (43/4294967296), by norm_num⟩
  | 3 => ⟨((-1418348169/17179869184), (-98375449/4294967296)), (65/17179869184), by norm_num⟩
  | 4 => ⟨((194776841/8589934592), (432305909/68719476736)), (37/34359738368), by norm_num⟩
  | 5 => ⟨((-1369499079/274877906944), (-379949267/274877906944)), (17/68719476736), by norm_num⟩
  | 6 => ⟨((1003032345/1099511627776), (69569489/274877906944)), (13/274877906944), by norm_num⟩
  | 7 => ⟨((-1259364183/8796093022208), (-21837113/549755813888)), (17/2199023255552), by norm_num⟩
  | 8 => ⟨((172944121/8796093022208), (383848331/70368744177664)), (77/70368744177664), by norm_num⟩
  | 9 => ⟨((-1351100705/562949953421312), (-374844883/562949953421312)), (77/562949953421312), by norm_num⟩
  | 10 => ⟨((593734335/2251799813685248), (82361839/1125899906842624)), (35/2251799813685248), by norm_num⟩
  | 11 => ⟨((-474388245/18014398509481984), (-16451587/2251799813685248)), (29/18014398509481984), by norm_num⟩
  | 12 => ⟨((1389783349/576460752303423488), (385576867/576460752303423488)), (11/72057594037927936), by norm_num⟩
  | 13 => ⟨((-939589579/4611686018427387904), (-130338303/2305843009213693952)), (61/4611686018427387904), by norm_num⟩
  | 14 => ⟨((1179708181/73786976294838206464), (40911789/9223372036854775808)), (79/73786976294838206464), by norm_num⟩
  | 15 => ⟨((-1382444699/1180591620717411303424), (-383540857/1180591620717411303424)), (95/1180591620717411303424), by norm_num⟩
  | 16 => ⟨((1518770735/18889465931478580854784), (421362699/18889465931478580854784)), (107/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (352525989001/10141204801825835211973625643008)), (38821/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222563507899715/79228162514264337593543950336), (417972195741/633825300114114700748351602688)), (46121/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891698339735793/39614081257132168796771975168), (235089412569/19807040628566084398385987584)), (3243/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((236449429573943/309485009821345068724781056), (249758344643/1237940039285380274899124224)), (13783/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1773261396926427/154742504910672534362390528), (62432793207/19342813113834066795298816)), (27567/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775747204179247/4835703278458516698824704), (468188217093/9671406556917033397649408)), (25845/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315121684142165/151115727451828646838272), (409606967163/604462909807314587353088)), (45231/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890550805175303/75557863725914323419136), (665503110875/75557863725914323419136)), (36751/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299608019327739/4722366482869645213696), (31189541763/295147905179352825856)), (27565/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812145786691923/295147905179352825856), (343008062371/295147905179352825856)), (75809/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827027712090741/73786976294838206464), (857289528715/73786976294838206464)), (94767/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826652419887427/9223372036854775808), (964133711119/9223372036854775808)), (106623/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597898791174637/1152921504606846976), (481868802901/576460752303423488)), (26659/288230376151711744), by norm_num⟩
  | 5 => ⟨((1198002176478529/144115188075855872), (842825000373/144115188075855872)), (93321/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496764724353319/36028797018963968), (1263347225325/36028797018963968)), (140009/36028797018963968), by norm_num⟩
  | 3 => ⟨((747829223145685/4503599627370496), (1577627251137/9007199254740992)), (175061/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120362239857711/2251799813685248), (1575294480777/2251799813685248)), (175135/2251799813685248), by norm_num⟩
  | 1 => ⟨((2235205610034151/2251799813685248), (4714236376693/2251799813685248)), (525777/2251799813685248), by norm_num⟩
  | 0 => ⟨((554671626017355/562949953421312), (1172748134225/281474976710656)), (1053053/2251799813685248), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554671626017355/562949953421312), (1172748134225/281474976710656)), (4017078408248137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2186021044934643/2251799813685248), (18488041022221/2251799813685248)), (2083911/2251799813685248), by norm_num⟩
  | 2 => ⟨((2122011988897081/2251799813685248), (35895949993927/2251799813685248)), (4080293/2251799813685248), by norm_num⟩
  | 3 => ⟨((1999132575834829/2251799813685248), (67654003501583/2251799813685248)), (244385/70368744177664), by norm_num⟩
  | 4 => ⟨((1772783693875993/2251799813685248), (120125529333189/2251799813685248)), (14355569/2251799813685248), by norm_num⟩
  | 5 => ⟨((173657304229637/281474976710656), (47285859587931/562949953421312)), (12067587/1125899906842624), by norm_num⟩
  | 6 => ⟨((1682444189047051/4503599627370496), (58346464756349/562949953421312)), (33835161/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1668468031/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1052686123/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1361047323180921/4503599627370496), (14788684689579/1125899906842624)), (43178397/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1799404363/4294967296), (-39103451/2147483648)), (29/1073741824), by norm_num⟩
  | 2 => ⟨((1247252061/4294967296), (27104447/2147483648)), (41/2147483648), by norm_num⟩
  | 3 => ⟨((-576352833/4294967296), (-6262457/1073741824)), (77/8589934592), by norm_num⟩
  | 4 => ⟨((1597989365/34359738368), (69452871/34359738368)), (109/34359738368), by norm_num⟩
  | 5 => ⟨((-1772226917/137438953472), (-77025699/137438953472)), (123/137438953472), by norm_num⟩
  | 6 => ⟨((1637885455/549755813888), (71186861/549755813888)), (29/137438953472), by norm_num⟩
  | 7 => ⟨((-1297480783/2199023255552), (-1762249/68719476736)), (93/2199023255552), by norm_num⟩
  | 8 => ⟨((1798690293/17592186044416), (78175867/17592186044416)), (131/17592186044416), by norm_num⟩
  | 9 => ⟨((-554114269/35184372088832), (-24083281/35184372088832)), (41/35184372088832), by norm_num⟩
  | 10 => ⟨((1229064779/562949953421312), (53418427/562949953421312)), (93/562949953421312), by norm_num⟩
  | 11 => ⟨((-38723763/140737488355328), (-26928605/2251799813685248)), (3/140737488355328), by norm_num⟩
  | 12 => ⟨((572613699/18014398509481984), (49774631/36028797018963968)), (45/18014398509481984), by norm_num⟩
  | 13 => ⟨((-1953996657/576460752303423488), (-10615737/72057594037927936)), (39/144115188075855872), by norm_num⟩
  | 14 => ⟨((1547894027/4611686018427387904), (67275595/4611686018427387904)), (63/2305843009213693952), by norm_num⟩
  | 15 => ⟨((-1144446273/36893488147419103232), (-24870341/18446744073709551616)), (95/36893488147419103232), by norm_num⟩
  | 16 => ⟨((1586539415/590295810358705651712), (68955227/590295810358705651712)), (133/590295810358705651712), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (56579360651/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((108650208541/38685626227668133590597632), (67055860407/633825300114114700748351602688)), (92207/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945633729551155/19807040628566084398385987584), (75429816133/39614081257132168796771975168)), (51867/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891137682700143/2475880078570760549798248448), (40067200823/1237940039285380274899124224)), (110217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772803706902289/154742504910672534362390528), (40061701773/77371252455336267181195264)), (55109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551065391807661/9671406556917033397649408), (75104007481/9671406556917033397649408)), (51665/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315027853729947/151115727451828646838272), (65704325607/604462909807314587353088)), (45207/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944970517326939/37778931862957161709568), (53373816229/37778931862957161709568)), (36731/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324787700667709/1180591620717411303424), (80041569879/4722366482869645213696)), (55097/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405915770295405/147573952589676412928), (55013021075/295147905179352825856)), (75759/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456560591948533/18446744073709551616), (68742947391/36893488147419103232)), (23675/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825769279963603/9223372036854775808), (154607504209/9223372036854775808)), (106539/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597016116530923/1152921504606846976), (9657961607/72057594037927936)), (106541/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197230359286281/144115188075855872), (135121385227/144115188075855872)), (46613/36028797018963968), by norm_num⟩
  | 4 => ⟨((373902011002415/9007199254740992), (202502063303/36028797018963968)), (279687/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494214423597557/9007199254740992), (252812868435/9007199254740992)), (349625/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118920955186113/2251799813685248), (126170715617/1125899906842624)), (699301/4503599627370496), by norm_num⟩
  | 1 => ⟨((557723855273075/562949953421312), (377335751859/1125899906842624)), (524541/1125899906842624), by norm_num⟩
  | 0 => ⟨((2210120636503289/2251799813685248), (749979088391/1125899906842624)), (2098699/2251799813685248), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2210120636503289/2251799813685248), (749979088391/1125899906842624)), (8005901345259856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2169211911439449/2251799813685248), (2944390083213/2251799813685248)), (515313/281474976710656), by norm_num⟩
  | 2 => ⟨((522412296455091/562949953421312), (1418200232901/562949953421312)), (497087/140737488355328), by norm_num⟩
  | 3 => ⟨((969580313620999/1125899906842624), (10528612513425/2251799813685248)), (14801421/2251799813685248), by norm_num⟩
  | 4 => ⟨((1669878940264323/2251799813685248), (18133646447113/2251799813685248)), (12815603/1125899906842624), by norm_num⟩
  | 5 => ⟨((619097405786213/1125899906842624), (6723731418797/562949953421312)), (19213875/1125899906842624), by norm_num⟩
  | 6 => ⟨((1361047323180921/4503599627370496), (14788684689579/1125899906842624)), (43178397/2251799813685248), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1052686123/33554432)), (1/16777216), by norm_num⟩, -5, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-1222130743/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((325685177062387/4503599627370496), (1075596872270359/4503599627370496)), (80678475/2251799813685248), by norm_num⟩
  | 1 => ⟨((-249943767/2147483648), (-825455849/2147483648)), (125/2147483648), by norm_num⟩
  | 2 => ⟨((402268975/4294967296), (1328519939/4294967296)), (203/4294967296), by norm_num⟩
  | 3 => ⟨((-53952245/1073741824), (-1425446905/8589934592)), (55/2147483648), by norm_num⟩
  | 4 => ⟨((173665577/8589934592), (573542073/8589934592)), (179/17179869184), by norm_num⟩
  | 5 => ⟨((-223603171/34359738368), (-1476928571/68719476736)), (29/8589934592), by norm_num⟩
  | 6 => ⟨((239916947/137438953472), (198085403/34359738368)), (251/274877906944), by norm_num⟩
  | 7 => ⟨((-441293063/1099511627776), (-1457399577/1099511627776)), (233/1099511627776), by norm_num⟩
  | 8 => ⟨((355116893/4398046511104), (1172797067/4398046511104)), (189/4398046511104), by norm_num⟩
  | 9 => ⟨((-1984509/137438953472), (-838908473/17592186044416)), (137/17592186044416), by norm_num⟩
  | 10 => ⟨((81764967/35184372088832), (1080136881/140737488355328)), (89/70368744177664), by norm_num⟩
  | 11 => ⟨((-191411837/562949953421312), (-1264300543/1125899906842624)), (211/1125899906842624), by norm_num⟩
  | 12 => ⟨((410753957/9007199254740992), (1356542151/9007199254740992)), (229/9007199254740992), by norm_num⟩
  | 13 => ⟨((-203410151/36028797018963968), (-335887749/18014398509481984)), (229/72057594037927936), by norm_num⟩
  | 14 => ⟨((187072005/288230376151711744), (1235635377/576460752303423488)), (213/576460752303423488), by norm_num⟩
  | 15 => ⟨((-321152829/4611686018427387904), (-265157123/1152921504606846976)), (23/576460752303423488), by norm_num⟩
  | 16 => ⟨((258437769/36893488147419103232), (853507853/36893488147419103232)), (75/18446744073709551616), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (207893146113/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779825868988477/633825300114114700748351602688), (985237875023/316912650057057350374175801344)), (46197/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236366354399105/4951760157141521099596496896), (2216509980999/39614081257132168796771975168)), (25989/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890779913902667/2475880078570760549798248448), (1177354006293/1237940039285380274899124224)), (110467/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443111454761853/38685626227668133590597632), (2354332493893/154742504910672534362390528)), (110483/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550729745511827/9671406556917033397649408), (2206787785441/9671406556917033397649408)), (25899/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629908799026985/302231454903657293676544), (1930540453317/604462909807314587353088)), (11333/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944731672743387/37778931862957161709568), (1568190260983/37778931862957161709568)), (4605/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1298792328789463/4722366482869645213696), (587907821743/1180591620717411303424)), (27637/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811584921754025/295147905179352825856), (3232430373195/590295810358705651712)), (76025/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456406329273401/18446744073709551616), (4038944475353/73786976294838206464)), (95065/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228134300788819/1152921504606846976), (2270811130925/4611686018427387904)), (213991/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596320379628455/1152921504606846976), (567360698331/144115188075855872)), (107055/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196620620084737/144115188075855872), (3968447731665/144115188075855872)), (23435/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494691500738203/36028797018963968), (5946521290865/36028797018963968)), (140743/18014398509481984), by norm_num⟩
  | 3 => ⟨((186633171121549/1125899906842624), (927799698757/1125899906842624)), (352325/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235533713591215/4503599627370496), (14812569152167/4503599627370496)), (706055/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227408043576467/2251799813685248), (1383650922737/140737488355328)), (132825/281474976710656), by norm_num⟩
  | 0 => ⟨((2203046368699003/2251799813685248), (21977914974995/1125899906842624)), (534825/562949953421312), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2203046368699003/2251799813685248), (21977914974995/1125899906842624)), (2040195467235374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((16831956618957/17592186044416), (21502073800245/562949953421312)), (4269485/2251799813685248), by norm_num⟩
  | 2 => ⟨((2058101094147545/2251799813685248), (164583058641863/2251799813685248)), (8496117/2251799813685248), by norm_num⟩
  | 3 => ⟨((467258735097277/562949953421312), (150425704367837/1125899906842624)), (8386263/1125899906842624), by norm_num⟩
  | 4 => ⟨((1511137898483151/2251799813685248), (499424319493133/2251799813685248)), (8081197/562949953421312), by norm_num⟩
  | 5 => ⟨((903327678139341/2251799813685248), (670307379922113/2251799813685248)), (57723603/2251799813685248), by norm_num⟩
  | 6 => ⟨((325685177062387/4503599627370496), (1075596872270359/4503599627370496)), (80678475/2251799813685248), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-1222130743/33554432)), (1/16777216), by norm_num⟩, -6, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1360577077/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-919548825961177/4503599627370496), (-138378981805745/2251799813685248)), (41460749/2251799813685248), by norm_num⟩
  | 1 => ⟨((785641821/2147483648), (472911551/4294967296)), (9/268435456), by norm_num⟩
  | 2 => ⟨((-351920293/1073741824), (-423671875/4294967296)), (131/4294967296), by norm_num⟩
  | 3 => ⟨((840742023/4294967296), (253039365/4294967296)), (5/268435456), by norm_num⟩
  | 4 => ⟨((-1506407481/17179869184), (-226692839/8589934592)), (145/17179869184), by norm_num⟩
  | 5 => ⟨((269911987/8589934592), (324943233/34359738368)), (53/17179869184), by norm_num⟩
  | 6 => ⟨((-644823145/68719476736), (-388146743/137438953472)), (1/1073741824), by norm_num⟩
  | 7 => ⟨((20631571/8589934592), (99352229/137438953472)), (133/549755813888), by norm_num⟩
  | 8 => ⟨((-1182938007/2199023255552), (-178015297/1099511627776)), (121/2199023255552), by norm_num⟩
  | 9 => ⟨((942017945/8796093022208), (17720033/549755813888)), (49/4398046511104), by norm_num⟩
  | 10 => ⟨((-1350295659/70368744177664), (-406400473/70368744177664)), (71/35184372088832), by norm_num⟩
  | 11 => ⟨((879783649/281474976710656), (66197445/70368744177664)), (47/140737488355328), by norm_num⟩
  | 12 => ⟨((-1050907123/2251799813685248), (-39536633/281474976710656)), (57/1125899906842624), by norm_num⟩
  | 13 => ⟨((579376243/9007199254740992), (174375721/9007199254740992)), (1/140737488355328), by norm_num⟩
  | 14 => ⟨((-74150205/9007199254740992), (-178536771/72057594037927936)), (133/144115188075855872), by norm_num⟩
  | 15 => ⟨((566866483/576460752303423488), (10663165/36028797018963968)), (129/1152921504606846976), by norm_num⟩
  | 16 => ⟨((-1015688389/9223372036854775808), (-152846615/4611686018427387904)), (117/9223372036854775808), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (-3711459522617/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889787478250195/316912650057057350374175801344), (-4396155718517/633825300114114700748351602688)), (11579/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890648116548215/39614081257132168796771975168), (-4944971654423/39614081257132168796771975168)), (6515/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890478960938599/2475880078570760549798248448), (-5253200650479/2475880078570760549798248448)), (27697/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772144231454595/154742504910672534362390528), (-1313066202527/38685626227668133590597632)), (13853/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550446333193649/9671406556917033397649408), (-4923003900915/9671406556917033397649408)), (203/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((629784469355675/302231454903657293676544), (-4306634022907/604462909807314587353088)), (45491/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889058011941581/75557863725914323419136), (-6996415738015/75557863725914323419136)), (73959/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649243612550311/2361183241434822606848), (-327855016013/295147905179352825856)), (55501/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405687133558901/147573952589676412928), (-3605079481889/295147905179352825856)), (76365/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228136999454965/9223372036854775808), (-4504360703363/36893488147419103232)), (95533/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824475232353153/9223372036854775808), (-10129342451843/9223372036854775808)), (26895/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797858301532283/576460752303423488), (-10122505526067/1152921504606846976)), (107713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598043573327913/72057594037927936), (-8849500100013/144115188075855872)), (47199/72057594037927936), by norm_num⟩
  | 4 => ⟨((93367560950313/2251799813685248), (-13258863977033/36028797018963968)), (70947/18014398509481984), by norm_num⟩
  | 3 => ⟨((746017105338277/4503599627370496), (-8273325213165/4503599627370496)), (177891/9007199254740992), by norm_num⟩
  | 2 => ⟨((34897149920677/70368744177664), (-16506248844441/2251799813685248)), (44669/562949953421312), by norm_num⟩
  | 1 => ⟨((278012508365505/281474976710656), (-6164586218629/281474976710656)), (269983/1125899906842624), by norm_num⟩
  | 0 => ⟨((1097949727293985/1125899906842624), (-12228109360315/281474976710656)), (547861/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1097949727293985/1125899906842624), (-12228109360315/281474976710656)), (2089923862937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1068568502241343/1125899906842624), (-5962274823847/70368744177664)), (279031/281474976710656), by norm_num⟩
  | 2 => ⟨((62879599937287/70368744177664), (-90538763380287/562949953421312)), (1153859/562949953421312), by norm_num⟩
  | 3 => ⟨((217469379371111/281474976710656), (-10112872708435/35184372088832)), (2433263/562949953421312), by norm_num⟩
  | 4 => ⟨((1158117542029447/2251799813685248), (-500049316443075/1125899906842624)), (20634685/2251799813685248), by norm_num⟩
  | 5 => ⟨((75725862393035/1125899906842624), (-514358231786857/1125899906842624)), (39554237/2251799813685248), by norm_num⟩
  | 6 => ⟨((-919548825961177/4503599627370496), (-138378981805745/2251799813685248)), (41460749/2251799813685248), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1360577077/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-1477631785/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((839490825234841/4503599627370496), (-91699067250413/9007199254740992)), (13570427/1125899906842624), by norm_num⟩
  | 1 => ⟨((-778948649/2147483648), (42542969/2147483648)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((757882041/2147483648), (-82784795/4294967296)), (101/4294967296), by norm_num⟩
  | 3 => ⟨((-983180237/4294967296), (107394515/8589934592)), (133/8589934592), by norm_num⟩
  | 4 => ⟨((956590201/8589934592), (-52245019/8589934592)), (33/4294967296), by norm_num⟩
  | 5 => ⟨((-1489150865/34359738368), (40665645/17179869184)), (105/34359738368), by norm_num⟩
  | 6 => ⟨((1931835855/137438953472), (-52754461/68719476736)), (69/68719476736), by norm_num⟩
  | 7 => ⟨((-537025571/137438953472), (14665063/68719476736)), (39/137438953472), by norm_num⟩
  | 8 => ⟨((1045003509/1099511627776), (-28536895/549755813888)), (77/1099511627776), by norm_num⟩
  | 9 => ⟨((-903770193/4398046511104), (98720415/8796093022208)), (135/8796093022208), by norm_num⟩
  | 10 => ⟨((1406924473/35184372088832), (-76840423/35184372088832)), (53/17592186044416), by norm_num⟩
  | 11 => ⟨((-1991089899/281474976710656), (54372567/140737488355328)), (19/35184372088832), by norm_num⟩
  | 12 => ⟨((645747007/562949953421312), (-70536087/1125899906842624)), (25/281474976710656), by norm_num⟩
  | 13 => ⟨((-193317793/1125899906842624), (84465777/9007199254740992)), (121/9007199254740992), by norm_num⟩
  | 14 => ⟨((859837841/36028797018963968), (-93921607/72057594037927936)), (17/9007199254740992), by norm_num⟩
  | 15 => ⟨((-446177915/144115188075855872), (24368401/144115188075855872)), (143/576460752303423488), by norm_num⟩
  | 16 => ⟨((868222133/2305843009213693952), (-47418719/2305843009213693952)), (141/4611686018427387904), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-71072675639/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444845040850515/158456325028528675187087900672), (-42082912247/316912650057057350374175801344)), (92209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945214802782815/19807040628566084398385987584), (-23668141005/9903520314283042199192993792)), (12967/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945123796861577/1237940039285380274899124224), (-50286189135/1237940039285380274899124224)), (27555/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221489220574483/19342813113834066795298816), (-100553010291/154742504910672534362390528)), (27555/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550231226698349/9671406556917033397649408), (-2945246061/302231454903657293676544)), (25833/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259381676213271/604462909807314587353088), (-82446322453/604462909807314587353088)), (90417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888755501231045/75557863725914323419136), (-33484180751/18889465931478580854784)), (9183/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((81141369249975/295147905179352825856), (-12552352845/590295810358705651712)), (55099/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405610316468109/147573952589676412928), (-138021110763/590295810358705651712)), (151523/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912357860341473/36893488147419103232), (-86222137007/36893488147419103232)), (189407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228006582101149/1152921504606846976), (-12117935505/576460752303423488)), (213087/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595300561275331/1152921504606846976), (-48436504633/288230376151711744)), (53273/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195730448919307/144115188075855872), (-169369336305/144115188075855872)), (93231/72057594037927936), by norm_num⟩
  | 4 => ⟨((373340144290789/9007199254740992), (-253737490137/36028797018963968)), (279705/36028797018963968), by norm_num⟩
  | 3 => ⟨((186426160336611/1125899906842624), (-316618739079/9007199254740992)), (174827/4503599627370496), by norm_num⟩
  | 2 => ⟨((2232244186235115/4503599627370496), (-631581208747/4503599627370496)), (699373/4503599627370496), by norm_num⟩
  | 1 => ⟨((555632539543537/562949953421312), (-471620987037/1125899906842624)), (1049233/2251799813685248), by norm_num⟩
  | 0 => ⟨((548378744845291/562949953421312), (-1870029436843/2251799813685248)), (1049591/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548378744845291/562949953421312), (-1870029436843/2251799813685248)), (4003871922019576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1068368608638671/1125899906842624), (-3643252438933/2251799813685248)), (2046591/1125899906842624), by norm_num⟩
  | 2 => ⟨((2027548201515199/2251799813685248), (-3457089316241/1125899906842624)), (7781303/2251799813685248), by norm_num⟩
  | 3 => ⟨((228201008289983/281474976710656), (-6225611338115/1125899906842624)), (3515137/562949953421312), by norm_num⟩
  | 4 => ⟨((1480011570571991/2251799813685248), (-5047307583721/562949953421312)), (22954191/2251799813685248), by norm_num⟩
  | 5 => ⟨((1945134403773935/4503599627370496), (-26539032746139/2251799813685248)), (7646305/562949953421312), by norm_num⟩
  | 6 => ⟨((839490825234841/4503599627370496), (-91699067250413/9007199254740992)), (13570427/1125899906842624), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-1477631785/33554432)), (1/16777216), by norm_num⟩, -7, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-1579029185/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1495382283069255/9007199254740992), (-97566694385433/9007199254740992)), (122619839/4503599627370496), by norm_num⟩
  | 1 => ⟨((1482753773/4294967296), (96742743/4294967296)), (245/4294967296), by norm_num⟩
  | 2 => ⟨((-192706237/536870912), (-100585439/4294967296)), (257/4294967296), by norm_num⟩
  | 3 => ⟨((1068590279/4294967296), (69720513/4294967296)), (45/1073741824), by norm_num⟩
  | 4 => ⟨((-1111035509/8589934592), (-36244933/4294967296)), (95/4294967296), by norm_num⟩
  | 5 => ⟨((1848266713/34359738368), (120590751/34359738368)), (319/34359738368), by norm_num⟩
  | 6 => ⟨((-1281120861/68719476736), (-83587139/68719476736)), (223/68719476736), by norm_num⟩
  | 7 => ⟨((761147411/137438953472), (99322611/274877906944)), (267/274877906944), by norm_num⟩
  | 8 => ⟨((-791380773/549755813888), (-51633891/549755813888)), (35/137438953472), by norm_num⟩
  | 9 => ⟨((1462782271/4398046511104), (5964981/274877906944)), (261/4398046511104), by norm_num⟩
  | 10 => ⟨((-152088511/2199023255552), (-79384507/17592186044416)), (55/4398046511104), by norm_num⟩
  | 11 => ⟨((460013335/35184372088832), (120054867/140737488355328)), (335/140737488355328), by norm_num⟩
  | 12 => ⟨((-1275427785/562949953421312), (-83215693/562949953421312)), (235/562949953421312), by norm_num⟩
  | 13 => ⟨((1632109243/4503599627370496), (106487489/4503599627370496)), (303/4503599627370496), by norm_num⟩
  | 14 => ⟨((-969678789/18014398509481984), (-126534005/36028797018963968)), (363/36028797018963968), by norm_num⟩
  | 15 => ⟨((537704095/72057594037927936), (70165351/144115188075855872)), (203/144115188075855872), by norm_num⟩
  | 16 => ⟨((-139765529/144115188075855872), (-72952373/1152921504606846976)), (213/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (-4007406170377/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779190484085421/633825300114114700748351602688), (-2372378510887/316912650057057350374175801344)), (92667/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945107778918071/19807040628566084398385987584), (-1334243749033/9903520314283042199192993792)), (13035/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236252415014155/309485009821345068724781056), (-5669494320979/2475880078570760549798248448)), (6927/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442921134422047/38685626227668133590597632), (-88567536799/2417851639229258349412352)), (110871/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775007657082965/4835703278458516698824704), (-2656403502609/4835703278458516698824704)), (6499/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((4918717738611/2361183241434822606848), (-1161865234719/151115727451828646838272)), (22757/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944222480572789/37778931862957161709568), (-1887447329819/18889465931478580854784)), (147997/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649013672869323/2361183241434822606848), (-2830149574075/2361183241434822606848)), (55533/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622116052380165/590295810358705651712), (-7779591763189/590295810358705651712)), (152827/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824305172723073/73786976294838206464), (-9719510448765/73786976294838206464)), (191199/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823585254876943/9223372036854775808), (-10927602935283/9223372036854775808)), (6729/288230376151711744), by norm_num⟩
  | 6 => ⟨((1594826250906653/1152921504606846976), (-10919045279319/1152921504606846976)), (215615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597653835173763/72057594037927936), (-9544537605849/144115188075855872)), (188985/144115188075855872), by norm_num⟩
  | 4 => ⟨((746355466378455/18014398509481984), (-14297553298835/36028797018963968)), (284123/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490570227405387/9007199254740992), (-17838250864669/9007199254740992)), (89071/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115242706316471/2251799813685248), (-4446929848111/562949953421312)), (178991/1125899906842624), by norm_num⟩
  | 1 => ⟨((554922878862305/562949953421312), (-6638817020417/281474976710656)), (270615/562949953421312), by norm_num⟩
  | 0 => ⟨((1093521400662231/1125899906842624), (-26302704440055/562949953421312)), (1099541/1125899906842624), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1093521400662231/1125899906842624), (-26302704440055/562949953421312)), (4194416050437545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1059616150078963/1125899906842624), (-102185176588753/1125899906842624)), (1119295/562949953421312), by norm_num⟩
  | 2 => ⟨((493980223478769/562949953421312), (-96169351071141/562949953421312)), (577493/140737488355328), by norm_num⟩
  | 3 => ⟨((417031595217115/562949953421312), (-337548709225149/1125899906842624)), (4843163/562949953421312), by norm_num⟩
  | 4 => ⟨((32292073156457/70368744177664), (-1000220185230503/2251799813685248)), (40318381/2251799813685248), by norm_num⟩
  | 5 => ⟨((59831465585735/4503599627370496), (-917998005264405/2251799813685248)), (145643695/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1495382283069255/9007199254740992), (-97566694385433/9007199254740992)), (122619839/4503599627370496), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-1579029185/33554432)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile023Terms0

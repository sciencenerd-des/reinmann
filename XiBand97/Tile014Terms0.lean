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
namespace Reinmann.XiBand97.Tile014Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

private def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
private theorem hc : c ∈ XiAdaptiveTiles.quarter 32 := Data.centre_mem_quarter _
private theorem hcre : -2<c.re := by linarith [hc.1]

private def J_variable : Jet 16 := fun k =>
  match k.val with
  | 0 => ⟨((69/80), (26103/1280)), 0, by norm_num⟩
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
  have h := variable_sound 16 ((69/80), (26103/1280))
  have he : value ((69/80), (26103/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-20060163/33554432), (-1897211715/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((2276522267317/2251799813685248), (-619242389109133/1125899906842624)), (48632625/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3009729/4294967296), (1637367691/4294967296)), (67/4294967296), by norm_num⟩
  | 2 => ⟨((2086185/8589934592), (-1134936799/8589934592)), (3/536870912), by norm_num⟩
  | 3 => ⟨((-3856089/68719476736), (1048904323/34359738368)), (91/68719476736), by norm_num⟩
  | 4 => ⟨((2672837/274877906944), (-363522537/68719476736)), (65/274877906944), by norm_num⟩
  | 5 => ⟨((-2964271/2199023255552), (806318789/1099511627776)), (37/1099511627776), by norm_num⟩
  | 6 => ⟨((171223/1099511627776), (-1490393587/17592186044416)), (35/8796093022208), by norm_num⟩
  | 7 => ⟨((-2170199/140737488355328), (1180642415/140737488355328)), (57/140737488355328), by norm_num⟩
  | 8 => ⟨((3008535/2251799813685248), (-1636717923/2251799813685248)), (81/2251799813685248), by norm_num⟩
  | 9 => ⟨((-1853651/18014398509481984), (63027023/1125899906842624)), (51/18014398509481984), by norm_num⟩
  | 10 => ⟨((2055765/288230376151711744), (-279596821/72057594037927936)), (29/144115188075855872), by norm_num⟩
  | 11 => ⟨((-2072651/4611686018427387904), (70473363/288230376151711744)), (15/1152921504606846976), by norm_num⟩
  | 12 => ⟨((3831073/147573952589676412928), (-2084198949/147573952589676412928)), (113/147573952589676412928), by norm_num⟩
  | 13 => ⟨((-3268305/2361183241434822606848), (1778038923/2361183241434822606848)), (99/2361183241434822606848), by norm_num⟩
  | 14 => ⟨((2589047/37778931862957161709568), (-1408505905/37778931862957161709568)), (81/37778931862957161709568), by norm_num⟩
  | 15 => ⟨((-957115/302231454903657293676544), (520694345/302231454903657293676544)), (61/604462909807314587353088), by norm_num⟩
  | 16 => ⟨((1326843/9671406556917033397649408), (-1443671269/19342813113834066795298816)), (87/19342813113834066795298816), by norm_num⟩
  | _ => zero

private def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791598507239655/5070602400912917605986812821504), (-1021871600757/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781045292513209/633825300114114700748351602688), (-2424558664491/633825300114114700748351602688)), (23111/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892302495875849/39614081257132168796771975168), (-2727476640327/39614081257132168796771975168)), (26003/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946118538362567/1237940039285380274899124224), (-724441621685/618970019642690137449562112)), (27633/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773902726870583/154742504910672534362390528), (-1448783416271/77371252455336267181195264)), (27637/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552095325660717/9671406556917033397649408), (-2716256748027/9671406556917033397649408)), (25915/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630506104875251/302231454903657293676544), (-2376512469045/604462909807314587353088)), (22681/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472851020374071/18889465931478580854784), (-1930717427483/37778931862957161709568)), (18433/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300247436302397/4722366482869645213696), (-2895727912973/4722366482869645213696)), (27659/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625169894041931/590295810358705651712), (-3981059898089/590295810358705651712)), (38045/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914062148414145/36893488147419103232), (-4975475704553/73786976294838206464)), (5947/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1827884268812063/9223372036854775808), (-5596242245477/9223372036854775808)), (53553/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399782095008921/288230376151711744), (-5594781869221/1152921504606846976)), (53589/1152921504606846976), by norm_num⟩
  | 5 => ⟨((4683888771987/562949953421312), (-2446895280981/72057594037927936)), (46931/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498369669542791/36028797018963968), (-1834349268119/9007199254740992)), (35239/18014398509481984), by norm_num⟩
  | 3 => ⟨((748827874300165/4503599627370496), (-2291496836737/2251799813685248)), (88241/9007199254740992), by norm_num⟩
  | 2 => ⟨((561173119960057/1125899906842624), (-4578670791647/1125899906842624)), (11057/281474976710656), by norm_num⟩
  | 1 => ⟨((1120545607319225/1125899906842624), (-3428593147067/281474976710656)), (133223/1125899906842624), by norm_num⟩
  | 0 => ⟨((69693525778385/70368744177664), (-854438574789/35184372088832)), (134301/562949953421312), by norm_num⟩
  | _ => zero

private def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((69693525778385/70368744177664), (-854438574789/35184372088832)), (512317659618186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1103732591743679/1125899906842624), (-13539837900249/281474976710656)), (68137/140737488355328), by norm_num⟩
  | 2 => ⟨((1079396482161047/1125899906842624), (-414789324483/4398046511104)), (1121171/1125899906842624), by norm_num⟩
  | 3 => ⟨((1024799165405409/1125899906842624), (-50900114011359/281474976710656)), (2361207/1125899906842624), by norm_num⟩
  | 4 => ⟨((447979512913627/562949953421312), (-370636103908459/1125899906842624)), (2576167/562949953421312), by norm_num⟩
  | 5 => ⟨((590968566918875/1125899906842624), (-294941637863239/562949953421312)), (5796183/562949953421312), by norm_num⟩
  | 6 => ⟨((2276522267317/2251799813685248), (-619242389109133/1125899906842624)), (48632625/2251799813685248), by norm_num⟩
  | _ => zero

private def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/33554432), (-1897211715/134217728)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-15897303/16777216), (-1503504713/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-399830000129953/1125899906842624), (350239140433813/2251799813685248)), (76213405/2251799813685248), by norm_num⟩
  | 1 => ⟨((837818435/2147483648), (-366951965/2147483648)), (81/2147483648), by norm_num⟩
  | 2 => ⟨((-920437629/4294967296), (201568969/2147483648)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((1348272121/17179869184), (-590523057/17179869184)), (17/2147483648), by norm_num⟩
  | 4 => ⟨((-1481228321/68719476736), (648755887/68719476736)), (19/8589934592), by norm_num⟩
  | 5 => ⟨((1301836509/274877906944), (-71273119/34359738368)), (17/34359738368), by norm_num⟩
  | 6 => ⟨((-953475725/1099511627776), (208804065/549755813888)), (51/549755813888), by norm_num⟩
  | 7 => ⟨((1197143027/8796093022208), (-262165385/4398046511104)), (65/4398046511104), by norm_num⟩
  | 8 => ⟨((-1315196041/70368744177664), (576036227/70368744177664)), (145/70368744177664), by norm_num⟩
  | 9 => ⟨((321086785/140737488355328), (-562524869/562949953421312)), (9/35184372088832), by norm_num⟩
  | 10 => ⟨((-1128799641/4503599627370496), (494397387/4503599627370496)), (129/4503599627370496), by norm_num⟩
  | 11 => ⟨((450950239/18014398509481984), (-197509471/18014398509481984)), (105/36028797018963968), by norm_num⟩
  | 12 => ⟨((-660559299/288230376151711744), (578630219/576460752303423488)), (39/144115188075855872), by norm_num⟩
  | 13 => ⟨((893167463/4611686018427387904), (-97798503/1152921504606846976)), (107/4611686018427387904), by norm_num⟩
  | 14 => ⟨((-280355643/18446744073709551616), (245583171/36893488147419103232)), (137/73786976294838206464), by norm_num⟩
  | 15 => ⟨((1314142527/1180591620717411303424), (-575574805/1180591620717411303424)), (41/295147905179352825856), by norm_num⟩
  | 16 => ⟨((-721866565/9444732965739290427392), (316166777/9444732965739290427392)), (183/18889465931478580854784), by norm_num⟩
  | _ => zero

private def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582741473400121/10141204801825835211973625643008), (888633573791/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780498684173625/633825300114114700748351602688), (2107215567847/316912650057057350374175801344)), (46307/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891687228181175/39614081257132168796771975168), (4740807770585/39614081257132168796771975168)), (26055/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891582937738951/2475880078570760549798248448), (5036618088397/2475880078570760549798248448)), (55381/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773248118830091/154742504910672534362390528), (2518033223325/77371252455336267181195264)), (55399/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775740566219445/4835703278458516698824704), (590090753357/1208925819614629174706176)), (51955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315118573176745/151115727451828646838272), (2065024420379/302231454903657293676544)), (45479/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890529033043649/75557863725914323419136), (1677557363167/18889465931478580854784)), (73937/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299590333808319/4722366482869645213696), (19655114505/18446744073709551616)), (55483/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812132526348121/295147905179352825856), (6917035135359/590295810358705651712)), (38169/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913495629241519/36893488147419103232), (8643945011641/73786976294838206464)), (11937/9223372036854775808), by norm_num⟩
  | 7 => ⟨((913303435693543/4611686018427387904), (9721206520831/9223372036854775808)), (107535/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199730946820791/144115188075855872), (9717164199671/1152921504606846976)), (107661/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598975495847435/72057594037927936), (4248983610631/72057594037927936)), (94347/144115188075855872), by norm_num⟩
  | 4 => ⟨((1496675222604981/36028797018963968), (3184459585363/9007199254740992)), (141805/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495524336958747/9007199254740992), (15906329565593/9007199254740992)), (44439/2251799813685248), by norm_num⟩
  | 2 => ⟨((70012178377937/140737488355328), (3970583541963/562949953421312)), (178507/2251799813685248), by norm_num⟩
  | 1 => ⟨((558634393174213/562949953421312), (23763363436563/1125899906842624)), (134821/562949953421312), by norm_num⟩
  | 0 => ⟨((554172481737513/562949953421312), (11821321270985/281474976710656)), (68353/140737488355328), by norm_num⟩
  | _ => zero

private def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554172481737513/562949953421312), (11821321270985/281474976710656)), (260746002734136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1089077858895659/1125899906842624), (93096033227741/1125899906842624)), (35079/35184372088832), by norm_num⟩
  | 2 => ⟨((1045762331250099/1125899906842624), (180102739014649/1125899906842624)), (589317/281474976710656), by norm_num⟩
  | 3 => ⟨((942518824641303/1125899906842624), (167283662670037/562949953421312)), (2566563/562949953421312), by norm_num⟩
  | 4 => ⟨((689587444584927/1125899906842624), (35009329018333/70368744177664)), (11644809/1125899906842624), by norm_num⟩
  | 5 => ⟨((143674978972553/1125899906842624), (343078365494665/562949953421312)), (51702449/2251799813685248), by norm_num⟩
  | 6 => ⟨((-399830000129953/1125899906842624), (350239140433813/2251799813685248)), (76213405/2251799813685248), by norm_num⟩
  | _ => zero

private def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15897303/16777216), (-1503504713/67108864)), (1/33554432), by norm_num⟩, -4, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-20060163/16777216), (-1897211715/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-1362323021791591/4503599627370496), (-1252082071511/1125899906842624)), (27049923/1125899906842624), by norm_num⟩
  | 1 => ⟨((900545465/2147483648), (6621377/4294967296)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((-312105275/1073741824), (-4589589/4294967296)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((144223261/1073741824), (4241681/8589934592)), (3/268435456), by norm_num⟩
  | 4 => ⟨((-399871787/8589934592), (-2940109/17179869184)), (135/34359738368), by norm_num⟩
  | 5 => ⟨((1773888011/137438953472), (3260685/68719476736)), (19/17179869184), by norm_num⟩
  | 6 => ⟨((-1639420631/549755813888), (-3013513/274877906944)), (143/549755813888), by norm_num⟩
  | 7 => ⟨((1298696901/2199023255552), (2387209/1099511627776)), (115/2199023255552), by norm_num⟩
  | 8 => ⟨((-1800376191/17592186044416), (-6618749/17592186044416)), (81/8796093022208), by norm_num⟩
  | 9 => ⟨((138658409/8796093022208), (4078015/70368744177664)), (51/35184372088832), by norm_num⟩
  | 10 => ⟨((-1230216771/562949953421312), (-4522663/562949953421312)), (115/562949953421312), by norm_num⟩
  | 11 => ⟨((1240321871/4503599627370496), (4559813/4503599627370496)), (59/2251799813685248), by norm_num⟩
  | 12 => ⟨((-1146300811/36028797018963968), (-2107081/18014398509481984)), (111/36028797018963968), by norm_num⟩
  | 13 => ⟨((488957031/144115188075855872), (7190239/576460752303423488)), (3/9007199254740992), by norm_num⟩
  | 14 => ⟨((-1549344857/4611686018427387904), (-5695879/4611686018427387904)), (77/2305843009213693952), by norm_num⟩
  | 15 => ⟨((572759477/18446744073709551616), (526411/4611686018427387904)), (115/36893488147419103232), by norm_num⟩
  | 16 => ⟨((-1588026467/590295810358705651712), (-5838085/590295810358705651712)), (81/295147905179352825856), by norm_num⟩
  | _ => zero

private def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582418261853239/10141204801825835211973625643008), (-1021871600757/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890056246779545/316912650057057350374175801344), (-4844344554369/633825300114114700748351602688)), (46339/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891252631698289/39614081257132168796771975168), (-1362317340671/9903520314283042199192993792)), (26073/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236390125578445/309485009821345068724781056), (-723642210543/309485009821345068724781056)), (55423/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886392994853713/77371252455336267181195264), (-2894168740553/77371252455336267181195264)), (55443/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387761919569447/2417851639229258349412352), (-5425715975303/9671406556917033397649408)), (51999/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19688981443433/9444732965739290427392), (-4746650843307/604462909807314587353088)), (2845/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((472477996999349/18889465931478580854784), (-3855856104347/37778931862957161709568)), (37005/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649563604782305/2361183241434822606848), (-5782387700999/4722366482869645213696)), (27771/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101476731518855/36893488147419103232), (-3974256484053/295147905179352825856)), (76427/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826193745351871/73786976294838206464), (-9932234490569/73786976294838206464)), (47809/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912854266532113/4611686018427387904), (-2792269266833/2305843009213693952)), (107687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399236954777071/288230376151711744), (-5581607457365/576460752303423488)), (107833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197162115417285/144115188075855872), (-9761213007441/144115188075855872)), (47259/72057594037927936), by norm_num⟩
  | 4 => ⟨((747744368873679/18014398509481984), (-14628606662677/36028797018963968)), (142105/36028797018963968), by norm_num⟩
  | 3 => ⟨((46688615789135/281474976710656), (-18262607239259/9007199254740992)), (178207/9007199254740992), by norm_num⟩
  | 2 => ⟨((279674494789511/562949953421312), (-18227823675955/2251799813685248)), (1399/17592186044416), by norm_num⟩
  | 1 => ⟨((1115003024469795/1125899906842624), (-13627289302831/562949953421312)), (270775/1125899906842624), by norm_num⟩
  | 0 => ⟨((1103732591743679/1125899906842624), (-13539837900249/281474976710656)), (550241/1125899906842624), by norm_num⟩
  | _ => zero

private def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1103732591743679/1125899906842624), (-13539837900249/281474976710656)), (2099002842429732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1079396482161047/1125899906842624), (-414789324483/4398046511104)), (1131753/1125899906842624), by norm_num⟩
  | 2 => ⟨((1024799165405409/1125899906842624), (-50900114011359/281474976710656)), (2383493/1125899906842624), by norm_num⟩
  | 3 => ⟨((447979512913627/562949953421312), (-370636103908459/1125899906842624)), (1300241/281474976710656), by norm_num⟩
  | 4 => ⟨((590968566918875/1125899906842624), (-294941637863239/562949953421312)), (2925445/281474976710656), by norm_num⟩
  | 5 => ⟨((2276522267317/2251799813685248), (-619242389109133/1125899906842624)), (24545821/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1362323021791591/4503599627370496), (-1252082071511/1125899906842624)), (27049923/1125899906842624), by norm_num⟩
  | _ => zero

private def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20060163/16777216), (-1897211715/67108864)), (1/33554432), by norm_num⟩, -4, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-2911141/2097152), (-68831081/2097152)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((185151333636063/4503599627370496), (-554233355602305/2251799813685248)), (2647145/140737488355328), by norm_num⟩
  | 1 => ⟨((-284185005/4294967296), (6645949/16777216)), (33/1073741824), by norm_num⟩
  | 2 => ⟨((228689061/4294967296), (-1369119013/4294967296)), (27/1073741824), by norm_num⟩
  | 3 => ⟨((-245373897/8589934592), (1469008031/8589934592)), (59/4294967296), by norm_num⟩
  | 4 => ⟨((98728513/8589934592), (-591069305/8589934592)), (97/17179869184), by norm_num⟩
  | 5 => ⟨((-254235859/68719476736), (761031479/34359738368)), (127/68719476736), by norm_num⟩
  | 6 => ⟨((272784553/274877906944), (-1633110553/274877906944)), (139/274877906944), by norm_num⟩
  | 7 => ⟨((-62718543/274877906944), (750968583/549755813888)), (65/549755813888), by norm_num⟩
  | 8 => ⟨((100941601/2199023255552), (-1208637309/4398046511104)), (53/2199023255552), by norm_num⟩
  | 9 => ⟨((-144408213/17592186044416), (1729090407/35184372088832)), (153/35184372088832), by norm_num⟩
  | 10 => ⟨((92966421/70368744177664), (-556572731/70368744177664)), (25/35184372088832), by norm_num⟩
  | 11 => ⟨((-217634447/1125899906842624), (1302937097/1125899906842624)), (119/1125899906842624), by norm_num⟩
  | 12 => ⟨((233512753/9007199254740992), (-1397997575/9007199254740992)), (65/4503599627370496), by norm_num⟩
  | 13 => ⟨((-231276479/72057594037927936), (1384609415/72057594037927936)), (131/72057594037927936), by norm_num⟩
  | 14 => ⟨((53175019/144115188075855872), (-1273395935/576460752303423488)), (61/288230376151711744), by norm_num⟩
  | 15 => ⟨((-91287351/2305843009213693952), (136630113/576460752303423488)), (53/2305843009213693952), by norm_num⟩
  | 16 => ⟨((293842647/73786976294838206464), (-1759181471/73786976294838206464)), (173/73786976294838206464), by norm_num⟩
  | _ => zero

private def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395541889876545/2535301200456458802993406410752), (-1830547809261/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889912715263155/316912650057057350374175801344), (-2168812521535/633825300114114700748351602688)), (46207/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890930316302163/39614081257132168796771975168), (-1219805271671/19807040628566084398385987584)), (25995/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945389665129387/1237940039285380274899124224), (-1295859342741/1237940039285380274899124224)), (55247/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221555649882213/19342813113834066795298816), (-1295652640259/77371252455336267181195264)), (6907/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775364562835255/4835703278458516698824704), (-303613689923/1208925819614629174706176)), (12953/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259817017110371/604462909807314587353088), (-2124856717717/604462909807314587353088)), (45345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944731164575339/37778931862957161709568), (-3452068979155/75557863725914323419136)), (73703/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298791503311813/4722366482869645213696), (-2588331593011/4722366482869645213696)), (55293/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811584302904213/295147905179352825856), (-3557785987041/590295810358705651712)), (76053/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456405904024057/18446744073709551616), (-2222739018701/36893488147419103232)), (743/576460752303423488), by norm_num⟩
  | 7 => ⟨((1825072281322759/9223372036854775808), (-4998751214181/9223372036854775808)), (26761/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798158995373713/576460752303423488), (-4995737920681/1152921504606846976)), (107109/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598309116682663/72057594037927936), (-4367882346385/144115188075855872)), (46897/72057594037927936), by norm_num⟩
  | 4 => ⟨((93417958052477/2251799813685248), (-6545050903679/36028797018963968)), (70419/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493059120837225/9007199254740992), (-8169470670181/9007199254740992)), (11019/562949953421312), by norm_num⟩
  | 2 => ⟨((1117759063605619/2251799813685248), (-8151724468387/2251799813685248)), (176691/2251799813685248), by norm_num⟩
  | 1 => ⟨((2227376972544469/2251799813685248), (-12183285030993/1125899906842624)), (266003/1125899906842624), by norm_num⟩
  | 0 => ⟨((2202953663221931/2251799813685248), (-24189746389383/1125899906842624)), (1071771/2251799813685248), by norm_num⟩
  | _ => zero

private def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2202953663221931/2251799813685248), (-24189746389383/1125899906842624)), (4088481911666106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2154127661571701/2251799813685248), (-47330042481609/1125899906842624)), (2143099/2251799813685248), by norm_num⟩
  | 2 => ⟨((1028356389079637/1125899906842624), (-90554189687173/1125899906842624)), (2140233/1125899906842624), by norm_num⟩
  | 3 => ⟨((1863961077381421/2251799813685248), (-82708932611849/562949953421312)), (8507789/2251799813685248), by norm_num⟩
  | 4 => ⟨((93394698015621/140737488355328), (-136927119545271/562949953421312)), (16584839/2251799813685248), by norm_num⟩
  | 5 => ⟨((858421442813293/2251799813685248), (-726928816452495/2251799813685248)), (15039807/1125899906842624), by norm_num⟩
  | 6 => ⟨((185151333636063/4503599627370496), (-554233355602305/2251799813685248)), (2647145/140737488355328), by norm_num⟩
  | _ => zero

private def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2911141/2097152), (-68831081/2097152)), (1/33554432), by norm_num⟩, -5, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-51854769/33554432), (-1226055285/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((383644576535451/4503599627370496), (55020658501063/281474976710656)), (65763749/4503599627370496), by norm_num⟩
  | 1 => ⟨((-81944323/536870912), (-752134597/2147483648)), (29/1073741824), by norm_num⟩
  | 2 => ⟨((587298067/4294967296), (1347644287/4294967296)), (53/2147483648), by norm_num⟩
  | 3 => ⟨((-43845703/536870912), (-201221201/1073741824)), (65/4294967296), by norm_num⟩
  | 4 => ⟨((157121907/4294967296), (1442159969/17179869184)), (119/17179869184), by norm_num⟩
  | 5 => ⟨((-56304933/4294967296), (-129200189/4294967296)), (87/34359738368), by norm_num⟩
  | 6 => ⟨((538052783/137438953472), (1234643531/137438953472)), (53/68719476736), by norm_num⟩
  | 7 => ⟨((-550892097/549755813888), (-1264105279/549755813888)), (55/274877906944), by norm_num⟩
  | 8 => ⟨((246766533/1099511627776), (566243151/1099511627776)), (25/549755813888), by norm_num⟩
  | 9 => ⟨((-393018909/8796093022208), (-450920679/4398046511104)), (81/8796093022208), by norm_num⟩
  | 10 => ⟨((281678141/35184372088832), (1292706235/70368744177664)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-367054165/281474976710656), (-842261323/281474976710656)), (39/140737488355328), by norm_num⟩
  | 12 => ⟨((438448517/2251799813685248), (251521617/562949953421312)), (95/2251799813685248), by norm_num⟩
  | 13 => ⟨((-483442635/18014398509481984), (-1109332281/18014398509481984)), (107/18014398509481984), by norm_num⟩
  | 14 => ⟨((494978811/144115188075855872), (567901891/72057594037927936)), (111/144115188075855872), by norm_num⟩
  | 15 => ⟨((-118251063/288230376151711744), (-542689915/576460752303423488)), (27/288230376151711744), by norm_num⟩
  | 16 => ⟨((105938731/2305843009213693952), (486184897/4611686018427387904)), (49/4611686018427387904), by norm_num⟩
  | _ => zero

private def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790981360387025/5070602400912917605986812821504), (1510791103355/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779583572336057/633825300114114700748351602688), (1789504346747/633825300114114700748351602688)), (46189/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945329154422363/19807040628566084398385987584), (2012915769367/39614081257132168796771975168)), (203/154742504910672534362390528), by norm_num⟩
  | 15 => ⟨((1890490424874135/2475880078570760549798248448), (1069192799957/1237940039285380274899124224)), (27611/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110759775562265/9671406556917033397649408), (1069003046627/77371252455336267181195264)), (27615/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775229253742119/4835703278458516698824704), (1001988782089/4835703278458516698824704)), (25893/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314895087163727/151115727451828646838272), (438269326917/151115727451828646838272)), (45321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944538986217961/37778931862957161709568), (711998767751/18889465931478580854784)), (18415/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298503436527973/4722366482869645213696), (533833844725/1180591620717411303424)), (27629/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50711651251513/18446744073709551616), (2935012491389/590295810358705651712)), (2375/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1825129397727389/73786976294838206464), (3667155740267/73786976294838206464)), (95031/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824516957361281/9223372036854775808), (1030834404673/2305843009213693952)), (106953/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595763505756413/1152921504606846976), (1030143340803/288230376151711744)), (107007/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598067000967197/72057594037927936), (3602393940835/144115188075855872)), (23423/36028797018963968), by norm_num⟩
  | 4 => ⟨((746981432651427/18014398509481984), (5397380493481/36028797018963968)), (140659/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492156832644903/9007199254740992), (6735868823007/9007199254740992)), (44009/2251799813685248), by norm_num⟩
  | 2 => ⟨((2233723404175329/4503599627370496), (3359803245065/1125899906842624)), (176355/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224709450252069/2251799813685248), (5019416915401/562949953421312)), (66333/281474976710656), by norm_num⟩
  | 0 => ⟨((2197716441580667/2251799813685248), (9957921506081/562949953421312)), (533871/1125899906842624), by norm_num⟩
  | _ => zero

private def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197716441580667/2251799813685248), (9957921506081/562949953421312)), (2036556248191451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2144227459758263/2251799813685248), (77750029766875/2251799813685248)), (2121969/2251799813685248), by norm_num⟩
  | 2 => ⟨((2039109473296385/2251799813685248), (74035776986017/1125899906842624)), (4187733/2251799813685248), by norm_num⟩
  | 3 => ⟨((1836771738701945/2251799813685248), (268171359279005/2251799813685248)), (508445/140737488355328), by norm_num⟩
  | 4 => ⟨((733150105548889/1125899906842624), (6835776026517/35184372088832)), (15209137/2251799813685248), by norm_num⟩
  | 5 => ⟨((869810490954865/2251799813685248), (284879315321945/1125899906842624)), (3214651/281474976710656), by norm_num⟩
  | 6 => ⟨((383644576535451/4503599627370496), (55020658501063/281474976710656)), (65763749/4503599627370496), by norm_num⟩
  | _ => zero

private def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-51854769/33554432), (-1226055285/33554432)), (1/33554432), by norm_num⟩, -6, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-56315997/33554432), (-665768331/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-674842634034615/9007199254740992), (-1540121917524015/9007199254740992)), (294812411/9007199254740992), by norm_num⟩
  | 1 => ⟨((39135907/268435456), (714525907/2147483648)), (69/1073741824), by norm_num⟩
  | 2 => ⟨((-609239669/4294967296), (-695201607/2147483648)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((197587609/2147483648), (901866575/4294967296)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((-192243867/4294967296), (-877475661/8589934592)), (87/4294967296), by norm_num⟩
  | 5 => ⟨((598542867/34359738368), (341497759/8589934592)), (273/34359738368), by norm_num⟩
  | 6 => ⟨((-24264805/4294967296), (-221507985/17179869184)), (179/68719476736), by norm_num⟩
  | 7 => ⟨((431699477/274877906944), (985222025/274877906944)), (201/274877906944), by norm_num⟩
  | 8 => ⟨((-420024197/1099511627776), (-958576769/1099511627776)), (197/1099511627776), by norm_num⟩
  | 9 => ⟨((22703593/274877906944), (829024117/4398046511104)), (43/1099511627776), by norm_num⟩
  | 10 => ⟨((-282746573/17592186044416), (-1290565155/35184372088832)), (135/17592186044416), by norm_num⟩
  | 11 => ⟨((400145037/140737488355328), (913208667/140737488355328)), (193/140737488355328), by norm_num⟩
  | 12 => ⟨((-259548763/562949953421312), (-592340671/562949953421312)), (63/281474976710656), by norm_num⟩
  | 13 => ⟨((310805275/4503599627370496), (1418635967/9007199254740992)), (19/562949953421312), by norm_num⟩
  | 14 => ⟨((-86399877/9007199254740992), (-788725179/36028797018963968)), (85/18014398509481984), by norm_num⟩
  | 15 => ⟨((22416853/18014398509481984), (51159611/18014398509481984)), (89/144115188075855872), by norm_num⟩
  | 16 => ⟨((-174484727/1152921504606846976), (-398208025/1152921504606846976)), (175/2305843009213693952), by norm_num⟩
  | _ => zero

private def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581789532100533/10141204801825835211973625643008), (-323010732441/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779375161095431/633825300114114700748351602688), (-3060131266711/633825300114114700748351602688)), (92501/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945211844961509/19807040628566084398385987584), (-3442129383973/39614081257132168796771975168)), (104083/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945120470050329/1237940039285380274899124224), (-1828317597651/1237940039285380274899124224)), (55305/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771906696939821/154742504910672534362390528), (-3655929580595/154742504910672534362390528)), (27659/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550224161086851/9671406556917033397649408), (-3426684369941/9671406556917033397649408)), (25937/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259375054374249/604462909807314587353088), (-2997599328463/604462909807314587353088)), (45403/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888743917354985/75557863725914323419136), (-152177932909/2361183241434822606848)), (73805/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298252500169773/4722366482869645213696), (-3651041214081/4722366482869645213696)), (110751/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202803395155817/73786976294838206464), (-5018184723883/590295810358705651712)), (152355/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456174084596331/18446744073709551616), (-783717037605/9223372036854775808)), (95275/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456007111568171/2305843009213693952), (-7049337081551/9223372036854775808)), (53629/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595273348243529/1152921504606846976), (-3522096873413/576460752303423488)), (214701/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195703265642873/144115188075855872), (-6157886009743/144115188075855872)), (188071/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493313073318929/36028797018963968), (-2306317203467/9007199254740992)), (141261/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491338160555559/9007199254740992), (-11511371061303/9007199254740992)), (44235/1125899906842624), by norm_num⟩
  | 2 => ⟨((1116033423959251/2251799813685248), (-5740539724671/1125899906842624)), (354973/2251799813685248), by norm_num⟩
  | 1 => ⟨((555544219980923/562949953421312), (-17145998162587/1125899906842624)), (535197/1125899906842624), by norm_num⟩
  | 0 => ⟨((548115529419959/562949953421312), (-16995080756087/562949953421312)), (1081375/1125899906842624), by norm_num⟩
  | _ => zero

private def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548115529419959/562949953421312), (-16995080756087/562949953421312)), (4125118259910201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((266579470339515/281474976710656), (-66188957860601/1125899906842624)), (542763/281474976710656), by norm_num⟩
  | 2 => ⟨((502998907397365/562949953421312), (-125372546682481/1125899906842624)), (4367585/1125899906842624), by norm_num⟩
  | 3 => ⟨((110612999638673/140737488355328), (-112021066198965/562949953421312)), (17555225/2251799813685248), by norm_num⟩
  | 4 => ⟨((1301821241047835/2251799813685248), (-704346016106563/2251799813685248)), (34581759/2251799813685248), by norm_num⟩
  | 5 => ⟨((266150486813585/1125899906842624), (-814399751916057/2251799813685248)), (15404743/562949953421312), by norm_num⟩
  | 6 => ⟨((-674842634034615/9007199254740992), (-1540121917524015/9007199254740992)), (294812411/9007199254740992), by norm_num⟩
  | _ => zero

private def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56315997/33554432), (-665768331/16777216)), (1/16777216), by norm_num⟩, -6, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-60180489/33554432), (-711454393/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-8263709371535/9007199254740992), (374634750747157/2251799813685248)), (240369361/9007199254740992), by norm_num⟩
  | 1 => ⟨((4096961/2147483648), (-742941917/2147483648)), (241/4294967296), by norm_num⟩
  | 2 => ⟨((-8519391/4294967296), (1544904285/4294967296)), (253/4294967296), by norm_num⟩
  | 3 => ⟨((738149/536870912), (-1070846049/4294967296)), (177/4294967296), by norm_num⟩
  | 4 => ⟨((-6139751/8589934592), (69586305/536870912)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((10213803/34359738368), (-1852168363/34359738368)), (39/4294967296), by norm_num⟩
  | 6 => ⟨((-7079669/68719476736), (1283825279/68719476736)), (109/34359738368), by norm_num⟩
  | 7 => ⟨((8412433/274877906944), (-1525508353/274877906944)), (261/274877906944), by norm_num⟩
  | 8 => ⟨((-8746581/1099511627776), (1586102721/1099511627776)), (137/549755813888), by norm_num⟩
  | 9 => ⟨((8083557/4398046511104), (-366467543/1099511627776)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-3361857/8796093022208), (304819133/4398046511104)), (215/17592186044416), by norm_num⟩
  | 11 => ⟨((10168415/140737488355328), (-460984413/35184372088832)), (41/17592186044416), by norm_num⟩
  | 12 => ⟨((-440513/35184372088832), (1278120185/562949953421312)), (115/281474976710656), by norm_num⟩
  | 13 => ⟨((2254821/1125899906842624), (-817777295/2251799813685248)), (297/4503599627370496), by norm_num⟩
  | 14 => ⟨((-10717185/36028797018963968), (1943451519/36028797018963968)), (355/36028797018963968), by norm_num⟩
  | 15 => ⟨((5942869/144115188075855872), (-1077678353/144115188075855872)), (199/144115188075855872), by norm_num⟩
  | 16 => ⟨((-1544731/288230376151711744), (140060571/144115188075855872)), (209/1152921504606846976), by norm_num⟩
  | _ => zero

private def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49426234663349/316912650057057350374175801344), (256665098631/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444799840716585/158456325028528675187087900672), (607781431279/158456325028528675187087900672)), (92439/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472556513683847/9903520314283042199192993792), (1367290463741/19807040628566084398385987584)), (52005/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890031126271319/2475880078570760549798248448), (1452480072613/1237940039285380274899124224)), (1727/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((885848539138401/77371252455336267181195264), (726090415679/38685626227668133590597632)), (27637/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775013925434253/4835703278458516698824704), (680550825275/2417851639229258349412352)), (25915/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314800872528689/151115727451828646838272), (37207691827/9444732965739290427392)), (22681/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944232756846671/37778931862957161709568), (3868408488943/75557863725914323419136)), (73733/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649022018472869/2361183241434822606848), (2900264148795/4722366482869645213696)), (110635/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811070537826089/295147905179352825856), (1993085091313/295147905179352825856)), (152179/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912169778863555/36893488147419103232), (1245043553477/18446744073709551616)), (190309/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227953525393597/1152921504606846976), (2799603594125/4611686018427387904)), (107107/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594874522375623/1152921504606846976), (5594848666999/1152921504606846976)), (214361/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597677942584049/72057594037927936), (2445296329353/72057594037927936)), (187731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492795181296455/36028797018963968), (7326097664219/36028797018963968)), (140963/18014398509481984), by norm_num⟩
  | 3 => ⟨((372674086394579/2251799813685248), (9140506439521/9007199254740992)), (176493/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115399908772287/2251799813685248), (9114871311489/2251799813685248)), (353855/2251799813685248), by norm_num⟩
  | 1 => ⟨((555079414137149/562949953421312), (13608353227965/1125899906842624)), (1065919/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188907900973647/2251799813685248), (26961695301247/1125899906842624)), (2149305/2251799813685248), by norm_num⟩
  | _ => zero

private def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188907900973647/2251799813685248), (26961695301247/1125899906842624)), (8198947915084075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((66452538845113/70368744177664), (26208665401725/562949953421312)), (4281491/2251799813685248), by norm_num⟩
  | 2 => ⟨((1001628151696041/1125899906842624), (99000337495835/1125899906842624)), (265159/70368744177664), by norm_num⟩
  | 3 => ⟨((1764735713020361/2251799813685248), (176146253251441/1125899906842624)), (16589273/2251799813685248), by norm_num⟩
  | 4 => ⟨((1327907617941281/2251799813685248), (552183336970463/2251799813685248)), (31192791/2251799813685248), by norm_num⟩
  | 5 => ⟨((647674005164701/2251799813685248), (325627729075657/1125899906842624)), (52087477/2251799813685248), by norm_num⟩
  | 6 => ⟨((-8263709371535/9007199254740992), (374634750747157/2251799813685248)), (240369361/9007199254740992), by norm_num⟩
  | _ => zero

private def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60180489/33554432), (-711454393/16777216)), (1/16777216), by norm_num⟩, -7, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 16 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 16 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 16 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 16 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 16 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 16 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiBand97.Tile014Terms0
